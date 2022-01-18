use crate::{util, Address, Offset, Process, ProcessId};
use core::{
    convert::Infallible,
    fmt::{self, Debug, Display, Formatter},
};
use Endianness::*;

/// The order in which multi-byte integers (such as `u16`, `u32`, …) are stored.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Endianness {
    /// Little endian. The least significant byte is stored first.
    Le,
    /// Big endian. The most significant byte is stored first.
    Be,
}

impl Display for Endianness {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.pad(match self {
            Self::Le => "little endian",
            Self::Be => "big endian",
        })
    }
}

/// Error while reading memory from another process.
///
/// Possible reasons:
/// - the process is no longer open
/// - the pointer is invalid
/// - other (OS-specific) errors
#[derive(Clone, Copy, Debug)]
pub struct ReadMemoryError {
    pub(crate) process_id: ProcessId,
    pub(crate) address: Address,
    pub(crate) len: usize,
}

impl Display for ReadMemoryError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let Self {
            process_id,
            address,
            len,
        } = self;
        write!(f, "failed reading {len} bytes of memory from process {process_id:#010X} at address {address:#018X}")
    }
}

impl From<ReadAsTypeError<Infallible>> for ReadMemoryError {
    #[inline]
    fn from(err: ReadAsTypeError<Infallible>) -> Self {
        match err {
            ReadAsTypeError::Read(err) => err,
            ReadAsTypeError::AsType(err) => match err {},
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ReadAsTypeError<T: Debug + Display> {
    Read(ReadMemoryError),
    AsType(T),
}

impl<T: Debug + Display> Display for ReadAsTypeError<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read(err) => Display::fmt(err, f),
            Self::AsType(err) => Display::fmt(err, f),
        }
    }
}

impl<T: Debug + Display> From<ReadMemoryError> for ReadAsTypeError<T> {
    #[inline]
    fn from(err: ReadMemoryError) -> Self {
        Self::Read(err)
    }
}

pub type ReadAsTypeResult<T> = Result<T, ReadAsTypeError<<T as ReadMemoryAs>::Error>>;

/// Null pointer error. This happens when trying to read a pointer from another
/// process' memory and the value that is read is zero.
///
/// Trying to dereference that pointer would also lead to an error, but it would
/// be harder to debug because you wouldn't be told the last valid pointer.
#[derive(Clone, Copy, Debug)]
pub struct NullptrError {
    process_id: ProcessId,
    address: Address,
}

impl Display for NullptrError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let Self {
            process_id,
            address,
        } = self;
        write!(f, "found null pointer while reading from process {process_id:#018X} at address {address:#018X}")
    }
}

#[derive(Debug)]
pub enum FollowPathError<T: ReadMemoryAs> {
    Read(ReadMemoryError),
    Follow(NullptrError),
    AsType(T::Error),
}

impl<T: ReadMemoryAs> FollowPathError<T> {
    pub fn from_read_as_type(err: ReadAsTypeError<T::Error>) -> Self {
        match err {
            ReadAsTypeError::Read(err) => Self::Read(err),
            ReadAsTypeError::AsType(err) => Self::AsType(err),
        }
    }
}

impl<T: ReadMemoryAs> Display for FollowPathError<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read(err) => Display::fmt(err, f),
            Self::Follow(err) => Display::fmt(err, f),
            Self::AsType(err) => Display::fmt(err, f),
        }
    }
}

impl<T: ReadMemoryAs> From<ReadMemoryError> for FollowPathError<T> {
    fn from(err: ReadMemoryError) -> Self {
        Self::Read(err)
    }
}

impl<T: ReadMemoryAs> From<ReadAsTypeError<NullptrError>> for FollowPathError<T> {
    fn from(err: ReadAsTypeError<NullptrError>) -> Self {
        match err {
            ReadAsTypeError::Read(err) => Self::Read(err),
            ReadAsTypeError::AsType(err) => Self::Follow(err),
        }
    }
}

pub type FollowPathResult<T> = Result<T, FollowPathError<T>>;

pub trait ReadMemoryAs: Clone + Sized {
    type Error: Debug + Display;

    /// Reads memory from a process at the given address and returns it as this
    /// type.
    fn read_as(process: &Process, endian: Endianness, addr: Address) -> ReadAsTypeResult<Self>;
}

impl<const N: usize> ReadMemoryAs for [u8; N] {
    type Error = Infallible;

    fn read_as(process: &Process, _: Endianness, addr: Address) -> ReadAsTypeResult<Self> {
        // Safety: read_exact doesn't read the buffer. If an error occurs, the
        // buffer isn't returned, otherwise it'll contain valid data.
        let mut buf = unsafe { util::array_assume_init(util::uninit_array::<u8, N>()) };
        if let Err(err) = process.read_exact(addr, &mut buf) {
            Err(ReadAsTypeError::Read(err))
        } else {
            Ok(buf)
        }
    }
}

macro_rules! read_as_int_impl {
    ($($t:ty),+) => {$(
        impl ReadMemoryAs for $t {
            type Error = Infallible;

            fn read_as(
                process: &Process,
                endian: Endianness,
                addr: Address
            ) -> ReadAsTypeResult<Self> {
                let val = Self::from_ne_bytes(ReadMemoryAs::read_as(process, endian, addr)?);

                Ok(match endian {
                    Le => Self::from_le(val),
                    Be => Self::from_be(val),
                })
            }
        }
    )+};
}

read_as_int_impl!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128);

impl ReadMemoryAs for Address {
    type Error = NullptrError;

    fn read_as(process: &Process, endian: Endianness, addr: Address) -> ReadAsTypeResult<Self> {
        Address::new(process.read_memory(endian, addr)?).ok_or_else(|| {
            ReadAsTypeError::AsType(NullptrError {
                process_id: process.process_id(),
                address: addr,
            })
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PointerPath<'a> {
    pub base_offset: Offset,
    pub offsets: &'a [Offset],
}

impl<'a> PointerPath<'a> {
    #[must_use]
    pub fn follower<'b>(
        self,
        process: &'b Process,
        endian: Endianness,
        base: Address,
    ) -> PointerPathFollower<'a, 'b> {
        PointerPathFollower {
            path: self,
            process,
            endian,
            current: util::ptr_offset(base, self.base_offset),
            depth: 0,
        }
    }

    #[inline]
    pub fn follow<'b>(
        self,
        process: &'b Process,
        endian: Endianness,
        base: Address,
    ) -> Result<PointerPathFollower<'a, 'b>, ReadAsTypeError<NullptrError>> {
        let mut follower = self.follower(process, endian, base);
        follower.follow()?;
        Ok(follower)
    }
}

pub struct PointerPathFollower<'a, 'b> {
    path: PointerPath<'a>,
    pub process: &'b Process,
    pub endian: Endianness,
    current: Address,
    depth: usize,
}

impl<'a, 'b> PointerPathFollower<'a, 'b> {
    #[inline]
    #[must_use]
    pub const fn path(&self) -> PointerPath<'a> {
        self.path
    }

    #[inline]
    #[must_use]
    pub const fn current_ptr(&self) -> Address {
        self.current
    }

    #[inline]
    #[must_use]
    pub const fn current_depth(&self) -> usize {
        self.depth
    }

    pub fn set_depth(&mut self, d: usize) {
        assert!(d <= self.path.offsets.len());
        self.depth = d;
    }

    /// # Safety
    ///
    /// The depth must be less than or equal to the path's offset count.
    #[inline]
    pub unsafe fn set_depth_unchecked(&mut self, d: usize) {
        self.depth = d;
    }

    #[inline]
    #[must_use]
    pub fn followed_path(&self) -> &[Offset] {
        // Safety: depth <= offsets.len().
        unsafe { self.path.offsets.get_unchecked(..self.depth) }
    }

    #[inline]
    #[must_use]
    pub fn remaining_offsets(&self) -> &[Offset] {
        // Safety: depth <= offsets.len().
        unsafe { self.path.offsets.get_unchecked(self.depth..) }
    }

    pub fn try_next(&mut self) -> Result<Option<Address>, ReadAsTypeError<NullptrError>> {
        Ok(if let Some(offset) = self.path.offsets.get(self.depth) {
            self.depth += 1;
            let mut addr = self.process.read_ptr(self.endian, self.current)?;
            addr = util::ptr_offset(addr, *offset);

            self.current = addr;
            Some(addr)
        } else {
            None
        })
    }

    #[inline]
    pub fn follow(&mut self) -> Result<&mut Self, ReadAsTypeError<NullptrError>> {
        while self.depth < self.path.offsets.len() {
            self.try_next()?;
        }

        Ok(self)
    }

    #[inline]
    pub fn advance_by(
        &mut self,
        n: usize,
    ) -> Result<Address, (ReadAsTypeError<NullptrError>, usize)> {
        for idx in 0..n {
            self.try_next().map_err(|err| (err, idx))?;
        }

        Ok(self.current)
    }
}

#[macro_export]
macro_rules! pointer_path {
    ($($name:ident: $ty:ty = $base:literal $(, $offset:literal)+;)+) => {
        #[allow(non_upper_case_globals)]
        mod pointer_path {
            pub fn follower(
                process: &$crate::process::Process,
                endian: $crate::mem::Endianness,
                base: $crate::Address,
            ) -> Follower<'_> {
                Follower {
                    process,
                    endian,
                    base,
                }
            }

            pub struct Follower<'a> {
                process: &'a $crate::process::Process,
                endian: $crate::mem::Endianness,
                base: $crate::Address,
            }

            $(
                pub static $name: $crate::mem::PointerPath<'static> = $crate::mem::PointerPath {
                    base_offset: $base,
                    offsets: &[$($offset,)+],
                };

                impl<'a> Follower<'a> {
                    pub fn $name(&self) -> $crate::mem::FollowPathResult<$ty> {
                        ::core::result::Result::map_err(
                            <$ty as $crate::mem::ReadMemoryAs>::read_as(
                                self.process,
                                self.endian,
                                $crate::mem::PointerPath::follow(
                                    $name,
                                    self.process,
                                    self.endian,
                                    self.base,
                                )?
                                .current_ptr(),
                            ),
                            $crate::mem::FollowPathError::from_read_as_type,
                        )
                    }
                }
            )+
        }
    };
}
