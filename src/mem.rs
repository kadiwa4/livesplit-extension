//! Operations on a [`Process`]'s memory.

use crate::{
    env,
    process::Process,
    util::{self, StringBuf},
    Address, Offset, ProcessId,
};
use core::{
    fmt::{self, Debug, Display, Formatter},
    marker::PhantomData,
};

/// The order in which multi-byte integers (such as `u16`, `u32`, …) are stored.
/// Note that this might differ from WebAssembly's endianness, because it is not
/// related to that of your computer.
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
/// - The process is no longer open.
/// - The pointer is invalid.
/// - Other (OS-specific) errors.
#[derive(Clone, Copy, Debug)]
pub struct ReadMemoryError {
    process_id: ProcessId,
    address: Address,
    len: usize,
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
        write!(f, "found null pointer while reading from process {process_id:#010X} at address {address:#018X}")
    }
}

/// Error while reading a pointer from another process.
#[derive(Clone, Copy, Debug)]
pub enum ReadPtrError {
    /// A [`ReadMemoryError`] occurred.
    Read(ReadMemoryError),
    /// The pointer that was read was null pointer.
    Nullptr(NullptrError),
}

impl Display for ReadPtrError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read(err) => Display::fmt(err, f),
            Self::Nullptr(err) => Display::fmt(err, f),
        }
    }
}

impl From<ReadMemoryError> for ReadPtrError {
    #[inline]
    fn from(err: ReadMemoryError) -> Self {
        Self::Read(err)
    }
}

impl From<NullptrError> for ReadPtrError {
    #[inline]
    fn from(err: NullptrError) -> Self {
        Self::Nullptr(err)
    }
}

/// Contains the information necessary for reading memory.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemoryReader<'a> {
    /// The process to extract information from.
    pub process: &'a Process,
    /// The computer's endianness.
    pub endian: Endianness,
    /// The base address. Consider using [`Process::get_module`] to get this
    /// value.
    pub base: Address,
}

impl<'a> MemoryReader<'a> {
    /// Reads memory from a process at the given address and writes it to the
    /// buffer. The [`MemoryReader`]'s `base` address is ignored. The buffer
    /// will not be read.
    pub fn read_buf(self, addr: Address, buf: &mut [u8]) -> Result<(), ReadMemoryError> {
        let success =
            unsafe { env::process_read(self.process.id(), addr, buf.as_mut_ptr(), buf.len()) };
        if success {
            Ok(())
        } else {
            Err(ReadMemoryError {
                process_id: self.process.id(),
                address: addr,
                len: buf.len(),
            })
        }
    }

    /// Reads memory from a process at the given address and returns it as a
    /// specific type. The [`MemoryReader`]'s `base` address is ignored.
    #[inline]
    pub fn read<T: FromMemory>(self, addr: Address) -> Result<T, T::Error> {
        T::read_from(self, addr)
    }

    /// Reads memory from a process at the given address and returns it as an
    /// [`Address`]. The [`MemoryReader`]'s `base` address is ignored.
    #[inline]
    pub fn read_ptr(self, addr: Address) -> Result<Address, ReadPtrError> {
        Address::read_from(self, addr)
    }

    /// Reads memory from a process at the given address and returns it as an
    /// array. The [`MemoryReader`]'s `base` address is ignored.
    #[inline]
    pub fn read_array<const N: usize>(self, addr: Address) -> Result<[u8; N], ReadMemoryError> {
        <[u8; N]>::read_from(self, addr)
    }
}

/// Indicates that the type can be extracted from another process' memory.
pub trait FromMemory: Clone + Sized {
    type Error: Debug + Display;

    /// Reads memory from a process at the given address and returns it as a
    /// specific type. The [`MemoryReader`]'s `base` address is ignored.
    fn read_from(reader: MemoryReader<'_>, addr: Address) -> Result<Self, Self::Error>;
}

impl<const N: usize> FromMemory for [u8; N] {
    type Error = ReadMemoryError;

    fn read_from(reader: MemoryReader<'_>, addr: Address) -> Result<Self, Self::Error> {
        // Safety: read_exact doesn't read the buffer. If an error occurs, the
        // buffer isn't returned, otherwise it'll contain valid data.
        let mut buf = unsafe { util::array_assume_init(util::uninit_array::<u8, N>()) };
        reader.read_buf(addr, &mut buf)?;
        Ok(buf)
    }
}

macro_rules! read_as_int_impl {
    ($($t:ty),+) => {$(
        impl FromMemory for $t {
            type Error = ReadMemoryError;

            fn read_from(reader: MemoryReader<'_>, addr: Address) -> Result<Self, Self::Error> {
                let val = Self::from_ne_bytes(FromMemory::read_from(reader, addr)?);

                Ok(match reader.endian {
                    Endianness::Le => Self::from_le(val),
                    Endianness::Be => Self::from_be(val),
                })
            }
        }
    )+};
}

read_as_int_impl!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128);

impl FromMemory for Address {
    type Error = ReadPtrError;

    fn read_from(reader: MemoryReader<'_>, addr: Address) -> Result<Self, Self::Error> {
        Self::new(FromMemory::read_from(reader, addr)?).ok_or_else(|| {
            ReadPtrError::Nullptr(NullptrError {
                process_id: reader.process.id(),
                address: addr,
            })
        })
    }
}

impl<const N: usize> FromMemory for StringBuf<N> {
    type Error = ReadMemoryError;

    #[inline]
    fn read_from(reader: MemoryReader<'_>, addr: Address) -> Result<Self, Self::Error> {
        <[u8; N]>::read_from(reader, addr).map(StringBuf)
    }
}

/// TODO: Documentation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PointerPath<'a, T: FromMemory> {
    pub base_offset: Offset,
    pub offsets: &'a [Offset],
    pub marker: PhantomData<*const T>,
}

impl<'a, T: FromMemory> PointerPath<'a, T> {
    #[inline]
    #[must_use]
    pub fn walker<'b>(self, reader: MemoryReader<'b>) -> PointerPathWalker<'a, 'b, T> {
        PointerPathWalker {
            path: self,
            reader,
            current: util::ptr_offset(reader.base, self.base_offset),
            depth: 0,
        }
    }

    #[inline]
    pub fn walk(self, reader: MemoryReader<'_>) -> Result<PointerPathEnd<'_, T>, ReadPtrError> {
        self.walker(reader).walk()
    }
}

impl<'a, T: FromMemory> Copy for PointerPath<'a, T> {}
unsafe impl<'a, T: FromMemory> Send for PointerPath<'a, T> {}
unsafe impl<'a, T: FromMemory> Sync for PointerPath<'a, T> {}

/// Follows a [pointer path] by repeatedly reading the current pointer and
/// adding an offset. The first address will be the [`MemoryReader`]'s `base`
/// address, offset by the pointer path's `base_offset`. The reader can be
/// changed at any time.
///
/// [pointer path]: PointerPath
#[derive(Clone, Debug)]
pub struct PointerPathWalker<'a, 'b, T: FromMemory> {
    path: PointerPath<'a, T>,
    pub reader: MemoryReader<'b>,
    current: Address,
    depth: usize,
}

impl<'a, 'b, T: FromMemory> PointerPathWalker<'a, 'b, T> {
    /// The whole pointer path that this is walking.
    #[inline]
    #[must_use]
    pub fn path(&self) -> PointerPath<'a, T> {
        self.path
    }

    /// The current pointer.
    #[inline]
    #[must_use]
    pub fn current_ptr(&self) -> Address {
        self.current
    }

    /// Indicates how far the path has been walked. Always less than or equal to
    /// `offsets.len()`. This is the same as `walked_offsets().len()`.
    #[inline]
    #[must_use]
    pub fn current_depth(&self) -> usize {
        self.depth
    }

    /// The pointer path offsets that have been applied so far, excluding the
    /// `base_offset`.
    #[inline]
    #[must_use]
    pub fn walked_offsets(&self) -> &[Offset] {
        // Safety: depth <= offsets.len().
        unsafe { self.path.offsets.get_unchecked(..self.depth) }
    }

    /// The pointer path offsets that have not been applied yet.
    #[inline]
    #[must_use]
    pub fn remaining_offsets(&self) -> &[Offset] {
        // Safety: depth <= offsets.len().
        unsafe { self.path.offsets.get_unchecked(self.depth..) }
    }

    /// Dereferences the current pointer and applies the next offset. Returns
    /// the pointer path end if it has been reached.
    pub fn advance(&mut self) -> Result<Option<PointerPathEnd<'b, T>>, ReadPtrError> {
        Ok(if let Some(offset) = self.path.offsets.get(self.depth) {
            self.depth += 1;
            let mut addr = self.reader.read_ptr(self.current)?;
            addr = util::ptr_offset(addr, *offset);

            self.current = addr;
            None
        } else {
            Some(self.end())
        })
    }

    /// Dereferences the pointer and applies the next offset `n` times. Returns
    /// the pointer path end if it has been reached.
    ///
    /// # Errors
    ///
    /// Returns the error and the number of successful iterations on failure.
    #[inline]
    pub fn advance_by(
        &mut self,
        n: usize,
    ) -> Result<Option<PointerPathEnd<'b, T>>, (ReadPtrError, usize)> {
        for idx in 0..n {
            if let Some(end) = self.advance().map_err(|err| (err, idx))? {
                return Ok(Some(end));
            }
        }

        Ok(None)
    }

    /// Dereferences the pointer and applies the next offset until the end is
    /// reached.
    #[inline]
    pub fn walk(&mut self) -> Result<PointerPathEnd<'b, T>, ReadPtrError> {
        while self.depth < self.path.offsets.len() {
            self.advance()?;
        }

        Ok(self.end())
    }

    #[inline]
    fn end(&self) -> PointerPathEnd<'b, T> {
        PointerPathEnd {
            reader: self.reader,
            addr: self.current,
            marker: PhantomData,
        }
    }
}

/// The result of walking a [`PointerPath`]. The value at this address can be
/// read more than once but it might become invalid if the pointer path changes.
#[derive(Clone, Debug)]
pub struct PointerPathEnd<'a, T: FromMemory> {
    pub reader: MemoryReader<'a>,
    addr: Address,
    marker: PhantomData<*const T>,
}

impl<'a, T: FromMemory> PointerPathEnd<'a, T> {
    /// Reads the value at the end of the [`PointerPath`]. It can be read more
    /// than once but it might become invalid if the pointer path changes.
    #[inline]
    pub fn read(&self) -> Result<T, T::Error> {
        T::read_from(self.reader, self.addr)
    }

    /// The final pointer of a [`PointerPath`]. It can be read from more
    /// than once but it might become invalid if the pointer path changes.
    #[inline]
    #[must_use]
    pub fn address(&self) -> Address {
        self.addr
    }
}

#[macro_export]
macro_rules! pointer_path {
    ($($vis:vis $name:ident: $ty:ty = $base:literal $(, $offset:literal)+;)+) => {$(
        $vis static $name: $crate::mem::PointerPath<'static, $ty> = $crate::mem::PointerPath {
            base_offset: $base,
            offsets: &[$($offset,)+],
            marker: ::core::marker::PhantomData,
        };
    )+};
}
