//! Operations on a [`Process`]'s memory.

use crate::{
    env,
    process::Process,
    util::{self, StringBuf},
    Address, Address32, Address64, Offset, ProcessId,
};
use core::{
    fmt::{self, Debug, Display, Formatter},
    marker::PhantomData,
};

/// The order in which multi-byte integers (such as `u16`, `u32`, …) are stored.
///
/// You probably want little endian.
///
/// Note that this might differ from WebAssembly's endianness, because it is not
/// related to that of your computer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Endianness {
    /// Little endian. The least significant byte is stored first.
    Le,
    /// Big endian. The most significant byte is stored first.
    Be,
}

impl Default for Endianness {
    #[inline]
    fn default() -> Self {
        Self::Le
    }
}

impl Display for Endianness {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.pad(match self {
            Self::Le => "little endian",
            Self::Be => "big endian",
        })
    }
}

/// How many bits a pointer takes up.
///
/// You probably want 64 bits.
///
/// Note that this might differ from WebAssembly's pointer width, because it is
/// not related to that of your computer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PointerWidth {
    /// 32 bits.
    U32,
    /// 64 bits.
    U64,
}

impl Default for PointerWidth {
    #[inline]
    fn default() -> Self {
        Self::U64
    }
}

/// Indicates that the type can be extracted from another process' memory.
pub trait FromMemory: Clone {
    /// Implements `std::error::Error` if available and `Debug + Display` otherwise.
    #[cfg(feature = "std")]
    type Error: std::error::Error;
    /// Implements `std::error::Error` if available and `Debug + Display` otherwise.
    #[cfg(not(feature = "std"))]
    type Error: Debug + Display;

    /// Reads memory from a process at the given address and returns it as a
    /// specific type. The [`MemoryReader`]'s `base` address is ignored.
    fn read_from(reader: &MemoryReader<'_>, addr: Address) -> Result<Self, Self::Error>;
}

impl<const N: usize> FromMemory for [u8; N] {
    type Error = ReadMemoryError;

    fn read_from(reader: &MemoryReader<'_>, addr: Address) -> Result<Self, Self::Error> {
        let mut buf = util::uninit_array::<u8, N>();
        unsafe {
            reader.read_raw(addr, buf.as_mut_ptr().cast(), buf.len())?;
        }

        Ok(unsafe { util::array_assume_init(buf) })
    }
}

macro_rules! int_from_memory_impl {
    ($($t:ty),+) => {$(
        impl FromMemory for $t {
            type Error = ReadMemoryError;

            fn read_from(reader: &MemoryReader<'_>, addr: Address) -> Result<Self, Self::Error> {
                let val = Self::from_ne_bytes(FromMemory::read_from(reader, addr)?);

                Ok(match reader.endian {
                    Endianness::Le => Self::from_le(val),
                    Endianness::Be => Self::from_be(val),
                })
            }
        }
    )+};
}

int_from_memory_impl!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128);

impl FromMemory for Address32 {
    type Error = ReadPtrError;

    fn read_from(reader: &MemoryReader<'_>, addr: Address) -> Result<Self, Self::Error> {
        Self::new(u32::read_from(reader, addr)?).ok_or_else(|| {
            ReadPtrError::Nullptr(NullptrError {
                process_id: reader.process.id(),
                address: addr,
            })
        })
    }
}

impl FromMemory for Address64 {
    type Error = ReadPtrError;

    fn read_from(reader: &MemoryReader<'_>, addr: Address) -> Result<Self, Self::Error> {
        Self::new(u64::read_from(reader, addr)?).ok_or_else(|| {
            ReadPtrError::Nullptr(NullptrError {
                process_id: reader.process.id(),
                address: addr,
            })
        })
    }
}

impl FromMemory for bool {
    type Error = ReadMemoryError;

    fn read_from(reader: &MemoryReader<'_>, addr: Address) -> Result<Self, Self::Error> {
        <[u8; 1]>::read_from(reader, addr).map(|[n]| n != 0)
    }
}

impl<const N: usize> FromMemory for StringBuf<N> {
    type Error = ReadMemoryError;

    fn read_from(reader: &MemoryReader<'_>, addr: Address) -> Result<Self, Self::Error> {
        <[u8; N]>::read_from(reader, addr).map(StringBuf)
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

#[cfg(feature = "std")]
impl std::error::Error for ReadMemoryError {}

impl Display for ReadMemoryError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let Self {
            process_id,
            address,
            len,
        } = self;
        write!(
            f,
            "failed reading {len} bytes of memory from process {process_id} at {address:#018X}"
        )
    }
}

impl From<ReadMemoryError> for crate::Error {
    #[inline]
    fn from(err: ReadMemoryError) -> Self {
        Self::ReadMemory(err)
    }
}

/// Null pointer error. This happens when trying to read a pointer from another
/// process' memory and the value that is read is zero.
///
/// Trying to dereference that pointer would also lead to an error, but it would
/// be harder to debug because you wouldn't know the last valid pointer.
#[derive(Clone, Copy, Debug)]
pub struct NullptrError {
    process_id: ProcessId,
    address: Address,
}

#[cfg(feature = "std")]
impl std::error::Error for NullptrError {}

impl Display for NullptrError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let Self {
            process_id,
            address,
        } = self;
        write!(
            f,
            "found null pointer while reading from process {process_id} at {address:#018X}"
        )
    }
}

impl From<NullptrError> for crate::Error {
    #[inline]
    fn from(err: NullptrError) -> Self {
        Self::Nullptr(err)
    }
}

/// Error while reading a pointer from another process.
#[derive(Clone, Copy, Debug)]
pub enum ReadPtrError {
    /// A [`ReadMemoryError`] occurred.
    ReadMemory(ReadMemoryError),
    /// The pointer that was read was null pointer.
    Nullptr(NullptrError),
}

#[cfg(feature = "std")]
impl std::error::Error for ReadPtrError {}

impl Display for ReadPtrError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReadMemory(err) => Display::fmt(err, f),
            Self::Nullptr(err) => Display::fmt(err, f),
        }
    }
}

impl From<ReadMemoryError> for ReadPtrError {
    #[inline]
    fn from(err: ReadMemoryError) -> Self {
        Self::ReadMemory(err)
    }
}

impl From<NullptrError> for ReadPtrError {
    #[inline]
    fn from(err: NullptrError) -> Self {
        Self::Nullptr(err)
    }
}

impl From<ReadPtrError> for crate::Error {
    #[inline]
    fn from(err: ReadPtrError) -> Self {
        match err {
            ReadPtrError::ReadMemory(err) => Self::ReadMemory(err),
            ReadPtrError::Nullptr(err) => Self::Nullptr(err),
        }
    }
}

/// Contains the information necessary for reading memory.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemoryReader<'a> {
    /// The process to extract information from.
    pub process: &'a Process,
    /// The computer's endianness.
    pub endian: Endianness,
    /// The process' pointer width.
    pub ptr_width: PointerWidth,
    /// The base address. Consider using [`Process::get_module`] to get this
    /// value.
    pub base: Address,
}

impl<'a> MemoryReader<'a> {
    /// In most cases, you want little endian, 64-bit pointers.
    /// This is a convenience function that uses those default settings.
    #[inline]
    pub const fn new_default(process: &'a Process, base: Address) -> Self {
        Self {
            process,
            endian: Endianness::Le,
            ptr_width: PointerWidth::U64,
            base,
        }
    }

    /// Reads memory from a process at the given address and writes it to the
    /// buffer. The [`MemoryReader`]'s `base` address is ignored. The buffer
    /// will not be read.
    pub fn read_buf(&self, addr: Address, buf: &mut [u8]) -> Result<(), ReadMemoryError> {
        unsafe { self.read_raw(addr, buf.as_mut_ptr(), buf.len()) }
    }

    /// # Safety
    ///
    /// The pointer has to be valid.
    unsafe fn read_raw(
        &self,
        addr: Address,
        buf_ptr: *mut u8,
        buf_len: usize,
    ) -> Result<(), ReadMemoryError> {
        let success = env::process_read(self.process.id().into(), addr, buf_ptr, buf_len);
        if success {
            Ok(())
        } else {
            Err(ReadMemoryError {
                process_id: self.process.id(),
                address: addr,
                len: buf_len,
            })
        }
    }

    /// Reads memory from a process at the given address and returns it as a
    /// specific type. The [`MemoryReader`]'s `base` address is ignored.
    pub fn read<T: FromMemory>(&self, addr: Address) -> Result<T, T::Error> {
        T::read_from(self, addr)
    }

    /// Reads memory from a process at the given address as an [`Address32`] or
    /// [`Address64`] and returns it as an [`Address`]. The [`MemoryReader`]'s
    /// `base` address is ignored.
    pub fn read_ptr(&self, addr: Address) -> Result<Address, ReadPtrError> {
        match self.ptr_width {
            PointerWidth::U32 => Ok(Address32::read_from(self, addr)?.into()),
            PointerWidth::U64 => Address64::read_from(self, addr),
        }
    }

    /// Reads memory from a process at the given address and returns it as an
    /// array. The [`MemoryReader`]'s `base` address is ignored.
    pub fn read_array<const N: usize>(&self, addr: Address) -> Result<[u8; N], ReadMemoryError> {
        <[u8; N]>::read_from(self, addr)
    }
}

/// A list of pointer offsets.
///
/// LiveSplit reads the value at `base + offsets[0]` and interprets the value
/// as yet another address. It adds the next offset to this address and reads
/// the value of the calculated address. It does this over and over until there
/// are no more offsets. (Note that the value at the end will not be treated as
/// a pointer and not be dereferenced.) At that point, it has found the value it was searching
/// for. This resembles the way objects are stored in memory. Every object has a
/// clearly defined layout where each variable has a consistent offset within
/// the object, so you basically follow these variables from object to object.
///
/// _[Cheat Engine]_ is a tool that allows you to find addresses and pointer
/// paths for those addresses.
///
/// Source: [LiveSplit Auto Splitter Documentation][asl-docs]
///
/// See the [`pointer_path`] macro for prettier definitions.
///
/// # Examples
///
/// ```no_run
/// # use core::marker::PhantomData;
/// # use livesplit_extension::{mem::{MemoryReader, PointerPath}, Error};
/// static IS_LOADING: PointerPath<'_, bool> = PointerPath {
///     offsets: &[0x04BA_9DC8, 0x48, 0, 0x60],
///     marker: PhantomData,
/// };
///
/// fn is_loading(reader: MemoryReader<'_>) -> Result<bool, Error> {
///     Ok(IS_LOADING.walk(reader)?.read()?)
/// }
/// ```
///
/// [Cheat Engine]: https://www.cheatengine.org
/// [asl-docs]: https://github.com/LiveSplit/LiveSplit.AutoSplitters#pointer-paths
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PointerPath<'a, T: FromMemory> {
    pub offsets: &'a [Offset],
    pub marker: PhantomData<*const T>,
}

impl<'a, T: FromMemory> PointerPath<'a, T> {
    #[inline]
    pub fn walker(self, reader: MemoryReader<'a>) -> PointerPathWalker<'a, T> {
        PointerPathWalker {
            path: self,
            reader,
            current: reader.base,
            depth: 0,
        }
    }

    pub fn walk(self, reader: MemoryReader<'a>) -> Result<PointerPathEnd<'a, T>, ReadPtrError> {
        self.walker(reader).walk()
    }
}

impl<'a, T: FromMemory> Copy for PointerPath<'a, T> {}
unsafe impl<'a, T: FromMemory> Send for PointerPath<'a, T> {}
unsafe impl<'a, T: FromMemory> Sync for PointerPath<'a, T> {}

/// Follows a [pointer path] by repeatedly adding an offset to the current
/// pointer and reading a new address. The first address will be the
/// [`MemoryReader`]'s `base` address with the first offset. The reader can be
/// changed at any time.
///
/// [pointer path]: PointerPath
#[must_use = "pointer path walkers are lazy and do nothing unless walked"]
#[derive(Clone, Debug)]
pub struct PointerPathWalker<'a, T: FromMemory> {
    path: PointerPath<'a, T>,
    pub reader: MemoryReader<'a>,
    current: Address,
    depth: usize,
}

impl<'a, T: FromMemory> PointerPathWalker<'a, T> {
    /// The whole pointer path that this is walking.
    #[inline]
    pub fn path(&self) -> PointerPath<'a, T> {
        self.path
    }

    /// The current pointer (without an offset).
    #[inline]
    pub fn current_ptr(&self) -> Address {
        self.current
    }

    /// Indicates how far the path has been walked. Always less than or equal to
    /// `offsets.len()`. This is the same as `walked_offsets().len()`.
    #[inline]
    pub fn current_depth(&self) -> usize {
        self.depth
    }

    /// The pointer path offsets that have been applied so far.
    #[inline]
    pub fn walked_offsets(&self) -> &[Offset] {
        // Safety: depth <= offsets.len().
        unsafe { self.path.offsets.get_unchecked(..self.depth) }
    }

    /// The pointer path offsets that have not been applied yet.
    #[inline]
    pub fn remaining_offsets(&self) -> &[Offset] {
        // Safety: depth <= offsets.len().
        unsafe { self.path.offsets.get_unchecked(self.depth..) }
    }

    /// Applies the next offset. Returns the pointer path end if it has been
    /// reached. Otherwise dereferences the resulting pointer.
    pub fn advance(&mut self) -> Result<Option<PointerPathEnd<'a, T>>, ReadPtrError> {
        if let Some(offset) = self.path.offsets.get(self.depth) {
            self.depth += 1;
            self.current = util::ptr_offset(self.current, *offset);
            if self.depth != self.path.offsets.len() {
                self.current = self.reader.read_ptr(self.current)?;
                return Ok(None);
            }
        }

        let end = PointerPathEnd {
            reader: self.reader,
            addr: self.current,
            marker: PhantomData,
        };

        Ok(Some(end))
    }

    /// Applies the next offset and dereferences the resulting pointer `n`
    /// times. Returns the pointer path end if it has been reached.
    ///
    /// # Errors
    ///
    /// Returns the error and the number of successful iterations on failure.
    pub fn advance_by(
        &mut self,
        n: usize,
    ) -> Result<Option<PointerPathEnd<'a, T>>, (ReadPtrError, usize)> {
        for idx in 0..n {
            if let Some(end) = self.advance().map_err(|err| (err, idx))? {
                return Ok(Some(end));
            }
        }

        Ok(None)
    }

    /// Applies the next offset and dereferences the resulting pointer
    /// repeatedly until the end is reached.
    pub fn walk(&mut self) -> Result<PointerPathEnd<'a, T>, ReadPtrError> {
        loop {
            if let Some(end) = self.advance()? {
                return Ok(end);
            }
        }
    }
}

/// The result of walking a [`PointerPath`]. The value at this address can be
/// read more than once but it might become invalid if the pointer path changes.
#[derive(Clone, Debug)]
pub struct PointerPathEnd<'a, T> {
    pub reader: MemoryReader<'a>,
    addr: Address,
    marker: PhantomData<*const T>,
}

impl<'a, T> PointerPathEnd<'a, T> {
    /// The final pointer of a [`PointerPath`]. It can be read from more
    /// than once but it might become invalid if the pointer path changes.
    #[inline]
    pub fn address(&self) -> Address {
        self.addr
    }
}

impl<'a, T: FromMemory> PointerPathEnd<'a, T> {
    /// Reads the value at the end of the [`PointerPath`]. It can be read more
    /// than once but it might become invalid if the pointer path changes.
    pub fn read(&self) -> Result<T, T::Error> {
        T::read_from(&self.reader, self.addr)
    }

    /// Reads the value at the end of the [`PointerPath`] as an [`Address32`] or
    /// [`Address64`] and returns it as an [`Address`]. It can be read more than
    /// once but it might become invalid if the pointer path changes.
    pub fn read_ptr(&self) -> Result<Address, ReadPtrError> {
        self.reader.read_ptr(self.addr)
    }
}

unsafe impl<'a, T> Send for PointerPathEnd<'a, T> {}
unsafe impl<'a, T> Sync for PointerPathEnd<'a, T> {}

/// Makes pointer path definitions more readable. This is the same as declaring
/// one or more static [`PointerPath`]s.
///
/// # Syntax
///
/// ```text
/// pointer_path! {
///     [<visibility>] NAME: TargetType = <offset1>, <offset2>, [...];
///     [...];
/// }
/// ```
///
/// # Example
///
/// ```no_run
/// # use livesplit_extension::pointer_path;
/// pointer_path! {
///     IS_LOADING: bool = 0x04BA_9DC8, 0x48, 0, 0x60;
/// }
/// ```
#[macro_export]
macro_rules! pointer_path {
    ($($vis:vis $name:ident: $ty:ty = $($offset:literal),+;)+) => {$(
        $vis static $name: $crate::mem::PointerPath<'static, $ty> = $crate::mem::PointerPath {
            offsets: &[$($offset,)+],
            marker: ::core::marker::PhantomData,
        };
    )+};
}
