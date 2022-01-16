//! Other processes.

use crate::{env, util};
use core::{
    fmt::{self, Debug, Display, Formatter},
    num::NonZeroU64,
};

/// Error while reading memory from another process.
///
/// Possible reasons:
/// - the process is no longer open
/// - the pointer is invalid
/// - other (OS-specific) errors
#[derive(Clone, Copy, Debug)]
pub struct ReadMemoryError {
    process_id: NonZeroU64,
    address: NonZeroU64,
    len: usize,
}

impl Display for ReadMemoryError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let Self {
            process_id,
            address,
            len,
        } = self;
        write!(f, "failed reading {len} bytes of memory from process {process_id:#018X} at address {address:#018X}")
    }
}

/// Null pointer error. This happens when trying to read a pointer from another
/// process' memory and the value that is read is zero.
///
/// Trying to dereference that pointer would also lead to an error, but it would
/// be harder to debug because you wouldn't be told the last valid pointer.
#[derive(Clone, Copy, Debug)]
pub struct NullptrError {
    process_id: NonZeroU64,
    address: NonZeroU64,
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

/// Error returned by [`Process::read_ptr`].
#[derive(Clone, Copy, Debug)]
pub enum ReadPtrError {
    Nullptr(NullptrError),
    ReadMemory(ReadMemoryError),
}

impl Display for ReadPtrError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Nullptr(err) => Display::fmt(&err, f),
            Self::ReadMemory(err) => Display::fmt(&err, f),
        }
    }
}

impl From<ReadMemoryError> for ReadPtrError {
    fn from(err: ReadMemoryError) -> Self {
        Self::ReadMemory(err)
    }
}

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

macro_rules! read_int_impl {
    ($($f:ident<$t:ty>,)+) => {$(
        /// Reads memory from a process at the given address and returns it as
        #[doc = concat!("a `", stringify!($t), "`.")]
        pub fn $f(&self, end: Endianness, addr: NonZeroU64) -> Result<$t, ReadMemoryError> {
            self.read_array(addr).map(match end {
                Endianness::Le => <$t>::from_le_bytes,
                Endianness::Be => <$t>::from_be_bytes,
            })
        }
    )+};
}

/// Represents another process.
///
/// This can be used to read memory from a game, which is useful for auto
/// splitters.
#[derive(PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct Process {
    pub process_id: NonZeroU64,
}

impl Process {
    /// Attaches to a process based on its name.
    #[must_use = "if unused, `Process` is immediately detached again"]
    pub fn attach(name: &str) -> Option<Self> {
        let process_id = unsafe { env::process_attach(name.as_ptr(), name.len()) };
        NonZeroU64::new(process_id).map(|process_id| Self { process_id })
    }

    /// Checks whether is a process is still open. You should detach from a
    /// process and stop using it if this returns `false`.
    #[must_use]
    pub fn is_open(&self) -> bool {
        unsafe { env::process_is_open(self.process_id) }
    }

    /// Gets the address of a module in a process.
    #[must_use]
    pub fn get_module(&self, name: &str) -> Option<NonZeroU64> {
        unsafe { env::process_get_module(self.process_id, name.as_ptr(), name.len()) }
    }

    /// Reads memory from a process at the given address and writes it to the
    /// given buffer. The buffer will not be read.
    pub fn read_exact(&self, addr: NonZeroU64, buf: &mut [u8]) -> Result<(), ReadMemoryError> {
        let success =
            unsafe { env::process_read(self.process_id, addr.get(), buf.as_mut_ptr(), buf.len()) };
        if success {
            Ok(())
        } else {
            Err(ReadMemoryError {
                process_id: self.process_id,
                address: addr,
                len: buf.len(),
            })
        }
    }

    /// Reads memory from a process at the given address and returns it as an
    /// array.
    pub fn read_array<const N: usize>(&self, addr: NonZeroU64) -> Result<[u8; N], ReadMemoryError> {
        // Safety: read_exact doesn't read the buffer. If an error occurs, the
        // buffer isn't returned, otherwise it'll contain valid data.
        let mut buf = unsafe { util::array_assume_init(util::uninit_array::<u8, N>()) };
        self.read_exact(addr, &mut buf)?;
        Ok(buf)
    }

    /// Reads memory from a process at the given address and returns it as
    /// a [`NonZeroU64`].
    pub fn read_ptr(&self, end: Endianness, addr: NonZeroU64) -> Result<NonZeroU64, ReadPtrError> {
        let array = self.read_array(addr)?;
        NonZeroU64::new(match end {
            Endianness::Le => u64::from_le_bytes(array),
            Endianness::Be => u64::from_be_bytes(array),
        })
        .ok_or(ReadPtrError::Nullptr(NullptrError {
            process_id: self.process_id,
            address: addr,
        }))
    }

    /// Reads memory from a process at the given address and returns it as a `u8`.
    pub fn read_u8(&self, addr: NonZeroU64) -> Result<u8, ReadMemoryError> {
        self.read_array(addr).map(u8::from_ne_bytes)
    }

    /// Reads memory from a process at the given address and returns it as a `i8`.
    pub fn read_i8(&self, addr: NonZeroU64) -> Result<i8, ReadMemoryError> {
        self.read_array(addr).map(i8::from_ne_bytes)
    }

    read_int_impl!(
        read_u16<u16>,
        read_u32<u32>,
        read_u64<u64>,
        read_u128<u128>,
        read_i16<i16>,
        read_i32<i32>,
        read_i64<i64>,
        read_i128<i128>,
    );
}

impl Debug for Process {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        struct Hex(u64);

        impl Debug for Hex {
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                write!(f, "{:#018X}", self.0)
            }
        }

        f.debug_tuple("Process")
            .field(&Hex(self.process_id.get()))
            .finish()
    }
}

impl Drop for Process {
    fn drop(&mut self) {
        unsafe {
            env::process_detach(self.process_id);
        }
    }
}
