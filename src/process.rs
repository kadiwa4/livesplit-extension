//! Other processes.

use crate::{
    env,
    mem::{Endianness, ReadAsTypeError, ReadAsTypeResult, ReadMemoryAs, ReadMemoryError},
    util::{self, AsciiError},
    Address, ProcessId,
};
use core::{
    convert::Infallible,
    fmt::{self, Debug, Formatter},
    str::Utf8Error,
};

/// Represents another process.
///
/// This can be used to read memory from a game, which is useful for auto
/// splitters.
#[derive(PartialEq, Eq, Hash)]
pub struct Process {
    process_id: ProcessId,
}

impl Process {
    /// Attaches to a process based on its name.
    #[must_use = "if unused, `Process` is immediately detached again"]
    pub fn attach(name: &str) -> Option<Self> {
        let process_id = unsafe { env::process_attach(name.as_ptr(), name.len()) };
        ProcessId::new(process_id).map(|process_id| Self { process_id })
    }

    /// The process ID, or PID for short.
    #[inline]
    #[must_use]
    pub fn process_id(&self) -> ProcessId {
        self.process_id
    }

    /// Checks whether is a process is still open. You should detach from a
    /// process and stop using it if this returns `false`.
    #[must_use]
    pub fn is_open(&self) -> bool {
        unsafe { env::process_is_open(self.process_id) }
    }

    /// Gets the address of a module in a process.
    #[must_use]
    pub fn get_module(&self, name: &str) -> Option<Address> {
        unsafe { env::process_get_module(self.process_id, name.as_ptr(), name.len()) }
    }

    /// Reads memory from a process at the given address and writes it to the
    /// given buffer. The buffer will not be read.
    pub fn read_exact(&self, addr: Address, buf: &mut [u8]) -> Result<(), ReadMemoryError> {
        let success =
            unsafe { env::process_read(self.process_id, addr, buf.as_mut_ptr(), buf.len()) };
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
    pub fn read_array<const N: usize>(&self, addr: Address) -> Result<[u8; N], ReadMemoryError> {
        // Safety: read_exact doesn't read the buffer. If an error occurs, the
        // buffer isn't returned, otherwise it'll contain valid data.
        let mut buf = unsafe { util::array_assume_init(util::uninit_array::<u8, N>()) };
        self.read_exact(addr, &mut buf)?;
        Ok(buf)
    }

    /// Reads memory from a process at the given address and returns it as
    /// an [`Address`].
    #[inline]
    pub fn read_ptr(&self, endian: Endianness, addr: Address) -> ReadAsTypeResult<Address> {
        Address::read_as(self, endian, addr)
    }

    /// Reads memory from a process at the given address and returns it as a `u8`.
    #[inline]
    pub fn read_u8(&self, addr: Address) -> Result<u8, ReadMemoryError> {
        self.read_memory(Endianness::Le, addr)
    }

    /// Reads memory from a process at the given address and returns it as a `i8`.
    #[inline]
    pub fn read_i8(&self, addr: Address) -> Result<i8, ReadMemoryError> {
        self.read_memory(Endianness::Le, addr)
    }

    pub fn read_utf8_c_str<'a>(
        &self,
        addr: Address,
        buf: &'a mut [u8],
    ) -> Result<&'a str, ReadAsTypeError<Utf8Error>> {
        self.read_exact(addr, buf)?;
        let len = buf.iter().position(|b| *b == b'\0').unwrap_or(buf.len());
        core::str::from_utf8(unsafe { buf.get_unchecked(..len) }).map_err(ReadAsTypeError::AsType)
    }

    pub fn read_ascii_c_str<'a>(
        &self,
        addr: Address,
        buf: &'a mut [u8],
    ) -> Result<&'a str, ReadAsTypeError<AsciiError>> {
        self.read_exact(addr, buf)?;
        let len = buf.iter().position(|b| *b == b'\0').unwrap_or(buf.len());
        util::str_from_ascii(unsafe { buf.get_unchecked(..len) }).map_err(ReadAsTypeError::AsType)
    }

    #[inline]
    pub fn read_as<T: ReadMemoryAs>(
        &self,
        endian: Endianness,
        addr: Address,
    ) -> ReadAsTypeResult<T> {
        T::read_as(self, endian, addr)
    }

    #[inline]
    pub fn read_memory<T: ReadMemoryAs<Error = Infallible>>(
        &self,
        endian: Endianness,
        addr: Address,
    ) -> Result<T, ReadMemoryError> {
        Ok(T::read_as(self, endian, addr)?)
    }
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
