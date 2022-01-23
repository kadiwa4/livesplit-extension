//! Other processes.

use crate::{env, Address, ProcessId};
use core::fmt::{self, Debug, Formatter};

/// Represents another process.
///
/// This can be used to read memory from a game, which is useful for auto
/// splitters. See [`mem`](crate::mem);
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
    pub const fn id(&self) -> ProcessId {
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
}

impl Debug for Process {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        struct Hex(u64);

        impl Debug for Hex {
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                write!(f, "{:#010X}", self.0)
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
