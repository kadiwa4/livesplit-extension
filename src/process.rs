//! Other processes.

use crate::{env, mem::NonNullAddress, ProcessId};
use core::num::NonZeroU32;

/// Represents another process.
///
/// This can be used to read memory from a game, which is useful for auto
/// splitters. See [module `mem`](crate::mem);
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Process {
    process_id: ProcessId,
}

impl Process {
    /// Attaches to a process based on its name.
    #[inline]
    #[must_use = "if unused, the process is immediately detached again"]
    pub fn attach(name: &str) -> Option<Self> {
        let process_id = unsafe { env::process_attach(name.as_ptr(), name.len()) };
        debug_assert!(process_id <= u32::MAX as u64);
        let process = Self {
            process_id: ProcessId(NonZeroU32::new(process_id as u32)?),
        };
        Some(process)
    }

    /// The process ID, or PID for short.
    #[inline]
    pub fn id(&self) -> ProcessId {
        self.process_id
    }

    /// Checks whether is a process is still open. You should detach from a
    /// process and stop using it if this returns `false`.
    #[inline]
    pub fn is_open(&self) -> bool {
        unsafe { env::process_is_open(self.process_id.0.into()) }
    }

    /// Gets the address of a module in a process.
    #[inline]
    #[must_use]
    pub fn get_module(&self, name: &str) -> Option<NonNullAddress> {
        unsafe {
            env::process_get_module_address(self.process_id.0.into(), name.as_ptr(), name.len())
        }
    }
}

impl Drop for Process {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            env::process_detach(self.process_id.0.into());
        }
    }
}

/// If called with a process, checks if that process is still open, and if not,
/// sets the `Option` to `None`.
///
/// # Examples
///
/// ```no_run
/// # use livesplit_extension::process::{self, Process};
/// # fn get_state_from_somewhere() -> State { State { process: None } }
/// struct State {
///     process: Option<Process>,
///     // ...
/// }
///
/// // In your loop:
/// let mut state = get_state_from_somewhere();
/// process::check(&mut state.process);
/// ```
#[inline]
pub fn check(process_opt: &mut Option<Process>) {
    if let Some(process) = process_opt {
        if !process.is_open() {
            *process_opt = None;
        }
    }
}
