//! Convenience library for the LiveSplit WebAssembly extension API.
//! You need to provide an `update` function as follows:
//!
//! ```no_run
//! #[no_mangle]
//! extern "C" fn update() {
//!     // ...
//! }
//! ```
//!
//! This will be run repeatedly by LiveSplit, at a rate that you can control
//! using [`runtime::set_tick_rate`].
//!
//! # Examples
//!
//! ```ignore
//! # use livesplit_extension::util::SyncRefCell;
//! struct State {
//!     // Persistent variables
//! }
//!
//! static STATE: SyncRefCell<Option<State>> = SyncRefCell::new(None);
//!
//! fn init() -> State {
//!     // One-time initialization
//!
//!     State {
//!         // Initial values of STATE
//!     }
//! }
//!
//! #[no_mangle]
//! extern "C" fn update() {
//!     let mut state = STATE.borrow_mut();
//!     let state = state.get_or_insert_with(init);
//!
//!     // Loop
//! }
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

mod env;
pub mod mem;
pub mod process;
pub mod util;

use core::{
    fmt::{self, Arguments, Display, Formatter},
    num::NonZeroU32,
    str::Utf8Error,
};
use mem::{NullptrError, ReadMemoryError};

use ascii::AsAsciiStrError;

/// Any error returned by this crate.
#[non_exhaustive]
#[derive(Clone, Debug)]
pub enum Error {
    ReadMemory(ReadMemoryError),
    Nullptr(NullptrError),
    Utf8(Utf8Error),
    Ascii(AsAsciiStrError),
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

impl From<Utf8Error> for crate::Error {
    fn from(err: Utf8Error) -> Self {
        Self::Utf8(err)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReadMemory(err) => Display::fmt(err, f),
            Self::Nullptr(err) => Display::fmt(err, f),
            Self::Utf8(err) => Display::fmt(err, f),
            Self::Ascii(err) => Display::fmt(err, f),
        }
    }
}

/// Convenience type definition.
pub type Result<T, E = Error> = core::result::Result<T, E>;

#[cfg(all(target_arch = "wasm32", not(feature = "std")))]
#[panic_handler]
fn panic_impl(info: &core::panic::PanicInfo) -> ! {
    static PANICKING: util::SyncCell<bool> = util::SyncCell::new(false);

    if PANICKING.replace(true) {
        runtime::print_message("panicked while processing panic");
        core::arch::wasm32::unreachable();
    }

    let res = runtime::print_fmt(format_args!("{info}"));
    if res.is_err() {
        runtime::print_message("panicked and failed to print formatted message");
    }

    core::arch::wasm32::unreachable();
}

pub mod runtime {
    use core::fmt::{self, Arguments};

    use crate::env;

    /// Sets the tick rate of the runtime. This influences the amount of
    /// times the `update` function is called per second.
    pub fn set_tick_rate(ticks_per_second: f64) {
        unsafe {
            env::runtime_set_tick_rate(ticks_per_second);
        }
    }

    /// Prints a log message (including a line break) for debugging purposes.
    pub fn print_message(text: &str) {
        unsafe {
            env::runtime_print_message(text.as_ptr(), text.len());
        }
    }

    /// Prints a log message (including a line break) for debugging purposes.
    /// Can be used with [`format_args`].
    ///
    /// # Errors
    ///
    /// Fails if the formatting fails or the string gets too long (without
    /// feature `alloc`).
    pub fn print_fmt(args: Arguments<'_>) -> fmt::Result {
        #[cfg(feature = "alloc")]
        print_message(&alloc::fmt::format(args));

        #[cfg(not(feature = "alloc"))]
        {
            const BUF_LEN: usize = 1024;

            let mut buf = arrayvec::ArrayString::<BUF_LEN>::new();
            fmt::write(&mut buf, args)?;
            print_message(&buf);
        }

        Ok(())
    }
}

pub mod timer {
    use crate::env;

    /// Describes which phase the timer is currently in. This tells you if
    /// there's an active speedrun attempt and whether it is paused or it ended.
    #[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
    #[repr(u8)]
    pub enum TimerPhase {
        /// There's currently no active attempt.
        NotRunning = 0,
        /// There's an active attempt that didn't end yet and isn't paused.
        Running = 1,
        /// There's an attempt that already ended, but didn't get reset yet.
        Ended = 2,
        /// There's an active attempt that is currently paused. This is separate
        /// from the game time being paused. Game time may even always be paused.
        Paused = 3,
    }

    /// Gets the state that the timer currently is in.
    pub fn get_phase() -> TimerPhase {
        use {env::timer_state::*, TimerPhase::*};

        let state = unsafe { env::timer_get_state() };
        match state {
            NOT_RUNNING => NotRunning,
            RUNNING => Running,
            ENDED => Ended,
            _ => Paused,
        }
    }

    /// Starts the timer.
    pub fn start() {
        unsafe {
            env::timer_start();
        }
    }

    /// Splits the current segment.
    pub fn split() {
        unsafe {
            env::timer_split();
        }
    }

    /// Resets the timer.
    pub fn reset() {
        unsafe {
            env::timer_reset();
        }
    }

    /// Sets a custom key value pair. This may be arbitrary information that
    /// the auto splitter wants to provide for visualization.
    pub fn set_variable(key: &str, value: &str) {
        unsafe {
            env::timer_set_variable(key.as_ptr(), key.len(), value.as_ptr(), value.len());
        }
    }

    /// Sets the game time.
    pub fn set_game_time(secs: i64, nanos: i32) {
        unsafe {
            env::timer_set_game_time(secs, nanos);
        }
    }

    /// Pauses the game time. This does not pause the timer, only the
    /// automatic flow of time for the game time.
    pub fn pause_game_time() {
        unsafe {
            env::timer_pause_game_time();
        }
    }

    /// Resumes the game time. This does not resume the timer, only the
    /// automatic flow of time for the game time.
    pub fn resume_game_time() {
        unsafe {
            env::timer_resume_game_time();
        }
    }
}

#[track_caller]
#[doc(hidden)]
pub fn _print_fmt(args: Arguments<'_>) {
    assert!(
        runtime::print_fmt(args).is_ok(),
        "failed printing formatted message; maybe the string got too long"
    );
}

/// Prints a log message (including a line break) for debugging purposes,
/// similarly to `std::println`.
///
/// # Panics
///
/// Panics if the formatting fails or the string gets too long.
#[macro_export]
macro_rules! println {
    () => {
        $crate::runtime::print_message("");
    };
    ($($arg:tt)*) => {
        match format_args!($($arg)*) {
            args => {
                if let Some(s) = args.as_str() {
                    $crate::runtime::print_message(s);
                } else {
                    $crate::_print_fmt(args);
                }
            }
        }
    };
}

/// Prints and returns the value of a given expression for quick and dirty
/// debugging, similarly to `std::dbg`.
///
/// # Panics
///
/// Panics if the formatting fails or the string gets too long.
#[macro_export]
macro_rules! dbg {
    () => {
        $crate::println!("[{}:{}]", ::core::file!(), ::core::line!())
    };
    ($val:expr $(,)?) => {
        match $val {
            tmp => {
                $crate::println!(
                    "[{}:{}] {} = {:#?}",
                    ::core::file!(),
                    ::core::line!(),
                    ::core::stringify!($val),
                    &tmp
                );

                tmp
            }
        }
    };
    ($($val:expr),+ $(,)?) => {
        ($($crate::dbg!($val)),+,)
    };
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ProcessId(NonZeroU32);

impl Display for ProcessId {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
