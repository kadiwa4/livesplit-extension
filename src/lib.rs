//! Convenience library for the LiveSplit WebAssembly extension API.
//! You need to provide an `update` function as follows:
//!
//! ```
//! #[no_mangle]
//! pub extern "C" fn update() {
//!     // ...
//! }
//! ```
//!
//! This will be run repeatedly by LiveSplit, at a rate that you can control
//! using [`runtime::set_tick_rate`].
//!
//! # Examples
//!
//! ```
//! use livesplit_extension::util::SyncRefCell;
//!
//! struct State {
//!     // Persistent variables
//! }
//!
//! static STATE: SyncRefCell<State> = SyncRefCell::new(State {
//!     // Initial values of STATE
//! });
//!
//! fn init() {
//!     let state = STATE.borrow_mut();
//!
//!     // One-time initialization
//! }
//!
//! #[no_mangle]
//! pub extern "C" fn update() {
//!     livesplit_extension::init(init);
//!
//!     let state = STATE.borrow_mut();
//!
//!     // Loop
//! }
//! ```
//!
//! Make sure you _don't_ borrow `STATE` _before_ calling the `init` function
//! (unless you make `init` a closure; in that case, you will only need to call
//! [`borrow_mut`] once).
//!
//! [`borrow_mut`]: core::cell::RefCell::borrow_mut

#![no_std]

mod env;
pub mod mem;
pub mod process;
pub mod util;

use core::{fmt::Arguments, num::NonZeroU64};

use util::SyncCell;

#[cfg(target_arch = "wasm32")]
#[cfg_attr(not(test), panic_handler)]
fn _panic_handler(info: &core::panic::PanicInfo) -> ! {
    let msg = info
        .payload()
        .downcast_ref::<&str>()
        .unwrap_or(&"&(dyn Any)");
    let res = if let Some(loc) = info.location() {
        runtime::print_fmt(format_args!("panicked at '{msg}', {loc}"))
    } else {
        runtime::print_fmt(format_args!("panicked at '{msg}'"))
    };

    if res.is_err() {
        runtime::print_message("panicked and failed to print formatted message");
    }

    core::arch::wasm32::unreachable()
}

/// Calls the provided function only if this function hasn't been called before.
#[inline]
pub fn init(f: impl FnOnce()) {
    static SHOULD_RUN_INIT: SyncCell<bool> = SyncCell::new(true);

    if SHOULD_RUN_INIT.get() {
        SHOULD_RUN_INIT.set(false);
        f();
    }
}

pub mod runtime {
    use core::fmt::{self, Arguments};

    use crate::{env, util::WriteBuf};

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
    /// Fails if the formatting fails or the string gets too long.
    pub fn print_fmt(args: Arguments<'_>) -> fmt::Result {
        const BUF_LEN: usize = 2048;

        let mut buf = WriteBuf::<BUF_LEN>::new();
        let res = fmt::write(&mut buf, args);
        print_message(buf.as_str());
        res
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
        /// There's an active attempt that is currently paused.
        Paused = 3,
    }

    /// Gets the state that the timer currently is in.
    #[must_use]
    pub fn get_state() -> TimerPhase {
        use {env::timer_state::*, TimerPhase::*};

        match unsafe { env::timer_get_state() } {
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
pub fn __print_fmt(args: Arguments) {
    if runtime::print_fmt(args).is_err() {
        panic!("failed printing formatted message; maybe the string got too long");
    }
}

/// Prints a log message (including a line break) for debugging purposes.
///
/// # Panics
///
/// Panics if the formatting fails or the string gets too long.
#[macro_export]
macro_rules! println {
    () => {
        $crate::runtime::print_message("");
    };
    ($($arg:tt)*) => {{
        let args = format_args!($($arg:tt)*);
        if let Some(s) = args.as_str() {
            $crate::runtime::print_message(s);
        } else {
            $crate::__print_fmt(args);
        }
    }};
}

pub type ProcessId = NonZeroU64;
pub type Address = NonZeroU64;
pub type Offset = i64;
