//! External functions.

use core::num::NonZeroU64;

pub mod timer_state {
    pub type State = u32;

    /// The timer is not running.
    pub const NOT_RUNNING: State = 0;
    /// The timer is running.
    pub const RUNNING: State = 1;
    /// The timer started but got paused. This is separate from the game
    /// time being paused. Game time may even always be paused.
    pub const PAUSED: State = 2;
    // /// The timer has ended, but didn't get reset yet.
    // pub const ENDED: State = 3;
}

extern "C" {
    /// Attaches to a process based on its name.
    pub fn process_attach(name_ptr: *const u8, name_len: usize) -> u64;
    /// Detaches from a process.
    pub fn process_detach(process: NonZeroU64);
    /// Checks whether is a process is still open. You should detach from a
    /// process and stop using it if this returns `false`.
    pub fn process_is_open(process: NonZeroU64) -> bool;
    /// Reads memory from a process at the address given. This will write
    /// the memory to the buffer given. Returns `false` if this fails.
    pub fn process_read(
        process: NonZeroU64,
        address: u64,
        buf_ptr: *mut u8,
        buf_len: usize,
    ) -> bool;
    /// Gets the address of a module in a process.
    pub fn process_get_module(
        process: NonZeroU64,
        name_ptr: *const u8,
        name_len: usize,
    ) -> Option<NonZeroU64>;

    /// Sets the tick rate of the runtime. This influences the amount of
    /// times the `update` function is called per second.
    pub fn runtime_set_tick_rate(ticks_per_second: f64);
    /// Prints a log message for debugging purposes.
    pub fn runtime_print_message(text_ptr: *const u8, text_len: usize);

    /// Gets the state that the timer currently is in.
    pub fn timer_get_state() -> timer_state::State;
    /// Starts the timer.
    pub fn timer_start();
    /// Splits the current segment.
    pub fn timer_split();
    /// Resets the timer.
    pub fn timer_reset();
    /// Sets a custom key value pair. This may be arbitrary information that
    /// the auto splitter wants to provide for visualization.
    pub fn timer_set_variable(
        key_ptr: *const u8,
        key_len: usize,
        value_ptr: *const u8,
        value_len: usize,
    );
    /// Sets the game time.
    pub fn timer_set_game_time(secs: i64, nanos: i32);
    /// Pauses the game time. This does not pause the timer, only the
    /// automatic flow of time for the game time.
    pub fn timer_pause_game_time();
    /// Resumes the game time. This does not resume the timer, only the
    /// automatic flow of time for the game time.
    pub fn timer_resume_game_time();
}
