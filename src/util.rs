//! Useful but unrelated utilities.

use core::{
    fmt::{self, Debug},
    mem::MaybeUninit,
    num::NonZeroU64,
    str::Utf8Error,
};

use ascii::{AsAsciiStr, AsAsciiStrError, AsMutAsciiStr, AsciiChar, AsciiStr};

#[cfg(target_arch = "wasm32")]
mod wasm {
    use core::{
        cell::{Cell, RefCell},
        cmp::Ordering,
        fmt::{self, Debug, Formatter},
        ops::Deref,
    };

    /// A mutable memory location.
    ///
    /// See [`core::cell`] for more.
    #[repr(transparent)]
    #[derive(Default)]
    pub struct SyncCell<T: ?Sized>(pub Cell<T>);

    impl<T> SyncCell<T> {
        #[inline]
        pub const fn new(v: T) -> Self {
            Self(Cell::new(v))
        }
    }

    impl<T: Copy> Clone for SyncCell<T> {
        #[inline]
        fn clone(&self) -> Self {
            Self(Cell::new(self.0.get()))
        }
    }

    impl<T: Copy + Debug> Debug for SyncCell<T> {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            f.debug_tuple("SyncCell").field(&self.0).finish()
        }
    }

    impl<T> Deref for SyncCell<T> {
        type Target = Cell<T>;

        #[inline]
        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl<T: Copy + PartialEq> PartialEq for SyncCell<T> {
        fn eq(&self, other: &Self) -> bool {
            self.0.get() == other.0.get()
        }
    }

    impl<T: Copy + Eq> Eq for SyncCell<T> {}

    impl<T: PartialOrd + Copy> PartialOrd for SyncCell<T> {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            self.0.get().partial_cmp(&other.0.get())
        }
    }

    impl<T: Ord + Copy> Ord for SyncCell<T> {
        fn cmp(&self, other: &Self) -> Ordering {
            self.0.get().cmp(&other.0.get())
        }
    }

    impl<T> From<T> for SyncCell<T> {
        #[inline]
        fn from(t: T) -> Self {
            Self(Cell::new(t))
        }
    }

    impl<T> From<Cell<T>> for SyncCell<T> {
        #[inline]
        fn from(cell: Cell<T>) -> Self {
            Self(cell)
        }
    }

    // Safety: No threading.
    unsafe impl<T> Sync for SyncCell<T> {}

    /// A mutable memory location with dynamically checked borrow rules.
    ///
    /// See [`core::cell`] for more.
    #[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
    pub struct SyncRefCell<T: ?Sized>(pub RefCell<T>);

    impl<T> SyncRefCell<T> {
        #[inline]
        pub const fn new(v: T) -> Self {
            Self(RefCell::new(v))
        }
    }

    impl<T> Deref for SyncRefCell<T> {
        type Target = RefCell<T>;

        #[inline]
        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl<T> From<T> for SyncRefCell<T> {
        #[inline]
        fn from(t: T) -> Self {
            Self(RefCell::new(t))
        }
    }

    impl<T> From<RefCell<T>> for SyncRefCell<T> {
        #[inline]
        fn from(cell: RefCell<T>) -> Self {
            Self(cell)
        }
    }

    // Safety: No threading.
    unsafe impl<T> Sync for SyncRefCell<T> {}
}

#[cfg(target_arch = "wasm32")]
pub use wasm::*;

/// Create a new array of `MaybeUninit<T>` items, in an uninitialized state.
#[inline]
pub(crate) fn uninit_array<T, const N: usize>() -> [MaybeUninit<T>; N] {
    // Safety: An uninitialized [MaybeUninit<_>; N] is valid.
    unsafe { MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init() }
}

/// Extracts the values from an array of `MaybeUninit` containers.
///
/// # Safety
///
/// It is up to the caller to guarantee that all elements of the array are
/// in an initialized state.
#[inline]
pub(crate) unsafe fn array_assume_init<T, const N: usize>(array: [MaybeUninit<T>; N]) -> [T; N] {
    (&array as *const [_; N] as *const [T; N]).read()
}

/// A fixed size array that contains a C string and can be borrowed as a `&str`
/// using [`as_str`] (for UTF-8 strings) or [`as_ascii_str`].
///
/// Useful as the target type of a pointer path.
///
/// [`as_ascii_str`]: Self::as_ascii_str
/// [`as_str`]: Self::as_str
#[derive(Clone)]
pub struct StringBuf<const N: usize>(pub [u8; N]);

impl<const N: usize> StringBuf<N> {
    /// Finds out the length of the contained string and returns it as a string
    /// slice. Returns `Ok(None)` if no NUL byte is found.
    ///
    /// # Errors
    ///
    /// Fails if the string is not valid UTF-8 (Unicode).
    pub fn as_str(&self) -> Result<Option<&str>, Utf8Error> {
        Ok(if let Some(s) = get_c_str_slice(&self.0) {
            Some(core::str::from_utf8(s)?)
        } else {
            None
        })
    }

    /// Finds out the length of the contained string and returns it as a mutable
    /// string slice. Returns `Ok(None)` if no NUL byte is found.
    ///
    /// # Errors
    ///
    /// Fails if the string is not valid UTF-8 (Unicode).
    pub fn as_mut_str(&mut self) -> Result<Option<&mut str>, Utf8Error> {
        Ok(if let Some(s) = get_c_str_slice_mut(&mut self.0) {
            Some(core::str::from_utf8_mut(s)?)
        } else {
            None
        })
    }

    /// Finds out the length of the contained string and returns it as an ASCII
    /// string slice. Returns `Ok(None)` if no NUL byte is found.
    ///
    /// # Errors
    ///
    /// Fails if the string is not valid ASCII. Checking this is cheaper than
    /// checking for a valid UTF-8 string.
    pub fn as_ascii_str(&self) -> Result<Option<&AsciiStr>, AsAsciiStrError> {
        Ok(if let Some(s) = get_c_str_slice(&self.0) {
            Some(s.as_ascii_str()?)
        } else {
            None
        })
    }

    /// Finds out the length of the contained string and returns it as a mutable
    /// ASCII string slice. Returns `Ok(None)` if no NUL byte is found.
    ///
    /// # Errors
    ///
    /// Fails if the string is not valid ASCII. Checking this is cheaper than
    /// checking for a valid UTF-8 string.
    pub fn as_mut_ascii_str(&mut self) -> Result<Option<&mut AsciiStr>, AsAsciiStrError> {
        Ok(if let Some(s) = get_c_str_slice_mut(&mut self.0) {
            Some(s.as_mut_ascii_str()?)
        } else {
            None
        })
    }

    /// Finds out the length of the contained string and returns it as a string
    /// slice. Returns `Ok(None)` if no NUL byte is found.
    ///
    /// # Errors
    ///
    /// Fails if the string is not valid ASCII. Checking this is cheaper than
    /// checking for a valid UTF-8 string.
    pub fn as_str_check_ascii(&self) -> Result<Option<&str>, AsAsciiStrError> {
        Ok(self.as_ascii_str()?.map(AsciiStr::as_str))
    }

    /// Finds out the length of the contained string and returns it as a mutable
    /// string slice. Returns `Ok(None)` if no NUL byte is found.
    ///
    /// # Errors
    ///
    /// Fails if the string is not valid ASCII. Checking this is cheaper than
    /// checking for a valid UTF-8 string.
    #[allow(clippy::cast_ref_to_mut)]
    pub fn as_mut_str_check_ascii(&mut self) -> Result<Option<&mut str>, AsAsciiStrError> {
        // Safety: The input slice was also mutable.
        Ok(self
            .as_str_check_ascii()?
            .map(|s| unsafe { &mut *(s as *const _ as *mut _) }))
    }
}

impl<const N: usize> Debug for StringBuf<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // This has no generics.
        fn fmt(f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("StringBuf").finish()
        }

        fmt(f)
    }
}

/// Finds the first NUL byte and returns a slice containing everything up to
/// that. Returns `None` if none is found.
///
/// # Examples
///
/// ```
/// # use livesplit_extension::util::get_c_str_slice;
/// let b1 = b"hello\0world";
/// let b2 = b"nonull";
/// assert_eq!(get_c_str_slice(b1), Some(b"hello"));
/// assert_eq!(get_c_str_slice(b2), None);
/// ```
pub fn get_c_str_slice(buf: &[u8]) -> Option<&[u8]> {
    buf.split(|&b| b == AsciiChar::Null as u8).next()
}

/// Finds the first NUL byte and returns a mutable slice containing everything
/// up to that. Returns `None` if none is found.
///
/// # Examples
///
/// ```
/// # use livesplit_extension::util::get_c_str_slice_mut;
/// let mut b1 = *b"hello\0world";
/// let mut b2 = *b"nonull";
/// assert_eq!(get_c_str_slice_mut(&mut b1), Some(b"hello"));
/// assert_eq!(get_c_str_slice_mut(&mut b2), None);
/// ```
pub fn get_c_str_slice_mut(buf: &mut [u8]) -> Option<&mut [u8]> {
    buf.split_mut(|&b| b == AsciiChar::Null as u8).next()
}

/// Adds the offset to the pointer, returning `None` if the result is a
/// null-pointer.
#[inline]
pub const fn try_ptr_offset(ptr: NonZeroU64, offset: i64) -> Option<NonZeroU64> {
    NonZeroU64::new(ptr.get().wrapping_add(offset as u64))
}

/// Adds the offset to the pointer.
///
/// # Panics
///
/// Panics if the result is a null-pointer.
#[inline]
pub const fn ptr_offset(ptr: NonZeroU64, offset: i64) -> NonZeroU64 {
    match NonZeroU64::new(ptr.get().wrapping_add(offset as u64)) {
        Some(n) => n,
        None => panic!("offset led to nullptr"),
    }
}
