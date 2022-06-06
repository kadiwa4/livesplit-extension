//! Useful but unrelated utilities.

use crate::mem::{FromMemory, MemoryReader, NonNullAddress, ReadMemoryError};
use core::{fmt::Debug, str::Utf8Error};

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
            T::partial_cmp(&self.0.get(), &other.0.get())
        }
    }

    impl<T: Ord + Copy> Ord for SyncCell<T> {
        fn cmp(&self, other: &Self) -> Ordering {
            T::cmp(&self.0.get(), &other.0.get())
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

/// A string that is stored as a raw byte slice.
pub trait RawString {
    /// Finds out the length of the contained string and returns it as a raw byte
    /// slice. Returns `None` if no NUL byte is found.
    fn as_bytes(&self) -> Option<&[u8]>;

    /// Finds out the length of the contained string and returns it as a mutable
    /// raw byte slice. Returns `None` if no NUL byte is found.
    fn as_mut_bytes(&mut self) -> Option<&mut [u8]>;

    /// Finds out the length of the contained string and returns it as a string
    /// slice. Returns `Ok(None)` if no NUL byte is found.
    ///
    /// # Errors
    ///
    /// Fails if the string is not valid UTF-8 (Unicode).
    fn as_str(&self) -> Result<Option<&str>, Utf8Error> {
        Ok(if let Some(s) = self.as_bytes() {
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
    fn as_mut_str(&mut self) -> Result<Option<&mut str>, Utf8Error> {
        Ok(if let Some(s) = self.as_mut_bytes() {
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
    fn as_ascii_str(&self) -> Result<Option<&AsciiStr>, AsAsciiStrError> {
        Ok(if let Some(s) = self.as_bytes() {
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
    fn as_mut_ascii_str(&mut self) -> Result<Option<&mut AsciiStr>, AsAsciiStrError> {
        Ok(if let Some(s) = self.as_mut_bytes() {
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
    fn as_str_check_ascii(&self) -> Result<Option<&str>, AsAsciiStrError> {
        Ok(self.as_ascii_str()?.map(AsciiStr::as_str))
    }

    /// Finds out the length of the contained string and returns it as a mutable
    /// string slice. Returns `Ok(None)` if no NUL byte is found.
    ///
    /// # Errors
    ///
    /// Fails if the string is not valid ASCII. Checking this is cheaper than
    /// checking for a valid UTF-8 string.
    fn as_mut_str_check_ascii(&mut self) -> Result<Option<&mut str>, AsAsciiStrError> {
        Ok(if let Some(s) = self.as_mut_bytes() {
            s.as_mut_ascii_str()?;

            // Safety: UTF-8 is a superset of ASCII, so right now, this is valid UTF-8.
            // The caller might change the string so that it is no longer valid ASCII,
            // but this is fine because the underlying buffer consists of u8, not AsciiChar.
            Some(unsafe { core::str::from_utf8_unchecked_mut(s) })
        } else {
            None
        })
    }
}

/// A fixed size byte array that contains a C string and can be borrowed as a `&str`
/// using the methods on [`RawString`].
///
/// Useful as the target type of a pointer path.
#[derive(Clone, Debug)]
pub struct StringBuf<const N: usize>(pub [u8; N]);

impl<const N: usize> FromMemory for StringBuf<N> {
    type Error = ReadMemoryError;

    fn read_from(reader: &MemoryReader<'_>, addr: NonNullAddress) -> Result<Self, Self::Error> {
        <[u8; N]>::read_from(reader, addr).map(StringBuf)
    }
}

impl<const N: usize> RawString for StringBuf<N> {
    fn as_bytes(&self) -> Option<&[u8]> {
        get_c_str_slice(&self.0)
    }

    fn as_mut_bytes(&mut self) -> Option<&mut [u8]> {
        get_c_str_slice_mut(&mut self.0)
    }
}

#[cfg(feature = "alloc")]
mod dynamic_string {
    use crate::{
        mem::{FromMemory, MemoryReader, NonNullAddress, ReadMemoryError},
        util::{get_c_str_slice, RawString},
    };
    use alloc::{boxed::Box, vec::Vec};

    const BUF_SIZE: usize = 32;

    /// A dynamically sized byte slice that contains a C string and can be borrowed as a `&str`
    /// using the methods on [`RawString`].
    ///
    /// Useful as the target type of a pointer path.
    #[derive(Clone, Debug)]
    pub struct DynamicString {
        pub bytes: Box<[u8]>,
    }

    impl FromMemory for DynamicString {
        type Error = ReadMemoryError;

        fn read_from(reader: &MemoryReader<'_>, addr: NonNullAddress) -> Result<Self, Self::Error> {
            let mut vec = Vec::new();
            let mut buf;

            loop {
                buf = <[u8; BUF_SIZE]>::read_from(reader, addr)?;
                if let Some(s) = get_c_str_slice(&buf) {
                    vec.extend_from_slice(s);
                    return Ok(Self {
                        bytes: vec.into_boxed_slice(),
                    });
                }

                vec.extend_from_slice(&buf);
            }
        }
    }

    impl RawString for DynamicString {
        /// Returns the contained byte slice.
        #[inline]
        fn as_bytes(&self) -> Option<&[u8]> {
            Some(&self.bytes)
        }

        /// Returns the contained byte slice.
        #[inline]
        fn as_mut_bytes(&mut self) -> Option<&mut [u8]> {
            Some(&mut self.bytes)
        }
    }
}

#[cfg(feature = "alloc")]
pub use dynamic_string::*;

/// Finds the first NUL byte and returns a slice containing everything up to
/// that. Returns `None` if none is found.
///
/// # Examples
///
/// ```
/// # use livesplit_extension::util::get_c_str_slice;
/// let b1 = b"hello\0world";
/// let res1: &[u8] = b"hello";
/// assert_eq!(get_c_str_slice(b1), Some(res1));
/// let b2 = b"no null";
/// assert_eq!(get_c_str_slice(b2), None);
/// ```
pub fn get_c_str_slice(buf: &[u8]) -> Option<&[u8]> {
    buf.iter()
        .position(|&b| b == AsciiChar::Null as u8)
        .and_then(|p| buf.get(..p))
}

/// Finds the first NUL byte and returns a mutable slice containing everything
/// up to that. Returns `None` if none is found.
///
/// # Examples
///
/// ```
/// # use livesplit_extension::util::get_c_str_slice_mut;
/// let mut b1 = *b"hello\0world";
/// let mut res1 = *b"hello";
/// assert_eq!(get_c_str_slice_mut(&mut b1), Some(&mut res1[..]));
/// let mut b2 = *b"no null";
/// assert_eq!(get_c_str_slice_mut(&mut b2), None);
/// ```
pub fn get_c_str_slice_mut(buf: &mut [u8]) -> Option<&mut [u8]> {
    buf.iter()
        .position(|&b| b == AsciiChar::Null as u8)
        .and_then(|p| buf.get_mut(..p))
}
