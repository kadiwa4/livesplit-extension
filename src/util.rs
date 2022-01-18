//! Useful but unrelated utilities.

use core::{
    cell::{Cell, RefCell},
    fmt::{self, Debug, Display, Write},
    mem::MaybeUninit,
    num::NonZeroU64,
    ops::Deref,
    ptr,
};

/// A mutable memory location.
///
/// See [`core::cell`] for more.
#[repr(transparent)]
pub struct SyncCell<T: ?Sized>(pub Cell<T>);

impl<T> SyncCell<T> {
    pub const fn new(v: T) -> Self {
        Self(Cell::new(v))
    }
}

impl<T> Deref for SyncCell<T> {
    type Target = Cell<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

// Safety: No threading.
unsafe impl<T> Sync for SyncCell<T> {}

/// A mutable memory location with dynamically checked borrow rules.
///
/// See [`core::cell`] for more.
pub struct SyncRefCell<T: ?Sized>(pub RefCell<T>);

impl<T> SyncRefCell<T> {
    pub const fn new(v: T) -> Self {
        Self(RefCell::new(v))
    }
}

impl<T> Deref for SyncRefCell<T> {
    type Target = RefCell<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

// Safety: No threading.
unsafe impl<T> Sync for SyncRefCell<T> {}

pub struct WriteBuf<const N: usize> {
    buf: [u8; N],
    pos: usize,
    full: bool,
}

impl<const N: usize> WriteBuf<N> {
    #[must_use]
    pub fn new() -> Self {
        Self {
            // Safety: This field is private and only the initialized part of
            // the buf can be extracted through to_str.
            buf: unsafe { array_assume_init(uninit_array::<u8, N>()) },
            pos: 0,
            full: N == 0,
        }
    }

    #[inline]
    #[must_use]
    pub fn to_str(&self) -> &str {
        // Safety: Only valid UTF-8 was written to buf and everything up to pos
        // was initialized.
        unsafe { core::str::from_utf8_unchecked(self.buf.get_unchecked(..self.pos)) }
    }
}

impl<const N: usize> Clone for WriteBuf<N> {
    fn clone(&self) -> Self {
        let mut buf = Self::new();
        let _ = buf.write_str(self.to_str());
        buf.full = self.full;
        buf
    }
}

impl<const N: usize> Debug for WriteBuf<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // This has no generics.
        fn fmt(pos: usize, full: bool, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let mut f = f.debug_struct("WriteBuf");
            let f = f.field("full", &full);
            if full { f } else { f.field("len", &pos) }.finish()
        }

        fmt(self.pos, self.full, f)
    }
}

impl<const N: usize> Default for WriteBuf<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> Write for WriteBuf<N> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        // This has no generics.
        fn write_str(buf: &mut [u8], pos: &mut usize, full: &mut bool, s: &str) -> fmt::Result {
            if *full {
                return Err(fmt::Error);
            }

            // Safety: pos is a valid index.
            let buf = unsafe { buf.get_unchecked_mut(*pos..) };
            if s.len() >= buf.len() {
                *full = true;
            }

            let count = if s.len() > buf.len() {
                // buf.len() is always >= 1
                let mut idx = buf.len().wrapping_sub(1);
                while !s.is_char_boundary(idx) {
                    idx -= 1;
                }

                idx
            } else {
                s.len()
            };

            // Safety: buf is large enough and the two slices can't overlap.
            unsafe {
                ptr::copy_nonoverlapping(s.as_ptr(), buf.as_mut_ptr(), count);
            }

            *pos += count;
            if *full {
                Err(fmt::Error)
            } else {
                Ok(())
            }
        }

        write_str(&mut self.buf, &mut self.pos, &mut self.full, s)
    }

    #[inline]
    fn write_char(&mut self, c: char) -> fmt::Result {
        // This has no generics.
        fn write_char(buf: &mut [u8], pos: &mut usize, full: &mut bool, c: char) -> fmt::Result {
            if *full {
                return Err(fmt::Error);
            }

            // Safety: pos is a valid index.
            let buf = unsafe { buf.get_unchecked_mut(*pos..) };
            let len = c.len_utf8();
            if len >= buf.len() {
                *full = true;
            }

            encode_utf8(c as u32, len, buf)?;

            *pos += len;
            if *full {
                Err(fmt::Error)
            } else {
                Ok(())
            }
        }

        write_char(&mut self.buf, &mut self.pos, &mut self.full, c)
    }
}

/// Encodes this character as UTF-8 into the provided byte buffer. Returns an
/// error if it doesn't fit. Same as [`char::encode_utf8`] except it doesn't
/// panic. `len` must be equal to `char.len_utf8()` for correct results.
fn encode_utf8(code: u32, len: usize, dst: &mut [u8]) -> fmt::Result {
    // UTF-8 ranges and tags for encoding characters
    const TAG_CONT: u8 = 0b1000_0000;
    const TAG_TWO_B: u8 = 0b1100_0000;
    const TAG_THREE_B: u8 = 0b1110_0000;
    const TAG_FOUR_B: u8 = 0b1111_0000;

    match (len, dst) {
        (1, [a, ..]) => {
            *a = code as u8;
        }
        (2, [a, b, ..]) => {
            *a = (code >> 6 & 0x1F) as u8 | TAG_TWO_B;
            *b = (code & 0x3F) as u8 | TAG_CONT;
        }
        (3, [a, b, c, ..]) => {
            *a = (code >> 12 & 0x0F) as u8 | TAG_THREE_B;
            *b = (code >> 6 & 0x3F) as u8 | TAG_CONT;
            *c = (code & 0x3F) as u8 | TAG_CONT;
        }
        (4, [a, b, c, d, ..]) => {
            *a = (code >> 18 & 0x07) as u8 | TAG_FOUR_B;
            *b = (code >> 12 & 0x3F) as u8 | TAG_CONT;
            *c = (code >> 6 & 0x3F) as u8 | TAG_CONT;
            *d = (code & 0x3F) as u8 | TAG_CONT;
        }
        _ => return Err(fmt::Error),
    }

    Ok(())
}

#[inline]
pub(crate) fn uninit_array<T, const N: usize>() -> [MaybeUninit<T>; N] {
    // Safety: An uninitialized [MaybeUninit<_>; N] is valid.
    unsafe { MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init() }
}

#[inline]
pub(crate) unsafe fn array_assume_init<T, const N: usize>(array: [MaybeUninit<T>; N]) -> [T; N] {
    (&array as *const [_; N]).cast::<[T; N]>().read()
}

#[derive(Clone, Copy, Debug)]
pub struct AsciiError;

impl Display for AsciiError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("invalid ascii string")
    }
}

#[inline]
pub fn str_from_ascii(buf: &[u8]) -> Result<&str, AsciiError> {
    if buf.is_ascii() {
        // Safety: UTF-8 is a superset of ASCII.
        Ok(unsafe { core::str::from_utf8_unchecked(buf) })
    } else {
        Err(AsciiError)
    }
}

#[inline]
pub fn try_ptr_offset(ptr: NonZeroU64, offset: i64) -> Option<NonZeroU64> {
    NonZeroU64::new(ptr.get().wrapping_add(offset as u64))
}

#[inline]
pub fn ptr_offset(ptr: NonZeroU64, offset: i64) -> NonZeroU64 {
    NonZeroU64::new(ptr.get().wrapping_add(offset as u64)).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn format() {
        let mut buf = WriteBuf::<256>::new();
        buf.write_str("hello,").unwrap();
        buf.write_char(' ').unwrap();
        write!(buf, "num: {:#018X}\nstr: {:?}", 10293, "something").unwrap();
        assert_eq!(
            buf.to_str(),
            "hello, num: 0x0000000000002835\nstr: \"something\""
        );
        let buf2 = buf.clone();
        assert_eq!(buf.to_str(), buf2.to_str());
    }

    #[test]
    fn too_short() {
        let mut buf = WriteBuf::<4>::new();
        buf.write_str("老虎").unwrap_err();
        assert_eq!(buf.to_str(), "老");
        let mut buf2 = buf.clone();
        buf2.write_char('e').unwrap_err();
        assert_eq!(buf.to_str(), buf2.to_str());
        buf.write_char('e').unwrap_err();
    }
}
