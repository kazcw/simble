#![no_std]

//! Simple, tiny symbols. Human-readable strings up to 8 bytes long that can be stored inline and
//! manipulated efficiently.
//!
//! ```
//! use simble::*;
//!
//! # fn foo() -> Result<(), simble::Error> {
//! let foo: Symbol = "foo".parse()?;
//! let foos: Symbol = "foosball".parse()?;
//! // symbol/symbol comparisons are efficient (1 instruction on any 64-bit platform; no pointer-following)
//! assert!(foo != foos);
//! // comparison is lexical: shorter comes first
//! assert!(foo < foos);
//! // Symbols can be formatted or turned into Strings
//! assert_eq!(format!("{}", foo), "foo");
//! assert_eq!(foo.to_string(), "foo");
//!
//! let foo2 = foo.to_printable();
//! assert_eq!(&foo2, "foo");
//! let bar: Printable = "bar".parse()?;
//! // one of these is true, but which is unspecified
//! assert!(foo2 < bar || foo2 > bar);
//!
//! let toobig: Result<Symbol, _> = "ninechars".parse();
//! assert!(toobig.is_err());
//!
//! // compile-time parsing on nightly:
//! #[cfg(feature = "nightly")]
//! # {
//! const consts: Printable = printable("consts");
//! assert_eq!(&consts, "consts");
//! const hackery: Symbol = symbol("hackery");
//! assert_eq!(&hackery.to_printable(), "hackery");
//! # }
//! # Ok(())
//! # }
//! # fn main() { foo().unwrap() }
//! ```
//!
//! # Value restrictions
//!
//! - NUL characters (`"\0".parse()`) are not allowed*
//! - The empty symbol (`"".parse()`) is not allowed*
//!
//! \**These restrictions are to be considered unstable and may be lifted with only a patch version
//! increase.*
//!
//! # Storage size
//!
//! Both [`Lexical`] and [`Printable`] have the same memory layout as a [`u64`].
//!
//! Further, with features="nightly" [`Lexical`] is implemented as a non-zero type so that
//! `Option<Lexical>` can also be 8 bytes.
//!
//! Whether [`Printable`] is a non-zero type is unspecified.

#![cfg_attr(feature = "nightly", feature(const_fn, const_let, const_slice_len, const_str_as_bytes))]

extern crate failure;

#[cfg(feature = "serde")]
extern crate serde;

use core::cmp::{Ordering, PartialEq, PartialOrd};
use core::convert::AsRef;
use core::fmt::{self, Debug, Display, Formatter};
use core::mem;
use core::slice;
use core::str::{self, FromStr};

#[cfg(feature = "nightly")]
use core::num::NonZeroU64;

#[cfg(not(feature = "nightly"))]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct NonZeroU64(u64);

#[cfg(not(feature = "nightly"))]
impl NonZeroU64 {
    unsafe fn new_unchecked(x: u64) -> Self {
        NonZeroU64(x)
    }
    fn get(self) -> u64 {
        self.0
    }
}

#[derive(Debug)]
enum ErrorInner {
    TooLong,
    IllegalChar,
    Empty,
}

/// Error constructing a symbol.
#[derive(Debug)]
pub struct Error(ErrorInner);
impl failure::Fail for Error {}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        use self::ErrorInner::*;
        f.write_str(match self.0 {
            TooLong => "symbol may not exceed 8 bytes",
            IllegalChar => "symbol may not contain NUL bytes",
            Empty => "symbol may not be zero-length",
        })
    }
}

/// Iterator over the bytes of a symbol.
///
/// This `struct` is created by the `bytes` method on either [`Printable`] or [`Lexical`].
#[derive(Copy, Clone, Debug)]
pub struct Bytes(u64);
impl Iterator for Bytes {
    type Item = u8;

    #[inline]
    fn next(&mut self) -> Option<u8> {
        let byte = self.0 & 0xff;
        if byte == 0 {
            None
        } else {
            self.0 >>= 8;
            Some(byte as u8)
        }
    }

    #[inline]
    fn count(self) -> usize {
        let pad = self.0.leading_zeros() >> 3;
        8 - pad as usize
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.count();
        (len, Some(len))
    }
}
impl ExactSizeIterator for Bytes {
    #[inline]
    fn len(&self) -> usize {
        self.count()
    }
}

#[cfg(feature = "serde")]
struct ParseVisitor<T>(core::marker::PhantomData<FnOnce() -> T>);

#[cfg(feature = "serde")]
impl<T> ParseVisitor<T> {
    #[inline]
    pub fn new() -> Self {
        ParseVisitor(core::marker::PhantomData)
    }
}

#[cfg(feature = "serde")]
impl<'de, T> serde::de::Visitor<'de> for ParseVisitor<T>
where
    T: FromStr,
    <T as FromStr>::Err: Display,
{
    type Value = T;
    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a string of 8 or fewer non-NUL utf-8 bytes")
    }
    #[inline]
    fn visit_str<E>(self, value: &str) -> Result<T, E>
    where
        E: serde::de::Error,
    {
        value.parse().map_err(E::custom)
    }
}

/// Symbol that can be borrowed directly as a &[`str`] or `&[u8]`. Comparison is supported, but order is
/// unspecified and must not be relied on (for predictable sorting, use [`Lexical`]).
// Right-padded byte array stored as a big-endian integer.
#[derive(PartialEq, Eq, Hash, Copy, Clone, PartialOrd, Ord)]
pub struct Printable(NonZeroU64);

impl Debug for Printable {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "<{}>", self.as_str())
    }
}

impl Display for Printable {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        f.write_str(self.as_ref())
    }
}

impl FromStr for Printable {
    type Err = Error;
    #[inline]
    fn from_str(s: &str) -> Result<Self, Error> {
        if s.is_empty() {
            return Err(Error(ErrorInner::Empty));
        }
        if s.len() > 8 {
            return Err(Error(ErrorInner::TooLong));
        }
        if s.contains('\0') {
            return Err(Error(ErrorInner::IllegalChar));
        }
        let mut buf = [0u8; 8];
        buf[..s.len()].copy_from_slice(s.as_bytes());
        unsafe {
            // reinterpret bytes as int (platform-endian!)
            Ok(Printable(mem::transmute(buf)))
        }
    }
}

impl AsRef<[u8]> for Printable {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<str> for Printable {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

// This would make adding any inherent method that's incompatible with the trait method of the same
// name a compatibility-breaking change, so let's defer deref.
/*
impl core::ops::Deref for Printable {
    type Target = str;
    #[inline]
    fn deref(&self) -> &str { self.as_str() }
}
*/

impl PartialEq<str> for Printable {
    #[inline]
    fn eq(&self, s: &str) -> bool {
        self.as_str() == s
    }
}
impl PartialEq<Printable> for str {
    #[inline]
    fn eq(&self, p: &Printable) -> bool {
        self == p.as_str()
    }
}

impl PartialOrd<str> for Printable {
    #[inline]
    fn partial_cmp(&self, s: &str) -> Option<Ordering> {
        self.as_str().partial_cmp(s)
    }
}
impl PartialOrd<Printable> for str {
    #[inline]
    fn partial_cmp(&self, p: &Printable) -> Option<Ordering> {
        self.partial_cmp(p.as_str())
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for Printable {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Printable, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        deserializer.deserialize_str(ParseVisitor::new())
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Printable {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        serializer.serialize_str(self.as_str())
    }
}

impl From<Lexical> for Printable {
    fn from(x: Lexical) -> Self {
        x.to_printable()
    }
}

#[cfg_attr(feature = "cargo-clippy", allow(len_without_is_empty))]
impl Printable {
    #[inline]
    fn get(self) -> u64 {
        self.0.get()
    }

    /// Return the length of this symbol.
    #[inline]
    #[cfg(target_endian = "little")]
    pub fn len(self) -> usize {
        let pad = self.get().leading_zeros() >> 3;
        8 - pad as usize
    }

    /// Return the length of this symbol.
    #[inline]
    #[cfg(target_endian = "big")]
    pub fn len(self) -> usize {
        let pad = self.get().trailing_zeros() >> 3;
        8 - pad as usize
    }

    /// Convert a Printable into a byte array. The result is right-padded with NUL bytes.
    #[inline]
    pub fn into_bytes(self) -> [u8; 8] {
        // reinterpret int as bytes (platform-endian!)
        unsafe { mem::transmute(self.0) }
    }

    /// Obtain a pointer to the first byte.
    #[cfg_attr(feature = "cargo-clippy", allow(trivially_copy_pass_by_ref))]
    #[inline]
    pub fn as_ptr(&self) -> *const u8 {
        &self.0 as *const NonZeroU64 as *const u8
    }

    /// Borrow as a byte slice.
    #[cfg_attr(feature = "cargo-clippy", allow(trivially_copy_pass_by_ref))]
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        // reinterpret int as bytes (platform-endian!)
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    /// Borrow as a &[`str`].
    #[cfg_attr(feature = "cargo-clippy", allow(trivially_copy_pass_by_ref))]
    #[inline]
    pub fn as_str(&self) -> &str {
        // safe because Printable can only be created from a valid str
        unsafe { str::from_utf8_unchecked(self.as_bytes()) }
    }

    /// Obtain an iterator over the bytes.
    #[inline]
    pub fn bytes(self) -> Bytes {
        Bytes(self.get())
    }

    /// Convert to a lexically-sortable symbol.
    #[inline]
    pub fn to_lexical(self) -> Lexical {
        Lexical::from_printable(self)
    }
}

/// Symbol that compares lexicographically and consistently with the C locale. Interconvertible
/// with [`Printable`] that can be borrowed as &[`str`] or `&[u8]`.
// Native-endian integer with the first char beginning at the highest-order byte.
#[derive(PartialEq, Eq, Hash, Copy, Clone, PartialOrd, Ord)]
pub struct Lexical(NonZeroU64);

impl Debug for Lexical {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        Debug::fmt(&self.to_printable(), f)
    }
}

impl Display for Lexical {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        Display::fmt(&self.to_printable(), f)
    }
}

impl FromStr for Lexical {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Error> {
        Printable::from_str(s).map(Printable::to_lexical)
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for Lexical {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Lexical, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        deserializer.deserialize_str(ParseVisitor::new())
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Lexical {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        serializer.serialize_str(self.to_printable().as_str())
    }
}

impl From<Printable> for Lexical {
    fn from(x: Printable) -> Self {
        x.to_lexical()
    }
}

#[cfg_attr(feature = "cargo-clippy", allow(len_without_is_empty))]
impl Lexical {
    #[inline]
    fn get(self) -> u64 {
        self.0.get()
    }

    /// Return the length of this symbol.
    #[inline]
    pub fn len(self) -> usize {
        let pad = self.get().trailing_zeros() >> 3;
        8 - pad as usize
    }

    /// Convert a Lexical into a byte array. The result is right-padded with NUL bytes.
    #[inline]
    pub fn into_bytes(self) -> [u8; 8] {
        self.to_printable().into_bytes()
    }

    /// Obtain an iterator over the bytes.
    #[inline]
    pub fn bytes(self) -> Bytes {
        self.to_printable().bytes()
    }

    #[inline]
    fn from_printable(x: Printable) -> Self {
        // This is safe because Printable is also non-zero
        Lexical(unsafe { NonZeroU64::new_unchecked(u64::from_be(x.get())) })
    }

    /// Convert to a symbol that can be borrowed as a &str.
    #[inline]
    pub fn to_printable(self) -> Printable {
        // This is safe because Lexical is also non-zero
        Printable(unsafe { NonZeroU64::new_unchecked(u64::to_be(self.get())) })
    }
}

/// Alias for [`Lexical`], which is the default Symbol type because it sorts without surprises. If
/// consistent sort order is not important, you can just use [`Printable`] exclusively: `use
/// simble::Printable as Symbol`.
pub type Symbol = Lexical;

#[cfg(feature = "nightly")]
#[cfg_attr(feature = "cargo-clippy", allow(cast_lossless))]
const fn to_int_be(s: &[u8]) -> u64 {
    s[0] as u64
        + ((s[((s.len() > 1) as usize)] as u64 * ((s.len() > 1) as u64)) << 8)
        + ((s[2 * ((s.len() > 2) as usize)] as u64 * ((s.len() > 2) as u64)) << 16)
        + ((s[3 * ((s.len() > 3) as usize)] as u64 * ((s.len() > 3) as u64)) << 24)
        + ((s[4 * ((s.len() > 4) as usize)] as u64 * ((s.len() > 4) as u64)) << 32)
        + ((s[5 * ((s.len() > 5) as usize)] as u64 * ((s.len() > 5) as u64)) << 40)
        + ((s[6 * ((s.len() > 6) as usize)] as u64 * ((s.len() > 6) as u64)) << 48)
        + ((s[7 * ((s.len() > 7) as usize)] as u64 * ((s.len() > 7) as u64)) << 56)
}

#[cfg(feature = "nightly")]
#[cfg_attr(feature = "cargo-clippy", allow(cast_lossless))]
const fn to_int_le(s: &[u8]) -> u64 {
    ((s[0] as u64) << 56)
        + ((s[((s.len() > 1) as usize)] as u64 * ((s.len() > 1) as u64)) << 48)
        + ((s[2 * ((s.len() > 2) as usize)] as u64 * ((s.len() > 2) as u64)) << 40)
        + ((s[3 * ((s.len() > 3) as usize)] as u64 * ((s.len() > 3) as u64)) << 32)
        + ((s[4 * ((s.len() > 4) as usize)] as u64 * ((s.len() > 4) as u64)) << 24)
        + ((s[5 * ((s.len() > 5) as usize)] as u64 * ((s.len() > 5) as u64)) << 16)
        + ((s[6 * ((s.len() > 6) as usize)] as u64 * ((s.len() > 6) as u64)) << 8)
        + (s[7 * ((s.len() > 7) as usize)] as u64 * ((s.len() > 7) as u64))
}

#[cfg(all(feature = "nightly", endian = "little"))]
const fn to_int_native(s: &[u8]) {
    to_int_le(s)
}

#[cfg(all(feature = "nightly", endian = "big"))]
const fn to_int_native(s: &[u8]) {
    to_int_be(s)
}

#[cfg(feature = "nightly")]
#[cfg_attr(feature = "cargo-clippy", allow(unnecessary_operation))]
const fn validate(s: &[u8]) {
    [()][(s.len() == 0) as usize]; // assert non-empty
    [()][(s.len() > 8) as usize]; // assert length <= 8
    [()][(s[0] == 0              // assert no nulls
             || s[((s.len() > 1) as usize)] == 0
             || s[2 * ((s.len() > 2) as usize)] == 0
             || s[3 * ((s.len() > 3) as usize)] == 0
             || s[4 * ((s.len() > 4) as usize)] == 0
             || s[5 * ((s.len() > 5) as usize)] == 0
             || s[6 * ((s.len() > 6) as usize)] == 0
             || s[7 * ((s.len() > 7) as usize)] == 0) as usize];
}

/// [nightly-only, experimental] `const fn` for parsing and validating a [`Printable`] at compile
/// time. Note that due to current compiler limitations, the current implementation may be
/// inefficient if used at runtime.
///
/// # Panics
///
/// Panics if the value provided is not a legal symbol; see [value
/// restrictions](index.html#value-restrictions). Note: due to current compiler limitations,
///
/// # Examples
/// ```
/// # #[cfg(feature = "nightly")]
/// # {
/// use simble::{Printable, printable};
/// const HELLO: Printable = printable("hello");
/// assert_eq!(&HELLO, "hello");
/// # }
/// ```
#[cfg(feature = "nightly")]
pub const fn printable(s: &str) -> Printable {
    let s = s.as_bytes();
    validate(s);
    let n = to_int_be(s);
    // this is safe because a non-empty sequence of non-zero bytes must be non-zero
    Printable(unsafe { NonZeroU64::new_unchecked(n) })
}

/// [nightly-only, experimental] `const fn` for parsing and validating a [`Lexical`] at compile
/// time. Note that due to current compiler limitations, the current implementation may be
/// inefficient if used at runtime.
///
/// # Panics
///
/// Panics if the value provided is not a legal symbol; see [value
/// restrictions](index.html#value-restrictions).
///
/// # Examples
/// ```
/// # #[cfg(feature = "nightly")]
/// # {
/// use simble::{Lexical, lexical};
/// const HELLO: Lexical = lexical("hello");
/// assert_eq!(&HELLO.to_printable(), "hello");
/// # }
/// ```
#[cfg(feature = "nightly")]
pub const fn lexical(s: &str) -> Lexical {
    let s = s.as_bytes();
    validate(s);
    let n = to_int_le(s);
    // this is safe because a non-empty sequence of non-zero bytes must be non-zero
    Lexical(unsafe { NonZeroU64::new_unchecked(n) })
}

/// Alias for [`lexical`].
#[cfg(feature = "nightly")]
pub const fn symbol(s: &str) -> Lexical {
    lexical(s)
}

#[cfg(test)]
mod tests {
    extern crate std;

    use super::Lexical;
    use super::Printable;

    use core::str::FromStr;

    #[test]
    fn test_bytes() {
        let foo: Lexical = "foo".parse().unwrap();
        let bar: std::vec::Vec<_> = foo.bytes().collect();
        assert_eq!(&bar, &['f' as u8, 'o' as u8, 'o' as u8]);
    }

    #[test]
    fn test_len() {
        assert_eq!(Lexical::from_str("somestr").unwrap().len(), 7);
        assert_eq!(Printable::from_str("somestr").unwrap().len(), 7);
    }

    #[test]
    fn test_round_trip() {
        let fool: Lexical = "foo".parse().unwrap();
        let foop: Printable = "foo".parse().unwrap();
        assert_eq!(fool.to_printable(), foop);
        assert_eq!(fool, foop.to_lexical());
    }

    #[test]
    fn test_into_bytes() {
        let array = ['f' as u8, 'o' as u8, 'o' as u8, 0u8, 0u8, 0u8, 0u8, 0u8];
        assert_eq!(Lexical::from_str("foo").unwrap().into_bytes(), array);
        assert_eq!(Printable::from_str("foo").unwrap().into_bytes(), array);
    }
}
