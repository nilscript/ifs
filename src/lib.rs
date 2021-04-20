#![feature(option_result_contains)]

use std::io::{BufRead, Error, ErrorKind};
use std::str;

/// Checks the haystacks back if it contains the needle
/// Not a general search implementation at all.
fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    haystack
        .rchunks_exact(needle.len())
        .next()
        .contains(&needle)
}

/// Converts vec to string and
/// wraps up FromUtf8Error into [`io::Error`] type.
fn utf8_wrapup(buf: Vec<u8>) -> Option<Result<String, Error>> {
    if buf.is_empty() {
        None
    } else {
        Some(String::from_utf8(buf).map_err(|e| Error::new(ErrorKind::Other, e)))
    }
}

/// An iterator over delimeted bytes.
///
/// Can be created by importing [`ifs::Ifs`] and calling
/// [`std::io::BufReader`]::[`split_binary`].
///
/// The iterator will yield instances of [`io::Result`]<[`Vec<u8>`]>.
///
/// # Examples
///
/// Simple usage
/// ```no_run
/// # use ifs::Ifs;
/// # use std::io::{self, BufReader};
/// # use std::fs::File;
/// let file = File::open("ladder.hex").unwrap(); // 0x0123456789ABCDEF
/// let mut ifs = BufReader::new(file).split_binary(&[0x89]);
///
/// assert_eq!(ifs.next().unwrap().unwrap(), [0x01, 0x23, 0x45, 0x67]);
/// assert_eq!(ifs.next().unwrap().unwrap(), [0xAB, 0xCD, 0xEF]);
/// assert!(ifs.next().is_none());
/// ```
///
/// For demonstration purposes I will be using [`mockstream::MockStream`]
/// The iterator can take in longer deliminators.
/// ```
/// # use ifs::Ifs;
/// # use mockstream::MockStream;
/// # use std::io::{self, BufReader};
/// let mut stream = MockStream::new();
/// stream.push_bytes_to_read(b"Testing string to test with");
/// let mut iter = BufReader::new(stream).split_binary(b"ing");
///
/// assert_eq!(iter.next().unwrap().unwrap(), b"Test");
/// assert_eq!(iter.next().unwrap().unwrap(), b" str");
/// assert_eq!(iter.next().unwrap().unwrap(), b" to test with");
/// assert!(iter.next().is_none());
/// ```
///
/// It can also take in zero deliminators.
/// ```
/// # use ifs::Ifs;
/// # use mockstream::MockStream;
/// # use std::io::{self, BufReader};
/// let mut stream = MockStream::new();
/// stream.push_bytes_to_read(&[1, 2, 3]);
/// let mut iter = BufReader::new(stream).split_binary(&[]);
///
/// assert_eq!(iter.next().unwrap().unwrap(), [1]);
/// assert_eq!(iter.next().unwrap().unwrap(), [2]);
/// assert_eq!(iter.next().unwrap().unwrap(), [3]);
/// assert!(iter.next().is_none());
/// ```
///
/// If delim pattern is right besids each other, 
/// you will end up with empty vectors.
/// ```
/// # use ifs::Ifs;
/// # use mockstream::MockStream;
/// # use std::io::{self, BufReader};
/// let mut stream = MockStream::new();
/// stream.push_bytes_to_read(&[0, 0, 0, 0, 1, 0, 0, 2, 0, 3]);
/// let mut iter = BufReader::new(stream).split_binary(&[0]);
///
/// assert_eq!(iter.next().unwrap().unwrap(), []);
/// assert_eq!(iter.next().unwrap().unwrap(), []);
/// assert_eq!(iter.next().unwrap().unwrap(), []);
/// assert_eq!(iter.next().unwrap().unwrap(), []);
/// assert_eq!(iter.next().unwrap().unwrap(), [1]);
/// assert_eq!(iter.next().unwrap().unwrap(), []);
/// assert_eq!(iter.next().unwrap().unwrap(), [2]);
/// assert_eq!(iter.next().unwrap().unwrap(), [3]);
/// assert!(iter.next().is_none());
/// ```
///
/// Unlike [`str::split`] deliminators (or separators) at the end of a stream
/// can't be sepparated into an empty array.
/// ```
/// # use ifs::Ifs;
/// # use mockstream::MockStream;
/// # use std::io::{self, BufReader};
/// let mut stream = MockStream::new();
/// stream.push_bytes_to_read(&[0, 1, 0]);
/// let mut iter = BufReader::new(stream).split_binary(&[0]);
///
/// assert_eq!(iter.next().unwrap().unwrap(), []);
/// assert_eq!(iter.next().unwrap().unwrap(), [1]);
/// assert!(iter.next().is_none());
/// ```
///
/// If it can't detect a delim pattern it will return everything there is.
/// ```
/// # use ifs::Ifs;
/// # use mockstream::MockStream;
/// # use std::io::{self, BufReader};
/// let mut stream = MockStream::new();
/// stream.push_bytes_to_read(&[1, 2, 3, 4, 5, 6]);
/// let mut iter = BufReader::new(stream).split_binary(&[0]);
///
/// assert_eq!(iter.next().unwrap().unwrap(), [1, 2, 3, 4, 5, 6]);
/// assert!(iter.next().is_none());
/// ```
///
/// If it input only consist of an EOF it won't return anything.
/// ```
/// # use ifs::Ifs;
/// # use mockstream::MockStream;
/// # use std::io::{self, BufReader};
/// let mut stream = MockStream::new();
/// stream.push_bytes_to_read(&[]);
/// let mut iter = BufReader::new(stream).split_binary(&[0]);
///
/// assert!(iter.next().is_none());
/// ```
///
/// [`ifs::Ifs`]: crate::Ifs
/// [`split_binary`]: crate::Ifs::split_binary
/// [`io::Result`]: std::io::Result
/// [`read_to_end`]: std::io::Read::read_to_end
#[derive(Debug)]
pub struct SplitBinary<'a, R> {
    inner: R,
    delim: &'a [u8],
}

impl<'a, R> SplitBinary<'a, R> {
    /// Constructs a new iterator.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use ifs::SplitBinary;
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///    let reader = BufReader::new(File::open("a.out")?);
    ///    let mut ifs = SplitBinary::new(reader, &[0x42]);
    ///
    ///    Ok(())
    /// }
    /// ```
    pub fn new(inner: R, delim: &'a [u8]) -> SplitBinary<'a, R> {
        SplitBinary { inner, delim }
    }

    /// Gets a reference to the underlying buffered reader.
    ///
    /// It's completly fine to borrow it but output won't be delimeted.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use ifs::SplitBinary;
    /// # use std::io::BufReader;
    /// # use std::fs::File;
    /// # let reader1 = BufReader::new(File::open("").unwrap());
    /// let mut ifs = SplitBinary::new(reader1, &[0, 1, 0, 1]);
    ///
    /// let reader2 = ifs.get_ref();
    /// ```
    pub fn get_ref(&self) -> &R {
        &self.inner
    }

    /// Gets a mutable reference to the underlying buffered reader.
    ///
    /// It's completly fine to borrow it but output won't be delimeted.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use ifs::SplitBinary;
    /// # use std::io::BufReader;
    /// # use std::fs::File;
    /// # let reader1 = BufReader::new(File::open("").unwrap());
    /// let mut ifs = SplitBinary::new(reader1, &[0x45, 0x67, 0x89]);
    ///
    /// let mut reader2 = ifs.get_mut();
    /// ```
    pub fn get_mut(&mut self) -> &mut R {
        &mut self.inner
    }

    /// Destroys iterator and returns the underlying buffered reader.
    ///
    /// Note that no data is being lost here. No internal buffer is being used
    /// together with the buffered reader.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use ifs::SplitBinary;
    /// # use std::io::BufReader;
    /// # use std::fs::File;
    /// # let reader1 = BufReader::new(File::open("").unwrap());
    /// let mut ifs = SplitBinary::new(reader1, &[0x45, 0x67, 0x89]);
    ///
    /// let reader2 = ifs.into_inner();
    /// ```
    pub fn into_inner(self) -> R {
        self.inner
    }

    /// Gets a reference to the delimeter used.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use ifs::SplitBinary;
    /// # use std::io::BufReader;
    /// # use std::fs::File;
    /// # let reader1 = BufReader::new(File::open("").unwrap());
    /// let delim1 = &[0x45, 0x67, 0x89];
    /// let mut ifs = SplitBinary::new(reader1, delim1);
    ///
    /// let delim2 = ifs.get_delim();
    /// ```
    pub fn get_delim(&self) -> &[u8] {
        self.delim
    }

    /// Sets a new delimeter.
    ///
    /// # Examples
    ///    
    /// ```no_run
    /// # use ifs::SplitBinary;
    /// # use std::io::BufReader;
    /// # use std::fs::File;
    /// # let reader1 = BufReader::new(File::open("").unwrap());
    /// let delim1 = [0x45, 0x67, 0x89];
    /// let mut ifs = SplitBinary::new(reader1, &delim1);
    ///     
    /// let delim2 = [0xCD];
    /// ifs.set_delim(&delim2);
    /// ```
    pub fn set_delim(&mut self, delim: &'a [u8]) {
        self.delim = delim;
    }
}

impl<R: BufRead> Iterator for SplitBinary<'_, R> {
    // Why return a Vec<T>? Well the implementation requires a dynamic resizable
    // buffer and it's possible that some performance is gained by not doing any
    // preemptive shrinking or memory optimization as the consumer might as well
    // use the Vec once and drop it.
    type Item = Result<Vec<u8>, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut buf = Vec::new();
        let delim = self.delim;

        // Edge check; Check so delim is not null
        // else return one byte at a time
        if delim.is_empty() {
            buf.resize(1, 0);
            return match self.inner.read_exact(&mut buf[..1]) {
                Ok(_) => Some(Ok(buf)),
                Err(e) if e.kind() == ErrorKind::UnexpectedEof => None,
                Err(e) => Some(Err(e)),
            };
        }

        // Read until end of delim byte and check if delim exists at the end
        // of the buffer or read in more if it was a false positive
        loop {
            match self.inner.read_until(*delim.last().unwrap(), &mut buf) {
                Ok(0) => return if buf.is_empty() { None } else { Some(Ok(buf)) },
                Ok(_) if contains(&buf, &delim) => {
                    buf.truncate(buf.len() - delim.len());
                    return Some(Ok(buf));
                }
                Err(e) => return Some(Err(e)),
                _ => continue,
            }
        }
    }
}

/// An iterator over delimeted utf8 string fields.
///
/// Can be created by importing `ifs::Ifs` and calling `fields` on
/// `std::io::BufReader`.
#[derive(Debug)]
pub struct SplitString<'a, R> {
    inner: R,
    delim: &'a str,
}

impl<'a, R> SplitString<'a, R> {
    /// Constructs a new iterator.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use ifs::SplitString;
    /// use std::io::{self, BufReader};
    /// use std::fs::File;
    ///
    /// fn main() {
    ///    let reader = BufReader::new(io::stdin());
    ///    let mut ifs = SplitString::new(reader, ";");
    /// }
    /// ```
    pub fn new(inner: R, delim: &'a str) -> SplitString<'a, R> {
        SplitString { inner, delim }
    }

    /// Gets a reference to the underlying buffered reader.
    ///
    /// It's completly fine to borrow it but output won't be delimeted.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use ifs::SplitString;
    /// # use std::io::BufReader;
    /// # use std::fs::File;
    /// # let reader1 = BufReader::new(File::open("").unwrap());
    /// let mut ifs = SplitString::new(reader1, "bar");
    ///
    /// let reader2 = ifs.get_ref();
    /// ```
    pub fn get_ref(&self) -> &R {
        &self.inner
    }

    /// Gets a mutable reference to the underlying buffered reader.
    ///
    /// It's completly fine to borrow it but output won't be delimeted.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use ifs::SplitString;
    /// # use std::io::BufReader;
    /// # use std::fs::File;
    /// # let reader1 = BufReader::new(File::open("").unwrap());
    /// let mut ifs = SplitString::new(reader1, "bar");
    ///
    /// let mut reader2 = ifs.get_mut();
    /// ```
    pub fn get_mut(&mut self) -> &mut R {
        &mut self.inner
    }

    /// Destroys iterator and returns the underlying buffered reader.
    ///
    /// Note that no data is being lost here. No internal buffer is being used
    /// together with the buffered reader.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use ifs::SplitString;
    /// # use std::io::BufReader;
    /// # use std::fs::File;
    /// # let reader1 = BufReader::new(File::open("").unwrap());
    /// let mut ifs = SplitString::new(reader1, "bar");
    ///
    /// let reader2 = ifs.into_inner();
    /// ```
    pub fn into_inner(self) -> R {
        self.inner
    }

    /// Gets a reference to the delimeter used.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use ifs::SplitString;
    /// # use std::io::BufReader;
    /// # use std::fs::File;
    /// # let reader1 = BufReader::new(File::open("").unwrap());
    /// let delim1 = "bar";
    /// let mut ifs = SplitString::new(reader1, delim1);
    ///
    /// let delim2 = ifs.get_delim();
    /// ```
    pub fn get_delim(&self) -> &str {
        &self.delim
    }

    /// Sets a new delimeter.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use ifs::SplitString;
    /// # use std::io::BufReader;
    /// # use std::fs::File;
    /// # let reader1 = BufReader::new(File::open("").unwrap());
    /// let delim1 = "bar";
    /// let ifs = SplitString::new(reader1, delim1);
    ///
    /// let delim2 = ifs.get_delim();
    /// ```
    pub fn set_delim(&mut self, delim: &'a str) {
        self.delim = delim;
    }
}

impl<R: BufRead> Iterator for SplitString<'_, R> {
    type Item = Result<String, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut buf = Vec::new();
        let delim = self.delim.as_bytes();

        // Due to implementation difficulty
        // it cannot return one character at the time,
        // like it's binary counterpart can and it will likely stay that way.
        if delim.is_empty() {
            let mut buf = String::new();
            return match self.inner.read_to_string(&mut buf) {
                Ok(0) => None,
                Ok(_) => Some(Ok(buf)),
                Err(e) => Some(Err(e)),
            };
        }

        loop {
            match self.inner.read_until(*delim.last().unwrap(), &mut buf) {
                Ok(0) => return utf8_wrapup(buf),
                Ok(_) if contains(&buf, &delim) => {
                    buf.truncate(buf.len() - delim.len());
                    return utf8_wrapup(buf);
                }
                Err(e) => return Some(Err(e)),
                _ => continue,
            }
        }
    }
}

pub trait Ifs<'a> {
    /// Returns an iterator over delimeted bytes of this reader.
    ///
    /// The iterator will yield instances of [`io::Result`]<[`Vec<u8>`]>.
    /// Each Vector wont have the delimeter at it's end.
    /// If the delimeter is empty the iterator will shortcircuit and
    /// return everything read by [`read_to_end`].
    ///
    /// [`io::Result`]: std::io::Result
    /// [`read_to_end`]: std::io::Read::read_to_end
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use ifs::Ifs;
    /// use std::io::{self, BufRead};
    /// use std::fs::File;
    ///
    /// fn main() -> io::Result<()> {
    ///     let file = File::open("ladder.bin")?; // 0x0123456789ABCDEF
    ///     let reader = io::BufReader::new(file);
    ///
    ///     let mut ifs = reader.split_binary(&[0x45, 0x67, 0x89]);
    ///
    ///     assert_eq!(ifs.next().unwrap().unwrap(), [0x01, 0x23]);
    ///     assert_eq!(ifs.next().unwrap().unwrap(), [0xAB, 0xCD, 0xEF]);
    ///     assert!(ifs.next().is_none());
    ///     Ok(())
    /// }
    /// ```
    fn split_binary(self, delim: &'a [u8]) -> SplitBinary<'a, Self>
    where
        Self: BufRead + Sized,
    {
        SplitBinary::new(self, delim)
    }

    /// Returns an iterator over delimeted strings of this reader.
    ///
    /// The iterator will yield instances of [`io::Result`]<[`String`]>.
    /// Each String wont have the delimeter at it's end.
    /// If the delimeter is empty the iterator will shortcircuit and
    /// return everything read by [`read_to_end`].
    ///
    /// [`io::Result`]: std::io::Result
    /// [`read_to_end`]: std::io::Read::read_to_end
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use ifs::Ifs;
    /// use std::io::{self, BufRead};
    /// use std::fs::File;
    ///
    /// fn main() -> io::Result<()> {
    ///     let file = File::open("doctest.txt")?; // foobarbazfoobarbaz
    ///     let reader = io::BufReader::new(file);
    ///
    ///     let mut ifs = reader.split_string("bar");
    ///
    ///     assert_eq!(ifs.next().unwrap().unwrap(), "foo");
    ///     assert_eq!(ifs.next().unwrap().unwrap(), "bazfoo");
    ///     assert_eq!(ifs.next().unwrap().unwrap(), "baz");
    ///     assert!(ifs.next().is_none());
    ///     Ok(())
    /// }
    /// ```
    fn split_string(self, delim: &'a str) -> SplitString<'a, Self>
    where
        Self: BufRead + Sized,
    {
        SplitString::new(self, delim)
    }
}

impl<R> Ifs<'_> for std::io::BufReader<R> {}
