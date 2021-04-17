#![feature(option_result_contains)]

use std::io::{BufRead, Error, ErrorKind};
use std::str;

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
/// ```
/// # use ifs::Ifs;
/// # use std::io::{self, BufReader};
/// # use std::fs::File;
/// let file = File::open("res/doctest-ladder.bin").unwrap();
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
    /// ```
    /// use ifs::SplitBinary;
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///    let reader = BufReader::new(File::open("res/doctest-ladder.bin")?);
    ///    let mut ifs = SplitBinary::new(reader, &[0x45, 0x67, 0x89]);
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
    /// ```
    /// use ifs::SplitBinary;
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let reader1 = BufReader::new(File::open("res/doctest-ladder.bin")?);
    ///     let mut ifs = SplitBinary::new(reader1, &[0x45, 0x67, 0x89]);
    ///
    ///     let reader2 = ifs.get_ref();
    ///     Ok(())
    /// }
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
    /// ```
    /// use ifs::SplitBinary;
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let reader1 = BufReader::new(File::open("res/doctest-ladder.bin")?);
    ///     let mut ifs = SplitBinary::new(reader1, &[0x45, 0x67, 0x89]);
    ///
    ///     let mut reader2 = ifs.get_mut();
    ///     Ok(())
    /// }
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
    /// ```
    /// use ifs::SplitBinary;
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let reader1 = BufReader::new(File::open("res/doctest-ladder.bin")?);
    ///     let mut ifs = SplitBinary::new(reader1, &[0x45, 0x67, 0x89]);
    ///
    ///     let reader2 = ifs.into_inner();
    ///     Ok(())
    /// }
    /// ```
    pub fn into_inner(self) -> R {
        self.inner
    }

    /// Gets a reference to the delimeter used.
    ///
    /// # Examples
    ///
    /// ```
    /// use ifs::SplitBinary;
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let reader1 = BufReader::new(File::open("res/doctest-ladder.bin")?);
    ///     let delim1 = &[0x45, 0x67, 0x89];
    ///     let mut ifs = SplitBinary::new(reader1, delim1);
    ///
    ///     let delim2 = ifs.get_delim();
    ///     Ok(())
    /// }
    /// ```
    pub fn get_delim(&self) -> &[u8] {
        self.delim
    }

    /// Sets a new delimeter.
    ///
    /// # Examples
    ///
    /// ```
    /// use ifs::SplitBinary;
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let reader1 = BufReader::new(File::open("res/doctest-ladder.bin")?);
    ///     let delim1 = [0x45, 0x67, 0x89];
    ///     let mut ifs = SplitBinary::new(reader1, &delim1);
    ///     assert_eq!(ifs.next().unwrap().unwrap(), [0x01, 0x23]);
    ///     
    ///     let delim2 = [0xCD];
    ///     ifs.set_delim(&delim2);
    ///     assert_eq!(ifs.next().unwrap().unwrap(), [0xAB]);
    ///     assert_eq!(ifs.next().unwrap().unwrap(), [0xEF]);
    ///     assert!(ifs.next().is_none());
    ///     Ok(())
    /// }
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

        // Check the back for our matching delimeter
        // With read_until we get the last byte in delim,
        // so theory goes we also read in the entire delim
        // and buffer contains it
        let contains = |haystack: &[u8], needle: &[u8]| {
            haystack
                .rchunks_exact(needle.len())
                .next()
                .contains(&needle)
        };

        // Edge check; Check so delim is not null
        // else return everything in reader
        /*
        if delim.is_empty() {
            return match self.inner.read_to_end(&mut buf) {
                Ok(0) => None,
                Ok(_) => Some(Ok(buf)),
                Err(e) => Some(Err(e)),
            };
        }*/

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

/// An iterator over delimeted string fields.
///
/// Can be created by importing `ifs::Ifs` and calling `fields` on
/// `std::io::BufReader`.
#[derive(Debug)]
pub struct SplitString<'a, R> {
    inner: SplitBinary<'a, R>,
}

impl<'a, R> SplitString<'a, R> {
    /// Constructs a new iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use ifs::SplitString;
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///    let reader = BufReader::new(File::open("res/doctest.txt")?);
    ///    let mut ifs = SplitString::new(reader, "bar");
    ///
    ///    Ok(())
    /// }
    /// ```
    pub fn new(inner: R, delim: &'a str) -> SplitString<'a, R> {
        SplitString {
            inner: SplitBinary::new(inner, delim.as_bytes()),
        }
    }

    /// Gets a reference to the underlying buffered reader.
    ///
    /// It's completly fine to borrow it but output won't be delimeted.
    ///
    /// # Examples
    ///
    /// ```
    /// use ifs::SplitString;
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let reader1 = BufReader::new(File::open("res/doctest.txt")?);
    ///     let mut ifs = SplitString::new(reader1, "bar");
    ///
    ///     let reader2 = ifs.get_ref();
    ///     Ok(())
    /// }
    /// ```
    pub fn get_ref(&self) -> &R {
        self.inner.get_ref()
    }

    /// Gets a mutable reference to the underlying buffered reader.
    ///
    /// It's completly fine to borrow it but output won't be delimeted.
    ///
    /// # Examples
    ///
    /// ```
    /// use ifs::SplitString;
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let reader1 = BufReader::new(File::open("res/doctest.txt")?);
    ///     let mut ifs = SplitString::new(reader1, "bar");
    ///
    ///     let mut reader2 = ifs.get_mut();
    ///     Ok(())
    /// }
    /// ```
    pub fn get_mut(&mut self) -> &mut R {
        self.inner.get_mut()
    }

    /// Destroys iterator and returns the underlying buffered reader.
    ///
    /// Note that no data is being lost here. No internal buffer is being used
    /// together with the buffered reader.
    ///
    /// # Examples
    ///
    /// ```
    /// use ifs::SplitString;
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let reader1 = BufReader::new(File::open("res/doctest.txt")?);
    ///     let mut ifs = SplitString::new(reader1, "bar");
    ///
    ///     let reader2 = ifs.into_inner();
    ///     Ok(())
    /// }
    /// ```
    pub fn into_inner(self) -> R {
        self.inner.into_inner()
    }

    /// Gets a reference to the delimeter used.
    ///
    /// # Examples
    ///
    /// ```
    /// use ifs::SplitString;
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let reader1 = BufReader::new(File::open("res/doctest.txt")?);
    ///     let delim1 = "bar";
    ///     let mut ifs = SplitString::new(reader1, delim1);
    ///
    ///     let delim2 = ifs.get_delim();
    ///     Ok(())
    /// }
    /// ```
    pub fn get_delim(&self) -> &str {
        unsafe { str::from_utf8_unchecked(self.inner.get_delim()) }
    }

    /// Sets a new delimeter.
    ///
    /// # Examples
    ///
    /// ```
    /// use ifs::SplitString;
    /// use std::io::BufReader;
    /// use std::fs::File;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let reader1 = BufReader::new(File::open("res/doctest.txt")?);
    ///     let delim1 = "bar";
    ///     let ifs = SplitString::new(reader1, delim1);
    ///
    ///     let delim2 = ifs.get_delim();
    ///     Ok(())
    /// }
    /// ```
    pub fn set_delim(&mut self, delim: &'a str) {
        self.inner.set_delim(delim.as_bytes());
    }
}

impl<R: BufRead> Iterator for SplitString<'_, R> {
    type Item = Result<String, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        let conv = |vec| String::from_utf8(vec).map_err(|e| Error::new(ErrorKind::Other, e));
        self.inner.next().map(|res| res.and_then(conv))
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
    /// ```
    /// use ifs::Ifs;
    /// use std::io::{self, BufRead};
    /// use std::fs::File;
    ///
    /// fn main() -> io::Result<()> {
    ///     let file = File::open("res/doctest-ladder.bin")?;
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
    /// ```
    /// use ifs::Ifs;
    /// use std::io::{self, BufRead};
    /// use std::fs::File;
    ///
    /// fn main() -> io::Result<()> {
    ///     let file = File::open("res/doctest.txt")?; // foobarbaz
    ///     let reader = io::BufReader::new(file);
    ///
    ///     let mut ifs = reader.split_string("bar");
    ///
    ///     assert_eq!(ifs.next().unwrap().unwrap(), "foo");
    ///     assert_eq!(ifs.next().unwrap().unwrap(), "bazfoo");
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

/*
#[cfg(test)]
mod separator_tests {
    use super::{Ifs, Separator};
    use mockstream::MockStream;
    use std::io::{BufRead, BufReader};

    fn assert_none<R, D>(mut reader: Separator<R, D>)
    where
        R: BufRead,
        D: AsRef<[u8]>,
    {
        assert!(reader.next().is_none());
        assert!(reader.next().is_none());
    }

    #[test]
    fn no_input() {
        let reader = BufReader::new(MockStream::new()).separator([4]);
        assert_none(reader);
    }

    #[test]
    fn no_detectable_delim_pattern() {
        let mut stream = MockStream::new();
        stream.push_bytes_to_read(&[0, 1, 2, 3, 4, 5, 6]);
        let mut reader = BufReader::new(stream).separator([7]);
        assert_eq!(reader.next().unwrap().unwrap(), [0, 1, 2, 3, 4, 5, 6]);
        assert_none(reader);
    }

    #[test]
    fn detectable_delim_pattern() {
        let mut stream = MockStream::new();
        stream.push_bytes_to_read(&[0, 1, 2, 3, 4, 5, 6, 7]);
        let mut reader = BufReader::new(stream).separator([3]);
        assert_eq!(reader.next().unwrap().unwrap(), [0, 1, 2]);
        assert_eq!(reader.next().unwrap().unwrap(), [4, 5, 6, 7]);
        assert_none(reader);
    }

    #[test]
    fn no_delim() {
        let mut stream = MockStream::new();
        stream.push_bytes_to_read(&[0, 1, 2, 3, 4, 5, 6]);
        let mut reader = BufReader::new(stream).separator([]);
        assert_eq!(reader.next().unwrap().unwrap(), [0, 1, 2, 3, 4, 5, 6]);
        assert_none(reader);
    }

    #[test]
    fn complex_delim() {
        let mut stream = MockStream::new();
        stream.push_bytes_to_read(&[0, 1, 2, 3, 4, 5, 6]);
        let mut reader = BufReader::new(stream).separator([3, 4]);
        assert_eq!(reader.next().unwrap().unwrap(), [0, 1, 2]);
        assert_eq!(reader.next().unwrap().unwrap(), [5, 6]);
        assert_none(reader);
    }

    #[test]
    fn complexer_delim() {
        let mut stream = MockStream::new();
        stream.push_bytes_to_read(&[9, 0, 9, 9, 9, 0, 9, 0, 9, 9, 9, 9, 9, 9, 9]);
        let mut reader = BufReader::new(stream).separator([9, 9]);
        assert_eq!(reader.next().unwrap().unwrap(), [9, 0]);
        assert_eq!(reader.next().unwrap().unwrap(), [9, 0, 9, 0]);
        assert_eq!(reader.next().unwrap().unwrap(), []);
        assert_eq!(reader.next().unwrap().unwrap(), []);
        assert_eq!(reader.next().unwrap().unwrap(), [9]);
        assert_none(reader);
    }

    #[test]
    fn many_returns_complex_delim() {
        let mut stream = MockStream::new();
        stream.push_bytes_to_read(&[
            0, 1, 3, 4, 0, 1, 0, 3, 4, 3, 0, 1, 2, 3, 4, 3, 4, 3, 1, 3, 3, 4, 3, 4,
        ]);
        let mut reader = BufReader::new(stream).separator([3, 4]);
        assert_eq!(reader.next().unwrap().unwrap(), vec![0, 1]);
        assert_eq!(reader.next().unwrap().unwrap(), vec![0, 1, 0]);
        assert_eq!(reader.next().unwrap().unwrap(), vec![3, 0, 1, 2]);
        assert_eq!(reader.next().unwrap().unwrap(), vec![]);
        assert_eq!(reader.next().unwrap().unwrap(), vec![3, 1, 3]);
        assert_eq!(reader.next().unwrap().unwrap(), vec![]);
        assert_none(reader);
    }

    #[test]
    fn simple_bit_string_delim() {
        let mut stream = MockStream::new();
        stream.push_bytes_to_read(b"Hello World!");
        let mut reader = BufReader::new(stream).separator(" ");
        assert_eq!(reader.next().unwrap().unwrap(), b"Hello");
        assert_eq!(reader.next().unwrap().unwrap(), b"World!")
    }

    #[test]
    fn complex_delim_string() {
        let mut stream = MockStream::new();
        stream.push_bytes_to_read(b"foo, bar, baz");
        let mut reader = BufReader::new(stream).separator(b", ");
        assert_eq!(reader.next().unwrap().unwrap(), b"foo");
        assert_eq!(reader.next().unwrap().unwrap(), b"bar");
        assert_eq!(reader.next().unwrap().unwrap(), b"baz");
    }
}
*/
