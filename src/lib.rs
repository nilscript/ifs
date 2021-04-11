#![feature(option_result_contains)]

use std::io::{BufRead, Error, ErrorKind};

#[derive(Debug)]
pub struct Separator<R, D> {
    inner: R,
    delim: D,
}

impl<R: BufRead, D: AsRef<[u8]>> Separator<R, D> {
    /// Construct a new IfsReader.
    ///
    /// If delim is empty returns everything from inner reader.
    pub fn new(inner: R, delim: D) -> Separator<R, D> {
        Separator { inner, delim }
    }

    pub fn get_ref(&self) -> &R {
        &self.inner
    }

    pub fn get_mut(&mut self) -> &mut R {
        &mut self.inner
    }

    pub fn into_inner(self) -> R {
        self.inner
    }

    pub fn get_delim(&self) -> &D {
        &self.delim
    }

    pub fn set_delim(&mut self, delim: D) {
        self.delim = delim;
    }
}

impl<R: BufRead, D: AsRef<[u8]>> Iterator for Separator<R, D> {
    type Item = Result<Vec<u8>, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut buf = Vec::new();
        let delim = self.delim.as_ref();

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
        if delim.is_empty() {
            return match self.inner.read_to_end(&mut buf) {
                Ok(0) => None,
                Ok(_) => Some(Ok(buf)),
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

pub struct Fields<R, D> {
    inner: Separator<R, D>,
}

impl<R: BufRead, D: AsRef<[u8]>> Fields<R, D> {
    pub fn new(inner: R, delim: D) -> Fields<R, D> {
        Fields {
            inner: Separator::new(inner, delim),
        }
    }

    pub fn get_ref(&self) -> &R {
        self.inner.get_ref()
    }

    pub fn get_mut(&mut self) -> &mut R {
        self.inner.get_mut()
    }

    pub fn into_inner(self) -> R {
        self.inner.into_inner()
    }

    pub fn get_delim(&self) -> &D {
        self.inner.get_delim()
    }

    pub fn set_delim(&mut self, delim: D) {
        self.inner.set_delim(delim);
    }
}

impl<R: BufRead, D: AsRef<[u8]>> Iterator for Fields<R, D> {
    type Item = Result<String, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        let conv = |vec| String::from_utf8(vec).map_err(|e| Error::new(ErrorKind::Other, e));
        self.inner.next().map(|res| res.and_then(conv))
    }
}

pub trait Ifs<D> {
    fn separator(self, delim: D) -> Separator<Self, D>
    where
        D: AsRef<[u8]>,
        Self: BufRead + Sized,
    {
        Separator::new(self, delim)
    }

    fn fields(self, delim: D) -> Fields<Self, D>
    where
        D: AsRef<[u8]>,
        Self: BufRead + Sized,
    {
        Fields::new(self, delim)
    }
}

impl<R, D> Ifs<D> for std::io::BufReader<R> {}

#[cfg(test)]
mod tests {
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
    fn many_returns() {
        let mut stream = MockStream::new();
        stream.push_bytes_to_read(&[0, 1, 0, 1, 0, 1, 1, 0, 1]);
        let mut reader = BufReader::new(stream).separator([1]);
        assert_eq!(reader.next().unwrap().unwrap(), [0]);
        assert_eq!(reader.next().unwrap().unwrap(), [0]);
        assert_eq!(reader.next().unwrap().unwrap(), [0]);
        assert_eq!(reader.next().unwrap().unwrap(), []);
        assert_eq!(reader.next().unwrap().unwrap(), [0]);
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
    fn string() {
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
        let mut reader = BufReader::new(stream).separator(", ");
        assert_eq!(reader.next().unwrap().unwrap(), b"foo");
        assert_eq!(reader.next().unwrap().unwrap(), b"bar");
        assert_eq!(reader.next().unwrap().unwrap(), b"baz");
    }
}
