#![feature(option_result_contains)]
#![feature(associated_type_bounds)]
#![feature(shrink_to)]
#![feature(read_initializer)]
#![feature(toowned_clone_into)]

use std::io::{BufRead, Error, ErrorKind};

#[derive(Debug)]
pub struct IfsReader<'a, R> {
    inner: R,
    delim: &'a [u8],
}

impl<R: BufRead> IfsReader<'_, R> {
    /// Construct a new IfsReader.
    ///
    /// If delim is empty returns everything from inner reader.
    pub fn new(inner: R, delim: &'_ [u8]) -> IfsReader<R> {
        IfsReader { inner, delim }
    }
}

impl<'a, R> IfsReader<'a, R> {
    pub fn get_ref(&self) -> &R {
        &self.inner
    }

    pub fn get_mut(&mut self) -> &mut R {
        &mut self.inner
    }

    pub fn into_inner(self) -> R {
        self.inner
    }

    pub fn get_delim(&self) -> &[u8] {
        &self.delim
    }

    pub fn set_delim(&mut self, delim: &'a [u8]) {
        self.delim = delim;
    }
}

impl<R: BufRead> Iterator for IfsReader<'_, R> {
    type Item = Result<Vec<u8>, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut buf = Vec::new();

        // Edge check; Check so delim is not null
        // else return everything in reader
        if self.delim.is_empty() {
            return match self.inner.read_to_end(&mut buf) {
                Ok(read) if read == 0 => None,
                Ok(_) => Some(Ok(buf)),
                Err(e) => Some(Err(e)),
            };
        }

        loop {
            // Read until delim[0] or eof
            if let Err(e) = self.inner.read_until(self.delim[0], &mut buf) {
                return Some(Err(e));
            } else if self.delim.first() != buf.last() {
                // Reader did not put matching delim at the end of buffer
                return if buf.is_empty() { None } else { Some(Ok(buf)) };
            }

            // Last position before delim
            let pos = buf.len() - 1;
            buf.resize(pos + self.delim.len(), 0);

            // Read in rest of delim
            match self.inner.read_exact(&mut buf[pos + 1..]) {
                // Skip comparing 1 byte of delim as it's already checked
                Ok(_) if self.delim[1..].eq(&buf[pos + 1..]) => {
                    return Some(Ok(buf[..pos].to_vec()));
                }
                // Eof means that we found no delim, which is not an issue
                Err(e) if e.kind().eq(&ErrorKind::UnexpectedEof) => {
                    return Some(Ok(buf));
                }
                Err(e) => return Some(Err(e)),
                _ => (),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::IfsReader;
    use mockstream::MockStream;
    use std::io::BufRead;
    use std::io::BufReader;
    fn assert_none<R: BufRead>(mut reader: IfsReader<R>) {
        assert!(reader.next().is_none());
        assert!(reader.next().is_none());
    }

    #[test]
    fn no_detectable_delim_pattern() {
        let mut stream = MockStream::new();
        stream.push_bytes_to_read(&[0, 1, 2, 3, 4, 5, 6]);
        let inner = BufReader::new(stream);
        let delim = [7];
        let mut reader = IfsReader::new(inner, &delim);
        assert_eq!(reader.next().unwrap().unwrap(), vec![0, 1, 2, 3, 4, 5, 6]);
        assert_none(reader);
    }

    #[test]
    fn detectable_delim_pattern() {
        let mut stream = MockStream::new();
        stream.push_bytes_to_read(&[0, 1, 2, 3, 4, 5, 6, 7]);
        let inner = BufReader::new(stream);
        let delim = [3];
        let mut reader = IfsReader::new(inner, &delim);
        assert_eq!(reader.next().unwrap().unwrap(), vec![0, 1, 2]);
        assert_eq!(reader.next().unwrap().unwrap(), vec![4, 5, 6, 7]);
        assert_none(reader);
    }

    #[test]
    fn no_delim() {
        let mut stream = MockStream::new();
        stream.push_bytes_to_read(&[0, 1, 2, 3, 4, 5, 6]);
        let inner = BufReader::new(stream);
        let delim = [];
        let mut reader = IfsReader::new(inner, &delim);
        assert_eq!(reader.next().unwrap().unwrap(), vec![0, 1, 2, 3, 4, 5, 6]);
        assert_none(reader);
    }

    #[test]
    fn complex_delim() {
        let mut stream = MockStream::new();
        stream.push_bytes_to_read(&[0, 1, 2, 3, 4, 5, 6]);
        let inner = BufReader::new(stream);
        let delim = [3, 4];
        let mut reader = IfsReader::new(inner, &delim);
        assert_eq!(reader.next().unwrap().unwrap(), vec![0, 1, 2]);
        assert_eq!(reader.next().unwrap().unwrap(), vec![5, 6]);
        assert_none(reader);
    }

    #[test]
    fn many_returns() {
        let mut stream = MockStream::new();
        stream.push_bytes_to_read(&[0, 1, 0, 1, 0, 1, 1, 0, 1]);
        let inner = BufReader::new(stream);
        let delim = [1];
        let mut reader = IfsReader::new(inner, &delim);
        assert_eq!(reader.next().unwrap().unwrap(), vec![0]);
        assert_eq!(reader.next().unwrap().unwrap(), vec![0]);
        assert_eq!(reader.next().unwrap().unwrap(), vec![0]);
        assert_eq!(reader.next().unwrap().unwrap(), vec![]);
        assert_eq!(reader.next().unwrap().unwrap(), vec![0]);
        assert_none(reader);
    }

    #[test]
    fn many_returns_complex_delim() {
        let mut stream = MockStream::new();
        stream.push_bytes_to_read(&[0, 1, 3, 4, 0, 1, 0, 3, 4, 3, 0, 1, 2, 3, 4, 3, 4, 3, 1]);
        let inner = BufReader::new(stream);
        let delim = [3, 4];
        let mut reader = IfsReader::new(inner, &delim);
        assert_eq!(reader.next().unwrap().unwrap(), vec![0, 1]);
        assert_eq!(reader.next().unwrap().unwrap(), vec![0, 1, 0]);
        assert_eq!(reader.next().unwrap().unwrap(), vec![3, 0, 1, 2]);
        assert_eq!(reader.next().unwrap().unwrap(), vec![]);
        assert_eq!(reader.next().unwrap().unwrap(), vec![3, 1]);
        assert_none(reader);
    }

    #[test]
    fn string() {
        let mut stream = MockStream::new();
        stream.push_bytes_to_read(b"Hello World!");
        let inner = BufReader::new(stream);
        let delim = b" ";
        let mut reader = IfsReader::new(inner, delim);
        assert_eq!(reader.next().unwrap().unwrap(), b"Hello");
        assert_eq!(reader.next().unwrap().unwrap(), b"World!")
    }

    #[test]
    fn complex_delim_string() {
        let mut stream = MockStream::new();
        stream.push_bytes_to_read(b"foo, bar, baz");
        let inner = BufReader::new(stream);
        let delim = b", ";
        let mut reader = IfsReader::new(inner, delim);
        assert_eq!(reader.next().unwrap().unwrap(), b"foo");
        assert_eq!(reader.next().unwrap().unwrap(), b"bar");
        assert_eq!(reader.next().unwrap().unwrap(), b"baz");
    }
}
