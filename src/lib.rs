/*!
TODO
*/

extern crate encoding_rs;

use std::io::{self, Read};

use encoding_rs::{Decoder, Encoding, UTF_8};

use util::BomPeeker;

mod util;

/// A builder for constructing a byte oriented transcoder to UTF-8.
pub struct DecodeReaderBytesBuilder {
    encoding: Option<&'static Encoding>,
    utf8_passthru: bool,
}

impl Default for DecodeReaderBytesBuilder {
    fn default() -> DecodeReaderBytesBuilder {
        DecodeReaderBytesBuilder::new()
    }
}

impl DecodeReaderBytesBuilder {
    /// Create a new decoder builder with a default configuration.
    ///
    /// By default, no explicit encoding is used, but if a UTF-8 or UTF-16
    /// BOM is detected, then an appropriate encoding is automatically
    /// detected and transcoding is performed (where invalid sequences map to
    /// the Unicode replacement codepoint).
    pub fn new() -> DecodeReaderBytesBuilder {
        DecodeReaderBytesBuilder {
            encoding: None,
            utf8_passthru: false,
        }
    }

    /// Build a new decoder that wraps the given reader.
    pub fn build<R: io::Read>(
        &self,
        rdr: R,
    ) -> DecodeReaderBytes<R, Vec<u8>> {
        self.build_with_buffer(rdr, Vec::with_capacity(8 * (1<<10)))
    }

    /// Build a new decoder that wraps the given reader and uses the given
    /// buffer internally for transcoding.
    ///
    /// This is useful for cases where it is advantageuous to amortize
    /// allocation. Namely, this method permits reusing a buffer for
    /// subsequent decoders.
    pub fn build_with_buffer<R: io::Read, B: AsMut<[u8]>>(
        &self,
        rdr: R,
        buffer: B,
    ) -> DecodeReaderBytes<R, B> {
        let encoding = self.encoding
            .map(|enc| enc.new_decoder_with_bom_removal());
        DecodeReaderBytes {
            rdr: BomPeeker::new(rdr),
            buf: buffer,
            buflen: 0,
            pos: 0,
            first: encoding.is_none(),
            last: false,
            decoder: encoding,
            utf8_passthru: self.utf8_passthru,
        }
    }

    /// Set an explicit encoding to be used by this decoder.
    ///
    /// When an explicit encoding is set, BOM sniffing is disabled and the
    /// encoding provided will be used unconditionally. Errors in the encoded
    /// bytes are replaced by the Unicode replacement codepoint.
    ///
    /// By default, no explicit encoding is set.
    pub fn encoding(
        &mut self,
        encoding: Option<&'static Encoding>,
    ) -> &mut DecodeReaderBytesBuilder {
        self.encoding = encoding;
        self
    }

    /// Enable UTF-8 passthru, even when a UTF-8 BOM is observed.
    ///
    /// When an explicit encoding is not set (thereby invoking automatic
    /// encoding detection via BOM sniffing), then a UTF-8 BOM will cause
    /// UTF-8 transcoding to occur. In particular, if the source contains
    /// invalid UTF-8 sequences, then they are replaced with the Unicode
    /// replacement codepoint.
    ///
    /// This transcoding may not be desirable. For example, the caller may
    /// already have its own UTF-8 handling where invalid UTF-8 is
    /// appropriately handled, in which case, doing an extra transcoding
    /// step is extra and unnecessary work. Enabling this option will prevent
    /// that extra transcoding step from occurring. In this case, the bytes
    /// emitted by the reader are passed through unchanged and the caller will
    /// be responsible for handling any invalid UTF-8.
    pub fn utf8_passthru(
        &mut self,
        yes: bool,
    ) -> &mut DecodeReaderBytesBuilder {
        self.utf8_passthru = yes;
        self
    }
}

/// A reader that transcodes to UTF-8 in a streaming fashion.
///
/// When no explicit source encoding is specified (via
/// `DecodeReaderBytesBuilder`), the source encoding is determined by
/// inspecting the BOM from the stream read from `R`, if one exists. If a
/// UTF-16 BOM exists, then the source stream is transcoded to UTF-8 with
/// invalid UTF-16 sequences translated to the Unicode replacement character.
/// Similarly if a UTF-8 BOM is seen. In all other cases, the source of the
/// underlying reader is passed through unchanged _as if_ it were UTF-8.
///
/// Since this particular reader does not guarantee providing valid UTF-8 to
/// the caller, the caller must be prepared to handle invalid UTF-8 itself.
///
/// `R` is the type of the underlying reader and `B` is the type of an internal
/// buffer used to store the results of transcoding. Callers may elect to reuse
/// the internal buffer via the `DecodeReaderBytesBuilder::build_with_buffer`
/// constructor.
pub struct DecodeReaderBytes<R, B> {
    /// The underlying reader, wrapped in a peeker for reading a BOM if one
    /// exists.
    rdr: BomPeeker<R>,
    /// The internal buffer to store transcoded bytes before they are read by
    /// callers.
    buf: B,
    /// The current position in `buf`. Subsequent reads start here.
    pos: usize,
    /// The number of transcoded bytes in `buf`. Subsequent reads end here.
    buflen: usize,
    /// Whether this is the first read or not (in which we inspect the BOM).
    first: bool,
    /// Whether a "last" read has occurred. After this point, EOF will always
    /// be returned.
    last: bool,
    /// The underlying text decoder derived from the BOM, if one exists.
    decoder: Option<Decoder>,
    /// When enabled, if a UTF-8 BOM is observed, then the bytes are passed
    /// through from the underlying reader as-is instead of passing through
    /// the UTF-8 transcoder (which will replace invalid sequences with the
    /// REPLACEMENT CHARACTER).
    utf8_passthru: bool,
}

impl<R: io::Read, B: AsMut<[u8]>> DecodeReaderBytes<R, B> {
    /// Create a new transcoder that converts a source stream to valid UTF-8.
    ///
    /// If an encoding is specified, then it is used to transcode `rdr` to
    /// UTF-8. Otherwise, if no encoding is specified, and if a UTF-16 BOM is
    /// found, then the corresponding UTF-16 encoding is used to transcode
    /// `rdr` to UTF-8. In all other cases, `rdr` is assumed to be at least
    /// ASCII-compatible and passed through untouched.
    ///
    /// Errors in the encoding of `rdr` are handled with the Unicode
    /// replacement character. If no encoding of `rdr` is specified, then
    /// errors are not handled.
    pub fn new(
        rdr: R,
        buf: B,
        enc: Option<&'static Encoding>,
    ) -> DecodeReaderBytes<R, B> {
        DecodeReaderBytesBuilder::new()
            .encoding(enc)
            .build_with_buffer(rdr, buf)
    }

    /// Fill the internal buffer from the underlying reader.
    ///
    /// If there are unread bytes in the internal buffer, then we move them
    /// to the beginning of the internal buffer and fill the remainder.
    ///
    /// If the internal buffer is too small to read additional bytes, then an
    /// error is returned.
    fn fill(&mut self) -> io::Result<()> {
        if self.pos < self.buflen {
            if self.buflen >= self.buf.as_mut().len() {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "DecodeReaderBytes: internal buffer exhausted",
                ));
            }
            let newlen = self.buflen - self.pos;
            let mut tmp = Vec::with_capacity(newlen);
            tmp.extend_from_slice(&self.buf.as_mut()[self.pos..self.buflen]);
            self.buf.as_mut()[..newlen].copy_from_slice(&tmp);
            self.buflen = newlen;
        } else {
            self.buflen = 0;
        }
        self.pos = 0;
        self.buflen += self.rdr.read(&mut self.buf.as_mut()[self.buflen..])?;
        Ok(())
    }

    /// Transcode the inner stream to UTF-8 in `buf`. This assumes that there
    /// is a decoder capable of transcoding the inner stream to UTF-8. This
    /// returns the number of bytes written to `buf`.
    ///
    /// When this function returns, exactly one of the following things will
    /// be true:
    ///
    /// 1. A non-zero number of bytes were written to `buf`.
    /// 2. The underlying reader reached EOF.
    /// 3. An error is returned: the internal buffer ran out of room.
    /// 4. An I/O error occurred.
    ///
    /// Note that `buf` must have at least 4 bytes of space.
    fn transcode(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        // BREADCRUMBS:
        //
        // So the key case we need to support here is when `buf` has length
        // less than 4. In this case, we are not guaranteed that the decoder
        // will produce any output to write. If it doesn't, and we return 0
        // bytes written, then we've effectively signaled EOF, which is bad.
        //
        // Our *only* choice is to incrementally transcode to a secondary
        // buffer (say, [u8; 4], which may not be optimal but perhaps we don't
        // need to care about performance here for now), and then feed bytes
        // from that secondary buffer back to the caller until the secondary
        // buffer has been exhausted. At which point, we start over again.
        //
        // We should do our best to come up with an abstraction for the above,
        // since it's kind of gnarly.
        //
        // Finally, consider using naming from:
        // https://github.com/hsivonen/encoding_rs/issues/8#issuecomment-285057121
        // and call this ReadBytesDecoder. We probably want a
        // ReadBytesDecoderBuilder that permits configuring things like UTF-8
        // passthru or a pre-selected encoding.
        assert!(buf.len() >= 4);
        if self.last {
            return Ok(0);
        }
        if self.pos >= self.buflen {
            self.fill()?;
        }
        let mut nwrite = 0;
        loop {
            let (_, nin, nout, _) =
                self.decoder.as_mut().unwrap().decode_to_utf8(
                    &self.buf.as_mut()[self.pos..self.buflen], buf, false);
            self.pos += nin;
            nwrite += nout;
            // If we've written at least one byte to the caller-provided
            // buffer, then our mission is complete.
            if nwrite > 0 {
                break;
            }
            // Otherwise, we know that our internal buffer has insufficient
            // data to transcode at least one char, so we attempt to refill it.
            self.fill()?;
            // Quit on EOF.
            if self.buflen == 0 {
                self.pos = 0;
                self.last = true;
                let (_, _, nout, _) =
                    self.decoder.as_mut().unwrap().decode_to_utf8(
                        &[], buf, true);
                return Ok(nout);
            }
        }
        Ok(nwrite)
    }

    fn detect(&mut self) -> io::Result<()> {
        let bom = self.rdr.peek_bom()?;
        if let Some(encoding) = bom.encoding() {
            // If we got a UTF-8 BOM, and the decoder was configured for
            // passing through UTF-8, then don't build a decoder at all.
            if encoding == UTF_8 && self.utf8_passthru {
                return Ok(());
            }
            self.decoder = Some(encoding.new_decoder_with_bom_removal());
        }
        Ok(())
    }
}

impl<R: io::Read, B: AsMut<[u8]>> io::Read for DecodeReaderBytes<R, B> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if self.first {
            self.first = false;
            self.detect()?;
        }
        if self.decoder.is_none() {
            return self.rdr.read(buf);
        }
        // When decoding UTF-8, we need at least 4 bytes of space to guarantee
        // that we can decode at least one codepoint. If we don't have it, we
        // can either return `0` for the number of bytes read or return an
        // error. Since `0` would be interpreted as a possibly premature EOF,
        // we opt for an error.
        if buf.len() < 4 {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                "DecodeReaderBytes: byte buffer must have length at least 4"));
        }
        self.transcode(buf)
    }
}

#[cfg(test)]
mod tests {
    use std::io::Read;

    use encoding_rs::Encoding;

    use super::{DecodeReaderBytes, DecodeReaderBytesBuilder};

    fn read_to_string<R: Read>(mut rdr: R) -> String {
        let mut s = String::new();
        rdr.read_to_string(&mut s).unwrap();
        s
    }

    // In cases where all we have is a bom, we expect the bytes to be
    // passed through unchanged.
    #[test]
    fn trans_utf16_bom() {
        let srcbuf = vec![0xFF, 0xFE];
        let mut dstbuf = vec![0; 8 * (1<<10)];
        let mut rdr = DecodeReaderBytes::new(&*srcbuf, vec![0; 8 * (1<<10)], None);
        let n = rdr.read(&mut dstbuf).unwrap();
        assert_eq!(&*srcbuf, &dstbuf[..n]);

        let srcbuf = vec![0xFE, 0xFF];
        let mut rdr = DecodeReaderBytes::new(&*srcbuf, vec![0; 8 * (1<<10)], None);
        let n = rdr.read(&mut dstbuf).unwrap();
        assert_eq!(&*srcbuf, &dstbuf[..n]);

        let srcbuf = vec![0xEF, 0xBB, 0xBF];
        let mut rdr = DecodeReaderBytes::new(&*srcbuf, vec![0; 8 * (1<<10)], None);
        let n = rdr.read(&mut dstbuf).unwrap();
        assert_eq!(n, 0);

        let srcbuf = vec![0xEF, 0xBB, 0xBF];
        let mut rdr = DecodeReaderBytesBuilder::new()
            .utf8_passthru(true)
            .build(&*srcbuf);
        let n = rdr.read(&mut dstbuf).unwrap();
        assert_eq!(&*srcbuf, &dstbuf[..n]);
    }

    // Test basic UTF-16 decoding.
    #[test]
    fn trans_utf16_basic() {
        let srcbuf = vec![0xFF, 0xFE, 0x61, 0x00];
        let mut rdr = DecodeReaderBytes::new(&*srcbuf, vec![0; 8 * (1<<10)], None);
        assert_eq!("a", read_to_string(&mut rdr));

        let srcbuf = vec![0xFE, 0xFF, 0x00, 0x61];
        let mut rdr = DecodeReaderBytes::new(&*srcbuf, vec![0; 8 * (1<<10)], None);
        assert_eq!("a", read_to_string(&mut rdr));
    }

    // Test incomplete UTF-16 decoding. This ensures we see a replacement char
    // if the stream ends with an unpaired code unit.
    #[test]
    fn trans_utf16_incomplete() {
        let srcbuf = vec![0xFF, 0xFE, 0x61, 0x00, 0x00];
        let mut rdr = DecodeReaderBytes::new(&*srcbuf, vec![0; 8 * (1<<10)], None);
        assert_eq!("a\u{FFFD}", read_to_string(&mut rdr));
    }

    macro_rules! test_trans_simple {
        ($name:ident, $enc:expr, $srcbytes:expr, $dst:expr) => {
            #[test]
            fn $name() {
                let srcbuf = &$srcbytes[..];
                let enc = Encoding::for_label($enc.as_bytes());
                let mut rdr = DecodeReaderBytes::new(
                    &*srcbuf, vec![0; 8 * (1<<10)], enc);
                assert_eq!($dst, read_to_string(&mut rdr));
            }
        }
    }

    // This isn't exhaustive obviously, but it lets us test base level support.
    test_trans_simple!(trans_simple_auto, "does not exist", b"\xD0\x96", "Ж");
    test_trans_simple!(trans_simple_utf8, "utf-8", b"\xD0\x96", "Ж");
    test_trans_simple!(trans_simple_utf16le, "utf-16le", b"\x16\x04", "Ж");
    test_trans_simple!(trans_simple_utf16be, "utf-16be", b"\x04\x16", "Ж");
    test_trans_simple!(trans_simple_chinese, "chinese", b"\xA7\xA8", "Ж");
    test_trans_simple!(trans_simple_korean, "korean", b"\xAC\xA8", "Ж");
    test_trans_simple!(
        trans_simple_big5_hkscs, "big5-hkscs", b"\xC7\xFA", "Ж");
    test_trans_simple!(trans_simple_gbk, "gbk", b"\xA7\xA8", "Ж");
    test_trans_simple!(trans_simple_sjis, "sjis", b"\x84\x47", "Ж");
    test_trans_simple!(trans_simple_eucjp, "euc-jp", b"\xA7\xA8", "Ж");
    test_trans_simple!(trans_simple_latin1, "latin1", b"\xA9", "©");
}
