use {
    super::{
        memory::{FixedIoBuffer, LargeBuffer},
        IO_PRIO_BE_HIGHEST,
    },
    agave_io_uring::{Completion, Ring, RingOp},
    io_uring::{opcode, squeue, types, IoUring},
    std::{
        fs::{File, OpenOptions},
        io::{self, BufRead, Cursor, Read},
        mem,
        os::{
            fd::{AsRawFd as _, RawFd},
            unix::fs::OpenOptionsExt,
        },
        path::Path,
    },
};

// Based on transfers seen with `dd bs=SIZE` for NVME drives: values >=64KiB are fine,
// but peak at 1MiB. Also compare with particular NVME parameters, e.g.
// 32 pages (Maximum Data Transfer Size) * page size (MPSMIN = Memory Page Size) = 128KiB.
pub const DEFAULT_READ_SIZE: usize = 1024 * 1024;
const SQPOLL_IDLE_TIMEOUT: u32 = 50;
// For large file we don't really use workers as few regularly submitted requests get handled
// within sqpoll thread. Allow some workers just in case, but limit them.
const MAX_IOWQ_WORKERS: u32 = 2;

/// Reader for non-seekable files.
///
/// Implements read-ahead using io_uring.
pub struct SequentialFileReader<B> {
    // Note: state is tied to `backing_buffer` and contains unsafe pointer references to it
    inner: Ring<SequentialFileReaderState, ReadOp>,
    /// Owned buffer used (chunked into `FixedIoBuffer` items) across lifespan of `inner`
    /// (should get dropped last)
    _backing_buffer: B,
}

impl SequentialFileReader<LargeBuffer> {
    /// Create a new `SequentialFileReader` for the given `path` using internally allocated
    /// buffer of specified `buf_size` and default read size.
    pub fn with_capacity(buf_size: usize, path: impl AsRef<Path>) -> io::Result<Self> {
        Self::with_buffer(path, LargeBuffer::new(buf_size), DEFAULT_READ_SIZE)
    }
}

/// Holds the state of the reader.
struct SequentialFileReaderState {
    file: File,
    read_capacity: usize,
    offset: usize,
    eof_buf_index: Option<usize>,
    buffers: Vec<ReadBufState>,
    current_buf: usize,
}

impl<B: AsMut<[u8]>> SequentialFileReader<B> {
    /// Create a new `SequentialFileReader` for the given file using provided backing `buffer`.
    ///
    /// `buffer` is the internal buffer used for reading. It must be at least `read_capacity` long.
    /// The reader will execute multiple `read_capacity` sized reads in parallel to fill the buffer.
    pub fn with_buffer(
        path: impl AsRef<Path>,
        mut buffer: B,
        read_capacity: usize,
    ) -> io::Result<Self> {
        // Let submission queue hold half of buffers before we explicitly syscall
        // to submit them for reading.
        let ring_qsize = (buffer.as_mut().len() / read_capacity / 2).max(1) as u32;
        let ring = IoUring::builder()
            .setup_sqpoll(SQPOLL_IDLE_TIMEOUT)
            .build(ring_qsize)?;
        // Maximum number of spawned [bounded IO, unbounded IO] kernel threads, we don't expect
        // any unbounded work, but limit it to 1 just in case (0 leaves it unlimited).
        ring.submitter()
            .register_iowq_max_workers(&mut [MAX_IOWQ_WORKERS, 1])?;
        Self::with_buffer_and_ring(buffer, ring, path, read_capacity)
    }

    /// Create a new `SequentialFileReader` for the given file, using a custom
    /// ring instance.
    fn with_buffer_and_ring(
        mut backing_buffer: B,
        ring: IoUring,
        path: impl AsRef<Path>,
        read_capacity: usize,
    ) -> io::Result<Self> {
        let buffer = backing_buffer.as_mut();
        assert!(buffer.len() >= read_capacity, "buffer too small");
        let read_aligned_buf_len = buffer.len() / read_capacity * read_capacity;
        let buffer = &mut buffer[..read_aligned_buf_len];

        let file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOATIME)
            .open(path)?;
        // Safety: buffers contain unsafe pointers to `buffer`, but we make sure they are
        // dropped before `backing_buffer` is dropped.
        let buffers = unsafe { FixedIoBuffer::split_buffer_chunks(buffer, read_capacity) }
            .map(ReadBufState::Uninit)
            .collect();
        let ring = Ring::new(
            ring,
            SequentialFileReaderState {
                file,
                read_capacity,
                buffers,
                offset: 0,
                eof_buf_index: None,
                current_buf: 0,
            },
        );

        // Safety: kernel holds unsafe pointers to `buffer`, struct field declaration order
        // guarantees that the ring is destroyed before `_backing_buffer` is dropped.
        unsafe { FixedIoBuffer::register(buffer, &ring)? };

        let mut reader = Self {
            inner: ring,
            _backing_buffer: backing_buffer,
        };

        // Start reading all buffers.
        for i in 0..reader.inner.context().buffers.len() {
            reader.start_reading_buf(i)?;
        }
        // Make sure work is started in case submission queue is large and we
        // never submitted work when adding buffers.
        reader.inner.submit()?;

        Ok(reader)
    }

    /// Start reading into the buffer at `index`.
    ///
    /// This is called at start and as soon as a buffer is fully consumed by BufRead::fill_buf().
    ///
    /// Reads [state.offset, state.offset + state.read_capacity) from the file into
    /// state.buffers[index]. Once a read is complete, ReadOp::complete(state) is called to update
    /// the state.
    fn start_reading_buf(&mut self, index: usize) -> io::Result<()> {
        let SequentialFileReaderState {
            buffers,
            current_buf: _,
            file,
            offset,
            read_capacity,
            eof_buf_index: _,
        } = &mut self.inner.context_mut();
        let read_buf = mem::replace(&mut buffers[index], ReadBufState::Reading);
        match read_buf {
            ReadBufState::Uninit(buf) => {
                let op = ReadOp {
                    fd: file.as_raw_fd(),
                    buf,
                    buf_off: 0,
                    file_off: *offset,
                    read_len: *read_capacity,
                    reader_buf_index: index,
                };

                // We always advance by `read_capacity`. If we get a short read, we submit a new
                // read for the remaining data. See ReadOp::complete().
                *offset += *read_capacity;

                // Safety:
                // The op points to a buffer which is guaranteed to be valid for
                // the lifetime of the operation
                self.inner.push(op)?;
            }
            _ => unreachable!("called start_reading_buf on a non-empty buffer"),
        }
        Ok(())
    }
}

// BufRead requires Read, but we never really use the Read interface.
impl<B: AsMut<[u8]>> Read for SequentialFileReader<B> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let available = self.fill_buf()?;
        if available.is_empty() {
            return Ok(0); // EOF.
        }

        let bytes_to_read = available.len().min(buf.len());
        buf[..bytes_to_read].copy_from_slice(&available[..bytes_to_read]);
        self.consume(bytes_to_read);
        Ok(bytes_to_read)
    }
}

impl<B: AsMut<[u8]>> BufRead for SequentialFileReader<B> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        let _have_data = loop {
            let state = self.inner.context_mut();
            let num_buffers = state.buffers.len();
            let read_buf = &mut state.buffers[state.current_buf];
            match read_buf {
                ReadBufState::Full(ref mut cursor) => {
                    if !cursor.fill_buf()?.is_empty() {
                        // we have some data available
                        break true;
                    }
                    let index = state.current_buf;

                    if let Some(eof_index) = state.eof_buf_index {
                        if eof_index == index {
                            // This is the last filled buf for the whole file
                            return Ok(&[]);
                        }
                        // Some other buffer encountered EOF: move on, but don't issue new read.
                        state.current_buf = (state.current_buf + 1) % num_buffers;
                    } else {
                        // we have finished consuming this buffer, queue the next read
                        let cursor = mem::replace(cursor, Cursor::new(FixedIoBuffer::empty()));
                        let buf = cursor.into_inner();

                        // The very last read when we hit EOF could return less than `read_capacity`, in
                        // which case what's in the cursor is shorter than `read_capacity` and for
                        // strict correctness we should reset the length.
                        //
                        // Note though that once we hit EOF we don't queue any more reads, so even if we
                        // didn't reset the length it wouldn't matter.
                        debug_assert!(buf.len() == state.read_capacity);

                        state.buffers[index] = ReadBufState::Uninit(buf);
                        state.current_buf = (state.current_buf + 1) % num_buffers;

                        self.start_reading_buf(index)?;
                    }

                    // move to the next buffer and check again whether we have data
                    continue;
                }
                ReadBufState::Uninit(_) => unreachable!("should be initialized"),
                _ => break false,
            }
        };

        loop {
            self.inner.process_completions()?;
            let state = self.inner.context();

            match &state.buffers[state.current_buf] {
                ReadBufState::Full(_) => break,
                ReadBufState::Uninit(_) => unreachable!("should be initialized"),
                // Still no data, wait for more completions, but submit in case the SQPOLL
                // thread is asleep and there are queued entries in the submission queue.
                ReadBufState::Reading => self.inner.submit()?,
            }
        }

        // At this point we must have data or be at EOF.
        let state = self.inner.context_mut();
        match &mut state.buffers[state.current_buf] {
            ReadBufState::Full(cursor) => Ok(cursor.fill_buf()?),
            // after the loop above we either have some data or we must be at EOF
            _ => unreachable!(),
        }
    }

    fn consume(&mut self, amt: usize) {
        let state = self.inner.context_mut();
        match &mut state.buffers[state.current_buf] {
            ReadBufState::Full(cursor) => cursor.consume(amt),
            _ => assert_eq!(amt, 0),
        }
    }
}

enum ReadBufState {
    /// The buffer is pending submission to read queue (on initialization and
    /// in transition from `Full` to `Reading`).
    Uninit(FixedIoBuffer),
    /// The buffer is currently being read and there's a corresponding ReadOp in
    /// the ring.
    Reading,
    /// The buffer is filled and ready to be consumed.
    Full(Cursor<FixedIoBuffer>),
}

impl std::fmt::Debug for ReadBufState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Uninit(buf) => f
                .debug_struct("Uninit")
                .field("io_buf_index", &buf.io_buf_index())
                .finish(),
            Self::Reading => write!(f, "Reading"),
            Self::Full(cursor) => f
                .debug_struct("Full")
                .field("io_buf_index", &cursor.get_ref().io_buf_index())
                .finish(),
        }
    }
}

struct ReadOp {
    fd: RawFd,
    buf: FixedIoBuffer,
    /// This is the offset inside the buffer. It's typically 0, but can be non-zero if a previous
    /// read returned less data than requested (because of EINTR or whatever) and we submitted a new
    /// read for the remaining data.
    buf_off: usize,
    /// The offset in the file.
    file_off: usize,
    /// The length of the read. This is typically `read_capacity` but can be less if a previous read
    /// returned less data than requested.
    read_len: usize,
    /// This is the index of the buffer in the reader's state. It's used to update the state once the
    /// read completes.
    reader_buf_index: usize,
}

impl std::fmt::Debug for ReadOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ReadOp")
            .field("fd", &self.fd)
            .field("buf_off", &self.buf_off)
            .field("io_buf_index", &self.buf.io_buf_index())
            .field("file_off", &self.file_off)
            .field("read_len", &self.read_len)
            .field("reader_buf_index", &self.reader_buf_index)
            .finish()
    }
}

impl RingOp<SequentialFileReaderState> for ReadOp {
    fn entry(&mut self) -> squeue::Entry {
        let ReadOp {
            fd,
            buf,
            buf_off,
            file_off,
            read_len,
            reader_buf_index: _,
        } = self;
        debug_assert!(*buf_off + *read_len <= buf.len());
        opcode::ReadFixed::new(
            types::Fd(*fd),
            // Safety: we assert that the buffer is large enough to hold the read.
            unsafe { buf.as_mut_ptr().byte_add(*buf_off) },
            *read_len as u32,
            buf.io_buf_index()
                .expect("should have a valid fixed buffer"),
        )
        .offset(*file_off as u64)
        .ioprio(IO_PRIO_BE_HIGHEST)
        .build()
    }

    fn complete(
        &mut self,
        completion: &mut Completion<SequentialFileReaderState, Self>,
        res: io::Result<i32>,
    ) -> io::Result<()> {
        let ReadOp {
            fd,
            buf,
            buf_off,
            file_off,
            read_len,
            reader_buf_index,
        } = self;
        let reader_state = completion.context_mut();

        let last_read_len = res? as usize;
        if last_read_len == 0 {
            reader_state.eof_buf_index = Some(*reader_buf_index);
        }

        let total_read_len = *buf_off + last_read_len;
        let buf = mem::replace(buf, FixedIoBuffer::empty());

        if last_read_len > 0 && last_read_len < *read_len {
            // Partial read, retry the op with updated offsets
            let op: ReadOp = ReadOp {
                fd: *fd,
                buf,
                buf_off: total_read_len,
                file_off: *file_off + last_read_len,
                read_len: *read_len - last_read_len,
                reader_buf_index: *reader_buf_index,
            };
            // Safety:
            // The op points to a buffer which is guaranteed to be valid for the
            // lifetime of the operation
            completion.push(op);
        } else {
            reader_state.buffers[*reader_buf_index] =
                ReadBufState::Full(Cursor::new(buf.into_shrinked(total_read_len)));
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use {super::*, tempfile::NamedTempFile};

    fn check_reading_file(file_size: usize, backing_buffer_size: usize, read_capacity: usize) {
        let pattern: Vec<u8> = (0..251).collect();

        // Create a temp file and write the pattern to it repeatedly
        let mut temp_file = NamedTempFile::new().unwrap();
        for _ in 0..file_size / pattern.len() {
            io::Write::write_all(&mut temp_file, &pattern).unwrap();
        }
        io::Write::write_all(&mut temp_file, &pattern[..file_size % pattern.len()]).unwrap();

        let buf = vec![0; backing_buffer_size];
        let mut reader =
            SequentialFileReader::with_buffer(temp_file.path(), buf, read_capacity).unwrap();

        // Read contents from the reader and verify length
        let mut all_read_data = Vec::new();
        reader.read_to_end(&mut all_read_data).unwrap();
        assert_eq!(all_read_data.len(), file_size);

        // Verify the contents
        for (i, byte) in all_read_data.iter().enumerate() {
            assert_eq!(*byte, pattern[i % pattern.len()], "Mismatch - pos {i}");
        }
    }

    /// Test with buffer larger than the whole file
    #[test]
    fn test_reading_small_file() {
        check_reading_file(2500, 4096, 1024);
        check_reading_file(2500, 4096, 2048);
        check_reading_file(2500, 4096, 4096);
    }

    /// Test with buffer smaller than the whole file
    #[test]
    fn test_reading_file_in_chunks() {
        check_reading_file(25_000, 16384, 1024);
        check_reading_file(25_000, 4096, 1024);
        check_reading_file(25_000, 4096, 2048);
        check_reading_file(25_000, 4096, 4096);
    }

    /// Test with buffer much smaller than the whole file
    #[test]
    fn test_reading_large_file() {
        check_reading_file(250_000, 32768, 1024);
        check_reading_file(250_000, 16384, 1024);
        check_reading_file(250_000, 4096, 1024);
        check_reading_file(250_000, 4096, 2048);
        check_reading_file(250_000, 4096, 4096);
    }
}
