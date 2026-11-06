//! The disk access used by mbrman.
//!
//! mbrman reads and writes a disk through three small traits:
//!
//! - [`DiskSize`] gives the size of the disk;
//! - [`DiskRead`] reads bytes at an offset;
//! - [`DiskWrite`] writes bytes at an offset.
//!
//! With the `std` feature (enabled by default), they are implemented for every type that
//! implements `std::io::Seek`, `Read + Seek` and `Write + Seek` respectively, such as
//! `std::fs::File` or `std::io::Cursor`. [`Error`] and [`ErrorKind`] are then re-exports of
//! `std::io::Error` and `std::io::ErrorKind`.
//!
//! Without `std`, implement the traits for your block device. [`Error`] and [`ErrorKind`]
//! are then small stand-ins with the same API as the subset of `std::io` they provide, so
//! code that sticks to that subset builds the same whether `std` is enabled or not. An
//! [`Error`] is then only an [`ErrorKind`]: map your device errors to a kind and build the
//! error with `Error::from(kind)`.
//!
//! # Types that also implement `std::io`
//!
//! The `std` implementations cover every `std::io` type, so with `std` you cannot implement
//! the traits yourself for a type that also implements `std::io::Seek`, `Read` or `Write`:
//! the two implementations would conflict. If your crate implements both behind its own
//! `std` feature, make that feature enable `mbrman/std` and implement the traits only when
//! it is disabled:
//!
//! ```toml
//! [features]
//! std = ["mbrman/std"]
//! ```
//!
//! ```ignore
//! #[cfg(not(feature = "std"))]
//! impl mbrman::io::DiskRead for MyDevice {
//!     // ...
//! }
//! ```
//!
//! # Example
//!
//! A disk held in memory:
//!
//! ```
//! use mbrman::io::{DiskRead, DiskSize, DiskWrite, Error, ErrorKind, Result};
//!
//! struct RamDisk([u8; 100 * 512]);
//!
//! impl RamDisk {
//!     fn range(&self, offset: u64, len: usize) -> Result<core::ops::Range<usize>> {
//!         let start = usize::try_from(offset).map_err(|_| ErrorKind::UnexpectedEof)?;
//!         match start.checked_add(len) {
//!             Some(end) if end <= self.0.len() => Ok(start..end),
//!             _ => Err(Error::from(ErrorKind::UnexpectedEof)),
//!         }
//!     }
//! }
//!
//! impl DiskSize for RamDisk {
//!     fn disk_size(&mut self) -> Result<u64> {
//!         Ok(self.0.len() as u64)
//!     }
//! }
//!
//! impl DiskRead for RamDisk {
//!     fn read_disk(&mut self, offset: u64, buf: &mut [u8]) -> Result<()> {
//!         let range = self.range(offset, buf.len())?;
//!         buf.copy_from_slice(&self.0[range]);
//!         Ok(())
//!     }
//! }
//!
//! impl DiskWrite for RamDisk {
//!     fn write_disk(&mut self, offset: u64, buf: &[u8]) -> Result<()> {
//!         let range = self.range(offset, buf.len())?;
//!         self.0[range].copy_from_slice(buf);
//!         Ok(())
//!     }
//! }
//!
//! let mut disk = RamDisk([0; 100 * 512]);
//! // without `alloc`, read the partition table
//! let header = mbrman::MBRHeader::new([0xff; 4]);
//! header.write_into(&mut disk).expect("could not write the MBR header");
//! let header = mbrman::MBRHeader::read_from(&mut disk).expect("could not read the MBR header");
//! assert_eq!(header.disk_signature, [0xff; 4]);
//! assert_eq!(header.read_logical_partitions(&mut disk, 512).count(), 0);
//!
//! // with `alloc`, edit it
//! # #[cfg(feature = "alloc")] {
//! let mut mbr = mbrman::MBR::new_from(&mut disk, 512, [0xff; 4])
//!     .expect("could not make a partition table");
//! mbr.write_into(&mut disk).expect("could not write the partition table");
//! let mbr = mbrman::MBR::read_from(&mut disk, 512).expect("could not read the partition table");
//! assert_eq!(mbr.header.disk_signature, [0xff; 4]);
//! # }
//! ```

#[cfg(feature = "std")]
pub use std::io::{Error, ErrorKind};

#[cfg(not(feature = "std"))]
pub use self::error::{Error, ErrorKind};

/// The result of a disk access.
pub type Result<T> = core::result::Result<T, Error>;

/// A disk whose size is known.
pub trait DiskSize {
    /// Return the size of the disk in bytes.
    fn disk_size(&mut self) -> Result<u64>;
}

/// A disk that can be read at any offset.
pub trait DiskRead {
    /// Read exactly `buf.len()` bytes starting at byte `offset` of the disk.
    ///
    /// Return an error of kind [`ErrorKind::UnexpectedEof`] if the disk ends before `buf`
    /// is filled.
    fn read_disk(&mut self, offset: u64, buf: &mut [u8]) -> Result<()>;
}

/// A disk that can be written at any offset.
pub trait DiskWrite {
    /// Write all of `buf` starting at byte `offset` of the disk.
    fn write_disk(&mut self, offset: u64, buf: &[u8]) -> Result<()>;
}

#[cfg(feature = "std")]
impl<T: std::io::Seek + ?Sized> DiskSize for T {
    fn disk_size(&mut self) -> Result<u64> {
        self.seek(std::io::SeekFrom::End(0))
    }
}

#[cfg(feature = "std")]
impl<T: std::io::Read + std::io::Seek + ?Sized> DiskRead for T {
    fn read_disk(&mut self, offset: u64, buf: &mut [u8]) -> Result<()> {
        self.seek(std::io::SeekFrom::Start(offset))?;
        self.read_exact(buf)
    }
}

#[cfg(feature = "std")]
impl<T: std::io::Write + std::io::Seek + ?Sized> DiskWrite for T {
    fn write_disk(&mut self, offset: u64, buf: &[u8]) -> Result<()> {
        self.seek(std::io::SeekFrom::Start(offset))?;
        self.write_all(buf)
    }
}

/// Stand-ins for `std::io::Error` and `std::io::ErrorKind`, used without the `std` feature.
///
/// Only items that exist in `std::io` with the same signature belong here: a crate that uses
/// them must keep building when another crate enables `std`.
#[cfg(not(feature = "std"))]
mod error {
    use core::fmt;

    /// The category of an I/O [`Error`], like `std::io::ErrorKind`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    #[non_exhaustive]
    pub enum ErrorKind {
        /// An entity was not found.
        NotFound,
        /// The operation lacked the necessary privileges to complete.
        PermissionDenied,
        /// The operation needs to block to complete, but the blocking operation was
        /// requested to not occur.
        WouldBlock,
        /// A parameter was incorrect.
        InvalidInput,
        /// Data not valid for the operation were encountered.
        InvalidData,
        /// The I/O operation's timeout expired.
        TimedOut,
        /// A call to write returned `Ok(0)`.
        WriteZero,
        /// This operation was interrupted.
        Interrupted,
        /// This operation is unsupported on this platform.
        Unsupported,
        /// The operation could not complete because the end of the disk was reached.
        UnexpectedEof,
        /// An operation could not be completed, because it failed to allocate enough
        /// memory.
        OutOfMemory,
        /// A custom error that does not fall under any other I/O error kind.
        Other,
    }

    impl ErrorKind {
        fn as_str(self) -> &'static str {
            // the same descriptions as std
            match self {
                ErrorKind::NotFound => "entity not found",
                ErrorKind::PermissionDenied => "permission denied",
                ErrorKind::WouldBlock => "operation would block",
                ErrorKind::InvalidInput => "invalid input parameter",
                ErrorKind::InvalidData => "invalid data",
                ErrorKind::TimedOut => "timed out",
                ErrorKind::WriteZero => "write zero",
                ErrorKind::Interrupted => "operation interrupted",
                ErrorKind::Unsupported => "unsupported",
                ErrorKind::UnexpectedEof => "unexpected end of file",
                ErrorKind::OutOfMemory => "out of memory",
                ErrorKind::Other => "other error",
            }
        }
    }

    impl fmt::Display for ErrorKind {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str(self.as_str())
        }
    }

    /// An I/O error, like `std::io::Error`, reduced to its [`ErrorKind`].
    pub struct Error {
        kind: ErrorKind,
    }

    impl Error {
        /// Return the kind of this error.
        pub fn kind(&self) -> ErrorKind {
            self.kind
        }
    }

    impl From<ErrorKind> for Error {
        fn from(kind: ErrorKind) -> Error {
            Error { kind }
        }
    }

    impl fmt::Debug for Error {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            // the same output as std for an error built from a kind
            f.debug_tuple("Kind").field(&self.kind).finish()
        }
    }

    impl fmt::Display for Error {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            self.kind.fmt(f)
        }
    }

    impl core::error::Error for Error {}
}
