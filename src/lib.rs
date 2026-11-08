//! A library for reading and managing MBR partition tables.
//!
//! ## Features
//!
//! - Create and delete primary partitions and logical volumes
//! - Generate the EBR of a logical volume automatically, or provide it manually
//! - Compute the CHS addresses of logical partitions automatically when writing
//!   to disk, if the disk geometry is set
//!
//! ## `no_std`
//!
//! mbrman works without `std`: disable the default features.
//!
//! - With the `alloc` feature, everything is available except the `std::io` integration. The
//!   `MBR` type, to edit partition tables, needs `alloc`.
//! - Without `alloc`, you can read a partition table: `MBRHeader::from_bytes` decodes the MBR and
//!   `MBRHeader::ebr_walk` reads the EBR chain one logical partition at a time.
//!
//! ```toml
//! [dependencies]
//! mbrman = { version = "0.7", default-features = false, features = ["alloc"] }
//! ```
//!
//! ### Disk access
//!
//! mbrman does no I/O of its own: it turns 512-byte boot records into partition tables and back,
//! and tells you where on the disk they go. With the default `std` feature, `MBR::read_from` and
//! `MBR::write_into` do the I/O for you on any `std::io` type, such as `std::fs::File` or
//! `std::io::Cursor`. Without `std`, or in async code, you do it with whatever your block device
//! offers:
//!
//! - To read, `MBR::reader` asks for one boot record at a time: call `next_offset`, read the
//!   512 bytes at that byte offset and `feed` them, until `next_offset` returns `None`. Then
//!   `finish` builds the `MBR`. Without `alloc`, decode the MBR with `MBRHeader::from_bytes`
//!   and walk the EBR chain the same way with `MBRHeader::ebr_walk`.
//! - To write, `MBR::chunks` validates the whole partition table, then yields every boot
//!   record to write with its byte offset. Nothing is yielded if the table is invalid. Without
//!   `alloc`, `MBRHeader::to_bytes` encodes the MBR, which goes at offset 0.
//!
//! Without `std`, the I/O errors stay yours: mbrman only returns its own `Error`. Boot records
//! are 512 bytes whatever the sector size: on a device with larger sectors, read the sector that
//! contains the record and, to write, update the record inside it before writing it back.
//!
//! ### With `alloc`
//!
//! Write a partition table with an extended partition and a logical volume to a block device,
//! then read it back.
//!
//! ```rust
//! # #[cfg(feature = "alloc")] {
//! // a disk in memory, standing in for your block device
//! let mut disk = [0_u8; 64 * 512];
//!
//! // a partition table with an extended partition and a logical volume
//! let mut mbr = mbrman::MBR::new(512, disk.len() as u64, [0xff; 4]);
//! mbr[1] = mbrman::MBRPartitionEntry {
//!     boot: mbrman::BOOT_INACTIVE,
//!     first_chs: mbrman::CHS::empty(),
//!     sys: 0x0f,
//!     last_chs: mbrman::CHS::empty(),
//!     starting_lba: 1,
//!     sectors: mbr.disk_size - 1,
//! };
//! mbr.align = 1;
//! mbr.push(0x83, 1, mbr.disk_size - 1)
//!     .expect("could not add the logical volume");
//!
//! // write it: the whole table is validated first, then each boot record comes with its offset
//! for chunk in mbr.chunks().expect("invalid partition table") {
//!     let start = chunk.offset as usize;
//!     disk[start..start + 512].copy_from_slice(&chunk.data);
//! }
//!
//! // read it back: the reader asks for each 512-byte boot record, one at a time
//! let mut reader = mbrman::MBR::reader(512, disk.len() as u64);
//! while let Some(offset) = reader.next_offset().expect("invalid EBR chain") {
//!     let start = offset as usize;
//!     reader
//!         .feed(disk[start..start + 512].try_into().unwrap())
//!         .expect("could not read a boot record");
//! }
//! let read = reader.finish().expect("could not read the partition table");
//! assert_eq!(read.logical_partitions, mbr.logical_partitions);
//! # }
//! ```
//!
//! ### Without `alloc`
//!
//! Read the logical partitions of a disk without allocating. `MBRHeader::to_bytes` gives back
//! the 512 bytes of the MBR, to write at offset 0.
//!
//! ```rust
//! # #[cfg(feature = "std")] {
//! // the bytes of a disk image, standing in for your block device
//! let disk = std::fs::read("tests/fixtures/disk2.img").expect("could not read disk");
//! let sector = |offset: u64| -> [u8; 512] {
//!     let start = offset as usize;
//!     disk[start..start + 512].try_into().unwrap()
//! };
//!
//! let header = mbrman::MBRHeader::from_bytes(&sector(0))
//!     .expect("could not read the MBR header");
//! let mut walk = header.ebr_walk(512);
//! while let Some(offset) = walk.next_offset().expect("invalid EBR chain") {
//!     if let Some(l) = walk.feed(&sector(offset)).expect("could not read an EBR") {
//!         println!("logical partition: starting lba = {}", l.partition.starting_lba);
//!     }
//! }
//!
//! let mbr_bytes = header.to_bytes().expect("could not encode the MBR header");
//! assert_eq!(mbr_bytes.len(), 512);
//! # }
//! ```
//!
//! ### Async
//!
//! The same loops work with any async runtime: only the I/O calls change. `dev` is your async
//! block device.
//!
//! ```rust
//! # #[cfg(feature = "alloc")] {
//! use mbrman::MBR;
//!
//! /// An async block device, standing in for a tokio, embassy or other driver.
//! struct Device(Vec<u8>);
//!
//! impl Device {
//!     fn size(&self) -> u64 {
//!         self.0.len() as u64
//!     }
//!
//!     async fn read_at(&mut self, offset: u64, buf: &mut [u8; 512]) -> Result<(), Error> {
//!         let start = usize::try_from(offset).map_err(|_| Error::Device)?;
//!         buf.copy_from_slice(self.0.get(start..start + 512).ok_or(Error::Device)?);
//!         Ok(())
//!     }
//!
//!     async fn write_at(&mut self, offset: u64, buf: &[u8; 512]) -> Result<(), Error> {
//!         let start = usize::try_from(offset).map_err(|_| Error::Device)?;
//!         self.0.get_mut(start..start + 512).ok_or(Error::Device)?.copy_from_slice(buf);
//!         Ok(())
//!     }
//! }
//!
//! /// The errors of your application: the device's and mbrman's.
//! #[derive(Debug)]
//! enum Error {
//!     Device,
//!     Mbr(mbrman::Error),
//! }
//!
//! impl From<mbrman::Error> for Error {
//!     fn from(err: mbrman::Error) -> Error {
//!         Error::Mbr(err)
//!     }
//! }
//!
//! async fn read_mbr(dev: &mut Device) -> Result<MBR, Error> {
//!     let mut reader = MBR::reader(512, dev.size());
//!     let mut buf = [0; 512];
//!     while let Some(offset) = reader.next_offset()? {
//!         dev.read_at(offset, &mut buf).await?;
//!         reader.feed(&buf)?;
//!     }
//!     Ok(reader.finish()?)
//! }
//!
//! async fn write_mbr(dev: &mut Device, mbr: &mut MBR) -> Result<(), Error> {
//!     for chunk in mbr.chunks()? {
//!         dev.write_at(chunk.offset, &chunk.data).await?;
//!     }
//!     Ok(())
//! }
//!
//! async fn run() -> Result<(), Error> {
//!     let mut dev = Device(vec![0; 64 * 512]);
//!     let mut mbr = MBR::new(512, dev.size(), [0xff; 4]);
//!     write_mbr(&mut dev, &mut mbr).await?;
//!     assert_eq!(read_mbr(&mut dev).await?.header.disk_signature, [0xff; 4]);
//!     Ok(())
//! }
//!
//! // use your runtime's executor instead; this one only polls until the future is ready
//! # use core::{future::Future, pin::pin, task::{Context, Poll, Waker}};
//! # fn block_on<F: Future>(fut: F) -> F::Output {
//! #     let mut fut = pin!(fut);
//! #     let mut cx = Context::from_waker(Waker::noop());
//! #     loop {
//! #         if let Poll::Ready(out) = fut.as_mut().poll(&mut cx) {
//! #             return out;
//! #         }
//! #     }
//! # }
//! block_on(run()).expect("could not write and read the partition table");
//! # }
//! ```
//!
//! ## Examples
//!
//! ### Read the partitions of a disk
//!
//! Open a disk image, read its MBR and list the partitions in use.
//!
//! ```rust
//! # #[cfg(feature = "std")] {
//! let mut f = std::fs::File::open("tests/fixtures/disk1.img")
//!     .expect("could not open disk");
//! let mbr = mbrman::MBR::read_from(&mut f, 512)
//!     .expect("could not find MBR");
//!
//! println!("Disk signature: {:?}", mbr.header.disk_signature);
//!
//! for (i, p) in mbr.iter() {
//!     // NOTE: The first four partitions are always provided by iter()
//!     if p.is_used() {
//!         println!("Partition #{}: type = {:?}, size = {} bytes, starting lba = {}",
//!             i,
//!             p.sys,
//!             p.sectors * mbr.sector_size,
//!             p.starting_lba);
//!     }
//! }
//! # }
//! ```
//!
//! ### Create and delete a primary partition
//!
//! Find a free slot and free space, fill the slot with a new partition, then empty it again.
//!
//! ```rust
//! # #[cfg(feature = "std")] {
//! let mut f = std::fs::File::open("tests/fixtures/disk1.img")
//!     .expect("could not open disk");
//! let mut mbr = mbrman::MBR::read_from(&mut f, 512)
//!     .expect("could not find MBR");
//!
//! let free_partition_number = mbr.iter().find(|(i, p)| p.is_unused()).map(|(i, _)| i)
//!     .expect("no more places available");
//! let sectors = mbr.get_maximum_partition_size()
//!     .expect("no more space available");
//! let starting_lba = mbr.find_optimal_place(sectors)
//!     .expect("could not find a place to put the partition");
//!
//! mbr[free_partition_number] = mbrman::MBRPartitionEntry {
//!     boot: mbrman::BOOT_INACTIVE,        // boot flag
//!     first_chs: mbrman::CHS::empty(),    // first CHS address (only useful for old computers)
//!     sys: 0x83,                          // Linux filesystem
//!     last_chs: mbrman::CHS::empty(),     // last CHS address (only useful for old computers)
//!     starting_lba,                       // the sector where the partition starts
//!     sectors,                            // the number of sectors in that partition
//! };
//!
//! mbr[free_partition_number] = mbrman::MBRPartitionEntry::empty();
//!
//! // NOTE: nothing is written to the disk until you call mbr.write_into()
//! # }
//! ```
//!
//! ### Create a new partition table on an empty disk
//!
//! Write a fresh MBR to a blank in-memory disk.
//!
//! ```rust
//! # #[cfg(feature = "std")] {
//! let ss = 512; // sector size
//! let data = vec![0; 100 * ss as usize];
//! let mut cur = std::io::Cursor::new(data);
//!
//! let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
//!     .expect("could not create partition table");
//!
//! // NOTE: write the changes to the in-memory buffer
//! mbr.write_into(&mut cur);
//! # }
//! ```
//!
//! ### Add a logical volume
//!
//! A logical volume lives inside an extended partition, so create one first. `push` then places the volume and its EBR for you.
//!
//! ```rust
//! # #[cfg(feature = "std")] {
//! let ss = 512; // sector size
//! let data = vec![0; 100 * ss as usize];
//! let mut cur = std::io::Cursor::new(data);
//!
//! let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
//!     .expect("could not create partition table");
//!
//! mbr[1] = mbrman::MBRPartitionEntry {
//!     boot: mbrman::BOOT_INACTIVE,        // boot flag
//!     first_chs: mbrman::CHS::empty(),    // first CHS address (only useful for old computers)
//!     sys: 0x0f,                          // extended partition with LBA
//!     last_chs: mbrman::CHS::empty(),     // last CHS address (only useful for old computers)
//!     starting_lba: 1,                    // the sector where the partition starts
//!     sectors: mbr.disk_size - 1,         // the number of sectors in that partition
//! };
//!
//! // align on sectors, so the EBR only takes the first sector of the extended partition
//! mbr.align = 1;
//!
//! // this helper does the hard work for you: here it creates a Linux filesystem
//! // logical volume that fills the entire extended partition
//! // NOTE: 1 sector is lost because the EBR uses it
//! mbr.push(0x83, 1, mbr.disk_size - 1)
//!     .expect("could not add the logical volume");
//!
//! // NOTE: write the changes to the in-memory buffer
//! mbr.write_into(&mut cur);
//! # }
//! ```
//!
//! ### Add a logical volume manually
//!
//! Use this only if you need to choose exactly where the EBR and the partition go.
//!
//! ```rust
//! # #[cfg(feature = "std")] {
//! let ss = 512; // sector size
//! let data = vec![0; 100 * ss as usize];
//! let mut cur = std::io::Cursor::new(data);
//!
//! let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
//!     .expect("could not create partition table");
//!
//! mbr[1] = mbrman::MBRPartitionEntry {
//!     boot: mbrman::BOOT_INACTIVE,        // boot flag
//!     first_chs: mbrman::CHS::empty(),    // first CHS address (only useful for old computers)
//!     sys: 0x0f,                          // extended partition with LBA
//!     last_chs: mbrman::CHS::empty(),     // last CHS address (only useful for old computers)
//!     starting_lba: 1,                    // the sector where the partition starts
//!     sectors: mbr.disk_size - 1,         // the number of sectors in that partition
//! };
//!
//! // NOTE: mbrman does not check that a manually created partition is consistent
//! mbr.logical_partitions.push(
//!     mbrman::LogicalPartition {
//!         // this is the actual partition entry for the logical volume
//!         partition: mbrman::MBRPartitionEntry {
//!             boot: mbrman::BOOT_INACTIVE,
//!             first_chs: mbrman::CHS::empty(),
//!             sys: 0x83,
//!             last_chs: mbrman::CHS::empty(),
//!             starting_lba: 2,                    // the sector index 1 is used by the EBR
//!             sectors: mbr.disk_size - 2,
//!         },
//!         // this is the absolute LBA address of the EBR
//!         absolute_ebr_lba: 1,
//!         // the number of sectors in the first EBR is never known
//!         ebr_sectors: None,
//!         // empty boot sector in the EBR
//!         bootstrap_code: [0; 446],
//!         // this is the absolute CHS address of the EBR (only used by old computers)
//!         ebr_first_chs: mbrman::CHS::empty(),                // only for old computers
//!         // this is the absolute CHS address of the last EBR (only used by old computers)
//!         // NOTE: this is never known for the first EBR
//!         ebr_last_chs: None,
//!     }
//! );
//!
//! // NOTE: write the changes to the in-memory buffer
//! mbr.write_into(&mut cur);
//! # }
//! ```

#![no_std]
#![deny(missing_docs)]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "alloc")]
use alloc::{vec, vec::Vec};
use core::fmt;
#[cfg(feature = "alloc")]
use core::iter::FusedIterator;
use core::ops::{Index, IndexMut};
#[cfg(feature = "std")]
use std::io::{Read, Seek, SeekFrom, Write};

#[cfg(feature = "alloc")]
const DEFAULT_ALIGN: u32 = 2048;
#[cfg(feature = "alloc")]
const MAX_ALIGN: u32 = 16384;
#[cfg(feature = "alloc")]
const FIRST_USABLE_LBA: u32 = 1;
const BOOT_SIGNATURE: [u8; 2] = [0x55, 0xaa];
/// Size in bytes of an MBR or EBR sector on disk.
const BOOT_RECORD_SIZE: usize = 512;

/// Boot flag for a bootable partition
pub const BOOT_ACTIVE: u8 = 0x80;
/// Boot flag for a non-bootable partition
pub const BOOT_INACTIVE: u8 = 0x00;

/// The result of reading, writing or managing a MBR.
pub type Result<T> = core::result::Result<T, Error>;

/// Read exactly one boot record (MBR or EBR sector) at byte `offset`.
#[cfg(feature = "std")]
fn read_boot_record<R: Read + Seek + ?Sized>(
    reader: &mut R,
    offset: u64,
) -> Result<[u8; BOOT_RECORD_SIZE]> {
    let mut buf = [0; BOOT_RECORD_SIZE];
    reader.seek(SeekFrom::Start(offset))?;
    reader.read_exact(&mut buf)?;
    Ok(buf)
}

/// Write exactly one boot record (MBR or EBR sector) at byte `offset`.
#[cfg(feature = "std")]
fn write_boot_record<W: Write + Seek + ?Sized>(
    writer: &mut W,
    offset: u64,
    data: &[u8; BOOT_RECORD_SIZE],
) -> Result<()> {
    writer.seek(SeekFrom::Start(offset))?;
    writer.write_all(data)?;
    Ok(())
}

/// Return the size of a disk in bytes.
#[cfg(feature = "std")]
fn disk_size<S: Seek + ?Sized>(seeker: &mut S) -> Result<u64> {
    Ok(seeker.seek(SeekFrom::End(0))?)
}

/// Convert a disk size in bytes to sectors, saturating at `u32::MAX`.
#[cfg(feature = "alloc")]
fn disk_size_in_sectors(disk_size: u64, sector_size: u32) -> u32 {
    u32::try_from(disk_size / u64::from(sector_size)).unwrap_or(u32::MAX)
}

/// Copy `N` bytes starting at `offset` into an array.
fn chunk<const N: usize>(bytes: &[u8], offset: usize) -> [u8; N] {
    bytes[offset..offset + N].try_into().unwrap()
}

/// An error
#[derive(Debug)]
#[non_exhaustive]
pub enum Error {
    /// The CHS address requested cannot be represented in CHS
    ///
    /// # Remark
    ///
    /// There is a hard limit around 8GB for CHS addressing.
    LBAExceedsMaximumCHS,
    /// The CHS address requested exceeds the number of cylinders in the disk
    LBAExceedsMaximumCylinders,
    /// I/O errors.
    #[cfg(feature = "std")]
    Io(std::io::Error),
    /// Inconsistent extended boot record
    InconsistentEBR,
    /// No extended partition
    NoExtendedPartition,
    /// The EBR starts before the extended partition
    EBRStartsBeforeExtendedPartition,
    /// The EBR starts too close to the extended partition
    EBRStartsTooCloseToTheEndOfExtendedPartition,
    /// The EBR ends after the extended partition
    EBREndsAfterExtendedPartition,
    /// Not enough sectors to create a logical partition
    NotEnoughSectorsToCreateLogicalPartition,
    /// An operation that required to find a partition, was unable to find that partition.
    PartitionNotFound,
    /// An error that occurs when there is not enough space left on the table to continue.
    NoSpaceLeft,
    /// MBR doesn't have the expected signature value
    InvalidSignature,
    /// Partition has invalid boot flag
    InvalidBootFlag,
    /// A boot record was fed to a reader that expected none, or a reader was finished before
    /// it read the whole partition table
    OutOfSequence,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::LBAExceedsMaximumCHS => "exceeded the maximum limit of CHS",
            Error::LBAExceedsMaximumCylinders => "exceeded the maximum number of cylinders on disk",
            #[cfg(feature = "std")]
            Error::Io(_) => "generic I/O error",
            Error::InconsistentEBR => "inconsistent extended boot record",
            Error::NoExtendedPartition => "no extended partition",
            Error::EBRStartsBeforeExtendedPartition => "EBR starts before the extended partition",
            Error::EBRStartsTooCloseToTheEndOfExtendedPartition => {
                "EBR starts too close to the end of the extended partition"
            }
            Error::EBREndsAfterExtendedPartition => "EBR ends after the extended partition",
            Error::NotEnoughSectorsToCreateLogicalPartition => {
                "not enough sectors to create a logical partition"
            }
            Error::PartitionNotFound => "partition not found",
            Error::NoSpaceLeft => "no space left",
            Error::InvalidSignature => "invalid MBR signature",
            Error::InvalidBootFlag => "partition has invalid boot flag",
            Error::OutOfSequence => "boot record fed out of sequence or read not finished",
        })
    }
}

impl core::error::Error for Error {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            #[cfg(feature = "std")]
            Error::Io(err) => Some(err),
            _ => None,
        }
    }
}

#[cfg(feature = "std")]
impl From<std::io::Error> for Error {
    fn from(err: std::io::Error) -> Error {
        Error::Io(err)
    }
}

/// A type representing a MBR partition table including its partition, the sector size of the disk
/// and the alignment of the partitions to the sectors.
///
/// # Examples:
/// Read an existing MBR on a reader and list its partitions:
/// ```
/// # #[cfg(feature = "std")] {
/// let mut f = std::fs::File::open("tests/fixtures/disk1.img")
///     .expect("could not open disk");
/// let mbr = mbrman::MBR::read_from(&mut f, 512)
///     .expect("could not find MBR");
///
/// println!("Disk signature: {:?}", mbr.header.disk_signature);
///
/// for (i, p) in mbr.iter() {
///     if p.is_used() {
///         println!("Partition #{}: type = {:?}, size = {} bytes, starting lba = {}",
///             i,
///             p.sys,
///             p.sectors * mbr.sector_size,
///             p.starting_lba);
///     }
/// }
/// # }
/// ```
#[cfg(feature = "alloc")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MBR {
    /// Sector size of the disk.
    ///
    /// You should not change this, otherwise the starting locations of your partitions will be
    /// different in bytes.
    pub sector_size: u32,
    /// MBR partition header (disk GUID, first/last usable LBA, etc...)
    pub header: MBRHeader,
    /// A vector with all the logical partitions. You can push new ones (even empty ones)
    pub logical_partitions: Vec<LogicalPartition>,
    /// Partitions alignment (in sectors)
    ///
    /// This field change the behavior of the methods `get_maximum_partition_size()`,
    /// `find_free_sectors()`, `find_first_place()`, `find_last_place()` and `find_optimal_place()`
    /// so they return only values aligned to the alignment.
    ///
    /// # Panics
    /// The value must be greater than 0, otherwise you will encounter divisions by zero.
    pub align: u32,
    /// Disk geometry: number of cylinders
    pub cylinders: u16,
    /// Disk geometry: number of heads
    pub heads: u8,
    /// Disk geometry: number of sectors
    pub sectors: u8,
    /// Disk size in sectors
    pub disk_size: u32,
}

#[cfg(feature = "alloc")]
impl MBR {
    /// Get an iterator over the partition entries and their index. The
    /// index always starts at 1.
    pub fn iter(&self) -> impl Iterator<Item = (usize, &MBRPartitionEntry)> {
        self.header.iter().chain(
            self.logical_partitions
                .iter()
                .map(|x| &x.partition)
                .enumerate()
                .map(|(i, x)| (i + 5, x)),
        )
    }

    /// Get a mutable iterator over the partition entries and their
    /// index. The index always starts at 1.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (usize, &mut MBRPartitionEntry)> {
        self.header.iter_mut().chain(
            self.logical_partitions
                .iter_mut()
                .map(|x| &mut x.partition)
                .enumerate()
                .map(|(i, x)| (i + 5, x)),
        )
    }

    /// Get `Some(&MBRPartitionEntry)` if it exists, None otherwise.
    ///
    /// # Remarks
    ///
    ///  -  The partitions start at index 1
    ///  -  The first 4 partitions always exist
    pub fn get(&self, i: usize) -> Option<&MBRPartitionEntry> {
        match i {
            0 => None,
            1 => Some(&self.header.partition_1),
            2 => Some(&self.header.partition_2),
            3 => Some(&self.header.partition_3),
            4 => Some(&self.header.partition_4),
            i => self.logical_partitions.get(i - 5).map(|x| &x.partition),
        }
    }

    /// Get `Some(&mut MBRPartitionEntry)` if it exists, None otherwise.
    ///
    /// # Remarks
    ///
    ///  -  The partitions start at index 1
    ///  -  The first 4 partitions always exist
    pub fn get_mut(&mut self, i: usize) -> Option<&mut MBRPartitionEntry> {
        match i {
            0 => None,
            1 => Some(&mut self.header.partition_1),
            2 => Some(&mut self.header.partition_2),
            3 => Some(&mut self.header.partition_3),
            4 => Some(&mut self.header.partition_4),
            i => self
                .logical_partitions
                .get_mut(i - 5)
                .map(|x| &mut x.partition),
        }
    }

    /// The total number of partitions on the disk: primary partitions and logical partitions.
    ///
    /// # Remark
    ///
    /// The primary partitions are always counted even if they are empty.
    pub fn len(&self) -> usize {
        4 + self.logical_partitions.len()
    }

    /// Always false: primary partitions are always counted even if they are empty.
    pub fn is_empty(&self) -> bool {
        false
    }

    /// Make a new MBR for a disk of `disk_size` bytes, without doing any I/O.
    ///
    /// With `std`, `MBR::new_from` reads the disk size from the disk.
    ///
    /// # Examples
    /// Basic usage:
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// let mbr = mbrman::MBR::new(512, 100 * 512, [0x01, 0x02, 0x03, 0x04]);
    /// assert_eq!(mbr.disk_size, 100);
    /// # }
    /// ```
    pub fn new(sector_size: u32, disk_size: u64, disk_signature: [u8; 4]) -> MBR {
        MBR {
            sector_size,
            header: MBRHeader::new(disk_signature),
            logical_partitions: Vec::new(),
            align: DEFAULT_ALIGN,
            cylinders: 0,
            heads: 0,
            sectors: 0,
            disk_size: disk_size_in_sectors(disk_size, sector_size),
        }
    }

    /// Start reading the MBR of a disk of `disk_size` bytes, without doing any I/O: the
    /// returned reader asks for the boot records to read one at a time.
    ///
    /// With `std`, `MBR::read_from` does the I/O for you. See [`MBRReader`] for an example.
    pub fn reader(sector_size: u32, disk_size: u64) -> MBRReader {
        MBRReader {
            sector_size,
            disk_size: disk_size_in_sectors(disk_size, sector_size),
            table: None,
            logical_partitions: Vec::new(),
        }
    }

    fn find_alignment(header: &MBRHeader, logical_partitions: &[LogicalPartition]) -> u32 {
        let lbas = header
            .iter()
            .map(|(_, x)| x)
            .chain(logical_partitions.iter().map(|x| &x.partition))
            .filter(|x| x.is_used())
            .map(|x| x.starting_lba)
            // every alignment divides 0, so LBA 0 (only in a corrupt table) constrains nothing
            .filter(|&lba| lba != 0)
            .collect::<Vec<_>>();

        if lbas.is_empty() {
            return DEFAULT_ALIGN;
        }

        if lbas.len() == 1 && lbas[0] == FIRST_USABLE_LBA {
            return FIRST_USABLE_LBA;
        }

        (1..=MAX_ALIGN.min(*lbas.iter().max().unwrap_or(&1)))
            .filter(|div| lbas.iter().all(|x| x % div == 0))
            .max()
            .unwrap()
    }

    /// Return `true` if the MBR has a valid geometry. The geometry can be set by setting
    /// the fiels `cylinders`, `heads` and `sectors`.
    ///
    /// Remarks
    ///
    /// The cylinders, heads and sectors must have a value greater than zero.
    ///
    /// The cylinders cannot exceed 1023.
    ///
    /// The sectors cannot exceed 63.
    pub fn check_geometry(&self) -> bool {
        self.cylinders > 0
            && self.cylinders <= 1023
            && self.heads > 0
            && self.sectors > 0
            && self.sectors <= 63
    }

    /// Validate the MBR and the EBRs of the logical partitions, then return the boot records
    /// to write to the disk, each with its byte offset: the MBR first, then the EBRs. This
    /// function will update the CHS address of the partitions automatically if a valid
    /// geometry has been set. See `check_geometry`.
    ///
    /// Nothing is returned if the partition table is invalid, so a disk is never left with
    /// half of a partition table. With `std`, `MBR::write_into` does the I/O for you.
    ///
    /// # Examples
    /// Basic usage:
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// let mut disk = vec![0; 100 * 512];
    /// let mut mbr = mbrman::MBR::new(512, disk.len() as u64, [0xff; 4]);
    ///
    /// // actually write:
    /// for chunk in mbr.chunks().expect("invalid partition table") {
    ///     let start = chunk.offset as usize;
    ///     disk[start..start + 512].copy_from_slice(&chunk.data);
    /// }
    /// # }
    /// ```
    pub fn chunks(&mut self) -> Result<Chunks<'_>> {
        let header = self.header.to_bytes()?;
        let extended = self.header.get_extended_partition().cloned();

        if let Some(extended) = &extended {
            if let Some(first) = self.logical_partitions.get_mut(0) {
                first.absolute_ebr_lba = extended.starting_lba;
                first.ebr_sectors = None;
                first.ebr_last_chs = None;
            }

            if self.check_geometry() {
                for l in self.logical_partitions.iter_mut() {
                    l.update_chs(self.cylinders, self.heads, self.sectors)?;
                }
            }

            for i in 0..self.logical_partitions.len() {
                self.ebr(i, extended)?;
            }
        }

        Ok(Chunks {
            mbr: self,
            header: Some(header),
            extended,
            next: 0,
        })
    }

    /// Build and validate the EBR of the logical partition `i`.
    fn ebr(&self, i: usize, extended: &MBRPartitionEntry) -> Result<EBRHeader> {
        let l = &self.logical_partitions[i];
        let partition = MBRPartitionEntry {
            starting_lba: l.partition.starting_lba.saturating_sub(l.absolute_ebr_lba),
            ..l.partition
        };
        partition.check()?;
        let next_ebr = match self.logical_partitions.get(i + 1) {
            Some(next) => MBRPartitionEntry {
                boot: BOOT_INACTIVE,
                first_chs: next.ebr_first_chs,
                sys: extended.sys,
                last_chs: next.ebr_last_chs.unwrap(),
                starting_lba: next.absolute_ebr_lba.saturating_sub(extended.starting_lba),
                sectors: next.ebr_sectors.unwrap(),
            },
            None => MBRPartitionEntry::empty(),
        };
        Ok(EBRHeader {
            bootstrap_code: l.bootstrap_code,
            partition_1: partition,
            partition_2: next_ebr,
            _unused_partition_3: [0; 16],
            _unused_partition_4: [0; 16],
            boot_signature: BOOT_SIGNATURE,
        })
    }

    /// Get a cylinder size in sectors. This function is useful if you want to
    /// align your partitions to the cylinder.
    pub fn get_cylinder_size(&self) -> u32 {
        u32::from(self.heads) * u32::from(self.sectors)
    }

    /// Finds the primary partition (ignoring extended partitions) or logical
    /// partition where the given sector resides.
    pub fn find_at_sector(&self, sector: u32) -> Option<usize> {
        let between = |sector, start, len| sector >= start && sector < start + len;

        let primary = self
            .header
            .iter()
            .find(|(_, x)| x.is_used() && between(sector, x.starting_lba, x.sectors));

        match primary {
            Some((_, x)) if x.is_extended() => self
                .logical_partitions
                .iter()
                .enumerate()
                .find(|(_, x)| {
                    x.partition.is_used()
                        && between(sector, x.partition.starting_lba, x.partition.sectors)
                })
                .map(|(i, _)| 5 + i),
            Some((i, _)) => Some(i),
            None => None,
        }
    }

    /// Remove a partition entry that resides at a given sector. If the partition is the extended
    /// partition, it will delete also all the logical partitions.
    ///
    /// # Errors
    /// It is an error to provide a sector which does not belong to a partition.
    pub fn remove_at_sector(&mut self, sector: u32) -> Result<()> {
        let i = self
            .find_at_sector(sector)
            .ok_or(Error::PartitionNotFound)?;

        if i >= 5 {
            self.remove(i);
        } else {
            if self[i].is_extended() {
                self.logical_partitions.clear();
            }
            self[i] = MBRPartitionEntry::empty();
        }

        Ok(())
    }

    /// Find free spots in the partition table.
    /// This function will return a vector of tuple with on the left: the starting LBA of the free
    /// spot; and on the right: the size (in sectors) of the free spot.
    /// This function will automatically align with the alignment defined in the `MBR`.
    ///
    /// # Examples
    /// Basic usage:
    /// ```
    /// # #[cfg(feature = "std")] {
    /// let ss = 512;
    /// let data = vec![0; 100 * ss as usize];
    /// let mut cur = std::io::Cursor::new(data);
    /// let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
    ///     .expect("could not create partition table");
    ///
    /// mbr[1] = mbrman::MBRPartitionEntry {
    ///     boot: mbrman::BOOT_INACTIVE,
    ///     first_chs: mbrman::CHS::empty(),
    ///     sys: 0x83,
    ///     last_chs: mbrman::CHS::empty(),
    ///     starting_lba: 6,
    ///     sectors: mbr.disk_size - 11,
    /// };
    ///
    /// // NOTE: align to the sectors, so we can use every last one of them
    /// // NOTE: this is only for the demonstration purpose, this is not recommended
    /// mbr.align = 1;
    ///
    /// assert_eq!(
    ///     mbr.find_free_sectors(),
    ///     vec![(1, 5), (mbr.disk_size - 5, 5)]
    /// );
    /// # }
    /// ```
    pub fn find_free_sectors(&self) -> Vec<(u32, u32)> {
        assert!(self.align > 0, "align must be greater than 0");

        let collect_free_sectors = |positions: Vec<u32>| {
            positions
                .chunks(2)
                .map(|x| (x[0] + 1, x[1] - x[0] - 1))
                .filter(|(_, l)| *l > 0)
                .map(|(i, l)| (i, l, ((i - 1) / self.align + 1) * self.align - i))
                .map(|(i, l, s)| (i + s, l.saturating_sub(s)))
                .filter(|(_, l)| *l > 0)
                .collect::<Vec<_>>()
        };

        let mut positions = vec![0];
        for (_, partition) in self.header.iter().filter(|(_, x)| x.is_used()) {
            positions.push(partition.starting_lba);
            positions.push(partition.starting_lba + partition.sectors - 1);
        }
        positions.push(self.disk_size);
        positions.sort_unstable();

        let mut res = collect_free_sectors(positions);

        if let Some(extended) = self.header.get_extended_partition() {
            let mut positions = vec![extended.starting_lba];
            for l in self
                .logical_partitions
                .iter()
                .filter(|x| x.partition.is_used())
            {
                let starting_lba = l.absolute_ebr_lba + l.partition.starting_lba;
                positions.push(starting_lba);
                positions.push(starting_lba + l.partition.sectors - 1);
            }
            positions.push(extended.starting_lba + extended.sectors);
            positions.sort_unstable();
            res.extend(collect_free_sectors(positions));
        }

        res
    }

    /// Find the first place (most on the left) where you could start a new partition of the size
    /// given in parameter.
    /// This function will automatically align with the alignment defined in the `MBR`.
    ///
    /// # Examples:
    /// Basic usage:
    /// ```
    /// # #[cfg(feature = "std")] {
    /// let ss = 512;
    /// let data = vec![0; 100 * ss as usize];
    /// let mut cur = std::io::Cursor::new(data);
    /// let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
    ///     .expect("could not create partition table");
    ///
    /// mbr[1] = mbrman::MBRPartitionEntry {
    ///     boot: mbrman::BOOT_INACTIVE,
    ///     first_chs: mbrman::CHS::empty(),
    ///     sys: 0x83,
    ///     last_chs: mbrman::CHS::empty(),
    ///     starting_lba: 6,
    ///     sectors: mbr.disk_size - 6,
    /// };
    ///
    /// // NOTE: align to the sectors, so we can use every last one of them
    /// // NOTE: this is only for the demonstration purpose, this is not recommended
    /// mbr.align = 1;
    ///
    /// assert_eq!(mbr.find_first_place(5), Some(1));
    /// # }
    /// ```
    pub fn find_first_place(&self, size: u32) -> Option<u32> {
        self.find_free_sectors()
            .iter()
            .find(|(_, l)| *l >= size)
            .map(|(i, _)| *i)
    }

    /// Find the last place (most on the right) where you could start a new partition of the size
    /// given in parameter.
    /// This function will automatically align with the alignment defined in the `MBR`.
    ///
    /// # Examples:
    /// Basic usage:
    /// ```
    /// # #[cfg(feature = "std")] {
    /// let ss = 512;
    /// let data = vec![0; 100 * ss as usize];
    /// let mut cur = std::io::Cursor::new(data);
    /// let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
    ///     .expect("could not create partition table");
    ///
    /// mbr[1] = mbrman::MBRPartitionEntry {
    ///     boot: mbrman::BOOT_INACTIVE,
    ///     first_chs: mbrman::CHS::empty(),
    ///     sys: 0x83,
    ///     last_chs: mbrman::CHS::empty(),
    ///     starting_lba: 6,
    ///     sectors: 5,
    /// };
    ///
    /// // NOTE: align to the sectors, so we can use every last one of them
    /// // NOTE: this is only for the demonstration purpose, this is not recommended
    /// mbr.align = 1;
    ///
    /// assert_eq!(mbr.find_last_place(5), Some(mbr.disk_size - 5));
    /// # }
    /// ```
    pub fn find_last_place(&self, size: u32) -> Option<u32> {
        self.find_free_sectors()
            .iter()
            .filter(|(_, l)| *l >= size)
            .last()
            .map(|(i, l)| (i + l - size) / self.align * self.align)
    }

    /// Find the most optimal place (in the smallest free space) where you could start a new
    /// partition of the size given in parameter.
    /// This function will automatically align with the alignment defined in the `MBR`.
    ///
    /// # Examples:
    /// Basic usage:
    /// ```
    /// # #[cfg(feature = "std")] {
    /// let ss = 512;
    /// let data = vec![0; 100 * ss as usize];
    /// let mut cur = std::io::Cursor::new(data);
    /// let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
    ///     .expect("could not create partition table");
    ///
    /// mbr[1] = mbrman::MBRPartitionEntry {
    ///     boot: mbrman::BOOT_INACTIVE,
    ///     first_chs: mbrman::CHS::empty(),
    ///     sys: 0x83,
    ///     last_chs: mbrman::CHS::empty(),
    ///     starting_lba: 11,
    ///     sectors: mbr.disk_size - 11 - 5,
    /// };
    ///
    /// // NOTE: align to the sectors, so we can use every last one of them
    /// // NOTE: this is only for the demonstration purpose, this is not recommended
    /// mbr.align = 1;
    ///
    /// // NOTE: the space as the end is more optimal because it will allow you to still be able to
    /// //       insert a bigger partition later
    /// assert_eq!(mbr.find_optimal_place(5), Some(mbr.disk_size - 5));
    /// # }
    /// ```
    pub fn find_optimal_place(&self, size: u32) -> Option<u32> {
        self.find_free_sectors()
            .into_iter()
            .filter(|(_, l)| *l >= size)
            .min_by_key(|(_, l)| *l)
            .map(|(i, _)| i)
    }

    /// Get the maximum size (in sectors) of a partition you could create in the MBR.
    /// This function will automatically align with the alignment defined in the `MBR`.
    ///
    /// # Examples:
    /// Basic usage:
    /// ```
    /// # #[cfg(feature = "std")] {
    /// let ss = 512;
    /// let data = vec![0; 100 * ss as usize];
    /// let mut cur = std::io::Cursor::new(data);
    /// let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
    ///     .expect("could not create partition table");
    ///
    /// // NOTE: align to the sectors, so we can use every last one of them
    /// // NOTE: this is only for the demonstration purpose, this is not recommended
    /// mbr.align = 1;
    ///
    /// assert_eq!(
    ///     mbr.get_maximum_partition_size().unwrap_or(0),
    ///     mbr.disk_size - 1
    /// );
    /// # }
    /// ```
    pub fn get_maximum_partition_size(&self) -> Result<u32> {
        self.find_free_sectors()
            .into_iter()
            .map(|(_, l)| l / self.align * self.align)
            .max()
            .ok_or(Error::NoSpaceLeft)
    }

    /// Gets the maximum size (in sectors) a partition can grow to without overlapping another
    /// partition.
    /// This function will automatically align with the alignment defined in the `MBR`.
    ///
    /// # Examples:
    /// Basic usage:
    /// ```
    /// # #[cfg(feature = "std")] {
    /// let ss = 512;
    /// let data = vec![0; 100 * ss as usize];
    /// let mut cur = std::io::Cursor::new(data);
    /// let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
    ///     .expect("could not create partition table");
    ///
    /// // NOTE: align to the sectors, so we can use every last one of them
    /// // NOTE: this is only for the demonstration purpose, this is not recommended
    /// mbr.align = 1;
    ///
    /// mbr[1] = mbrman::MBRPartitionEntry {
    ///     boot: mbrman::BOOT_INACTIVE,
    ///     first_chs: mbrman::CHS::empty(),
    ///     sys: 0x83,
    ///     last_chs: mbrman::CHS::empty(),
    ///     starting_lba: mbr.find_optimal_place(1).unwrap(),
    ///     sectors: 1,
    /// };
    ///
    /// assert_eq!(
    ///     mbr.get_maximum_partition_size_for(1)
    ///         .expect("could not find a place to put the partition"),
    ///     mbr.disk_size - 1
    /// );
    /// # }
    /// ```
    pub fn get_maximum_partition_size_for(&mut self, i: usize) -> Result<u32> {
        let spots = self.find_free_sectors();
        let p = self.get_mut(i).ok_or(Error::PartitionNotFound)?;
        let free_sectors = spots
            .into_iter()
            .find(|(i, _)| *i == p.starting_lba + p.sectors)
            .map(|(_, l)| l)
            .unwrap_or(0);
        Ok(p.sectors + free_sectors)
    }

    /// Push a new logical partition to the end of the extended partition list. This function will
    /// take care of creating the EBR for you. The EBR will be located at `starting_lba` (provided
    /// in input) and the logical partition itself will be located a block further to stay
    /// aligned. The size of the logical partition will be one block smaller than the `sectors`
    /// provided in input.
    pub fn push(
        &mut self,
        sys: u8,
        mut starting_lba: u32,
        mut sectors: u32,
    ) -> Result<&mut LogicalPartition> {
        let extended = self
            .header
            .get_extended_partition()
            .ok_or(Error::NoExtendedPartition)?;

        starting_lba = ((starting_lba - 1) / self.align + 1) * self.align;
        sectors = ((sectors - 1) / self.align + 1) * self.align;
        if sectors < 2 * self.align {
            return Err(Error::NotEnoughSectorsToCreateLogicalPartition);
        }

        let mut l = LogicalPartition {
            partition: MBRPartitionEntry {
                boot: BOOT_INACTIVE,
                first_chs: CHS::empty(),
                sys,
                last_chs: CHS::empty(),
                starting_lba: starting_lba + self.align,
                sectors: sectors - self.align,
            },
            absolute_ebr_lba: starting_lba,
            ebr_sectors: if self.logical_partitions.is_empty() {
                None
            } else {
                Some(sectors)
            },
            ebr_first_chs: CHS::empty(),
            ebr_last_chs: if self.logical_partitions.is_empty() {
                None
            } else {
                Some(CHS::empty())
            },
            bootstrap_code: [0; 446],
        };

        if l.absolute_ebr_lba < extended.starting_lba {
            return Err(Error::EBRStartsBeforeExtendedPartition);
        }

        if l.absolute_ebr_lba > extended.starting_lba + extended.sectors - 2 * self.align {
            return Err(Error::EBRStartsTooCloseToTheEndOfExtendedPartition);
        }

        if let Some(ebr_sectors) = l.ebr_sectors {
            let ending_ebr_lba = l.absolute_ebr_lba + ebr_sectors - 1;

            if ending_ebr_lba > extended.starting_lba + extended.sectors - 1 {
                return Err(Error::EBREndsAfterExtendedPartition);
            }
        }

        if self.check_geometry() {
            l.update_chs(self.cylinders, self.heads, self.sectors)?;
        }
        self.logical_partitions.push(l);

        Ok(self.logical_partitions.last_mut().unwrap())
    }

    /// Remove a logical partition. This will remove a logical partition in the array.
    ///
    /// # Remark
    ///
    /// This operation will decrease by one the index of every logical partition after the one that
    /// has been removed.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    pub fn remove(&mut self, index: usize) -> LogicalPartition {
        assert!(index >= 5, "logical partitions start at 5");
        self.logical_partitions.remove(index - 5)
    }
}

/// The `std::io` integration.
#[cfg(feature = "std")]
impl MBR {
    /// Make a new MBR
    ///
    /// # Examples
    /// Basic usage:
    /// ```
    /// # #[cfg(feature = "std")] {
    /// let mut f = std::fs::File::open("tests/fixtures/disk1.img")
    ///     .expect("could not open disk");
    /// let mbr = mbrman::MBR::new_from(&mut f, 512, [0x01, 0x02, 0x03, 0x04])
    ///     .expect("could not make a partition table");
    /// # }
    /// ```
    pub fn new_from<S>(seeker: &mut S, sector_size: u32, disk_signature: [u8; 4]) -> Result<MBR>
    where
        S: Seek + ?Sized,
    {
        Ok(MBR::new(sector_size, disk_size(seeker)?, disk_signature))
    }

    /// Read the MBR on a reader.
    ///
    /// # Examples
    /// Basic usage:
    /// ```
    /// # #[cfg(feature = "std")] {
    /// let mut f = std::fs::File::open("tests/fixtures/disk1.img")
    ///     .expect("could not open disk");
    /// let mbr = mbrman::MBR::read_from(&mut f, 512)
    ///     .expect("could not read the partition table");
    /// # }
    /// ```
    pub fn read_from<R>(reader: &mut R, sector_size: u32) -> Result<MBR>
    where
        R: Read + Seek + ?Sized,
    {
        let mut mbr = MBR::reader(sector_size, disk_size(reader)?);
        while let Some(offset) = mbr.next_offset()? {
            mbr.feed(&read_boot_record(reader, offset)?)?;
        }
        mbr.finish()
    }

    /// Updates the header to match the specifications of the seeker given in argument.
    /// `disk_size` will be updated after this operation.
    pub fn update_from<S>(&mut self, seeker: &mut S) -> Result<()>
    where
        S: Seek + ?Sized,
    {
        self.disk_size = disk_size_in_sectors(disk_size(seeker)?, self.sector_size);
        Ok(())
    }

    /// Write the MBR and the EBRs of the logical partitions to a disk, each at its own
    /// offset. This function will update the CHS address of the partitions automatically if a valid
    /// geometry has been set. See `check_geometry`.
    ///
    /// Nothing is written if the partition table is invalid. See `MBR::chunks`.
    ///
    /// # Examples
    /// Basic usage:
    /// ```
    /// # #[cfg(feature = "std")] {
    /// let ss = 512;
    /// let data = vec![0; 100 * ss as usize];
    /// let mut cur = std::io::Cursor::new(data);
    /// let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
    ///     .expect("could not make a partition table");
    ///
    /// // actually write:
    /// mbr.write_into(&mut cur)
    ///     .expect("could not write MBR to disk")
    /// # }
    /// ```
    pub fn write_into<W>(&mut self, writer: &mut W) -> Result<()>
    where
        W: Write + Seek + ?Sized,
    {
        for chunk in self.chunks()? {
            write_boot_record(writer, chunk.offset, &chunk.data)?;
        }
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl Index<usize> for MBR {
    type Output = MBRPartitionEntry;

    fn index(&self, i: usize) -> &Self::Output {
        assert!(i != 0, "invalid partition index: 0");
        self.get(i).expect("invalid partition")
    }
}

#[cfg(feature = "alloc")]
impl IndexMut<usize> for MBR {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        assert!(i != 0, "invalid partition index: 0");
        self.get_mut(i).expect("invalid partition")
    }
}

/// An MBR partition table header
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MBRHeader {
    /// Bootstrap code area
    pub bootstrap_code: [u8; 440],
    /// 32-bit disk signature
    pub disk_signature: [u8; 4],
    /// `[0x5a, 0x5a]` if protected, `[0x00, 0x00]` if not
    pub copy_protected: [u8; 2],
    /// Partition 1
    pub partition_1: MBRPartitionEntry,
    /// Partition 2
    pub partition_2: MBRPartitionEntry,
    /// Partition 3
    pub partition_3: MBRPartitionEntry,
    /// Partition 4
    pub partition_4: MBRPartitionEntry,
    /// Boot signature
    pub boot_signature: [u8; 2],
}

impl MBRHeader {
    /// Check if the partition table is copy-protected
    pub fn is_copy_protected(&self) -> Option<bool> {
        match self.copy_protected {
            [0x00, 0x00] => Some(false),
            [0x5a, 0x5a] => Some(true),
            _ => None,
        }
    }

    /// Get `Some(&MBRPartitionEntry)` if it exists, None otherwise.
    ///
    /// # Remarks
    ///
    ///  -  The partitions start at index 1
    ///  -  The first 4 partitions always exist
    ///  -  This function does not return logical partitions
    pub fn get(&self, i: usize) -> Option<&MBRPartitionEntry> {
        match i {
            1 => Some(&self.partition_1),
            2 => Some(&self.partition_2),
            3 => Some(&self.partition_3),
            4 => Some(&self.partition_4),
            _ => None,
        }
    }

    /// Get `Some(&mut MBRPartitionEntry)` if it exists, None otherwise.
    ///
    /// # Remarks
    ///
    ///  -  The partitions start at index 1
    ///  -  The first 4 partitions always exist
    ///  -  This function does not return logical partitions
    pub fn get_mut(&mut self, i: usize) -> Option<&mut MBRPartitionEntry> {
        match i {
            1 => Some(&mut self.partition_1),
            2 => Some(&mut self.partition_2),
            3 => Some(&mut self.partition_3),
            4 => Some(&mut self.partition_4),
            _ => None,
        }
    }

    /// Get an iterator over the primary partition entries and their index. The
    /// index always starts at 1.
    pub fn iter(&self) -> impl Iterator<Item = (usize, &MBRPartitionEntry)> {
        [
            &self.partition_1,
            &self.partition_2,
            &self.partition_3,
            &self.partition_4,
        ]
        .into_iter()
        .enumerate()
        .map(|(i, x)| (i + 1, x))
    }

    /// Get a mutable iterator over the primary partition entries and their
    /// index. The index always starts at 1.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (usize, &mut MBRPartitionEntry)> {
        [
            &mut self.partition_1,
            &mut self.partition_2,
            &mut self.partition_3,
            &mut self.partition_4,
        ]
        .into_iter()
        .enumerate()
        .map(|(i, x)| (i + 1, x))
    }

    fn get_extended_partition(&self) -> Option<&MBRPartitionEntry> {
        self.iter().find(|(_, x)| x.is_extended()).map(|(_, x)| x)
    }

    /// Read and validate the MBR header in the first sector of a disk.
    #[cfg(feature = "std")]
    pub fn read_from<R>(reader: &mut R) -> Result<MBRHeader>
    where
        R: Read + Seek + ?Sized,
    {
        MBRHeader::from_bytes(&read_boot_record(reader, 0)?)
    }

    /// Walk the EBR chain of the extended partition, one logical partition at a time, without
    /// doing any I/O and without allocating. The walk is over at once if there is no extended
    /// partition.
    ///
    /// With `alloc`, `MBR::reader` reads the MBR and the same partitions into an `MBR`.
    ///
    /// # Examples
    /// Basic usage:
    /// ```
    /// let disk: &[u8] = include_bytes!("../tests/fixtures/disk2.img");
    /// let sector = |offset: u64| -> &[u8; 512] {
    ///     let start = offset as usize;
    ///     disk[start..start + 512].try_into().unwrap()
    /// };
    ///
    /// let header = mbrman::MBRHeader::from_bytes(sector(0))
    ///     .expect("could not read the MBR header");
    /// let mut walk = header.ebr_walk(512);
    /// while let Some(offset) = walk.next_offset().expect("invalid EBR chain") {
    ///     if let Some(l) = walk.feed(sector(offset)).expect("could not read an EBR") {
    ///         println!("logical partition: starting lba = {}", l.partition.starting_lba);
    ///     }
    /// }
    /// ```
    pub fn ebr_walk(&self, sector_size: u32) -> EBRWalk {
        let extended = self.get_extended_partition().cloned();
        EBRWalk {
            sector_size,
            ebr_first_chs: extended.as_ref().map_or_else(CHS::empty, |x| x.first_chs),
            extended,
            failed: false,
            relative_ebr_lba: 0,
            ebr_sectors: None,
            ebr_last_chs: None,
        }
    }

    /// Decode and validate a MBR header from the 512 bytes of the first sector.
    pub fn from_bytes(bytes: &[u8; 512]) -> Result<MBRHeader> {
        let header = MBRHeader {
            bootstrap_code: chunk(bytes, 0),
            disk_signature: chunk(bytes, 440),
            copy_protected: chunk(bytes, 444),
            partition_1: MBRPartitionEntry::from_bytes(&chunk(bytes, 446)),
            partition_2: MBRPartitionEntry::from_bytes(&chunk(bytes, 462)),
            partition_3: MBRPartitionEntry::from_bytes(&chunk(bytes, 478)),
            partition_4: MBRPartitionEntry::from_bytes(&chunk(bytes, 494)),
            boot_signature: chunk(bytes, 510),
        };
        header.check()?;
        Ok(header)
    }

    /// Validate the MBR header and encode it as the 512 bytes of the first sector.
    pub fn to_bytes(&self) -> Result<[u8; 512]> {
        self.check()?;
        let mut bytes = [0; BOOT_RECORD_SIZE];
        bytes[..440].copy_from_slice(&self.bootstrap_code);
        bytes[440..444].copy_from_slice(&self.disk_signature);
        bytes[444..446].copy_from_slice(&self.copy_protected);
        let partitions = [
            &self.partition_1,
            &self.partition_2,
            &self.partition_3,
            &self.partition_4,
        ];
        for (i, p) in partitions.into_iter().enumerate() {
            bytes[446 + 16 * i..462 + 16 * i].copy_from_slice(&p.to_bytes());
        }
        bytes[510..].copy_from_slice(&self.boot_signature);
        Ok(bytes)
    }

    /// Make a new MBR header
    pub fn new(disk_signature: [u8; 4]) -> MBRHeader {
        MBRHeader {
            bootstrap_code: [0; 440],
            disk_signature,
            copy_protected: [0x00, 0x00],
            partition_1: MBRPartitionEntry::empty(),
            partition_2: MBRPartitionEntry::empty(),
            partition_3: MBRPartitionEntry::empty(),
            partition_4: MBRPartitionEntry::empty(),
            boot_signature: BOOT_SIGNATURE,
        }
    }

    /// Validate the MBR header and write it to the first sector of a disk.
    #[cfg(feature = "std")]
    pub fn write_into<W>(&self, writer: &mut W) -> Result<()>
    where
        W: Write + Seek + ?Sized,
    {
        write_boot_record(writer, 0, &self.to_bytes()?)
    }

    /// Validate invariants
    fn check(&self) -> Result<()> {
        if self.boot_signature != BOOT_SIGNATURE {
            return Err(Error::InvalidSignature);
        }
        self.iter().try_for_each(|(_, partition)| partition.check())
    }
}

impl Index<usize> for MBRHeader {
    type Output = MBRPartitionEntry;

    fn index(&self, i: usize) -> &Self::Output {
        assert_ne!(i, 0, "invalid partition index: 0");
        self.get(i).expect("invalid partition")
    }
}

impl IndexMut<usize> for MBRHeader {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        assert_ne!(i, 0, "invalid partition index: 0");
        self.get_mut(i).expect("invalid partition")
    }
}

#[derive(Debug, Clone)]
struct EBRHeader {
    bootstrap_code: [u8; 446],
    partition_1: MBRPartitionEntry,
    partition_2: MBRPartitionEntry,
    _unused_partition_3: [u8; 16],
    _unused_partition_4: [u8; 16],
    boot_signature: [u8; 2],
}

impl EBRHeader {
    fn from_bytes(bytes: &[u8; BOOT_RECORD_SIZE]) -> Result<EBRHeader> {
        let header = EBRHeader {
            bootstrap_code: chunk(bytes, 0),
            partition_1: MBRPartitionEntry::from_bytes(&chunk(bytes, 446)),
            partition_2: MBRPartitionEntry::from_bytes(&chunk(bytes, 462)),
            _unused_partition_3: chunk(bytes, 478),
            _unused_partition_4: chunk(bytes, 494),
            boot_signature: chunk(bytes, 510),
        };
        header.check()?;
        Ok(header)
    }

    #[cfg(feature = "alloc")]
    fn to_bytes(&self) -> [u8; BOOT_RECORD_SIZE] {
        let mut bytes = [0; BOOT_RECORD_SIZE];
        bytes[..446].copy_from_slice(&self.bootstrap_code);
        bytes[446..462].copy_from_slice(&self.partition_1.to_bytes());
        bytes[462..478].copy_from_slice(&self.partition_2.to_bytes());
        bytes[478..494].copy_from_slice(&self._unused_partition_3);
        bytes[494..510].copy_from_slice(&self._unused_partition_4);
        bytes[510..].copy_from_slice(&self.boot_signature);
        bytes
    }

    /// Validate invariants
    fn check(&self) -> Result<()> {
        if self.boot_signature != BOOT_SIGNATURE {
            return Err(Error::InvalidSignature);
        }
        self.partition_1.check()?;
        self.partition_2.check()
    }

    fn unwrap(self) -> (MBRPartitionEntry, MBRPartitionEntry, [u8; 446]) {
        (self.partition_1, self.partition_2, self.bootstrap_code)
    }
}

/// An MBR partition entry
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MBRPartitionEntry {
    /// Boot flag
    pub boot: u8,
    /// CHS address of the first sector in the partition
    pub first_chs: CHS,
    /// Partition type (file system ID)
    pub sys: u8,
    /// CHS address of the last sector in the partition
    pub last_chs: CHS,
    /// Starting LBA of the partition
    pub starting_lba: u32,
    /// Number of sectors allocated to the partition
    pub sectors: u32,
}

impl MBRPartitionEntry {
    /// Decode a partition entry from its 16 on-disk bytes. No validation is done.
    pub fn from_bytes(bytes: &[u8; 16]) -> MBRPartitionEntry {
        MBRPartitionEntry {
            boot: bytes[0],
            first_chs: CHS::from_bytes(&chunk(bytes, 1)),
            sys: bytes[4],
            last_chs: CHS::from_bytes(&chunk(bytes, 5)),
            starting_lba: u32::from_le_bytes(chunk(bytes, 8)),
            sectors: u32::from_le_bytes(chunk(bytes, 12)),
        }
    }

    /// Encode a partition entry as its 16 on-disk bytes. No validation is done.
    pub fn to_bytes(&self) -> [u8; 16] {
        let mut bytes = [0; 16];
        bytes[0] = self.boot;
        bytes[1..4].copy_from_slice(&self.first_chs.to_bytes());
        bytes[4] = self.sys;
        bytes[5..8].copy_from_slice(&self.last_chs.to_bytes());
        bytes[8..12].copy_from_slice(&self.starting_lba.to_le_bytes());
        bytes[12..].copy_from_slice(&self.sectors.to_le_bytes());
        bytes
    }

    /// Creates an empty partition entry
    ///
    /// # Examples
    /// Basic usage:
    /// ```
    /// # #[cfg(feature = "std")] {
    /// let ss = 512;
    /// let data = vec![0; 100 * ss as usize];
    /// let mut cur = std::io::Cursor::new(data);
    /// let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
    ///     .expect("could not create partition table");
    ///
    /// mbr[1] = mbrman::MBRPartitionEntry::empty();
    ///
    /// // NOTE: an empty partition entry is considered as not allocated
    /// assert!(mbr[1].is_unused());
    /// # }
    /// ```
    pub fn empty() -> MBRPartitionEntry {
        MBRPartitionEntry {
            boot: BOOT_INACTIVE,
            first_chs: CHS::empty(),
            sys: 0,
            last_chs: CHS::empty(),
            starting_lba: 0,
            sectors: 0,
        }
    }

    /// Returns `true` if the partition entry is used (type (sys) != 0)
    pub fn is_used(&self) -> bool {
        self.sys > 0
    }

    /// Returns `true` if the partition entry is not used (type (sys) == 0)
    pub fn is_unused(&self) -> bool {
        !self.is_used()
    }

    /// Returns `true` if the partition is an extended type partition
    pub fn is_extended(&self) -> bool {
        self.sys == 0x05
            || self.sys == 0x0f
            || self.sys == 0x85
            || self.sys == 0xc5
            || self.sys == 0xd5
    }

    /// Returns `true` if the partition is marked active (bootable)
    pub fn is_active(&self) -> bool {
        self.boot == BOOT_ACTIVE
    }

    /// Validate invariants
    fn check(&self) -> Result<()> {
        if self.boot != BOOT_ACTIVE && self.boot != BOOT_INACTIVE {
            return Err(Error::InvalidBootFlag);
        }
        Ok(())
    }
}

/// An abstraction struct for a logical partition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LogicalPartition {
    /// MBR partition entry of the logical partition
    pub partition: MBRPartitionEntry,
    /// Absolute LBA of the EBR partition table
    pub absolute_ebr_lba: u32,
    /// Number of sectors in the EBR
    ///
    /// # Remark
    ///
    /// This information is known for all the EBR except the first logical partition
    pub ebr_sectors: Option<u32>,
    /// CHS address of the EBR header
    ///
    /// # Remark
    ///
    /// This information is copied from the extended partition for the first logical partition
    pub ebr_first_chs: CHS,
    /// CHS address of the last sector of the extended partition in the EBR header
    ///
    /// # Remark
    ///
    /// This information is known for all the EBR except the first logical partition
    pub ebr_last_chs: Option<CHS>,
    /// Bootstrap code area
    pub bootstrap_code: [u8; 446],
}

impl LogicalPartition {
    /// Update the fields `partition.first_chs`, `partition.last_chs`.
    /// `ebr_first_chs` and `ebr_last_chs` using the disk geometry provided in parameter.
    pub fn update_chs(&mut self, cylinders: u16, heads: u8, sectors: u8) -> Result<()> {
        self.partition.first_chs =
            CHS::from_lba_exact(self.partition.starting_lba, cylinders, heads, sectors)?;
        self.partition.last_chs = CHS::from_lba_exact(
            self.partition.starting_lba + self.partition.sectors - 1,
            cylinders,
            heads,
            sectors,
        )?;
        self.ebr_first_chs = CHS::from_lba_exact(self.absolute_ebr_lba, cylinders, heads, sectors)?;
        self.ebr_last_chs = if let Some(ebr_sectors) = self.ebr_sectors {
            Some(CHS::from_lba_exact(
                self.absolute_ebr_lba + ebr_sectors - 1,
                cylinders,
                heads,
                sectors,
            )?)
        } else {
            None
        };

        Ok(())
    }
}

/// A walk through the EBR chain of an extended partition, one logical partition at a time,
/// that does no I/O: it asks for each EBR to read and you feed it the 512 bytes you read.
///
/// Call `next_offset` to get the byte offset of the next EBR, read the 512 bytes there and give
/// them to `feed`, until `next_offset` returns `None`. The walk is over after the first error.
///
/// Created by [`MBRHeader::ebr_walk`], which has an example.
#[derive(Debug, Clone)]
pub struct EBRWalk {
    sector_size: u32,
    /// The extended partition, `None` once the walk is over.
    extended: Option<MBRPartitionEntry>,
    /// The walk ended on an error.
    failed: bool,
    relative_ebr_lba: u32,
    ebr_sectors: Option<u32>,
    ebr_first_chs: CHS,
    ebr_last_chs: Option<CHS>,
}

impl EBRWalk {
    /// Return the byte offset of the next EBR to read, or `None` when the walk is over.
    ///
    /// Return `Error::InconsistentEBR` if the EBR the chain links to cannot be addressed.
    pub fn next_offset(&self) -> Result<Option<u64>> {
        match &self.extended {
            Some(extended) => {
                let absolute_ebr_lba = self.absolute_ebr_lba(extended)?;
                Ok(Some(
                    u64::from(absolute_ebr_lba) * u64::from(self.sector_size),
                ))
            }
            None => Ok(None),
        }
    }

    /// Decode the 512 bytes read at the offset `next_offset` returned. Return the logical
    /// partition of that EBR, or `None` if the extended partition is empty.
    ///
    /// Return `Error::OutOfSequence` if the walk is already over.
    pub fn feed(&mut self, sector: &[u8; 512]) -> Result<Option<LogicalPartition>> {
        // the walk ends here unless the EBR links to another one
        let extended = self.extended.take().ok_or(Error::OutOfSequence)?;
        let res = self.decode(&extended, sector);
        match res {
            Ok(Some(_)) if self.relative_ebr_lba != 0 => self.extended = Some(extended),
            Err(_) => self.failed = true,
            _ => {}
        }
        res
    }

    /// Return `true` if the walk reached the end of the chain without error.
    #[cfg(feature = "alloc")]
    fn is_done(&self) -> bool {
        self.extended.is_none() && !self.failed
    }

    /// The absolute LBA of the next EBR.
    fn absolute_ebr_lba(&self, extended: &MBRPartitionEntry) -> Result<u32> {
        // check the link before following it: an EBR past u32::MAX cannot be
        // represented, so it must not be read
        extended
            .starting_lba
            .checked_add(self.relative_ebr_lba)
            .ok_or(Error::InconsistentEBR)
    }

    /// Decode the EBR `relative_ebr_lba` points to. Return `None` if the extended partition
    /// is empty.
    fn decode(
        &mut self,
        extended: &MBRPartitionEntry,
        sector: &[u8; BOOT_RECORD_SIZE],
    ) -> Result<Option<LogicalPartition>> {
        // NOTE: The number of sectors is an index field; thus, the zero
        //       value is invalid, reserved and must not be used in normal
        //       partition entries. The entry is used by operating systems
        //       in certain circumstances; in such cases the CHS addresses
        //       are ignored.

        let absolute_ebr_lba = self.absolute_ebr_lba(extended)?;
        let ebr = match EBRHeader::from_bytes(sector) {
            Ok(ebr) => ebr,
            // NOTE: if the extended partition is empty, it is not required that an
            //       EBR exists
            Err(Error::InvalidSignature) if self.relative_ebr_lba == 0 => return Ok(None),
            Err(err) => return Err(err),
        };
        let (partition, next, bootstrap_code) = ebr.unwrap();
        let starting_lba = partition
            .starting_lba
            .checked_add(absolute_ebr_lba)
            .ok_or(Error::InconsistentEBR)?;
        let logical_partition = LogicalPartition {
            partition: MBRPartitionEntry {
                starting_lba,
                ..partition
            },
            absolute_ebr_lba,
            ebr_sectors: self.ebr_sectors,
            ebr_first_chs: self.ebr_first_chs,
            ebr_last_chs: self.ebr_last_chs,
            bootstrap_code,
        };

        // the links must go forward, otherwise the chain could loop
        if next.starting_lba > 0 && self.relative_ebr_lba >= next.starting_lba {
            return Err(Error::InconsistentEBR);
        }

        self.relative_ebr_lba = next.starting_lba;
        self.ebr_sectors = Some(next.sectors);
        self.ebr_first_chs = next.first_chs;
        self.ebr_last_chs = Some(next.last_chs);

        Ok(Some(logical_partition))
    }
}

/// A read of an MBR and its EBRs that does no I/O: it asks for each boot record to read and you
/// feed it the 512 bytes you read.
///
/// Call `next_offset` to get the byte offset of the next boot record, read the 512 bytes there
/// and give them to `feed`, until `next_offset` returns `None`. Then `finish` returns the `MBR`.
/// The MBR comes first, at offset 0, then the EBRs.
///
/// Created by [`MBR::reader`].
///
/// # Examples
/// Basic usage:
/// ```
/// let disk: &[u8] = include_bytes!("../tests/fixtures/disk2.img");
///
/// let mut reader = mbrman::MBR::reader(512, disk.len() as u64);
/// while let Some(offset) = reader.next_offset().expect("invalid EBR chain") {
///     let start = offset as usize;
///     reader
///         .feed(disk[start..start + 512].try_into().unwrap())
///         .expect("could not read a boot record");
/// }
/// let mbr = reader.finish().expect("could not read the partition table");
/// assert_eq!(mbr.logical_partitions.len(), 5);
/// ```
#[cfg(feature = "alloc")]
#[derive(Debug, Clone)]
pub struct MBRReader {
    sector_size: u32,
    /// Disk size in sectors
    disk_size: u32,
    /// The MBR header and the walk of its EBR chain, once the MBR has been read
    table: Option<(MBRHeader, EBRWalk)>,
    logical_partitions: Vec<LogicalPartition>,
}

#[cfg(feature = "alloc")]
impl MBRReader {
    /// Return the byte offset of the next boot record to read, or `None` when the whole
    /// partition table has been read. `None` is also returned after `feed` failed: the reader
    /// then asks for nothing more, and `finish` returns `Error::OutOfSequence`.
    ///
    /// Return `Error::InconsistentEBR` if the EBR the chain links to cannot be addressed.
    pub fn next_offset(&self) -> Result<Option<u64>> {
        match &self.table {
            Some((_, walk)) => walk.next_offset(),
            None => Ok(Some(0)),
        }
    }

    /// Decode the 512 bytes read at the offset `next_offset` returned.
    ///
    /// Return `Error::OutOfSequence` if the whole partition table has already been read.
    pub fn feed(&mut self, sector: &[u8; 512]) -> Result<()> {
        match &mut self.table {
            Some((_, walk)) => self.logical_partitions.extend(walk.feed(sector)?),
            None => {
                let header = MBRHeader::from_bytes(sector)?;
                let walk = header.ebr_walk(self.sector_size);
                self.table = Some((header, walk));
            }
        }
        Ok(())
    }

    /// Return the MBR read.
    ///
    /// Return `Error::OutOfSequence` if the partition table has not been read completely and
    /// without error.
    pub fn finish(self) -> Result<MBR> {
        let (header, walk) = self.table.ok_or(Error::OutOfSequence)?;
        if !walk.is_done() {
            return Err(Error::OutOfSequence);
        }
        let align = MBR::find_alignment(&header, &self.logical_partitions);

        Ok(MBR {
            sector_size: self.sector_size,
            header,
            logical_partitions: self.logical_partitions,
            align,
            cylinders: 0,
            heads: 0,
            sectors: 0,
            disk_size: self.disk_size,
        })
    }
}

/// A boot record to write to the disk, produced by [`MBR::chunks`].
#[cfg(feature = "alloc")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Chunk {
    /// Byte offset of the boot record on the disk
    pub offset: u64,
    /// The 512 bytes of the boot record
    pub data: [u8; 512],
}

/// An iterator over the boot records to write to the disk: the MBR, then the EBRs.
///
/// Created by [`MBR::chunks`], which validated them all.
#[cfg(feature = "alloc")]
#[derive(Debug)]
pub struct Chunks<'a> {
    mbr: &'a MBR,
    /// The MBR, until it is returned
    header: Option<[u8; BOOT_RECORD_SIZE]>,
    /// The extended partition, `None` if there are no EBRs to write
    extended: Option<MBRPartitionEntry>,
    /// The index of the next logical partition
    next: usize,
}

#[cfg(feature = "alloc")]
impl Iterator for Chunks<'_> {
    type Item = Chunk;

    fn next(&mut self) -> Option<Chunk> {
        if let Some(data) = self.header.take() {
            return Some(Chunk { offset: 0, data });
        }
        let extended = self.extended.as_ref()?;
        let l = self.mbr.logical_partitions.get(self.next)?;
        let ebr = self
            .mbr
            .ebr(self.next, extended)
            .expect("the EBRs are validated by MBR::chunks");
        self.next += 1;
        Some(Chunk {
            offset: u64::from(l.absolute_ebr_lba) * u64::from(self.mbr.sector_size),
            data: ebr.to_bytes(),
        })
    }
}

#[cfg(feature = "alloc")]
impl FusedIterator for Chunks<'_> {}

/// A CHS address (cylinder/head/sector)
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct CHS {
    /// Cylinder
    pub cylinder: u16,
    /// Head
    pub head: u8,
    /// Sector
    pub sector: u8,
}

impl CHS {
    /// Creates a new CHS address based on input parameters.
    ///
    /// # Remark
    ///
    /// The values entered in input are not checked.
    pub fn new(cylinder: u16, head: u8, sector: u8) -> CHS {
        CHS {
            cylinder,
            head,
            sector,
        }
    }

    /// Creates an empty CHS addressing (0/0/0).
    ///
    /// # Remark
    ///
    /// This is what you need on recent hardware because CHS is never used.
    pub fn empty() -> CHS {
        CHS {
            cylinder: 0,
            head: 0,
            sector: 0,
        }
    }

    /// Creates a CHS address calculated from the number of cylinders, heads
    /// and sectors per track of the hard disk.
    ///
    /// # Remarks
    ///
    ///  *  You probably don't need to do this at all! This is only useful if you
    ///     intend to use partitions that use the CHS addressing. Check the column
    ///     "Access" of [this table on Wikipedia](https://en.wikipedia.org/wiki/Partition_type).
    ///  *  On old systems, partitions must be aligned on cylinders.
    pub fn from_lba_exact(lba: u32, cylinders: u16, heads: u8, sectors: u8) -> Result<CHS> {
        // NOTE: code inspired from libfdisk (long2chs)
        let cylinders = u32::from(cylinders);
        let heads = u32::from(heads);
        let sectors = u32::from(sectors);
        let cylinder_size = heads * sectors;

        let cylinder = lba / cylinder_size;
        let rem = lba % cylinder_size;
        let head = rem / sectors;
        let sector = rem % sectors + 1;

        if cylinder > 1023 {
            return Err(Error::LBAExceedsMaximumCHS);
        }

        if cylinder > cylinders {
            return Err(Error::LBAExceedsMaximumCylinders);
        }

        Ok(CHS {
            cylinder: u16::try_from(cylinder).unwrap(),
            head: u8::try_from(head).unwrap(),
            sector: u8::try_from(sector).unwrap(),
        })
    }

    /// Creates a CHS address, aligned to the nearest cylinder. The cylinder
    /// chosen will always be the exact cylinder (if the LBA is exactly at the
    /// beginning of a cylinder); or the next cylinder. But it will never
    /// choose the previous cylinder.
    pub fn from_lba_aligned(lba: u32, cylinders: u16, heads: u8, sectors: u8) -> Result<CHS> {
        let cylinders = u32::from(cylinders);
        let heads = u32::from(heads);
        let sectors = u32::from(sectors);
        let cylinder_size = heads * sectors;

        let cylinder = ((lba - 1) / cylinder_size) + 1;

        if cylinder > 1023 {
            return Err(Error::LBAExceedsMaximumCHS);
        }

        if cylinder > cylinders {
            return Err(Error::LBAExceedsMaximumCylinders);
        }

        // NOTE: In CHS addressing the sector numbers always start at 1, there is no sector 0
        //       https://en.wikipedia.org/wiki/Cylinder-head-sector
        Ok(CHS {
            cylinder: u16::try_from(cylinder).unwrap(),
            head: 0,
            sector: 1,
        })
    }

    /// Convert a CHS address to LBA
    pub fn to_lba(self, heads: u8, sectors: u8) -> u32 {
        let heads = u32::from(heads);
        let sectors = u32::from(sectors);
        let c = u32::from(self.cylinder);
        let h = u32::from(self.head);
        let s = u32::from(self.sector);

        // NOTE: In CHS addressing the sector numbers always start at 1, there is no sector 0
        //       https://en.wikipedia.org/wiki/Cylinder-head-sector
        c * (heads * sectors) + h * sectors + s - 1
    }

    /// Check if the CHS address is empty
    ///
    /// # Remark
    ///
    /// This function does not check if the CHS address is withing range of
    /// possible values for a provided hard disk.
    pub fn is_empty(self) -> bool {
        self.cylinder == 0 && self.head == 0 && self.sector == 0
    }

    /// Check if the CHS address is valid and within range of the possible
    /// values for the hard disk geometry provided in argument.
    pub fn is_valid(self, cylinders: u16, heads: u8, sectors: u8) -> bool {
        // NOTE: In CHS addressing the sector numbers always start at 1, there is no sector 0
        //       https://en.wikipedia.org/wiki/Cylinder-head-sector
        self.sector > 0 && self.sector <= sectors && self.head < heads && self.cylinder < cylinders
    }
}

// On disk, a CHS address is packed in 3 bytes:
// - byte 0: head
// - byte 1: bits 7-6 are bits 9-8 of the cylinder, bits 5-0 are the sector
// - byte 2: bits 7-0 of the cylinder
impl CHS {
    /// Decode a CHS address from its 3 packed on-disk bytes.
    pub fn from_bytes(&[head, sector_cylinder_high, cylinder_low]: &[u8; 3]) -> CHS {
        CHS {
            cylinder: (u16::from(sector_cylinder_high >> 6) << 8) | u16::from(cylinder_low),
            head,
            sector: sector_cylinder_high & 0x3f,
        }
    }

    /// Encode a CHS address as its 3 packed on-disk bytes.
    pub fn to_bytes(&self) -> [u8; 3] {
        let [cylinder_high, cylinder_low] = self.cylinder.to_be_bytes();
        [
            self.head,
            ((cylinder_high & 0x03) << 6) | (self.sector & 0x3f),
            cylinder_low,
        ]
    }
}

/// Tests that build in every feature set, `std` and `alloc` included: they feed byte slices to
/// the readers, without `std::io`.
#[cfg(test)]
mod core_tests {
    use super::*;

    const DISK2: &[u8] = include_bytes!("../tests/fixtures/disk2.img");

    /// The boot record at byte `offset` of `disk`.
    fn sector(disk: &[u8], offset: u64) -> &[u8; BOOT_RECORD_SIZE] {
        let start = usize::try_from(offset).unwrap();
        disk[start..start + BOOT_RECORD_SIZE].try_into().unwrap()
    }

    #[test]
    fn ebr_walk_of_disk2() {
        let header = MBRHeader::from_bytes(sector(DISK2, 0)).unwrap();
        let expected = [
            (5, None),
            (7, Some(3)),
            (10, Some(4)),
            (14, Some(2)),
            (16, Some(2)),
        ];

        let mut walk = header.ebr_walk(512);
        for (absolute_ebr_lba, ebr_sectors) in expected {
            let offset = walk.next_offset().unwrap().unwrap();
            assert_eq!(offset, u64::from(absolute_ebr_lba) * 512);
            let l = walk.feed(sector(DISK2, offset)).unwrap().unwrap();
            assert_eq!(l.absolute_ebr_lba, absolute_ebr_lba);
            assert_eq!(l.ebr_sectors, ebr_sectors);
            assert_eq!(l.partition.sys, 0x83);
        }
        assert_eq!(walk.next_offset().unwrap(), None);
    }

    #[test]
    fn ebr_walk_without_extended_partition() {
        let header = MBRHeader::new([0xff; 4]);
        let mut walk = header.ebr_walk(512);
        assert_eq!(walk.next_offset().unwrap(), None);
        assert!(matches!(
            walk.feed(sector(DISK2, 0)),
            Err(Error::OutOfSequence)
        ));
    }

    #[test]
    fn ebr_walk_of_empty_extended_partition() {
        let mut data = [0; 10240];
        data.copy_from_slice(DISK2);
        // the first EBR, at LBA 5, has no signature: the extended partition is empty
        data[5 * 512 + 510..6 * 512].fill(0);

        let header = MBRHeader::from_bytes(sector(&data, 0)).unwrap();
        let mut walk = header.ebr_walk(512);
        assert_eq!(walk.next_offset().unwrap(), Some(5 * 512));
        assert!(walk.feed(sector(&data, 5 * 512)).unwrap().is_none());
        // a finished walk asks for nothing more
        assert_eq!(walk.next_offset().unwrap(), None);
        assert!(matches!(
            walk.feed(sector(&data, 5 * 512)),
            Err(Error::OutOfSequence)
        ));
    }

    #[test]
    fn ebr_walk_with_backward_link() {
        let mut data = [0; 10240];
        data.copy_from_slice(DISK2);
        // the EBR at LBA 7 (relative LBA 2) links back to relative LBA 1
        let link = 7 * 512 + 462 + 8;
        data[link..link + 4].copy_from_slice(&1_u32.to_le_bytes());

        let header = MBRHeader::from_bytes(sector(&data, 0)).unwrap();
        let mut walk = header.ebr_walk(512);
        let l = walk.feed(sector(&data, 5 * 512)).unwrap().unwrap();
        assert_eq!(l.absolute_ebr_lba, 5);
        assert_eq!(walk.next_offset().unwrap(), Some(7 * 512));
        assert!(matches!(
            walk.feed(sector(&data, 7 * 512)),
            Err(Error::InconsistentEBR)
        ));
        // the walk is over after an error
        assert_eq!(walk.next_offset().unwrap(), None);
    }

    #[test]
    fn ebr_walk_with_overflowing_link() {
        let mut header = MBRHeader::new([0xff; 4]);
        header.partition_1 = MBRPartitionEntry {
            sys: 0x0f,
            starting_lba: u32::MAX - 1,
            sectors: 1,
            ..MBRPartitionEntry::empty()
        };
        // an EBR whose next link points past u32::MAX
        let mut ebr = [0; BOOT_RECORD_SIZE];
        ebr[446 + 4] = 0x83;
        ebr[462 + 4] = 0x0f;
        ebr[462 + 8..462 + 12].copy_from_slice(&5_u32.to_le_bytes());
        ebr[510..].copy_from_slice(&BOOT_SIGNATURE);

        let mut walk = header.ebr_walk(512);
        assert_eq!(
            walk.next_offset().unwrap(),
            Some(u64::from(u32::MAX - 1) * 512)
        );
        assert!(walk.feed(&ebr).unwrap().is_some());
        assert!(matches!(walk.next_offset(), Err(Error::InconsistentEBR)));
        assert!(matches!(walk.feed(&ebr), Err(Error::InconsistentEBR)));
        assert_eq!(walk.next_offset().unwrap(), None);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn mbr_reader_of_disk2() {
        let mut reader = MBR::reader(512, DISK2.len() as u64);
        let mut reads = 0;
        while let Some(offset) = reader.next_offset().unwrap() {
            reader.feed(sector(DISK2, offset)).unwrap();
            reads += 1;
        }
        // the MBR and 5 EBRs
        assert_eq!(reads, 6);
        let mbr = reader.finish().unwrap();
        assert_eq!(mbr.disk_size, 20);
        assert_eq!(mbr.logical_partitions.len(), 5);
        assert_eq!(mbr.header, MBRHeader::from_bytes(sector(DISK2, 0)).unwrap());
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn mbr_reader_out_of_sequence() {
        // finished before the MBR is read
        let reader = MBR::reader(512, DISK2.len() as u64);
        assert!(matches!(reader.finish(), Err(Error::OutOfSequence)));

        // finished before the EBRs are read
        let mut reader = MBR::reader(512, DISK2.len() as u64);
        reader.feed(sector(DISK2, 0)).unwrap();
        assert!(matches!(reader.finish(), Err(Error::OutOfSequence)));

        // fed after the whole table is read
        let mut reader = MBR::reader(512, DISK2.len() as u64);
        while let Some(offset) = reader.next_offset().unwrap() {
            reader.feed(sector(DISK2, offset)).unwrap();
        }
        assert!(matches!(
            reader.feed(sector(DISK2, 0)),
            Err(Error::OutOfSequence)
        ));
        assert_eq!(reader.finish().unwrap().logical_partitions.len(), 5);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn mbr_reader_after_an_error() {
        let mut data = [0; 10240];
        data.copy_from_slice(DISK2);
        // the EBR at LBA 7 (relative LBA 2) links back to relative LBA 1
        let link = 7 * 512 + 462 + 8;
        data[link..link + 4].copy_from_slice(&1_u32.to_le_bytes());

        let mut reader = MBR::reader(512, data.len() as u64);
        let err = loop {
            let offset = reader.next_offset().unwrap().unwrap();
            if let Err(err) = reader.feed(sector(&data, offset)) {
                break err;
            }
        };
        assert!(matches!(err, Error::InconsistentEBR));
        // a caller that goes on anyway asks for nothing more, and finish reports the misuse
        assert_eq!(reader.next_offset().unwrap(), None);
        assert!(matches!(reader.finish(), Err(Error::OutOfSequence)));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn chunks_of_invalid_table() {
        let mut mbr = MBR::new(512, 64 * 512, [0xff; 4]);
        mbr[1] = MBRPartitionEntry {
            sys: 0x0f,
            starting_lba: 1,
            sectors: 63,
            ..MBRPartitionEntry::empty()
        };
        mbr.align = 1;
        mbr.push(0x83, 1, 10).unwrap();
        mbr.push(0x83, 12, 10).unwrap();
        // the second logical partition is invalid: the MBR must not be written either
        mbr.logical_partitions[1].partition.boot = 0x42;
        assert!(matches!(mbr.chunks(), Err(Error::InvalidBootFlag)));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn chunks_round_trip() {
        let mut mbr = MBR::new(512, 64 * 512, [0xff; 4]);
        mbr[1] = MBRPartitionEntry {
            sys: 0x0f,
            starting_lba: 1,
            sectors: 63,
            ..MBRPartitionEntry::empty()
        };
        mbr.align = 1;
        mbr.push(0x83, 1, 10).unwrap();
        mbr.push(0x07, 12, 10).unwrap();

        let mut disk = [0; 64 * 512];
        let mut offsets = [0; 3];
        let mut chunks = mbr.chunks().unwrap();
        for (chunk, offset) in chunks.by_ref().zip(&mut offsets) {
            let start = usize::try_from(chunk.offset).unwrap();
            disk[start..start + BOOT_RECORD_SIZE].copy_from_slice(&chunk.data);
            *offset = chunk.offset;
        }
        assert!(chunks.next().is_none());
        // the MBR first, then each EBR
        assert_eq!(offsets, [0, 512, 12 * 512]);

        let mut reader = MBR::reader(512, disk.len() as u64);
        while let Some(offset) = reader.next_offset().unwrap() {
            reader.feed(sector(&disk, offset)).unwrap();
        }
        let read = reader.finish().unwrap();
        assert_eq!(read.header, mbr.header);
        assert_eq!(read.logical_partitions, mbr.logical_partitions);
    }
}

#[cfg(all(test, feature = "std"))]
#[allow(clippy::cognitive_complexity)]
mod tests {
    use super::*;
    use std::fs::File;
    use std::io::{Cursor, Read, Seek, SeekFrom, Write};
    use std::vec;

    #[test]
    fn error_messages() {
        use std::error::Error as _;
        use std::string::ToString;

        let cases = [
            (
                Error::LBAExceedsMaximumCHS,
                "exceeded the maximum limit of CHS",
            ),
            (
                Error::LBAExceedsMaximumCylinders,
                "exceeded the maximum number of cylinders on disk",
            ),
            (
                Error::Io(std::io::ErrorKind::UnexpectedEof.into()),
                "generic I/O error",
            ),
            (Error::InconsistentEBR, "inconsistent extended boot record"),
            (Error::NoExtendedPartition, "no extended partition"),
            (
                Error::EBRStartsBeforeExtendedPartition,
                "EBR starts before the extended partition",
            ),
            (
                Error::EBRStartsTooCloseToTheEndOfExtendedPartition,
                "EBR starts too close to the end of the extended partition",
            ),
            (
                Error::EBREndsAfterExtendedPartition,
                "EBR ends after the extended partition",
            ),
            (
                Error::NotEnoughSectorsToCreateLogicalPartition,
                "not enough sectors to create a logical partition",
            ),
            (Error::PartitionNotFound, "partition not found"),
            (Error::NoSpaceLeft, "no space left"),
            (Error::InvalidSignature, "invalid MBR signature"),
            (Error::InvalidBootFlag, "partition has invalid boot flag"),
            (
                Error::OutOfSequence,
                "boot record fed out of sequence or read not finished",
            ),
        ];
        for (err, msg) in cases {
            assert_eq!(err.to_string(), msg);
            assert_eq!(err.source().is_some(), matches!(err, Error::Io(_)));
        }

        let err = Error::from(std::io::Error::from(std::io::ErrorKind::UnexpectedEof));
        let source = err
            .source()
            .unwrap()
            .downcast_ref::<std::io::Error>()
            .unwrap();
        assert_eq!(source.kind(), std::io::ErrorKind::UnexpectedEof);
    }

    const DISK1: &str = "tests/fixtures/disk1.img";
    const DISK2: &str = "tests/fixtures/disk2.img";

    #[test]
    fn deserialize_maximum_chs_value() {
        let chs: CHS = CHS::from_bytes(&[0xff, 0xff, 0xff]);
        assert_eq!(
            chs,
            CHS {
                cylinder: 1023,
                head: 255,
                sector: 63,
            }
        );
    }

    #[test]
    fn serialize_maximum_chs_value() {
        let chs = CHS {
            cylinder: 1023,
            head: 255,
            sector: 63,
        };
        let slice = chs.to_bytes();
        assert_eq!(slice.len(), 3);
        for element in slice {
            assert_eq!(element, 0xff);
        }
    }

    #[test]
    fn serialize_and_deserialize_some_chs_value() {
        let chs: CHS = CHS::from_bytes(&[0xaa, 0xaa, 0xaa]);
        assert_eq!(
            chs,
            CHS {
                cylinder: 682,
                head: 170,
                sector: 42,
            }
        );
        let slice = chs.to_bytes();
        assert_eq!(slice.len(), 3);
        for element in slice {
            assert_eq!(element, 0xaa);
        }
    }

    #[test]
    fn align_chs_to_cylinder() {
        fn lba2c(lba: u32) -> u16 {
            let chs = CHS::from_lba_aligned(lba, 100, 2, 2).unwrap();

            assert_eq!(chs.head, 0);
            assert_eq!(chs.sector, 1);

            chs.cylinder
        }

        assert_eq!(lba2c(12), 3);
        assert_eq!(lba2c(10), 3);
    }

    #[test]
    fn convert_chs_to_lba_and_back() {
        // NOTE: 2484/16/63 is taken from a real life example of hard disk of 1280MB
        // LBA address 666666 is around 341MB for a sector size of 512 bytes
        let chs = CHS::from_lba_exact(666_666, 2484, 16, 63).unwrap();
        assert_eq!(chs.to_lba(16, 63), 666_666);

        let chs = CHS::from_lba_aligned(666_666, 2484, 16, 63).unwrap();
        assert_eq!(chs.to_lba(16, 63), 667_296);

        let chs = CHS::from_lba_exact(667_296, 2484, 16, 63).unwrap();
        assert_eq!(chs.head, 0);
        assert_eq!(chs.sector, 1);
    }

    #[test]
    #[allow(clippy::bool_assert_comparison)]
    fn read_disk1() {
        let mut mbr = MBR::read_from(&mut File::open(DISK1).unwrap(), 512).unwrap();
        assert!(mbr.header.partition_1.is_used());
        assert!(mbr.header.partition_2.is_used());
        assert!(mbr.header.partition_3.is_unused());
        assert!(mbr.header.partition_4.is_unused());
        assert!(mbr.header.partition_1.is_active());
        assert!(!mbr.header.partition_2.is_active());
        assert!(!mbr.header.partition_3.is_active());
        assert!(!mbr.header.partition_4.is_active());
        assert_eq!(mbr.len(), 4);
        assert_eq!(mbr.header.iter().count(), 4);
        assert_eq!(mbr.header.iter_mut().count(), 4);
        assert_eq!(mbr.iter_mut().count(), 4);
        assert_eq!(mbr.header.partition_1.boot, BOOT_ACTIVE);
        assert_eq!(mbr.header.partition_1.sys, 0x06);
        assert_eq!(mbr.header.partition_1.starting_lba, 1);
        assert_eq!(mbr.header.partition_1.sectors, 1);
        assert_eq!(mbr.header.partition_2.boot, BOOT_INACTIVE);
        assert_eq!(mbr.header.partition_2.sys, 0x0b);
        assert_eq!(mbr.header.partition_2.starting_lba, 3);
        assert_eq!(mbr.header.partition_2.sectors, 1);
    }

    #[test]
    fn read_used_partition_at_lba_0() {
        let ss = 512_u32;
        let mut data = vec![0; 10 * ss as usize];
        // partition 1 is used (sys 0x83) and starts at LBA 0, over the MBR itself
        data[446 + 4] = 0x83;
        data[446 + 12..446 + 16].copy_from_slice(&5_u32.to_le_bytes());
        data[510..512].copy_from_slice(&BOOT_SIGNATURE);

        let mbr = MBR::read_from(&mut Cursor::new(data), ss).unwrap();
        assert_eq!(mbr.align, DEFAULT_ALIGN);
    }

    #[test]
    fn read_disk2() {
        let mut mbr = MBR::read_from(&mut File::open(DISK2).unwrap(), 512).unwrap();
        assert!(mbr.header.partition_1.is_used());
        assert!(mbr.header.partition_2.is_used());
        assert!(mbr.header.partition_3.is_unused());
        assert!(mbr.header.partition_4.is_unused());
        assert!(!mbr.header.partition_1.is_active());
        assert!(!mbr.header.partition_2.is_active());
        assert!(!mbr.header.partition_3.is_active());
        assert!(!mbr.header.partition_4.is_active());
        assert_eq!(mbr.header.partition_2.sys, 0x05);
        assert_eq!(mbr.header.partition_2.starting_lba, 5);
        assert_eq!(mbr.header.partition_2.first_chs, CHS::new(0, 1, 3));
        assert_eq!(mbr.header.partition_2.last_chs, CHS::new(3, 0, 2));
        assert_eq!(mbr.header.partition_2.sectors, 15);
        assert_eq!(mbr.len(), 9);
        assert_eq!(mbr.iter().count(), 9);
        assert_eq!(mbr.iter_mut().count(), 9);
        assert_eq!(mbr.iter().filter(|(_, x)| x.is_used()).count(), 7);
        assert!(mbr
            .iter()
            .filter(|(_, x)| x.is_used() && !x.is_extended())
            .all(|(_, x)| x.sys == 0x83));
        assert!(mbr.get(9).is_some());
        assert!(mbr.get(10).is_none());
        assert_eq!(mbr.logical_partitions[0].absolute_ebr_lba, 5);
        assert_eq!(mbr.logical_partitions[0].ebr_sectors, None);
        assert_eq!(mbr.logical_partitions[1].absolute_ebr_lba, 7);
        assert_eq!(mbr.logical_partitions[1].ebr_sectors, Some(3));
        assert_eq!(mbr.logical_partitions[2].absolute_ebr_lba, 10);
        assert_eq!(mbr.logical_partitions[2].ebr_sectors, Some(4));
        // NOTE: this is actually for testing the CHS conversion to and from LBA
        assert_eq!(
            mbr.logical_partitions[2].partition.first_chs,
            CHS::new(1, 1, 3)
        );
        assert_eq!(
            mbr.logical_partitions[2].partition.first_chs.to_lba(2, 3),
            mbr.logical_partitions[2].partition.starting_lba
        );
        assert_eq!(
            CHS::from_lba_exact(
                mbr.logical_partitions[2].partition.starting_lba,
                u16::MAX,
                2,
                3
            )
            .unwrap(),
            mbr.logical_partitions[2].partition.first_chs
        );
        assert_eq!(mbr.logical_partitions[3].absolute_ebr_lba, 14);
        assert_eq!(mbr.logical_partitions[3].ebr_sectors, Some(2));
        assert_eq!(mbr.logical_partitions[4].absolute_ebr_lba, 16);
        assert_eq!(mbr.logical_partitions[4].ebr_sectors, Some(2));
        assert!(mbr.logical_partitions.get(5).is_none());
    }

    #[test]
    fn read_empty_extended_partition() {
        let ss = 512_u32;
        let data = vec![0; 10 * ss as usize];
        let mut cur = Cursor::new(data);
        let mut mbr = MBR::new_from(&mut cur, ss, [0xff; 4]).unwrap();
        mbr.header.partition_1.sys = 0x0f;
        mbr.header.partition_1.starting_lba = 1;
        mbr.header.partition_1.sectors = 10;

        mbr.write_into(&mut cur).unwrap();

        let mbr = MBR::read_from(&mut cur, ss).unwrap();
        assert_eq!(mbr.header.partition_1.sys, 0x0f);
        assert_eq!(mbr.header.partition_1.starting_lba, 1);
        assert_eq!(mbr.header.partition_1.sectors, 10);
        assert!(mbr.logical_partitions.is_empty());
    }

    #[test]
    fn read_extended_partition_with_unreadable_first_ebr() {
        let ss = 512_u32;
        let data = vec![0; 10 * ss as usize];
        let mut cur = Cursor::new(data);
        let mut mbr = MBR::new_from(&mut cur, ss, [0xff; 4]).unwrap();
        // the first EBR would be past the end of the disk
        mbr.header.partition_1.sys = 0x0f;
        mbr.header.partition_1.starting_lba = 20;
        mbr.header.partition_1.sectors = 10;
        mbr.write_into(&mut cur).unwrap();

        assert!(matches!(
            MBR::read_from(&mut cur, ss),
            Err(Error::Io(err)) if err.kind() == std::io::ErrorKind::UnexpectedEof
        ));
    }

    #[test]
    fn read_extended_partition_with_invalid_first_ebr_entry() {
        let ss = 512_u32;
        let data = vec![0; 10 * ss as usize];
        let mut cur = Cursor::new(data);
        let mut mbr = MBR::new_from(&mut cur, ss, [0xff; 4]).unwrap();
        mbr.header.partition_1.sys = 0x0f;
        mbr.header.partition_1.starting_lba = 1;
        mbr.header.partition_1.sectors = 9;
        mbr.write_into(&mut cur).unwrap();

        // valid signature, but the first entry has a boot flag that is neither 0x00 nor 0x80
        let ebr = cur.get_mut();
        ebr[ss as usize + 446] = 0x01;
        ebr[ss as usize + 510..ss as usize + 512].copy_from_slice(&BOOT_SIGNATURE);

        assert!(matches!(
            MBR::read_from(&mut cur, ss),
            Err(Error::InvalidBootFlag)
        ));
    }

    #[test]
    #[allow(clippy::bool_assert_comparison)]
    fn new_mbr_then_write_then_read_twice() {
        let ss = 512_u32;
        let data = vec![0; 12 * ss as usize];
        let mut cur = Cursor::new(data);
        let mut mbr = MBR::new_from(&mut cur, ss, [0xff; 4]).unwrap();
        mbr.header.partition_1.sys = 0x83;
        mbr.header.partition_1.starting_lba = 1;
        mbr.header.partition_1.sectors = 4;
        mbr.header.partition_3.sys = 0x0f;
        mbr.header.partition_3.starting_lba = 5;
        mbr.header.partition_3.sectors = 6;
        let mut empty = MBRPartitionEntry::empty();
        empty.starting_lba = 6;
        empty.sectors = 1;
        mbr.logical_partitions.push(LogicalPartition {
            partition: empty,
            absolute_ebr_lba: 5,
            ebr_sectors: None,
            ebr_first_chs: CHS::empty(),
            ebr_last_chs: None,
            bootstrap_code: [0; 446],
        });
        mbr.logical_partitions.push(LogicalPartition {
            partition: MBRPartitionEntry {
                boot: BOOT_ACTIVE,
                first_chs: CHS::empty(),
                sys: 0x83,
                last_chs: CHS::empty(),
                starting_lba: 9,
                sectors: 1,
            },
            absolute_ebr_lba: 7,
            ebr_sectors: Some(3),
            ebr_first_chs: CHS::empty(),
            ebr_last_chs: Some(CHS::empty()),
            bootstrap_code: [0; 446],
        });

        // NOTE: don't put this in a loop otherwise it's hard to guess if the error come from
        //       reading, writing or reading after writing again
        mbr.write_into(&mut cur).unwrap();

        let mut mbr = MBR::read_from(&mut cur, ss).unwrap();
        assert_eq!(mbr.header.partition_1.boot, BOOT_INACTIVE);
        assert_eq!(mbr.header.partition_1.sys, 0x83);
        assert_eq!(mbr.header.partition_1.starting_lba, 1);
        assert_eq!(mbr.header.partition_1.sectors, 4);
        assert_eq!(mbr.logical_partitions.len(), 2);
        assert_eq!(mbr.logical_partitions[0].absolute_ebr_lba, 5);
        assert_eq!(mbr.logical_partitions[0].partition.boot, BOOT_INACTIVE);
        assert_eq!(mbr.logical_partitions[0].partition.starting_lba, 6);
        assert_eq!(mbr.logical_partitions[0].partition.sectors, 1);
        assert_eq!(mbr.logical_partitions[0].partition.sys, 0);
        assert_eq!(mbr.logical_partitions[0].ebr_sectors, None);
        assert_eq!(mbr.logical_partitions[1].absolute_ebr_lba, 7);
        assert_eq!(mbr.logical_partitions[1].partition.boot, BOOT_ACTIVE);
        assert_eq!(mbr.logical_partitions[1].partition.starting_lba, 9);
        assert_eq!(mbr.logical_partitions[1].partition.sectors, 1);
        assert_eq!(mbr.logical_partitions[1].partition.sys, 0x83);
        assert_eq!(mbr.logical_partitions[1].ebr_sectors, Some(3));

        mbr.write_into(&mut cur).unwrap();

        let mbr = MBR::read_from(&mut cur, ss).unwrap();
        assert_eq!(mbr.header.partition_1.boot, BOOT_INACTIVE);
        assert_eq!(mbr.header.partition_1.sys, 0x83);
        assert_eq!(mbr.header.partition_1.starting_lba, 1);
        assert_eq!(mbr.header.partition_1.sectors, 4);
        assert_eq!(mbr.logical_partitions.len(), 2);
        assert_eq!(mbr.logical_partitions[0].absolute_ebr_lba, 5);
        assert_eq!(mbr.logical_partitions[0].partition.boot, BOOT_INACTIVE);
        assert_eq!(mbr.logical_partitions[0].partition.starting_lba, 6);
        assert_eq!(mbr.logical_partitions[0].partition.sectors, 1);
        assert_eq!(mbr.logical_partitions[0].partition.sys, 0);
        assert_eq!(mbr.logical_partitions[0].ebr_sectors, None);
        assert_eq!(mbr.logical_partitions[1].absolute_ebr_lba, 7);
        assert_eq!(mbr.logical_partitions[1].partition.boot, BOOT_ACTIVE);
        assert_eq!(mbr.logical_partitions[1].partition.starting_lba, 9);
        assert_eq!(mbr.logical_partitions[1].partition.sectors, 1);
        assert_eq!(mbr.logical_partitions[1].partition.sys, 0x83);
        assert_eq!(mbr.logical_partitions[1].ebr_sectors, Some(3));
    }

    #[test]
    fn find_at_sector() {
        let mbr = MBR::read_from(&mut File::open(DISK2).unwrap(), 512).unwrap();
        assert_eq!(mbr.find_at_sector(2), Some(1));
        assert_eq!(mbr.find_at_sector(4), None);
        assert_eq!(mbr.find_at_sector(8), Some(6));
        assert_eq!(mbr.find_at_sector(7), None);
    }

    #[test]
    fn find_free_sectors() {
        let ss = 512_u32;
        let data = vec![0; 10 * ss as usize];
        let mut cur = Cursor::new(data);
        let mut mbr = MBR::new_from(&mut cur, ss, [0xff; 4]).unwrap();
        mbr.align = 1;
        mbr.header.partition_1.sys = 0x83;
        mbr.header.partition_1.starting_lba = 1;
        mbr.header.partition_1.sectors = 1;
        mbr.header.partition_3.sys = 0x0f;
        mbr.header.partition_3.starting_lba = 5;
        mbr.header.partition_3.sectors = 5;
        mbr.logical_partitions.push(LogicalPartition {
            bootstrap_code: [0; 446],
            partition: MBRPartitionEntry {
                boot: BOOT_INACTIVE,
                first_chs: CHS::empty(),
                sys: 0x83,
                last_chs: CHS::empty(),
                starting_lba: 2,
                sectors: 1,
            },
            absolute_ebr_lba: 5,
            ebr_sectors: None,
            ebr_first_chs: CHS::empty(),
            ebr_last_chs: None,
        });

        assert_eq!(mbr.find_free_sectors(), vec![(2, 3), (6, 1), (8, 2)]);
    }

    #[test]
    fn push_logical_partition_aligned_to_cylinder() {
        let ss = 512_u32;
        let data = vec![0; 54 * ss as usize];
        let mut cur = Cursor::new(data);
        let mut mbr = MBR::new_from(&mut cur, ss, [0xff; 4]).unwrap();
        mbr.cylinders = 6;
        mbr.heads = 3;
        mbr.sectors = 3;
        let align = 9;
        mbr.align = mbr.get_cylinder_size();
        assert_eq!(mbr.align, align);
        mbr.header.partition_1.sys = 0x05;
        mbr.header.partition_1.first_chs = CHS::new(1, 0, 1);
        mbr.header.partition_1.last_chs = CHS::new(5, 0, 1);
        mbr.header.partition_1.starting_lba = align;
        mbr.header.partition_1.sectors = mbr.disk_size;
        let p = mbr.push(0x00, 2, 2 * align).unwrap();

        assert_eq!(p.absolute_ebr_lba, align);
        assert_eq!(p.partition.starting_lba, 2 * align);
        assert_eq!(p.ebr_sectors, None);
        assert_eq!(p.partition.sectors, align);
        assert_eq!(p.ebr_first_chs, CHS::new(1, 0, 1));
        assert_eq!(p.ebr_last_chs, None);
        assert_eq!(p.partition.first_chs, CHS::new(2, 0, 1));
        assert_eq!(p.partition.last_chs, CHS::new(2, 2, 3));

        let p = mbr
            .push(
                0x83,
                CHS::new(3, 0, 1).to_lba(mbr.heads, mbr.sectors),
                align * 3,
            )
            .unwrap();

        assert_eq!(p.absolute_ebr_lba, align * 3);
        assert_eq!(p.partition.starting_lba, 4 * align);
        assert_eq!(p.ebr_sectors, Some(align * 3));
        assert_eq!(p.partition.sectors, align * 2);
        assert_eq!(p.ebr_first_chs, CHS::new(3, 0, 1));
        assert_eq!(p.ebr_last_chs, Some(CHS::new(5, 2, 3)));
        assert_eq!(p.partition.first_chs, CHS::new(4, 0, 1));
        assert_eq!(p.partition.last_chs, CHS::new(5, 2, 3));

        mbr.write_into(&mut cur).unwrap();
        let mut same_mbr = MBR::read_from(&mut cur, ss).unwrap();
        same_mbr.cylinders = mbr.cylinders;
        same_mbr.heads = mbr.heads;
        same_mbr.sectors = mbr.sectors;

        assert_eq!(mbr, same_mbr);
    }

    #[test]
    fn push_logical_partition_check_within_range() {
        let ss = 512_u32;
        let data = vec![0; 10 * ss as usize];
        let mut cur = Cursor::new(data);
        let mut mbr = MBR::new_from(&mut cur, ss, [0xff; 4]).unwrap();
        mbr.align = 1;
        mbr.header.partition_1.sys = 0x0f;
        mbr.header.partition_1.starting_lba = 4;
        mbr.header.partition_1.sectors = 2;
        assert!(mbr.push(0x83, 3, 2).is_err());
        assert!(mbr.push(0x83, 6, 2).is_err());
        mbr.push(0x83, 4, 2).unwrap();
        assert!(mbr.push(0x83, 4, 3).is_err());
    }

    #[test]
    fn remove_logical_partition() {
        let ss = 512_u32;
        let data = vec![0; 10 * ss as usize];
        let mut cur = Cursor::new(data);
        let mut mbr = MBR::new_from(&mut cur, ss, [0xff; 4]).unwrap();
        mbr.align = 1;
        mbr.header.partition_1.sys = 0x0f;
        mbr.header.partition_1.starting_lba = 1;
        mbr.header.partition_1.sectors = mbr.disk_size - 1;
        mbr.push(0x00, 1, 2).unwrap();
        mbr.push(0x83, 4, 3).unwrap();

        mbr.logical_partitions.remove(0);
        mbr.write_into(&mut cur).unwrap();

        let same_mbr = MBR::read_from(&mut cur, ss).unwrap();

        assert_eq!(mbr, same_mbr);
        assert_eq!(mbr.logical_partitions[0].partition.starting_lba, 5);
        assert_eq!(mbr.logical_partitions[0].absolute_ebr_lba, 1);
        assert_eq!(mbr.logical_partitions[0].ebr_sectors, None);
    }

    fn read_corrupt_mbr(path: &str, bad_offset: usize, bad_data: u8) -> Error {
        let mut data = Vec::new();
        File::open(path).unwrap().read_to_end(&mut data).unwrap();
        data[bad_offset] = bad_data;
        let mut cur = Cursor::new(&data);
        MBR::read_from(&mut cur, 512).unwrap_err()
    }

    #[test]
    fn read_truncated_ebr_chain() {
        let mut data = Vec::new();
        File::open(DISK2).unwrap().read_to_end(&mut data).unwrap();
        // the second EBR, at LBA 7, is cut off
        data.truncate(7 * 512);
        let mut cur = Cursor::new(data);
        assert!(matches!(
            MBR::read_from(&mut cur, 512),
            Err(Error::Io(err)) if err.kind() == std::io::ErrorKind::UnexpectedEof
        ));
    }

    #[test]
    fn read_invalid_boot_signature() {
        // MBR
        assert!(matches!(
            read_corrupt_mbr(DISK2, 0xffe, 0xaa),
            Error::InvalidSignature
        ));
        // EBR
        assert!(matches!(
            read_corrupt_mbr(DISK2, 0x21fe, 0xaa),
            Error::InvalidSignature
        ));
    }

    #[test]
    fn write_invalid_boot_signature() {
        let ss = 512_u32;
        let data = vec![0; 10 * ss as usize];
        let mut cur = Cursor::new(data);

        // invalid in MBRHeader struct
        let mut mbr = MBR::new_from(&mut cur, ss, [0xff; 4]).unwrap();
        mbr.header.partition_1.sys = 0x0a;
        mbr.header.partition_1.starting_lba = 1;
        mbr.header.partition_1.sectors = 10;
        mbr.header.boot_signature = [0, 0];
        assert!(matches!(
            mbr.write_into(&mut cur).unwrap_err(),
            Error::InvalidSignature
        ));
    }

    #[test]
    fn read_invalid_boot_flag() {
        // primary partition
        assert!(matches!(
            read_corrupt_mbr(DISK2, 0x1be, BOOT_ACTIVE | 0x01),
            Error::InvalidBootFlag
        ));
        // EBR first partition
        assert!(matches!(
            read_corrupt_mbr(DISK2, 0xfbe, BOOT_ACTIVE | 0x01),
            Error::InvalidBootFlag
        ));
        // EBR second partition
        assert!(matches!(
            read_corrupt_mbr(DISK2, 0xfce, BOOT_ACTIVE | 0x01),
            Error::InvalidBootFlag
        ));
    }

    #[test]
    fn write_invalid_boot_flag() {
        let ss = 512_u32;
        let data = vec![0; 10 * ss as usize];
        let mut cur = Cursor::new(data);

        // primary partition
        let mut mbr = MBR::new_from(&mut cur, ss, [0xff; 4]).unwrap();
        mbr.header.partition_2.boot = BOOT_ACTIVE | 0x01;
        mbr.header.partition_2.sys = 0x0a;
        mbr.header.partition_2.starting_lba = 1;
        mbr.header.partition_2.sectors = 10;
        assert!(matches!(
            mbr.write_into(&mut cur).unwrap_err(),
            Error::InvalidBootFlag
        ));

        // logical partition
        let mut mbr = MBR::new_from(&mut cur, ss, [0xff; 4]).unwrap();
        mbr.align = 1;
        mbr.header.partition_1.sys = 0x0f;
        mbr.header.partition_1.starting_lba = 1;
        mbr.header.partition_1.sectors = 10;
        let partition = mbr.push(0x0f, 1, 9).unwrap();
        partition.partition.boot = BOOT_ACTIVE | 0x01;
        assert!(matches!(
            mbr.write_into(&mut cur).unwrap_err(),
            Error::InvalidBootFlag
        ));
        // the table is validated before anything is written: not even the MBR is
        assert!(cur.get_ref().iter().all(|&b| b == 0));
    }

    #[test]
    fn chunks_match_write_into() {
        let ss = 512_u32;
        let mut cur = Cursor::new(vec![0; 64 * ss as usize]);
        let mut mbr = MBR::new_from(&mut cur, ss, [0x12, 0x34, 0x56, 0x78]).unwrap();
        mbr.align = 1;
        mbr.cylinders = 4;
        mbr.heads = 2;
        mbr.sectors = 8;
        mbr.header.partition_1 = MBRPartitionEntry {
            boot: BOOT_INACTIVE,
            first_chs: CHS::empty(),
            sys: 0x0f,
            last_chs: CHS::empty(),
            starting_lba: 4,
            sectors: 60,
        };
        for (n, sys) in [(4, 0x83), (10, 0x07), (16, 0x0c)] {
            mbr.push(sys, n, 6).unwrap();
        }

        let mut chunked = mbr.clone();
        let mut disk = vec![0; 64 * ss as usize];
        for chunk in chunked.chunks().unwrap() {
            let start = usize::try_from(chunk.offset).unwrap();
            disk[start..start + 512].copy_from_slice(&chunk.data);
        }
        mbr.write_into(&mut cur).unwrap();
        assert_eq!(cur.into_inner(), disk);
        // both update the CHS addresses the same way
        assert_eq!(chunked, mbr);
    }

    #[test]
    fn update_from() {
        let ss = 512_u32;
        let data = vec![0; 10 * ss as usize];
        let mut cur = Cursor::new(data);
        let mut mbr = MBR::new_from(&mut cur, ss, [0xff; 4]).unwrap();
        assert_eq!(mbr.disk_size, 10);
        let mut data = cur.into_inner();
        data.resize(20 * ss as usize, 0);
        let mut cur = Cursor::new(data);
        mbr.update_from(&mut cur).unwrap();
        assert_eq!(mbr.disk_size, 20);
    }

    /// Build a 512-byte MBR sector with every byte of partition 1's first
    /// CHS address controlled by the caller and arbitrary data elsewhere.
    fn mbr_sector_with_chs(chs: [u8; 3]) -> Vec<u8> {
        let mut sector: Vec<u8> = (0..512).map(|i| (i * 7 + 3) as u8).collect();
        for entry in 0..4 {
            let off = 446 + entry * 16;
            sector[off] = if entry == 0 {
                BOOT_ACTIVE
            } else {
                BOOT_INACTIVE
            };
        }
        sector[447..450].copy_from_slice(&chs);
        sector[510] = 0x55;
        sector[511] = 0xaa;
        sector
    }

    #[test]
    fn header_round_trip_is_byte_identical_for_all_chs_encodings() {
        for b1 in 0..=255_u8 {
            for b2 in 0..=255_u8 {
                let b0 = b1 ^ b2.rotate_left(3);
                let sector = mbr_sector_with_chs([b0, b1, b2]);

                let header = MBRHeader::read_from(&mut Cursor::new(sector.clone())).unwrap();
                assert_eq!(
                    header.partition_1.first_chs,
                    CHS {
                        cylinder: (u16::from(b1 >> 6) << 8) | u16::from(b2),
                        head: b0,
                        sector: b1 & 0x3f,
                    }
                );

                let mut out = Cursor::new(vec![0; 512]);
                header.write_into(&mut out).unwrap();
                assert_eq!(
                    out.into_inner(),
                    sector,
                    "chs bytes {b0:#04x} {b1:#04x} {b2:#04x}"
                );
            }
        }
    }

    #[test]
    fn read_then_write_fixtures_is_byte_identical() {
        for path in [DISK1, DISK2] {
            let original = std::fs::read(path).unwrap();
            let ss = 512;

            let mut mbr = MBR::read_from(&mut Cursor::new(original.clone()), ss).unwrap();
            let mut out = Cursor::new(vec![0; original.len()]);
            mbr.write_into(&mut out).unwrap();
            let out = out.into_inner();

            let mut boot_records = vec![0_usize];
            boot_records.extend(
                mbr.logical_partitions
                    .iter()
                    .map(|l| l.absolute_ebr_lba as usize),
            );
            for (lba, (written, expected)) in out
                .chunks(ss as usize)
                .zip(original.chunks(ss as usize))
                .enumerate()
            {
                if boot_records.contains(&lba) {
                    assert_eq!(written, expected, "{path}: sector {lba} differs");
                } else {
                    assert!(
                        written.iter().all(|&b| b == 0),
                        "{path}: unexpected write in sector {lba}"
                    );
                }
            }
        }
    }

    #[test]
    fn header_bytes_round_trip() {
        for path in [DISK1, DISK2] {
            let original = std::fs::read(path).unwrap();
            let bytes: [u8; 512] = original[..512].try_into().unwrap();
            let header = MBRHeader::from_bytes(&bytes).unwrap();
            assert_eq!(header.to_bytes().unwrap(), bytes, "{path}");
            assert_eq!(
                MBRHeader::from_bytes(&header.to_bytes().unwrap()).unwrap(),
                header
            );
        }
    }

    #[test]
    fn header_from_bytes_rejects_invalid_signature() {
        let mut bytes = MBRHeader::new([0xff; 4]).to_bytes().unwrap();
        bytes[510] = 0xaa;
        assert!(matches!(
            MBRHeader::from_bytes(&bytes),
            Err(Error::InvalidSignature)
        ));
    }

    #[test]
    fn read_ebr_entry_with_overflowing_lba() {
        let ss = 512_u32;
        let data = vec![0; 10 * ss as usize];
        let mut cur = Cursor::new(data);
        let mut mbr = MBR::new_from(&mut cur, ss, [0xff; 4]).unwrap();
        mbr.header.partition_1.sys = 0x0f;
        mbr.header.partition_1.starting_lba = 1;
        mbr.header.partition_1.sectors = 9;
        mbr.write_into(&mut cur).unwrap();

        // valid EBR whose first entry starts at u32::MAX sectors after the EBR
        let ebr = cur.get_mut();
        let entry = ss as usize + 446;
        ebr[entry + 4] = 0x83;
        ebr[entry + 8..entry + 12].copy_from_slice(&u32::MAX.to_le_bytes());
        ebr[entry + 12..entry + 16].copy_from_slice(&1_u32.to_le_bytes());
        ebr[ss as usize + 510..ss as usize + 512].copy_from_slice(&BOOT_SIGNATURE);

        assert!(matches!(
            MBR::read_from(&mut cur, ss),
            Err(Error::InconsistentEBR)
        ));
    }

    /// A disk of any size that only stores the sectors actually written. Sectors never
    /// written read as zeros. Each read or write stays within one sector; `read_exact` and
    /// `write_all` loop over the rest.
    struct SparseDisk {
        len: u64,
        pos: u64,
        sectors: std::collections::HashMap<u64, [u8; 512]>,
    }

    impl SparseDisk {
        fn new(len: u64) -> SparseDisk {
            SparseDisk {
                len,
                pos: 0,
                sectors: Default::default(),
            }
        }

        /// The sector at `self.pos`, the offset in it and how many bytes of it fit in `n`.
        fn span(&self, n: usize) -> (u64, usize, usize) {
            let offset = (self.pos % 512) as usize;
            let remaining =
                usize::try_from(self.len.saturating_sub(self.pos)).unwrap_or(usize::MAX);
            (self.pos / 512, offset, n.min(512 - offset).min(remaining))
        }
    }

    impl Read for SparseDisk {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            let (lba, offset, n) = self.span(buf.len());
            match self.sectors.get(&lba) {
                Some(sector) => buf[..n].copy_from_slice(&sector[offset..offset + n]),
                None => buf[..n].fill(0),
            }
            self.pos += n as u64;
            Ok(n)
        }
    }

    impl Write for SparseDisk {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            let (lba, offset, n) = self.span(buf.len());
            let sector = self.sectors.entry(lba).or_insert([0; 512]);
            sector[offset..offset + n].copy_from_slice(&buf[..n]);
            self.pos += n as u64;
            Ok(n)
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    impl Seek for SparseDisk {
        fn seek(&mut self, pos: SeekFrom) -> std::io::Result<u64> {
            let new = match pos {
                SeekFrom::Start(n) => Some(n),
                SeekFrom::End(n) => self.len.checked_add_signed(n),
                SeekFrom::Current(n) => self.pos.checked_add_signed(n),
            };
            self.pos = new.ok_or_else(|| std::io::Error::from(std::io::ErrorKind::InvalidInput))?;
            Ok(self.pos)
        }
    }

    #[test]
    fn read_ebr_chain_with_overflowing_ebr_lba() {
        let ss = 512_u32;
        let mut disk = SparseDisk::new(4_u64 << 40);
        let mut mbr = MBR::new_from(&mut disk, ss, [0xff; 4]).unwrap();
        // the extended partition ends at u32::MAX, so a link 20 sectors in overflows
        let start = u32::MAX - 9;
        mbr.header.partition_1 = MBRPartitionEntry {
            boot: BOOT_INACTIVE,
            first_chs: CHS::empty(),
            sys: 0x0f,
            last_chs: CHS::empty(),
            starting_lba: start,
            sectors: 10,
        };
        mbr.write_into(&mut disk).unwrap();

        // valid first EBR whose link to the next EBR points past u32::MAX
        let mut ebr = [0; 512];
        ebr[446 + 4] = 0x83;
        ebr[446 + 8..446 + 12].copy_from_slice(&1_u32.to_le_bytes());
        ebr[446 + 12..446 + 16].copy_from_slice(&1_u32.to_le_bytes());
        ebr[462 + 4] = 0x0f;
        ebr[462 + 8..462 + 12].copy_from_slice(&20_u32.to_le_bytes());
        ebr[462 + 12..462 + 16].copy_from_slice(&1_u32.to_le_bytes());
        ebr[510..512].copy_from_slice(&BOOT_SIGNATURE);
        disk.sectors.insert(u64::from(start), ebr);

        assert!(matches!(
            MBR::read_from(&mut disk, ss),
            Err(Error::InconsistentEBR)
        ));
    }

    #[test]
    fn logical_partitions_past_4_gib() {
        let ss = 512_u32;
        let mut disk = SparseDisk::new(16_u64 << 30);
        let mut mbr = MBR::new_from(&mut disk, ss, [0xff; 4]).unwrap();
        // the extended partition starts at 8 GiB, so every EBR offset exceeds u32::MAX
        let start = u32::try_from((8_u64 << 30) / u64::from(ss)).unwrap();
        mbr.header.partition_1 = MBRPartitionEntry {
            boot: BOOT_INACTIVE,
            first_chs: CHS::empty(),
            sys: 0x0f,
            last_chs: CHS::empty(),
            starting_lba: start,
            sectors: 1 << 20,
        };
        mbr.push(0x83, start + 2048, 4096).unwrap();
        mbr.push(0x83, start + 8192, 4096).unwrap();
        mbr.write_into(&mut disk).unwrap();

        for l in &mbr.logical_partitions {
            assert!(
                disk.sectors.contains_key(&u64::from(l.absolute_ebr_lba)),
                "no EBR written at LBA {}",
                l.absolute_ebr_lba
            );
        }
        let read = MBR::read_from(&mut disk, ss).unwrap();
        assert_eq!(read.logical_partitions.len(), 2);
        for (r, w) in read.logical_partitions.iter().zip(&mbr.logical_partitions) {
            assert_eq!(r.absolute_ebr_lba, w.absolute_ebr_lba);
            assert_eq!(r.partition, w.partition);
        }
    }

    #[test]
    fn write_new_mbr_with_logical_partitions_is_stable() {
        let ss = 512_u32;
        let mut cur = Cursor::new(vec![0; 64 * ss as usize]);
        let mut mbr = MBR::new_from(&mut cur, ss, [0x12, 0x34, 0x56, 0x78]).unwrap();
        mbr.align = 1;
        mbr.header.partition_1 = MBRPartitionEntry {
            boot: BOOT_ACTIVE,
            first_chs: CHS::empty(),
            sys: 0x0f,
            last_chs: CHS::empty(),
            starting_lba: 4,
            sectors: 60,
        };
        // each logical partition is 6 sectors: its EBR plus 5 data sectors
        for (n, sys) in [(4, 0x83), (10, 0x07), (16, 0x0c)] {
            mbr.push(sys, n, 6).unwrap();
        }
        mbr.write_into(&mut cur).unwrap();
        let first = cur.get_ref().clone();

        let mut mbr = MBR::read_from(&mut Cursor::new(first.clone()), ss).unwrap();
        assert_eq!(mbr.logical_partitions.len(), 3);
        let mut cur = Cursor::new(vec![0; 64 * ss as usize]);
        mbr.write_into(&mut cur).unwrap();
        assert_eq!(cur.into_inner(), first);
    }
}

#[cfg(all(doctest, feature = "std"))]
mod test_readme {
    // for Rust < 1.54
    // https://blog.guillaume-gomez.fr/articles/2021-08-03+Improvements+for+%23%5Bdoc%5D+attributes+in+Rust
    macro_rules! check_doc {
        ($x:expr) => {
            #[doc = $x]
            extern "C" {}
        };
    }
    check_doc!(include_str!("../README.md"));
}
