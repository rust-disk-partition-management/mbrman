//! A library that allows managing MBR partition tables.
//!
//! ## Features
//!
//!  *  Create primary partitions and logical volumes
//!  *  Delete primary partitions and logical volumes
//!  *  Automatically generate logical volume's EBR (or can be provided manually)
//!  *  If the disk geometry is set, the partition CHS addresses will be calculated
//!     automatically when writing to disk
//!
//! ## Examples
//!
//! ### Read all the partitions of a disk
//!
//! ```rust
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
//! ```
//!
//! ### Create and delete primary partitions
//!
//! ```rust
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
//! // NOTE: no modification is committed to the disk until we call mbr.write_into()
//! ```
//!
//! ### Create a new partition table from an empty disk
//!
//! ```rust
//! let ss = 512; // sector size
//! let data = vec![0; 100 * ss as usize];
//! let mut cur = std::io::Cursor::new(data);
//!
//! let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
//!     .expect("could not create partition table");
//!
//! // NOTE: commit the change to the in-memory buffer
//! mbr.write_into(&mut cur);
//! ```
//!
//! ### Add a new logical volume to the disk
//!
//! ```rust
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
//! // this helper function will do all the hard work for you
//! // here it creates a logical volume with Linux filesystem that occupies the entire disk
//! // NOTE: you will lose 1 sector because it is used by the EBR
//! mbr.push(0x83, 1, mbr.disk_size - 1);
//!
//! // NOTE: commit the change to the in-memory buffer
//! mbr.write_into(&mut cur);
//! ```
//!
//! ### Add a new logical volume manually to the disk
//!
//! This is useful only if you need to specify exactly where goes the EBR and the partition itself.
//!
//! ```rust
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
//! // NOTE: mbrman won't check the consistency of the partition you have created manually
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
//!         // NOTE: this is not know the first EBR
//!         ebr_last_chs: None,
//!     }
//! );
//!
//! // NOTE: commit the change to the in-memory buffer
//! mbr.write_into(&mut cur);
//! ```

#![deny(missing_docs)]

use bincode::{deserialize_from, serialize_into};
use bitvec::prelude::*;
use serde::de::{SeqAccess, Visitor};
use serde::ser::SerializeTuple;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde_big_array::BigArray;
use std::convert::TryFrom;
use std::io::{Read, Seek, SeekFrom, Write};
use std::iter::{once, repeat};
use std::ops::{Index, IndexMut};
use thiserror::Error;

const DEFAULT_ALIGN: u32 = 2048;
const MAX_ALIGN: u32 = 16384;
const FIRST_USABLE_LBA: u32 = 1;
const BOOT_SIGNATURE: [u8; 2] = [0x55, 0xaa];

/// Boot flag for a bootable partition
pub const BOOT_ACTIVE: u8 = 0x80;
/// Boot flag for a non-bootable partition
pub const BOOT_INACTIVE: u8 = 0x00;

/// The result of reading, writing or managing a MBR.
pub type Result<T> = std::result::Result<T, Error>;

/// An error
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum Error {
    /// The CHS address requested cannot be represented in CHS
    ///
    /// # Remark
    ///
    /// There is a hard limit around 8GB for CHS addressing.
    #[error("exceeded the maximum limit of CHS")]
    LBAExceedsMaximumCHS,
    /// The CHS address requested exceeds the number of cylinders in the disk
    #[error("exceeded the maximum number of cylinders on disk")]
    LBAExceedsMaximumCylinders,
    /// Deserialization errors.
    #[error("deserialization failed")]
    Deserialize(#[from] bincode::Error),
    /// I/O errors.
    #[error("generic I/O error")]
    Io(#[from] std::io::Error),
    /// Inconsistent extended boot record
    #[error("inconsistent extended boot record")]
    InconsistentEBR,
    /// No extended partition
    #[error("no extended partition")]
    NoExtendedPartition,
    /// The EBR starts before the extended partition
    #[error("EBR starts before the extended partition")]
    EBRStartsBeforeExtendedPartition,
    /// The EBR starts too close to the extended partition
    #[error("EBR starts too close to the end of the extended partition")]
    EBRStartsTooCloseToTheEndOfExtendedPartition,
    /// The EBR ends after the extended partition
    #[error("EBR ends after the extended partition")]
    EBREndsAfterExtendedPartition,
    /// Not enough sectors to create a logical partition
    #[error("not enough sectors to create a logical partition")]
    NotEnoughSectorsToCreateLogicalPartition,
    /// An operation that required to find a partition, was unable to find that partition.
    #[error("partition not found")]
    PartitionNotFound,
    /// An error that occurs when there is not enough space left on the table to continue.
    #[error("no space left")]
    NoSpaceLeft,
    /// MBR doesn't have the expected signature value
    #[error("invalid MBR signature")]
    InvalidSignature,
    /// Partition has invalid boot flag
    #[error("partition has invalid boot flag")]
    InvalidBootFlag,
}

/// A type representing a MBR partition table including its partition, the sector size of the disk
/// and the alignment of the partitions to the sectors.
///
/// # Examples:
/// Read an existing MBR on a reader and list its partitions:
/// ```
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
/// ```
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
        let mut partitions: Vec<_> = vec![
            &mut self.header.partition_1,
            &mut self.header.partition_2,
            &mut self.header.partition_3,
            &mut self.header.partition_4,
        ];
        partitions.extend(self.logical_partitions.iter_mut().map(|x| &mut x.partition));
        partitions.into_iter().enumerate().map(|(i, x)| (i + 1, x))
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

    /// Make a new MBR
    ///
    /// # Examples
    /// Basic usage:
    /// ```
    /// let mut f = std::fs::File::open("tests/fixtures/disk1.img")
    ///     .expect("could not open disk");
    /// let mbr = mbrman::MBR::new_from(&mut f, 512, [0x01, 0x02, 0x03, 0x04])
    ///     .expect("could not make a partition table");
    /// ```
    pub fn new_from<S>(seeker: &mut S, sector_size: u32, disk_signature: [u8; 4]) -> Result<MBR>
    where
        S: Seek,
    {
        let disk_size = u32::try_from(seeker.seek(SeekFrom::End(0))? / u64::from(sector_size))
            .unwrap_or(u32::max_value());
        let header = MBRHeader::new(disk_signature);

        Ok(MBR {
            sector_size,
            header,
            logical_partitions: Vec::new(),
            align: DEFAULT_ALIGN,
            cylinders: 0,
            heads: 0,
            sectors: 0,
            disk_size,
        })
    }

    /// Read the MBR on a reader.
    ///
    /// # Examples
    /// Basic usage:
    /// ```
    /// let mut f = std::fs::File::open("tests/fixtures/disk1.img")
    ///     .expect("could not open disk");
    /// let mbr = mbrman::MBR::read_from(&mut f, 512)
    ///     .expect("could not read the partition table");
    /// ```
    pub fn read_from<R: ?Sized>(mut reader: &mut R, sector_size: u32) -> Result<MBR>
    where
        R: Read + Seek,
    {
        let disk_size = u32::try_from(reader.seek(SeekFrom::End(0))? / u64::from(sector_size))
            .unwrap_or(u32::max_value());
        let header = MBRHeader::read_from(&mut reader)?;

        let mut logical_partitions = Vec::new();
        if let Some(extended) = header.get_extended_partition() {
            // NOTE: The number of sectors is an index field; thus, the zero
            //       value is invalid, reserved and must not be used in normal
            //       partition entries. The entry is used by operating systems
            //       in certain circumstances; in such cases the CHS addresses
            //       are ignored.
            let mut relative_ebr_lba = 0;
            let mut ebr_sectors = None;
            let mut ebr_first_chs = extended.first_chs;
            let mut ebr_last_chs = None;
            loop {
                reader.seek(SeekFrom::Start(u64::from(
                    (extended.starting_lba + relative_ebr_lba) * sector_size,
                )))?;
                let (partition, next, bootstrap_code) = match EBRHeader::read_from(&mut reader) {
                    Ok(ebr) => ebr.unwrap(),
                    Err(err) => {
                        if relative_ebr_lba == 0 {
                            // NOTE: if the extended partition is empty, it is not required that an
                            //       EBR exists
                            break;
                        } else {
                            return Err(err);
                        }
                    }
                };
                let absolute_ebr_lba = extended.starting_lba + relative_ebr_lba;
                logical_partitions.push(LogicalPartition {
                    partition: MBRPartitionEntry {
                        starting_lba: partition.starting_lba + absolute_ebr_lba,
                        ..partition
                    },
                    absolute_ebr_lba,
                    ebr_sectors,
                    ebr_first_chs,
                    ebr_last_chs,
                    bootstrap_code,
                });

                if next.starting_lba > 0 && relative_ebr_lba >= next.starting_lba {
                    return Err(Error::InconsistentEBR);
                }

                relative_ebr_lba = next.starting_lba;
                ebr_sectors = Some(next.sectors);
                ebr_first_chs = next.first_chs;
                ebr_last_chs = Some(next.last_chs);

                if relative_ebr_lba == 0 {
                    break;
                }
            }
        }

        let align = MBR::find_alignment(&header, &logical_partitions);

        Ok(MBR {
            sector_size,
            header,
            logical_partitions,
            align,
            cylinders: 0,
            heads: 0,
            sectors: 0,
            disk_size,
        })
    }

    fn find_alignment(header: &MBRHeader, logical_partitions: &[LogicalPartition]) -> u32 {
        let lbas = header
            .iter()
            .map(|(_, x)| x)
            .chain(logical_partitions.iter().map(|x| &x.partition))
            .filter(|x| x.is_used())
            .map(|x| x.starting_lba)
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

    /// Write the MBR to a writer. This function will seek automatically in the writer.
    /// This function will update the CHS address of the partitions automatically if a valid
    /// geometry has been set. See `check_geometry`.
    ///
    /// # Examples
    /// Basic usage:
    /// ```
    /// let ss = 512;
    /// let data = vec![0; 100 * ss as usize];
    /// let mut cur = std::io::Cursor::new(data);
    /// let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
    ///     .expect("could not make a partition table");
    ///
    /// // actually write:
    /// mbr.write_into(&mut cur)
    ///     .expect("could not write MBR to disk")
    /// ```
    pub fn write_into<W: ?Sized>(&mut self, mut writer: &mut W) -> Result<()>
    where
        W: Write + Seek,
    {
        self.header.write_into(&mut writer)?;

        if let Some(extended) = self.header.get_extended_partition() {
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

            // newtype for bootstrap code so we can serialize it via BigArray
            // pending https://github.com/serde-rs/serde/issues/1937
            #[derive(Serialize)]
            struct BootstrapCode446(#[serde(with = "BigArray")] [u8; 446]);

            let next_logical_partitions = self
                .logical_partitions
                .iter()
                .skip(1)
                .map(Some)
                .chain(once(None));
            for (l, next) in self.logical_partitions.iter().zip(next_logical_partitions) {
                let partition = MBRPartitionEntry {
                    starting_lba: l.partition.starting_lba.saturating_sub(l.absolute_ebr_lba),
                    ..l.partition
                };
                partition.check()?;
                writer.seek(SeekFrom::Start(u64::from(
                    l.absolute_ebr_lba * self.sector_size,
                )))?;
                serialize_into(&mut writer, &BootstrapCode446(l.bootstrap_code))?;
                serialize_into(&mut writer, &partition)?;
                if let Some(next) = next {
                    serialize_into(
                        &mut writer,
                        &MBRPartitionEntry {
                            boot: BOOT_INACTIVE,
                            first_chs: next.ebr_first_chs,
                            sys: extended.sys,
                            last_chs: next.ebr_last_chs.unwrap(),
                            starting_lba: next
                                .absolute_ebr_lba
                                .saturating_sub(extended.starting_lba),
                            sectors: next.ebr_sectors.unwrap(),
                        },
                    )?;
                } else {
                    serialize_into(&mut writer, &MBRPartitionEntry::empty())?;
                }
                writer.write_all(&[0; 16 * 2])?;
                serialize_into(&mut writer, &BOOT_SIGNATURE)?;
            }
        }

        Ok(())
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
    /// ```
    pub fn find_optimal_place(&self, size: u32) -> Option<u32> {
        let mut slots = self
            .find_free_sectors()
            .into_iter()
            .filter(|(_, l)| *l >= size)
            .collect::<Vec<_>>();
        slots.sort_by(|(_, l1), (_, l2)| l1.cmp(l2));
        slots.first().map(|&(i, _)| i)
    }

    /// Get the maximum size (in sectors) of a partition you could create in the MBR.
    /// This function will automatically align with the alignment defined in the `MBR`.
    ///
    /// # Examples:
    /// Basic usage:
    /// ```
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
    /// ```
    pub fn get_maximum_partition_size(&self) -> Result<u32> {
        self.find_free_sectors()
            .into_iter()
            .map(|(_, l)| l / self.align * self.align)
            .max()
            .ok_or(Error::NoSpaceLeft)
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

impl Index<usize> for MBR {
    type Output = MBRPartitionEntry;

    fn index(&self, i: usize) -> &Self::Output {
        assert!(i != 0, "invalid partition index: 0");
        self.get(i).expect("invalid partition")
    }
}

impl IndexMut<usize> for MBR {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        assert!(i != 0, "invalid partition index: 0");
        self.get_mut(i).expect("invalid partition")
    }
}

/// An MBR partition table header
#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct MBRHeader {
    /// Bootstrap code area
    #[serde(with = "BigArray")]
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
        vec![
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
        vec![
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

    /// Attempt to read a MBR header from a reader.  This operation will seek at the
    /// correct location before trying to write to disk.
    pub fn read_from<R: ?Sized>(mut reader: &mut R) -> Result<MBRHeader>
    where
        R: Read + Seek,
    {
        reader.seek(SeekFrom::Start(0))?;
        let header: Self = deserialize_from(&mut reader)?;
        header.check()?;
        Ok(header)
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

    /// Write the MBR header into a writer. This operation will seek at the
    /// correct location before trying to write to disk.
    pub fn write_into<W: ?Sized>(&self, mut writer: &mut W) -> Result<()>
    where
        W: Write + Seek,
    {
        self.check()?;
        writer.seek(SeekFrom::Start(0))?;
        serialize_into(&mut writer, &self)?;

        Ok(())
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
        assert!(i != 0, "invalid partition index: 0");
        self.get(i).expect("invalid partition")
    }
}

impl IndexMut<usize> for MBRHeader {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        assert!(i != 0, "invalid partition index: 0");
        self.get_mut(i).expect("invalid partition")
    }
}

#[derive(Debug, Clone, Deserialize)]
struct EBRHeader {
    #[serde(with = "BigArray")]
    bootstrap_code: [u8; 446],
    partition_1: MBRPartitionEntry,
    partition_2: MBRPartitionEntry,
    _unused_partition_3: [u8; 16],
    _unused_partition_4: [u8; 16],
    boot_signature: [u8; 2],
}

impl EBRHeader {
    fn read_from<R: ?Sized>(mut reader: &mut R) -> Result<EBRHeader>
    where
        R: Read,
    {
        let header: Self = deserialize_from(&mut reader)?;
        header.check()?;
        Ok(header)
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
#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
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
    /// Creates an empty partition entry
    ///
    /// # Examples
    /// Basic usage:
    /// ```
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

struct CHSVisitor;

impl<'de> Visitor<'de> for CHSVisitor {
    type Value = CHS;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("CHS addressing")
    }

    fn visit_seq<A>(self, mut seq: A) -> std::result::Result<CHS, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let head = BitVec::<u8, Msb0>::from_vec(vec![seq.next_element::<u8>()?.unwrap()]);
        let mut bv = BitVec::<u8, Msb0>::from_vec(vec![seq.next_element::<u8>()?.unwrap()]);
        let mut cylinder = BitVec::<u16, Msb0>::with_capacity(10);
        cylinder.extend(repeat(false).take(6));
        cylinder.extend(bv.drain(..2));
        cylinder.extend(BitVec::<u8, Msb0>::from_vec(vec![seq
            .next_element::<u8>()?
            .unwrap()]));
        let mut sector = BitVec::<u8, Msb0>::with_capacity(8);
        sector.push(false);
        sector.push(false);
        sector.extend(bv.drain(..));

        Ok(CHS {
            cylinder: cylinder.as_raw_slice()[0],
            head: head.as_raw_slice()[0],
            sector: sector.as_raw_slice()[0],
        })
    }
}

impl<'de> Deserialize<'de> for CHS {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_tuple(3, CHSVisitor)
    }
}

impl Serialize for CHS {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut bv = BitVec::<u8, Msb0>::from_vec(vec![self.head]);
        let mut sector = BitVec::<u8, Msb0>::from_vec(vec![self.sector]);
        let mut cylinder = BitVec::<u16, Msb0>::from_vec(vec![self.cylinder]);
        bv.extend(cylinder.drain(..8).skip(6));
        bv.extend(sector.drain(2..));
        bv.extend(cylinder.drain(..));

        let mut seq = serializer.serialize_tuple(3)?;
        for x in bv.as_raw_slice() {
            seq.serialize_element(&x)?;
        }
        seq.end()
    }
}

#[cfg(test)]
#[allow(clippy::cognitive_complexity)]
mod tests {
    use super::*;
    use std::fs::File;
    use std::io::Cursor;

    const DISK1: &str = "tests/fixtures/disk1.img";
    const DISK2: &str = "tests/fixtures/disk2.img";

    #[test]
    fn deserialize_maximum_chs_value() {
        let chs: CHS = bincode::deserialize(&[0xff, 0xff, 0xff]).unwrap();
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
        let out = bincode::serialize(&chs).unwrap();
        assert_eq!(out, &[0xff, 0xff, 0xff]);
    }

    #[test]
    fn serialize_and_deserialize_some_chs_value() {
        let chs: CHS = bincode::deserialize(&[0xaa, 0xaa, 0xaa]).unwrap();
        assert_eq!(
            chs,
            CHS {
                cylinder: 682,
                head: 170,
                sector: 42,
            }
        );
        let out = bincode::serialize(&chs).unwrap();
        assert_eq!(out, &[0xaa, 0xaa, 0xaa]);
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
                u16::max_value(),
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
        mbr.push(0x0f, 1, 9).unwrap().partition.boot = BOOT_ACTIVE | 0x01;
        assert!(matches!(
            mbr.write_into(&mut cur).unwrap_err(),
            Error::InvalidBootFlag
        ));
    }
}

#[cfg(doctest)]
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
