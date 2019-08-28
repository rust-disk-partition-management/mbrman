#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate derive_error;

use bincode::{deserialize_from, serialize_into};
use bitvec::prelude::*;
use serde::de;
use serde::de::{Deserialize, Deserializer, SeqAccess, Visitor};
use serde::ser::{Serialize, SerializeTuple, Serializer};
use std::convert::TryFrom;
use std::io::{Read, Seek, SeekFrom, Write};
use std::iter::repeat;
use std::ops::{Index, IndexMut};

const DEFAULT_ALIGN: u32 = 2048;
const MAX_ALIGN: u32 = 16384;
const FIRST_USABLE_LBA: u32 = 1;
const BOOTSTRAP_CODE_SIZE: u64 = 440;
const EBR_BOOTSTRAP_CODE_SIZE: u32 = 446;

/// The result of reading, writing or managing a MBR.
pub type Result<T> = std::result::Result<T, Error>;

/// An error
#[derive(Debug, Error)]
pub enum Error {
    /// The CHS address requested cannot be represented in CHS
    ///
    /// ### Remark
    ///
    /// There is a hard limit around 8GB for CHS addressing.
    #[error(display = "exceeded the maximum limit of CHS")]
    LBAExceedsMaximumCHS,
    /// The CHS address requested exceeds the number of cylinders in the disk
    #[error(display = "exceeded the maximum number of cylinders on disk")]
    LBAExceedsMaximumCylinders,
    /// Derialization errors.
    #[error(display = "deserialization failed")]
    Deserialize(#[error(cause)] bincode::Error),
    /// I/O errors.
    #[error(display = "generic I/O error")]
    Io(#[error(cause)] std::io::Error),
    /// Inconsistent extended boot record
    #[error(display = "inconsistent extended boot record")]
    InconsistentEBR,
}

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
    /// ### Remarks
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
    /// ### Remarks
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

    pub fn len(&self) -> usize {
        4 + self.logical_partitions.len()
    }

    /// Make a new MBR
    ///
    /// # Examples:
    /// Basic usage:
    /// ```
    /// let mbr = mbrman::MBR::new(512, [0x01, 0x02, 0x03, 0x04])
    ///     .expect("could not make a partition table");
    /// ```
    pub fn new(sector_size: u32, disk_signature: [u8; 4]) -> Result<MBR> {
        let header = MBRHeader::new(disk_signature)?;

        Ok(MBR {
            sector_size,
            header,
            logical_partitions: Vec::new(),
            align: DEFAULT_ALIGN,
        })
    }

    /// Read the MBR on a reader. This function will try to read the backup header if the primary
    /// header could not be read.
    ///
    /// # Examples:
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
        let header = MBRHeader::read_from(&mut reader)?;

        let mut logical_partitions = Vec::new();
        if let Some(extended) = header.get_extended_partition() {
            // NOTE: The number of sectors is an index field; thus, the zero
            //       value is invalid, reserved and must not be used in normal
            //       partition entries. The entry is used by operating systems
            //       in certain circumstances; in such cases the CHS addresses
            //       are ignored.
            let mut relative_ebr_lba = 0;
            let mut ebr_sectors = extended.sectors;
            let mut ebr_first_chs = extended.first_chs;
            let mut ebr_last_chs = extended.last_chs;
            loop {
                reader.seek(SeekFrom::Start(
                    ((extended.starting_lba + relative_ebr_lba) * sector_size
                        + EBR_BOOTSTRAP_CODE_SIZE) as u64,
                ))?;
                let (partition, next) = match EBRHeader::read_from(&mut reader) {
                    Ok(ebr) => ebr.unwrap(),
                    Err(err) => {
                        if relative_ebr_lba == 0 {
                            // NOTE: if the extended partition is empty, it is not required that an
                            //       EBR exists
                            break;
                        } else {
                            return Err(err.into());
                        }
                    }
                };
                logical_partitions.push(LogicalPartition {
                    partition,
                    absolute_ebr_lba: extended.starting_lba + relative_ebr_lba,
                    ebr_sectors,
                    ebr_first_chs,
                    ebr_last_chs,
                });

                if next.starting_lba > 0 && relative_ebr_lba >= next.starting_lba {
                    return Err(Error::InconsistentEBR);
                }

                relative_ebr_lba = next.starting_lba;
                ebr_sectors = next.sectors;
                ebr_first_chs = next.first_chs;
                ebr_last_chs = next.last_chs;

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

    /// Write the MBR to a writer. This function will seek automatically in the writer to write the
    /// primary header and the backup header at their proper location.
    ///
    /// # Examples:
    /// Basic usage:
    /// ```
    /// let ss = 512;
    /// let data = vec![0; 100 * ss as usize];
    /// let mut cur = std::io::Cursor::new(data);
    /// let mut mbr = mbrman::MBR::new(ss as u32, [0xff; 4])
    ///     .expect("could not make a partition table");
    ///
    /// // actually write:
    /// mbr.write_into(&mut cur)
    ///     .expect("could not write MBR to disk")
    /// ```
    pub fn write_into<W: ?Sized>(&self, mut writer: &mut W) -> Result<()>
    where
        W: Write + Seek,
    {
        self.header.write_into(&mut writer)?;

        if let Some(extended) = self.header.get_extended_partition() {
            let next_logical_partitions = self
                .logical_partitions
                .iter()
                .skip(1)
                .map(|x| Some(x))
                .chain(repeat(None));
            for (l, next) in self.logical_partitions.iter().zip(next_logical_partitions) {
                writer.seek(SeekFrom::Start(
                    (l.absolute_ebr_lba * self.sector_size + EBR_BOOTSTRAP_CODE_SIZE) as u64,
                ))?;
                serialize_into(&mut writer, &l.partition)?;
                if let Some(next) = next {
                    serialize_into(
                        &mut writer,
                        &MBRPartitionEntry {
                            boot: false,
                            first_chs: next.ebr_first_chs,
                            sys: extended.sys,
                            last_chs: next.ebr_last_chs,
                            starting_lba: next
                                .absolute_ebr_lba
                                .saturating_sub(extended.starting_lba),
                            sectors: next.ebr_sectors,
                        },
                    )?;
                } else {
                    serialize_into(&mut writer, &MBRPartitionEntry::empty())?;
                }
                writer.seek(SeekFrom::Current(16 * 2))?;
                serialize_into(&mut writer, &Signature55AA)?;
            }
        }

        Ok(())
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

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct MBRHeader {
    pub disk_signature: [u8; 4],
    pub copy_protected: [u8; 2],
    pub partition_1: MBRPartitionEntry,
    pub partition_2: MBRPartitionEntry,
    pub partition_3: MBRPartitionEntry,
    pub partition_4: MBRPartitionEntry,
    pub boot_signature: Signature55AA,
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
    /// ### Remarks
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
    /// ### Remarks
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
        reader.seek(SeekFrom::Start(BOOTSTRAP_CODE_SIZE))?;

        Ok(deserialize_from(&mut reader)?)
    }

    /// Make a new MBR header
    pub fn new(disk_signature: [u8; 4]) -> Result<MBRHeader> {
        Ok(MBRHeader {
            disk_signature,
            copy_protected: [0x00, 0x00],
            partition_1: MBRPartitionEntry::empty(),
            partition_2: MBRPartitionEntry::empty(),
            partition_3: MBRPartitionEntry::empty(),
            partition_4: MBRPartitionEntry::empty(),
            boot_signature: Signature55AA,
        })
    }

    /// Write the MBR header into a writer. This operation will seek at the
    /// correct location before trying to write to disk.
    pub fn write_into<W: ?Sized>(&self, mut writer: &mut W) -> Result<()>
    where
        W: Write + Seek,
    {
        writer.seek(SeekFrom::Start(BOOTSTRAP_CODE_SIZE))?;
        serialize_into(&mut writer, &self)?;

        Ok(())
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
    partition_1: MBRPartitionEntry,
    partition_2: MBRPartitionEntry,
    unused_partition_3: [u8; 16],
    unused_partition_4: [u8; 16],
    boot_signature: Signature55AA,
}

impl EBRHeader {
    fn read_from<R: ?Sized>(mut reader: &mut R) -> bincode::Result<EBRHeader>
    where
        R: Read,
    {
        deserialize_from(&mut reader)
    }

    fn unwrap(self) -> (MBRPartitionEntry, MBRPartitionEntry) {
        (self.partition_1, self.partition_2)
    }
}

macro_rules! signature {
    ($name:ident, $n:expr, $bytes:expr, $visitor:ident) => {
        #[derive(Clone)]
        pub struct $name;

        struct $visitor;

        impl<'de> Visitor<'de> for $visitor {
            type Value = $name;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(formatter, "the sequence of bytes: {:?}", $bytes)
            }

            fn visit_seq<A>(self, mut seq: A) -> std::result::Result<$name, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut i = 0;
                let mut bytes = [0; $n];
                loop {
                    match seq.next_element::<u8>()? {
                        Some(x) => bytes[i] = x,
                        None => break,
                    }
                    i += 1;
                }

                if &bytes != $bytes {
                    return Err(de::Error::custom(format!(
                        "invalid signature {:?}, expected: {:?}",
                        bytes, $bytes
                    )));
                }

                Ok($name)
            }
        }

        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                deserializer.deserialize_tuple($n, $visitor)
            }
        }

        impl Serialize for $name {
            fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                let mut seq = serializer.serialize_tuple($n)?;
                for x in $bytes.iter() {
                    seq.serialize_element::<u8>(&x)?;
                }
                seq.end()
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{:?}", $bytes)
            }
        }
    };
}

signature!(Signature55AA, 2, &[0x55, 0xaa], Signature55AAVisitor);

/// An MBR partition entry
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct MBRPartitionEntry {
    pub boot: bool,
    pub first_chs: CHS,
    pub sys: u8,
    pub last_chs: CHS,
    pub starting_lba: u32,
    pub sectors: u32,
}

impl MBRPartitionEntry {
    pub fn empty() -> MBRPartitionEntry {
        MBRPartitionEntry {
            boot: false,
            first_chs: CHS::empty(),
            sys: 0,
            last_chs: CHS::empty(),
            starting_lba: 0,
            sectors: 0,
        }
    }

    pub fn is_used(&self) -> bool {
        self.sys > 0
    }

    pub fn is_unused(&self) -> bool {
        !self.is_used()
    }

    pub fn is_extended(&self) -> bool {
        self.sys == 0x05 || self.sys == 0x0f || self.sys == 0x85
    }

    /// Read a partition entry from the reader at the current position.
    pub fn read_from<R: ?Sized>(mut reader: &mut R) -> bincode::Result<MBRPartitionEntry>
    where
        R: Read,
    {
        deserialize_from(&mut reader)
    }
}

#[derive(Debug, Clone)]
pub struct LogicalPartition {
    pub partition: MBRPartitionEntry,
    pub absolute_ebr_lba: u32,
    pub ebr_sectors: u32,
    pub ebr_first_chs: CHS,
    pub ebr_last_chs: CHS,
}

/// A CHS address (cylinder/head/sector)
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct CHS {
    pub cylinder: u16,
    pub head: u8,
    pub sector: u8,
}

impl CHS {
    pub fn new(cylinder: u16, head: u8, sector: u8) -> CHS {
        CHS {
            cylinder,
            head,
            sector,
        }
    }

    /// Creates an empty CHS addressing (0/0/0).
    ///
    /// ### Remark
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
    /// ### Remarks
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
    pub fn to_lba(&self, heads: u8, sectors: u8) -> u32 {
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
    /// ### Remark
    ///
    /// This function does not check if the CHS address is withing range of
    /// possible values for a provided hard disk.
    pub fn is_empty(&self) -> bool {
        self.cylinder == 0 && self.head == 0 && self.sector == 0
    }

    /// Check if the CHS address is valid and within range of the possible
    /// values for the hard disk geometry provided in argument.
    pub fn is_valid(&self, cylinders: u16, heads: u8, sectors: u8) -> bool {
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
        let head = BitVec::<BigEndian, u8>::from_element(seq.next_element::<u8>()?.unwrap());
        let mut bv = BitVec::<BigEndian, u8>::from_element(seq.next_element::<u8>()?.unwrap());
        let mut cylinder = BitVec::<BigEndian, u16>::with_capacity(10);
        cylinder.extend(repeat(false).take(6));
        cylinder.extend(bv.drain(..2));
        cylinder.extend(BitVec::<BigEndian, u8>::from_element(
            seq.next_element::<u8>()?.unwrap(),
        ));
        let mut sector = BitVec::<BigEndian, u8>::with_capacity(8);
        sector.push(false);
        sector.push(false);
        sector.extend(bv.drain(..));

        Ok(CHS {
            cylinder: cylinder.as_slice()[0],
            head: head.as_slice()[0],
            sector: sector.as_slice()[0],
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
        let mut bv = BitVec::<BigEndian, u8>::from_element(self.head);
        let mut sector = BitVec::<BigEndian, u8>::from_element(self.sector);
        let mut cylinder = BitVec::<BigEndian, u16>::from_element(self.cylinder);
        bv.extend(cylinder.drain(..8).into_iter().skip(6));
        bv.extend(sector.drain(2..));
        bv.extend(cylinder.drain(..));

        let mut seq = serializer.serialize_tuple(3)?;
        for x in bv.as_slice() {
            seq.serialize_element(&x)?;
        }
        seq.end()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use std::io::Cursor;

    const DISK1: &str = "tests/fixtures/disk1.img";
    const DISK2: &str = "tests/fixtures/disk2.img";

    #[test]
    fn deserizlize_maximum_chs_value() {
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
    fn serialize_and_deserizlize_some_chs_value() {
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
        let chs = CHS::from_lba_exact(666666, 2484, 16, 63).unwrap();
        assert_eq!(chs.to_lba(16, 63), 666666);

        let chs = CHS::from_lba_aligned(666666, 2484, 16, 63).unwrap();
        assert_eq!(chs.to_lba(16, 63), 667296);

        let chs = CHS::from_lba_exact(667296, 2484, 16, 63).unwrap();
        assert_eq!(chs.head, 0);
        assert_eq!(chs.sector, 1);
    }

    #[test]
    fn read_disk1() {
        let mut mbr = MBR::read_from(&mut File::open(DISK1).unwrap(), 512).unwrap();
        assert!(mbr.header.partition_1.is_used());
        assert!(mbr.header.partition_2.is_used());
        assert!(mbr.header.partition_3.is_unused());
        assert!(mbr.header.partition_4.is_unused());
        assert_eq!(mbr.len(), 4);
        assert_eq!(mbr.header.iter().count(), 4);
        assert_eq!(mbr.header.iter_mut().count(), 4);
        assert_eq!(mbr.iter_mut().count(), 4);
        assert_eq!(mbr.header.partition_1.sys, 0x06);
        assert_eq!(mbr.header.partition_1.starting_lba, 1);
        assert_eq!(mbr.header.partition_1.sectors, 1);
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
        assert_eq!(mbr.logical_partitions[0].ebr_sectors, 15);
        assert_eq!(mbr.logical_partitions[1].absolute_ebr_lba, 7);
        assert_eq!(mbr.logical_partitions[1].ebr_sectors, 3);
        assert_eq!(mbr.logical_partitions[2].absolute_ebr_lba, 10);
        assert_eq!(mbr.logical_partitions[2].ebr_sectors, 4);
        // NOTE: this is actually for testing the CHS conversion to and from LBA
        assert_eq!(
            mbr.logical_partitions[2].partition.first_chs,
            CHS::new(1, 1, 3)
        );
        assert_eq!(
            mbr.logical_partitions[2].partition.first_chs.to_lba(2, 3),
            mbr.logical_partitions[2].absolute_ebr_lba
                + mbr.logical_partitions[2].partition.starting_lba
        );
        assert_eq!(
            CHS::from_lba_exact(
                mbr.logical_partitions[2].absolute_ebr_lba
                    + mbr.logical_partitions[2].partition.starting_lba,
                u16::max_value(),
                2,
                3
            )
            .unwrap(),
            mbr.logical_partitions[2].partition.first_chs
        );
        assert_eq!(mbr.logical_partitions[3].absolute_ebr_lba, 14);
        assert_eq!(mbr.logical_partitions[3].ebr_sectors, 2);
        assert_eq!(mbr.logical_partitions[4].absolute_ebr_lba, 16);
        assert_eq!(mbr.logical_partitions[4].ebr_sectors, 2);
        assert!(mbr.logical_partitions.get(5).is_none());
    }

    #[test]
    fn read_empty_extended_partition() {
        let ss = 512_u32;
        let data = vec![0; 10 * ss as usize];
        let mut cur = Cursor::new(data);
        let mut mbr = MBR::new(ss, [0xff; 4]).unwrap();
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
    fn new_mbr_then_write_then_read_twice() {
        let ss = 512_u32;
        let data = vec![0; 10 * ss as usize];
        let mut cur = Cursor::new(data);
        let mut mbr = MBR::new(ss, [0xff; 4]).unwrap();
        mbr.header.partition_1.sys = 0x83;
        mbr.header.partition_1.starting_lba = 1;
        mbr.header.partition_1.sectors = 4;
        mbr.header.partition_3.sys = 0x0f;
        mbr.header.partition_3.starting_lba = 5;
        mbr.header.partition_3.sectors = 6;
        let mut empty = MBRPartitionEntry::empty();
        empty.starting_lba = 1;
        empty.sectors = 1;
        mbr.logical_partitions.push(LogicalPartition {
            partition: empty,
            absolute_ebr_lba: 5,
            ebr_sectors: 2,
            ebr_first_chs: CHS::empty(),
            ebr_last_chs: CHS::empty(),
        });
        mbr.logical_partitions.push(LogicalPartition {
            partition: MBRPartitionEntry {
                boot: false,
                first_chs: CHS::empty(),
                sys: 0x83,
                last_chs: CHS::empty(),
                starting_lba: 2,
                sectors: 1,
            },
            absolute_ebr_lba: 7,
            ebr_sectors: 3,
            ebr_first_chs: CHS::empty(),
            ebr_last_chs: CHS::empty(),
        });

        // NOTE: don't put this in a loop otherwise it's hard to guess if the error come from
        //       reading, writing or reading after writing again
        mbr.write_into(&mut cur).unwrap();

        let mbr = MBR::read_from(&mut cur, ss).unwrap();
        assert_eq!(mbr.header.partition_1.sys, 0x83);
        assert_eq!(mbr.header.partition_1.starting_lba, 1);
        assert_eq!(mbr.header.partition_1.sectors, 4);
        assert_eq!(mbr.logical_partitions.len(), 2);
        assert_eq!(mbr.logical_partitions[0].absolute_ebr_lba, 5);
        assert_eq!(mbr.logical_partitions[0].partition.starting_lba, 1);
        assert_eq!(mbr.logical_partitions[0].partition.sectors, 1);
        assert_eq!(mbr.logical_partitions[0].partition.sys, 0);
        assert_eq!(mbr.logical_partitions[0].ebr_sectors, 6);
        assert_eq!(mbr.logical_partitions[1].absolute_ebr_lba, 7);
        assert_eq!(mbr.logical_partitions[1].partition.starting_lba, 2);
        assert_eq!(mbr.logical_partitions[1].partition.sectors, 1);
        assert_eq!(mbr.logical_partitions[1].partition.sys, 0x83);
        assert_eq!(mbr.logical_partitions[1].ebr_sectors, 3);

        mbr.write_into(&mut cur).unwrap();

        let mbr = MBR::read_from(&mut cur, ss).unwrap();
        assert_eq!(mbr.header.partition_1.sys, 0x83);
        assert_eq!(mbr.header.partition_1.starting_lba, 1);
        assert_eq!(mbr.header.partition_1.sectors, 4);
        assert_eq!(mbr.logical_partitions.len(), 2);
        assert_eq!(mbr.logical_partitions[0].absolute_ebr_lba, 5);
        assert_eq!(mbr.logical_partitions[0].partition.starting_lba, 1);
        assert_eq!(mbr.logical_partitions[0].partition.sectors, 1);
        assert_eq!(mbr.logical_partitions[0].partition.sys, 0);
        assert_eq!(mbr.logical_partitions[0].ebr_sectors, 6);
        assert_eq!(mbr.logical_partitions[1].absolute_ebr_lba, 7);
        assert_eq!(mbr.logical_partitions[1].partition.starting_lba, 2);
        assert_eq!(mbr.logical_partitions[1].partition.sectors, 1);
        assert_eq!(mbr.logical_partitions[1].partition.sys, 0x83);
        assert_eq!(mbr.logical_partitions[1].ebr_sectors, 3);
    }
}
