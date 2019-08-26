#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate err_derive;

use bitvec::prelude::*;
use serde::de;
use serde::de::{Deserialize, Deserializer, SeqAccess, Visitor};
use serde::ser::{Serialize, SerializeTuple, Serializer};
use std::convert::TryFrom;
use std::iter::repeat;
use std::ops::{Index, IndexMut};

pub struct MBR {
    /// Sector size of the disk.
    ///
    /// You should not change this, otherwise the starting locations of your partitions will be
    /// different in bytes.
    pub sector_size: u64,
    /// MBR partition header (disk GUID, first/last usable LBA, etc...)
    pub header: MBRHeader,
    logical_partitions: Vec<MBRPartitionEntry>,
    /// Partitions alignment (in sectors)
    ///
    /// This field change the behavior of the methods `get_maximum_partition_size()`,
    /// `find_free_sectors()`, `find_first_place()`, `find_last_place()` and `find_optimal_place()`
    /// so they return only values aligned to the alignment.
    ///
    /// # Panics
    /// The value must be greater than 0, otherwise you will encounter divisions by zero.
    pub align: u64,
}

impl MBR {
    /// Get an iterator over the partition entries and their index. The
    /// index always starts at 1.
    pub fn iter(&self) -> impl Iterator<Item = (usize, &MBRPartitionEntry)> {
        self.header.iter().chain(
            self.logical_partitions
                .iter()
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
        partitions.extend(self.logical_partitions.iter_mut());
        partitions.into_iter().enumerate().map(|(i, x)| (i + 1, x))
    }

    pub fn get(&self, i: usize) -> Option<&MBRPartitionEntry> {
        match i {
            0 => None,
            1 => Some(&self.header.partition_1),
            2 => Some(&self.header.partition_2),
            3 => Some(&self.header.partition_3),
            4 => Some(&self.header.partition_4),
            i => self.logical_partitions.get(i - 5),
        }
    }

    pub fn get_mut(&mut self, i: usize) -> Option<&mut MBRPartitionEntry> {
        match i {
            0 => None,
            1 => Some(&mut self.header.partition_1),
            2 => Some(&mut self.header.partition_2),
            3 => Some(&mut self.header.partition_3),
            4 => Some(&mut self.header.partition_4),
            i => self.logical_partitions.get_mut(i - 5),
        }
    }
}

impl Index<usize> for MBR {
    type Output = MBRPartitionEntry;

    fn index(&self, i: usize) -> &Self::Output {
        self.get(i).expect("invalid partition")
    }
}

impl IndexMut<usize> for MBR {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
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
    pub fn is_copy_protected(&self) -> Option<bool> {
        match self.copy_protected {
            [0x00, 0x00] => Some(false),
            [0x5a, 0x5a] => Some(true),
            _ => None,
        }
    }

    pub fn get(&self, i: usize) -> Option<&MBRPartitionEntry> {
        match i {
            1 => Some(&self.partition_1),
            2 => Some(&self.partition_2),
            3 => Some(&self.partition_3),
            4 => Some(&self.partition_4),
            _ => None,
        }
    }

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
        self.iter()
            .find(|(_, x)| x.sys == 0x05 || x.sys == 0x0f || x.sys == 0x85)
            .map(|(_, x)| x)
    }
}

impl Index<usize> for MBRHeader {
    type Output = MBRPartitionEntry;

    fn index(&self, i: usize) -> &Self::Output {
        self.get(i).expect("invalid partition")
    }
}

impl IndexMut<usize> for MBRHeader {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        self.get_mut(i).expect("invalid partition")
    }
}

pub struct MBRPartitionEntryIter<'a> {
    phantom: std::marker::PhantomData<&'a ()>,
}

impl<'a> Iterator for MBRPartitionEntryIter<'a> {
    type Item = &'a MBRPartitionEntry;

    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct EBRHeader {
    pub partition_1: MBRPartitionEntry,
    pub partition_2: MBRPartitionEntry,
    pub unused_partition_3: [u8; 16],
    pub unused_partition_4: [u8; 16],
    pub boot_signature: Signature55AA,
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
                loop {
                    match seq.next_element::<u8>()? {
                        Some(x) => {
                            if x != $bytes[i] {
                                return Err(de::Error::custom(format!("unexpected byte: {:?}", x)));
                            }
                        }
                        None => break,
                    }
                    i += 1;
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
                    seq.serialize_element(&x)?;
                }
                seq.end()
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                write!(f, "{:?}", $bytes)
            }
        }
    };
}

signature!(Signature55AA, 2, &[0x55, 0xaa], Signature55AAVisitor);

/// An MBR partition entry
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct MBRPartitionEntry {
    boot: bool,
    first_chs: CHS,
    sys: u8,
    last_chs: CHS,
    starting_lba: u32,
    ending_lba: u32,
}

impl MBRPartitionEntry {
    pub fn is_used(&self) -> bool {
        self.sys > 0
    }

    pub fn is_unused(&self) -> bool {
        !self.is_used()
    }
}

/// An MBR partition entry
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct EBRPartitionEntry {
    boot: bool,
    first_chs: CHS,
    sys: u8,
    last_chs: CHS,
    starting_lba: u32,
    ending_lba: u32,
}

/// A CHS address (cylinder/head/sector)
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct CHS {
    cylinder: u16,
    head: u8,
    sector: u8,
}

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
}

impl CHS {
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
    pub fn from_lba_exact(lba: u32, cylinders: u16, heads: u8, sectors: u8) -> Result<CHS, Error> {
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
    pub fn from_lba_aligned(
        lba: u32,
        cylinders: u16,
        heads: u8,
        sectors: u8,
    ) -> Result<CHS, Error> {
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
}
