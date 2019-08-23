#[macro_use]
extern crate serde_derive;

use bitvec::prelude::*;
use serde::de::{Deserialize, Deserializer, SeqAccess, Visitor};
use serde::ser::{Serialize, SerializeTuple, Serializer};
use std::convert::TryFrom;
use std::iter::repeat;

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct Partition {
    boot: bool,
    first_chs: CHS,
    sys: u8,
    last_chs: CHS,
    starting_lba: u32,
    ending_lba: u32,
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct CHS {
    cylinder: u16,
    head: u8,
    sector: u8,
}

pub enum Error {
    LBAExceedsMaximumCHS,
    LBAExceedsMaximumCylinders,
}

impl CHS {
    pub fn new() -> CHS {
        CHS {
            cylinder: 0,
            head: 0,
            sector: 0,
        }
    }

    pub fn from_lba(lba: u32, cylinders: u16, heads: u8, sectors: u8) -> Result<CHS, Error> {
        // NOTE: code inspired from libfdisk (long2chs)
        let cylinders = u32::from(cylinders);
        let heads = u32::from(heads);
        let sectors = u32::from(sectors);

        let cylinder = lba / (heads * sectors);
        let rem = lba % (heads * sectors);
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
    use std::io::Cursor;

    #[test]
    fn deserizlize_maximum_chs_value() {
        let data = &[0xff, 0xff, 0xff, 0xff];
        let mut cur = Cursor::new(data);
        let chs: CHS = bincode::deserialize_from(&mut cur).unwrap();
        assert_eq!(cur.position(), 3);
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
        let data = &[0xaa, 0xaa, 0xaa];
        let mut cur = Cursor::new(data);
        let chs: CHS = bincode::deserialize_from(&mut cur).unwrap();
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
}
