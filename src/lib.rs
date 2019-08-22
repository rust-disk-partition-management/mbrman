use serde::de::{Deserialize, Deserializer, SeqAccess, Visitor};
use serde::de;
use bitvec::prelude::*;
use std::iter::repeat;
use std::convert::TryFrom;

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct CHS {
    cylinder: u16,
    head: u8,
    sector: u8,
}

enum Error {
    LBAExceedsMaximumCHS,
}

impl CHS {
    fn from_lba(lba: u32, cylinders: u16, heads: u8, sectors: u8) -> Result<CHS, Error> {
        // NOTE: code inspired from libfdisk (long2chs)
        let cylinders = u32::from(cylinders);
        let heads = u32::from(heads);
        let sectors = u32::from(sectors);

        let cylinder = lba / (heads * sectors);
        let rem = lba % (heads * sectors);
        let head = rem / sectors;
        let sector = rem % sectors + 1;

        if cylinder > 1023 {
            return Err(Error::LBAExceedsMaximumCHS)
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
        cylinder.extend(BitVec::<BigEndian, u8>::from_element(seq.next_element::<u8>()?.unwrap()));
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn it_works() {
        let data = &[0xff, 0xff, 0xff, 0xff];
        let mut cur = Cursor::new(data);
        let chs: CHS = bincode::deserialize_from(&mut cur).unwrap();
        assert_eq!(cur.position(), 3);
        assert_eq!(chs, CHS {
            cylinder: 1023,
            head: 255,
            sector: 63,
        });
    }
}
