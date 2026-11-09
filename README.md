![Rust](https://github.com/rust-disk-partition-management/mbrman/workflows/Rust/badge.svg)
[![Latest Version](https://img.shields.io/crates/v/mbrman.svg)](https://crates.io/crates/mbrman)
![Rust 1.85+](https://img.shields.io/badge/rust-1.85%2B-orange.svg)
![License](https://img.shields.io/crates/l/mbrman)
[![Docs.rs](https://docs.rs/mbrman/badge.svg)](https://docs.rs/mbrman)
[![Changelog](https://img.shields.io/badge/changelog-CHANGELOG.md-blue)](CHANGELOG.md)
[![Dependency Status](https://deps.rs/repo/github/rust-disk-partition-management/mbrman/status.svg)](https://deps.rs/repo/github/rust-disk-partition-management/mbrman)

# mbrman

A library for reading and managing MBR partition tables.

## Features

- Create and delete primary partitions and logical volumes
- Generate the EBR of a logical volume automatically, or provide it manually
- Compute the CHS addresses of logical partitions automatically when writing
  to disk, if the disk geometry is set

## `no_std`

mbrman works without `std`: disable the default features.

- With the `alloc` feature, everything is available except the `std::io` integration. The
  `MBR` type, to edit partition tables, needs `alloc`.
- Without `alloc`, you can read a partition table: `MBRHeader::from_bytes` decodes the MBR and
  `MBRHeader::ebr_walk` reads the EBR chain one logical partition at a time.

```toml
[dependencies]
mbrman = { version = "0.7", default-features = false, features = ["alloc"] }
```

### Disk access

mbrman does no I/O of its own: it turns 512-byte boot records into partition tables and back,
and tells you where on the disk they go. With the default `std` feature, `MBR::read_from` and
`MBR::write_into` do the I/O for you on any `std::io` type, such as `std::fs::File` or
`std::io::Cursor`. Without `std`, or in async code, you do it with whatever your block device
offers:

- To read, `MBR::reader` asks for one boot record at a time: call `next_lba`, read the
  first 512 bytes of that sector and `feed` them, until `next_lba` returns `None`. Then
  `finish` builds the `MBR`. Without `alloc`, decode the MBR with `MBRHeader::from_bytes`
  and walk the EBR chain the same way with `MBRHeader::ebr_walk`.
- To write, `MBR::chunks` validates the whole partition table, then yields every boot
  record to write with its LBA. Nothing is yielded if the table is invalid. Without
  `alloc`, `MBRHeader::to_bytes` encodes the MBR, which goes at LBA 0.

LBAs count sectors of the size given to `MBR::reader` or `MBR::new`, so a block device takes
them as they are. For a byte-addressed device, the byte offset is
`u64::from(lba) * u64::from(sector_size)`.

Without `std`, the I/O errors stay yours: mbrman only returns its own `Error`. Boot records
are 512 bytes whatever the sector size: on a device with larger sectors, read the sector that
contains the record and, to write, update the record inside it before writing it back.

### With `alloc`

Write a partition table with an extended partition and a logical volume to a block device,
then read it back.

```rust
# #[cfg(feature = "alloc")] {
// a disk in memory, standing in for your block device
let mut disk = [0_u8; 64 * 512];

// a partition table with an extended partition and a logical volume
let mut mbr = mbrman::MBR::new(512, disk.len() as u64, [0xff; 4]);
mbr[1] = mbrman::MBRPartitionEntry {
    boot: mbrman::BOOT_INACTIVE,
    first_chs: mbrman::CHS::empty(),
    sys: 0x0f,
    last_chs: mbrman::CHS::empty(),
    starting_lba: 1,
    sectors: mbr.disk_size - 1,
};
mbr.align = 1;
mbr.push(0x83, 1, mbr.disk_size - 1)
    .expect("could not add the logical volume");

// write it: the whole table is validated first, then each boot record comes with its LBA
for chunk in mbr.chunks().expect("invalid partition table") {
    let start = chunk.lba as usize * 512;
    disk[start..start + 512].copy_from_slice(&chunk.data);
}

// read it back: the reader asks for each 512-byte boot record, one at a time
let mut reader = mbrman::MBR::reader(512, disk.len() as u64);
while let Some(lba) = reader.next_lba().expect("invalid EBR chain") {
    let start = lba as usize * 512;
    reader
        .feed(disk[start..start + 512].try_into().unwrap())
        .expect("could not read a boot record");
}
let read = reader.finish().expect("could not read the partition table");
assert_eq!(read.logical_partitions, mbr.logical_partitions);
# }
```

### Without `alloc`

Read the logical partitions of a disk without allocating. `MBRHeader::to_bytes` gives back
the 512 bytes of the MBR, to write at LBA 0.

```rust
# #[cfg(feature = "std")] {
// the bytes of a disk image, standing in for your block device
let disk = std::fs::read("tests/fixtures/disk2.img").expect("could not read disk");
let sector = |lba: u32| -> [u8; 512] {
    let start = lba as usize * 512;
    disk[start..start + 512].try_into().unwrap()
};

let header = mbrman::MBRHeader::from_bytes(&sector(0))
    .expect("could not read the MBR header");
let mut walk = header.ebr_walk();
while let Some(lba) = walk.next_lba().expect("invalid EBR chain") {
    if let Some(l) = walk.feed(&sector(lba)).expect("could not read an EBR") {
        println!("logical partition: starting lba = {}", l.partition.starting_lba);
    }
}

let mbr_bytes = header.to_bytes().expect("could not encode the MBR header");
assert_eq!(mbr_bytes.len(), 512);
# }
```

### Async

The same loops work with any async runtime: only the I/O calls change. `dev` is your async
block device.

```rust
# #[cfg(feature = "alloc")] {
use mbrman::MBR;

/// An async block device, standing in for a tokio, embassy or other driver.
struct Device(Vec<u8>);

impl Device {
    fn size(&self) -> u64 {
        self.0.len() as u64
    }

    async fn read_block(&mut self, lba: u32, buf: &mut [u8; 512]) -> Result<(), Error> {
        let start = lba as usize * 512;
        buf.copy_from_slice(self.0.get(start..start + 512).ok_or(Error::Device)?);
        Ok(())
    }

    async fn write_block(&mut self, lba: u32, buf: &[u8; 512]) -> Result<(), Error> {
        let start = lba as usize * 512;
        self.0.get_mut(start..start + 512).ok_or(Error::Device)?.copy_from_slice(buf);
        Ok(())
    }
}

/// The errors of your application: the device's and mbrman's.
#[derive(Debug)]
enum Error {
    Device,
    Mbr(mbrman::Error),
}

impl From<mbrman::Error> for Error {
    fn from(err: mbrman::Error) -> Error {
        Error::Mbr(err)
    }
}

async fn read_mbr(dev: &mut Device) -> Result<MBR, Error> {
    let mut reader = MBR::reader(512, dev.size());
    let mut buf = [0; 512];
    while let Some(lba) = reader.next_lba()? {
        dev.read_block(lba, &mut buf).await?;
        reader.feed(&buf)?;
    }
    Ok(reader.finish()?)
}

async fn write_mbr(dev: &mut Device, mbr: &mut MBR) -> Result<(), Error> {
    for chunk in mbr.chunks()? {
        dev.write_block(chunk.lba, &chunk.data).await?;
    }
    Ok(())
}

async fn run() -> Result<(), Error> {
    let mut dev = Device(vec![0; 64 * 512]);
    let mut mbr = MBR::new(512, dev.size(), [0xff; 4]);
    write_mbr(&mut dev, &mut mbr).await?;
    assert_eq!(read_mbr(&mut dev).await?.header.disk_signature, [0xff; 4]);
    Ok(())
}

// use your runtime's executor instead; this one only polls until the future is ready
# use core::{future::Future, pin::pin, task::{Context, Poll, Waker}};
# fn block_on<F: Future>(fut: F) -> F::Output {
#     let mut fut = pin!(fut);
#     let mut cx = Context::from_waker(Waker::noop());
#     loop {
#         if let Poll::Ready(out) = fut.as_mut().poll(&mut cx) {
#             return out;
#         }
#     }
# }
block_on(run()).expect("could not write and read the partition table");
# }
```

## Examples

### Read the partitions of a disk

Open a disk image, read its MBR and list the partitions in use.

```rust
# #[cfg(feature = "std")] {
let mut f = std::fs::File::open("tests/fixtures/disk1.img")
    .expect("could not open disk");
let mbr = mbrman::MBR::read_from(&mut f, 512)
    .expect("could not find MBR");

println!("Disk signature: {:?}", mbr.header.disk_signature);

for (i, p) in mbr.iter() {
    // NOTE: The first four partitions are always provided by iter()
    if p.is_used() {
        println!("Partition #{}: type = {:?}, size = {} bytes, starting lba = {}",
            i,
            p.sys,
            p.sectors * mbr.sector_size,
            p.starting_lba);
    }
}
# }
```

### Create and delete a primary partition

Find a free slot and free space, fill the slot with a new partition, then empty it again.

```rust
# #[cfg(feature = "std")] {
let mut f = std::fs::File::open("tests/fixtures/disk1.img")
    .expect("could not open disk");
let mut mbr = mbrman::MBR::read_from(&mut f, 512)
    .expect("could not find MBR");

let free_partition_number = mbr.iter().find(|(i, p)| p.is_unused()).map(|(i, _)| i)
    .expect("no more places available");
let sectors = mbr.get_maximum_partition_size()
    .expect("no more space available");
let starting_lba = mbr.find_optimal_place(sectors)
    .expect("could not find a place to put the partition");

mbr[free_partition_number] = mbrman::MBRPartitionEntry {
    boot: mbrman::BOOT_INACTIVE,        // boot flag
    first_chs: mbrman::CHS::empty(),    // first CHS address (only useful for old computers)
    sys: 0x83,                          // Linux filesystem
    last_chs: mbrman::CHS::empty(),     // last CHS address (only useful for old computers)
    starting_lba,                       // the sector where the partition starts
    sectors,                            // the number of sectors in that partition
};

mbr[free_partition_number] = mbrman::MBRPartitionEntry::empty();

// NOTE: nothing is written to the disk until you call mbr.write_into()
# }
```

### Create a new partition table on an empty disk

Write a fresh MBR to a blank in-memory disk.

```rust
# #[cfg(feature = "std")] {
let ss = 512; // sector size
let data = vec![0; 100 * ss as usize];
let mut cur = std::io::Cursor::new(data);

let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
    .expect("could not create partition table");

// NOTE: write the changes to the in-memory buffer
mbr.write_into(&mut cur);
# }
```

### Add a logical volume

A logical volume lives inside an extended partition, so create one first. `push` then places the volume and its EBR for you.

```rust
# #[cfg(feature = "std")] {
let ss = 512; // sector size
let data = vec![0; 100 * ss as usize];
let mut cur = std::io::Cursor::new(data);

let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
    .expect("could not create partition table");

mbr[1] = mbrman::MBRPartitionEntry {
    boot: mbrman::BOOT_INACTIVE,        // boot flag
    first_chs: mbrman::CHS::empty(),    // first CHS address (only useful for old computers)
    sys: 0x0f,                          // extended partition with LBA
    last_chs: mbrman::CHS::empty(),     // last CHS address (only useful for old computers)
    starting_lba: 1,                    // the sector where the partition starts
    sectors: mbr.disk_size - 1,         // the number of sectors in that partition
};

// align on sectors, so the EBR only takes the first sector of the extended partition
mbr.align = 1;

// this helper does the hard work for you: here it creates a Linux filesystem
// logical volume that fills the entire extended partition
// NOTE: 1 sector is lost because the EBR uses it
mbr.push(0x83, 1, mbr.disk_size - 1)
    .expect("could not add the logical volume");

// NOTE: write the changes to the in-memory buffer
mbr.write_into(&mut cur);
# }
```

### Add a logical volume manually

Use this only if you need to choose exactly where the EBR and the partition go.

```rust
# #[cfg(feature = "std")] {
let ss = 512; // sector size
let data = vec![0; 100 * ss as usize];
let mut cur = std::io::Cursor::new(data);

let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
    .expect("could not create partition table");

mbr[1] = mbrman::MBRPartitionEntry {
    boot: mbrman::BOOT_INACTIVE,        // boot flag
    first_chs: mbrman::CHS::empty(),    // first CHS address (only useful for old computers)
    sys: 0x0f,                          // extended partition with LBA
    last_chs: mbrman::CHS::empty(),     // last CHS address (only useful for old computers)
    starting_lba: 1,                    // the sector where the partition starts
    sectors: mbr.disk_size - 1,         // the number of sectors in that partition
};

// NOTE: mbrman does not check that a manually created partition is consistent
mbr.logical_partitions.push(
    mbrman::LogicalPartition {
        // this is the actual partition entry for the logical volume
        partition: mbrman::MBRPartitionEntry {
            boot: mbrman::BOOT_INACTIVE,
            first_chs: mbrman::CHS::empty(),
            sys: 0x83,
            last_chs: mbrman::CHS::empty(),
            starting_lba: 2,                    // the sector index 1 is used by the EBR
            sectors: mbr.disk_size - 2,
        },
        // this is the absolute LBA address of the EBR
        absolute_ebr_lba: 1,
        // the number of sectors in the first EBR is never known
        ebr_sectors: None,
        // empty boot sector in the EBR
        bootstrap_code: [0; 446],
        // this is the absolute CHS address of the EBR (only used by old computers)
        ebr_first_chs: mbrman::CHS::empty(),                // only for old computers
        // this is the absolute CHS address of the last EBR (only used by old computers)
        // NOTE: this is never known for the first EBR
        ebr_last_chs: None,
    }
);

// NOTE: write the changes to the in-memory buffer
mbr.write_into(&mut cur);
# }
```
