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

## Examples

### Read the partitions of a disk

Open a disk image, read its MBR and list the partitions in use.

```rust
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
```

### Create and delete a primary partition

Find a free slot and free space, fill the slot with a new partition, then empty it again.

```rust
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
```

### Create a new partition table on an empty disk

Write a fresh MBR to a blank in-memory disk.

```rust
let ss = 512; // sector size
let data = vec![0; 100 * ss as usize];
let mut cur = std::io::Cursor::new(data);

let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
    .expect("could not create partition table");

// NOTE: write the changes to the in-memory buffer
mbr.write_into(&mut cur);
```

### Add a logical volume

A logical volume lives inside an extended partition, so create one first. `push` then places the volume and its EBR for you.

```rust
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
```

### Add a logical volume manually

Use this only if you need to choose exactly where the EBR and the partition go.

```rust
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
```
