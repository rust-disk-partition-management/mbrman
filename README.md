![Rust](https://github.com/rust-disk-partition-management/mbrman/workflows/Rust/badge.svg)
[![Latest Version](https://img.shields.io/crates/v/mbrman.svg)](https://crates.io/crates/mbrman)
![Rust 1.51+](https://img.shields.io/badge/rust-1.51%2B-orange.svg)
![License](https://img.shields.io/crates/l/mbrman)
[![Docs.rs](https://docs.rs/mbrman/badge.svg)](https://docs.rs/mbrman)
[![LOC](https://tokei.rs/b1/github/rust-disk-partition-management/mbrman)](https://github.com/rust-disk-partition-management/mbrman)
[![Dependency Status](https://deps.rs/repo/github/rust-disk-partition-management/mbrman/status.svg)](https://deps.rs/repo/github/rust-disk-partition-management/mbrman)

mbrman
======

MBR Partition Management in Rust

Library Usage
-------------

A library that allows managing MBR partition tables.

## Features

 *  Create primary partitions and logical volumes
 *  Delete primary partitions and logical volumes
 *  Automatically generate logical volume's EBR (or can be provided manually)
 *  If the disk geometry is set, the partition CHS addresses will be calculated
    automatically when writing to disk

## Examples

### Read all the partitions of a disk

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

### Create and delete primary partitions

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
    boot: false,                        // boot flag
    first_chs: mbrman::CHS::empty(),    // first CHS address (only useful for old computers)
    sys: 0x83,                          // Linux filesystem
    last_chs: mbrman::CHS::empty(),     // last CHS address (only useful for old computers)
    starting_lba,                       // the sector where the partition starts
    sectors,                            // the number of sectors in that partition
};

mbr[free_partition_number] = mbrman::MBRPartitionEntry::empty();

// NOTE: no modification is committed to the disk until we call mbr.write_into()
```

### Create a new partition table from an empty disk

```rust
let ss = 512; // sector size
let data = vec![0; 100 * ss as usize];
let mut cur = std::io::Cursor::new(data);

let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
    .expect("could not create partition table");

// NOTE: commit the change to the in-memory buffer
mbr.write_into(&mut cur);
```

### Add a new logical volume to the disk

```rust
let ss = 512; // sector size
let data = vec![0; 100 * ss as usize];
let mut cur = std::io::Cursor::new(data);

let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
    .expect("could not create partition table");

mbr[1] = mbrman::MBRPartitionEntry {
    boot: false,                        // boot flag
    first_chs: mbrman::CHS::empty(),    // first CHS address (only useful for old computers)
    sys: 0x0f,                          // extended partition with LBA
    last_chs: mbrman::CHS::empty(),     // last CHS address (only useful for old computers)
    starting_lba: 1,                    // the sector where the partition starts
    sectors: mbr.disk_size - 1,         // the number of sectors in that partition
};

// this helper function will do all the hard work for you
// here it creates a logical volume with Linux filesystem that occupies the entire disk
// NOTE: you will lose 1 sector because it is used by the EBR
mbr.push(0x83, 1, mbr.disk_size - 1);

// NOTE: commit the change to the in-memory buffer
mbr.write_into(&mut cur);
```

### Add a new logical volume manually to the disk

This is useful only if you need to specify exactly where goes the EBR and the partition itself.

```rust
let ss = 512; // sector size
let data = vec![0; 100 * ss as usize];
let mut cur = std::io::Cursor::new(data);

let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
    .expect("could not create partition table");

mbr[1] = mbrman::MBRPartitionEntry {
    boot: false,                        // boot flag
    first_chs: mbrman::CHS::empty(),    // first CHS address (only useful for old computers)
    sys: 0x0f,                          // extended partition with LBA
    last_chs: mbrman::CHS::empty(),     // last CHS address (only useful for old computers)
    starting_lba: 1,                    // the sector where the partition starts
    sectors: mbr.disk_size - 1,         // the number of sectors in that partition
};

// NOTE: mbrman won't check the consistency of the partition you have created manually
mbr.logical_partitions.push(
    mbrman::LogicalPartition {
        // this is the actual partition entry for the logical volume
        partition: mbrman::MBRPartitionEntry {
            boot: false,
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
        // this helper generates an empty boot sector in the EBR
        bootstrap_code: mbrman::BootstrapCode446::new(),
        // this is the absolute CHS address of the EBR (only used by old computers)
        ebr_first_chs: mbrman::CHS::empty(),                // only for old computers
        // this is the absolute CHS address of the last EBR (only used by old computers)
        // NOTE: this is not know the first EBR
        ebr_last_chs: None,
    }
);

// NOTE: commit the change to the in-memory buffer
mbr.write_into(&mut cur);
```
