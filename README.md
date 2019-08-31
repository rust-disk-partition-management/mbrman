[![Build Status](https://travis-ci.org/cecton/mbrman.svg?branch=master)](https://travis-ci.org/cecton/mbrman)
[![Latest Version](https://img.shields.io/crates/v/mbrman.svg)](https://crates.io/crates/mbrman)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](http://opensource.org/licenses/MIT)
[![Docs.rs](https://docs.rs/mbrman/badge.svg)](https://docs.rs/mbrman)
[![LOC](https://tokei.rs/b1/github/cecton/mbrman)](https://github.com/cecton/mbrman)
[![Dependency Status](https://deps.rs/repo/github/cecton/mbrman/status.svg)](https://deps.rs/repo/github/cecton/mbrman)

mbrman
======

MBR Partition Management in Rust

Installation
------------

Library:

Cargo.toml:
```toml
[dependencies]
mbrman = { version = "0.1.0", default-features = false }
```

Library Usage
-------------

A library that allows managing GUID partition tables.

# Examples
Reading all the partitions of a disk:
```rust
let mut f = std::fs::File::open("tests/fixtures/disk1.img")
    .expect("could not open disk");
let mbr = mbrman::MBR::read_from(&mut f, 512)
    .expect("could not find MBR");

println!("Disk signature: {:?}", mbr.header.disk_signature);

for (i, p) in mbr.iter() {
    if p.is_used() {
        println!("Partition #{}: type = {:?}, size = {} bytes, starting lba = {}",
            i,
            p.sys,
            p.sectors * mbr.sector_size,
            p.starting_lba);
    }
}
```
Creating new partitions:
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
    boot: false,
    first_chs: mbrman::CHS::empty(),
    sys: 0x83,
    last_chs: mbrman::CHS::empty(),
    starting_lba,
    sectors,
};
```
Creating a new partition table with one entry that fills the entire disk:
```rust
let ss = 512;
let data = vec![0; 100 * ss as usize];
let mut cur = std::io::Cursor::new(data);
let mut mbr = mbrman::MBR::new_from(&mut cur, ss as u32, [0xff; 4])
    .expect("could not create partition table");

mbr[1] = mbrman::MBRPartitionEntry {
    boot: false,
    first_chs: mbrman::CHS::empty(),
    sys: 0x83,
    last_chs: mbrman::CHS::empty(),
    starting_lba: 1,
    sectors: mbr.disk_size - 1,
};
```
