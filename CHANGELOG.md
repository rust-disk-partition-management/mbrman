# Changelog

## Unreleased

Fixed:

- `MBR::find_free_sectors` panicked when two boundaries came out equal (debug) or wrapped a gap size around (release), from entries sharing a boundary or a one-sector partition whose first and last sector are the same, and the wrapped size returned spots inside a partition, past the end of the disk and overlapping each other; tables whose entries overlap returned spots inside a partition and overlapping each other in debug too, without panicking. `find_first_place`, `find_last_place`, `find_optimal_place`, `get_maximum_partition_size` and `get_maximum_partition_size_for` then handed those spots to the caller
- `MBR::find_free_sectors` added `absolute_ebr_lba` to the `starting_lba` of a logical partition, which is already absolute, so the free spots of an extended partition were wrong
- `MBR::find_free_sectors` and `MBR::find_at_sector` panicked (debug) or wrapped around (release) on partitions ending past `u32::MAX`, such as the protective MBR of a GPT disk of 2 TiB or more. A partition ending past the end of the disk made `find_free_sectors` report free spots past the end of the disk

## v0.7.0 (2026-11-09)

Breaking changes:

- Remove the `bincode`, `serde`, `serde-big-array` and `bitvec` dependencies (#40)
- `MBRHeader`, `MBRPartitionEntry` and `CHS` no longer implement serde's `Serialize`/`Deserialize`. Use the new `from_bytes`/`to_bytes` methods to encode them in memory (#40)
- Remove `Error::Deserialize` and `Error::Serialize` (#40)
- A truncated boot record now returns `Error::Io` with `UnexpectedEof` (#40)
- `MBR::read_from` only treats the first EBR as missing when its signature is invalid; I/O errors and invalid entries there are now returned instead of being ignored (#40)
- New default `std` feature: builds with `default-features = false` must enable it to keep the `std::io` integration (#41)
- `Error::Io`, `MBR::new_from`, `MBR::update_from`, `MBR::read_from`, `MBR::write_into`, `MBRHeader::read_from` and `MBRHeader::write_into` only exist with the `std` feature (#41)
- `MBR::write_into` validates the whole partition table before writing anything: an invalid logical partition no longer leaves the MBR written without its EBRs (#41)
- The sector size must be at least 512, the size of a boot record: `MBR::new`, `MBR::reader`, `MBR::new_from`, `MBR::read_from`, `MBR::update_from` and `MBR::write_into` panic otherwise. A sector size of 0 used to panic with a division by zero, and a sector size below 512 mis-addressed the boot records (#41)

Changed:

- Remove the `thiserror` dependency: mbrman has no dependencies left. `Error` keeps the same variants and messages (#41)

Added:

- `no_std` and async support, with no I/O trait to implement: mbrman decodes and encodes boot records and the caller does the I/O. The `MBR` type needs the `alloc` feature (#41)
- `MBR::new` and `MBR::reader`, which take the disk size in bytes, and `MBRReader`, which asks for each boot record to read and builds the `MBR` (#41)
- `MBR::chunks`, which validates the partition table and returns each boot record to write with its LBA (#41)
- `MBRHeader::ebr_walk`, which walks the EBR chain one logical partition at a time, without allocating (#41)
- `Error::OutOfSequence`, returned when a reader is fed or finished out of sequence (#41)
- `MBRHeader::from_bytes`/`to_bytes` to decode and encode a 512-byte MBR sector, with validation (#40)
- `MBRPartitionEntry::from_bytes`/`to_bytes` and `CHS::from_bytes`/`to_bytes` to decode and encode raw entries and CHS addresses (#40)

Fixed:

- `MBR::write_into` wrote EBRs located more than 4 GiB into the disk at the wrong offset (#40)
- `MBR::read_from` panicked (debug) or returned a wrong LBA (release) on EBR entries whose LBA overflows; it now returns `Error::InconsistentEBR` (#40)
- `MBR::read_from` panicked when every used partition starts at LBA 0; the alignment then falls back to the default (#41)
- `MBR::write_into` panicked on a logical partition whose `ebr_sectors` or `ebr_last_chs` was unset (only the first one may leave them empty); it now returns `Error::InconsistentEBR` (#41)

## v0.6.1 (2025-07-07)

- Fix overflow with extended partitions (#38)

## v0.6.0 (2025-05-14)

- Update dependencies to allow building with latest Rust version (#31)

## v0.5.4 (2025-02-12)

- Add helpers for resizing (#36)

## v0.5.3 (2025-02-11)

- Update to Rust 2021 and declare the MSRV in `Cargo.toml` (#30)
- Allow serde-big-array 0.5.x (#27) and ensure building with serde-big-array 0.4.1 works (#34)
- Fix clippy lints (#29)

## v0.5.2 (2023-03-27)

- Update MSRV badge in README (#26)

## v0.5.1 (2022-12-01)

- Update bitvec to 1.0.1 (#25)
- Fix `MBR::read_from()` doc comment (#23)

## v0.5.0 (2022-10-14)

- Add `InvalidSignature` and `InvalidBootFlag` error variants (#18)
- Make `Error` type non-exhaustive (#15)
- Zero-fill unused EBR partition entries when writing (#20)
- Derive `Eq` alongside `PartialEq` (#17)
- Update README examples and add doctests (#21)

## v0.4.2 (2022-01-11)

- Add correct (de)serialization of boot flags (#14)

## v0.4.1 (2022-01-03)

- Update bitvec (#13)

## v0.4.0 (2021-03-13)

- Switch from derive-error to thiserror
- Update bitvec
- Fix typo (#10)

## v0.3.4 (2020-12-23)

- Include test fixtures in packaged crate

## v0.3.3 (2020-12-12)

- Change licensing to MIT OR Apache-2.0

## v0.3.2 (2020-10-12)

- Update bitvec requirement from 0.16 to 0.17 (#4)
- Update serde to 1.0.116 and bitvec to 0.19
- Use `sort_unstable` instead of `sort`

## v0.3.1 (2020-01-03)

- Update installation version in README

## v0.3.0 (2020-01-03)

- Doc improvements (#3)

## v0.2.0 (2019-12-15)

- Read bootstrap code (#2)
- Update dependencies

## v0.1.0 (2019-08-31)

- Initial release
