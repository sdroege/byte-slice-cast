# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html),
specifically the [variant used by Rust](http://doc.crates.io/manifest.html#the-version-field).

## [0.3.4] - 2019-11-11
### Added
- Support for casting between `Vec<T>` and `Vec<u8>`

## [0.3.3] - 2019-11-02
### Added
- Support for `usize` and `isize`

## [0.3.2] - 2019-07-26
### Changed
- Add `no_std` support
- Migrate to 2018 edition

## [0.3.1] - 2019-06-05
### Fixed
- Casting of empty slices works correctly now instead of failing with an
  alignment mismatch error.

## [0.3.0] - 2019-05-11
### Added
- The `Error` type now implements `Clone`.

### Changed
- `AsByteSlice::as_byte_slice` and `ToByteSlice::to_byte_slice` were changed
  to always return `&[u8]` instead of `Result<&[u8], Error>`.
- `AsMutByteSlice::as_mut_byte_slice` and `ToMutByteSlice::to_mut_byte_slice`
  were changed to always return `&mut [u8]` instead of `Result<&mut [u8],
  Error>`.
- The `Display` impl for `Error` now produces more detailed error messages.
- The variants of the `Error` enum were renamed.

## [0.2.0] - 2018-06-01
### Changed
- Major refactoring of how the traits work. It is now possible to work
  directly on `AsRef<[T]>` and `AsMut<[T]>`, e.g. on `Vec<T>` and `Box<[T]>`.

### Added
- Trait impls for i128 and u128.

## [0.1.0] - 2017-08-14
- Initial release of the `byte-slice-cast` crate.

[Unreleased]: https://github.com/sdroege/byte-slice-cast/compare/0.3.2...HEAD
[0.3.1]: https://github.com/sdroege/byte-slice-cast/compare/0.3.1...0.3.2
[0.3.1]: https://github.com/sdroege/byte-slice-cast/compare/0.3.0...0.3.1
[0.3.0]: https://github.com/sdroege/byte-slice-cast/compare/0.2.0...0.3.0
[0.2.0]: https://github.com/sdroege/byte-slice-cast/compare/0.1.0...0.2.0
