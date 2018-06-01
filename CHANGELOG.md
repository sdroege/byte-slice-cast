# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html),
specifically the [variant used by Rust](http://doc.crates.io/manifest.html#the-version-field).

## [0.2.0] - 2018-06-01
### Changed
- Major refactoring of how the traits work. It is now possible to work
  directly on `AsRef<[T]>` and `AsMut<[T]>`, e.g. on `Vec<T>` and `Box<[T]>`.

### Added
- Trait impls for i128 and u128.

## [0.1.0] - 2017-08-14
- Initial release of the `byte-slice-cast` crate.

[Unreleased]: https://github.com/sdroege/byte-slice-cast/compare/0.2.0...HEAD
[0.2.0]: https://github.com/sdroege/byte-slice-cast/compare/0.1.0...0.2.0
