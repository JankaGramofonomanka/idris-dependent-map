
# Change Log
All notable changes to this project will be documented in this file.

## [0.1.1] - Unreleased

### Added

### Changed

### Fixed
- the `union` precedence bug - `union` used to preffer the right operand in some cases with both operands containing different values under the same key, which is inconsistent with the documentation

## [0.1.0]

### Added
- implementations of:
  - `DFunctor`
  - `DFoldable`
  - `DShow`
  - `DOrd`

### Changed
- Replaced `Some`, `GEq`, `GCompare`, and `DSum` modules with the `dtypes` package
  - `GEq` replaced by `DEq`, `GCompare` by `DOrd`
- Removed the `Data.ShowS` module

### Fixed

## [0.0.1] - first release
