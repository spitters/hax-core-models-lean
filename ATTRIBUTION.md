# Attribution

This package combines two works of Cryspen, both under the Apache License 2.0
(`LICENSE`):

- `Hax/` and `Hax.lean`: the Lean library of hax (`hax-lib/proof-libs/lean`,
  https://github.com/cryspen/hax, commit `1d89d64`), with prelude additions for
  `Logical_op`, `Vec`, `Num`, `Bit` and `Loop`, and repairs for Lean 4.33.1.
- `HaxCoreModels.lean`: the Lean extraction of the `core-models` crate, version
  0.0.7 (https://crates.io/crates/core-models), modules
  `core_arch::x86::interpretations::int_vec` and `abstractions`.

## Changes to the extraction

The hax Lean backend does not emit a complete, elaborating file for these
modules. The following were added or edited by hand:

- `FunArray` is modelled as a function `u64 → Option T` (the Rust type stores a
  512-slot array of `Option<T>`), with `get` (panics on `None`, as `unwrap`
  does), `from_fn`, `fold` and indexing; `BitVec::from_fn` and indexing likewise.
- Inherent integer operations the prelude lacks: `MIN`, `MAX`, `wrapping_add`,
  `wrapping_sub`, `overflowing_mul`, `abs`, `rem_euclid` on `i8` … `i128`;
  `bool` and 128-bit `as` casts; `u128 >> i32`; `hax_lib` integer operations and
  `assert_prop`.
- In eleven models the extraction drops the target type of an inner `as` cast;
  the targets are restored from the Rust source.
- `impl From<Bit> for isize` is extracted as `def Bit`, which clashes with the
  type; it is renamed `Bit_discr`. Anonymous `const _` items are renamed.
- The `requires`/`ensures` contract of `BitVec::chunked_shift` is removed; the
  function itself is kept.

`i128` and `u128` are both represented by `BitVec 128` in the prelude, so
comparisons on `i128` are unsigned.
- `_mm256_bsrli_epi128` follows the libcrux fix of
  https://github.com/celabshq/libcrux/pull/1498 (merged 2026-09-29, after the
  0.0.7 release): a shift count above 15 zeroes each 128-bit lane, as VPSRLDQ
  does, instead of wrapping modulo 16.
