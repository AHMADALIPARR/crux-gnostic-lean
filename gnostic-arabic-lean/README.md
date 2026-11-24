# Gnostic Arabic Lean

A Lean 4 project for the Gnostic/Arabic esoteric arithmetic runtime.

The Rust source lives verbatim in `rust/abjad_matrix.rs`. The Lean mirror
lives in `GnosticArabic/AbjadMatrix.lean` and carries the same letters,
values, constants, and functions, with the Rust tests as theorems, in pure
Lean 4 with no Mathlib dependency. One test result is recorded in STATUS.md.

Build with `lake build` using the toolchain in `lean-toolchain`.
