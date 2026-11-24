# STATUS

## Project
- Lean project at `gnostic-arabic-lean`, staged locally, not pushed, no repo name set.
- Toolchain: Lean v4.19.0 (`leanprover/lean4:v4.19.0`).
- No Mathlib dependency. Pure Lean 4.
- `lake build` exit 0, 2026-11-23.

## Files
- `rust/abjad_matrix.rs`: the pasted Rust file, verbatim. SHA-256 64f2e2b4f6557d8339bacb16f4221453aedf057124dd304c5c635f7d9e64709e.
- `GnosticArabic/AbjadMatrix.lean`: Lean mirror of the Rust file. Same names, values, constants, and functions. Rust u32/u64 arithmetic is carried as Nat.
- `GnosticArabic.lean`: root module, imports `GnosticArabic.AbjadMatrix`.
- `lakefile.lean`, `lean-toolchain`, `README.md`.

## Rust test run
- `rustc 1.99.0 --test` on the verbatim file: 6 passed, 1 failed.
- Failing test: `test_wafq_allah`, assertion `WAFQ_ALLAH_3X3.verify()`.

## Lean mirror, wafq
- Rows and columns of WAFQ_ALLAH_3X3 sum to 33. Constant sum is 33.
- Main diagonal sums to 21 (8 + 11 + 2). Anti-diagonal sums to 45 (24 + 11 + 10).
- `WAFQ_ALLAH_3X3.verify` is false.
- The Lean file states these as `test_wafq_allah_rows_columns` and `test_wafq_allah_diagonals`. The matrix and the verify function are left as the Rust source has them.
- The other six Rust tests are mirrored as stated and pass: `test_al_hamid`, `test_allah_equilibrium`, `test_decoherence_quadrants`, `test_exodus`, `test_al_hamid_matrix`, `test_pillar_constants`.
