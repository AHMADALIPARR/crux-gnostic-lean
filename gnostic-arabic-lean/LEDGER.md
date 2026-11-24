# LEDGER — Abjad Matrix LEAN-Ω Verification Record

Project: Abjad Matrix (Gnostic Arabic), LEAN-Ω restart.
Source: `rust/abjad_matrix.rs` (owner, verbatim).
Source hash (SHA-256): 64f2e2b4f6557d8339bacb16f4221453aedf057124dd304c5c635f7d9e64709e
Toolchain: Lean 4.19.0 (`leanprover/lean4:v4.19.0`), no Mathlib, core only.
Specification: `SPEC.md` (independent, written from the Rust source).

## Status (Article XV)

`GnosticArabic.AbjadMatrix` — PROVEN. Seal awaits the owner's audit.
No file is SEALED. No status is claimed beyond what the build observed.

## Build evidence (Article XII)

Clean rebuild: `rm -rf .lake && lake build`, exit 0, ~8 s, 2026-11-23.
Module `GnosticArabic.AbjadMatrix` builds with no errors and no warnings
that affect any theorem. The `#print axioms` output is in the build log.

## Ban compliance (Article II)

Grep over `GnosticArabic/AbjadMatrix.lean` for `by decide`, `sorry`,
`admit`, `sorryAx`, and `axiom` finds only:
- the header comment, which names the old version's failure and the rules;
- the words `#print axioms`, the inspection command itself.
No `decide` tactic, no `sorry`, no `admit`, no user axioms, no `sorryAx`
anywhere in code. Zero occurrences of `sorryAx` in the build log.

## Axiom inspection (Article III)

Transitive axiom closure for the sixteen substantive theorems, from
`#print axioms` at build time. Every one uses only `propext` and/or
`Quot.sound` — both inside the Article III authorized exception list.
No theorem uses `Classical.choice`. No theorem uses `sorryAx`.

- `ArabicLetter.abjadValue_injective` — [propext]
- `digitRoot_bounds` — [propext, Quot.sound]
- `digitRoot_eq_zero_iff` — [propext, Quot.sound]
- `letterSum_partition` — [propext, Quot.sound]
- `equilibrium_eq` — [propext, Quot.sound]
- `wafqVerify_eq_true` — [propext, Quot.sound]
- `wafqAllah_verify_false` — [propext, Quot.sound]
- `DecoherenceQuadrant.fromStep_period` — [propext, Quot.sound]
- `DecoherenceQuadrant.fromStep_polarity` — [propext, Quot.sound]
- `decodeProgram_append` — [propext]
- `decodeProgram_sourceCount` — [propext, Quot.sound]
- `decodeProgram_qutb` — [propext]
- `AlHamidMatrix.verifyInvariants_eq_true` — [propext, Quot.sound]
- `alHamidMatrix_invariants` — [propext, Quot.sound]
- `kenoma_iff` — [propext]
- `pleroma_iff` — [propext]

## Theorem inventory

59 theorems, 46 definitions/inductives/structures, 640 lines of Lean.
The universally quantified theorems (the proofs, not ground checks):

- Values: every Abjad value is positive and at most 1000; the value
  function is injective; polarity is Jamal exactly for the seven letters;
  every letter is Jamal or Jalal.
- Digit root: bounds 1..9 for positive inputs; zero exactly for zero;
  the digit root of a positive multiple of 9 is 9.
- Sums: sum of a concatenation is the sum of the sums; every list splits
  into Jamal and Jalal parts; equilibrium is half the total sum.
- Wafq: verification is exactly the conjunction of the eight line sums;
  every row and every column of the Allah wafq sums to 33.
- Quadrants: the quadrant repeats every 48 steps; a step is Jamal exactly
  when its residue is 0 or 1.
- Hieroglyphs: count addition is associative with zero as identity; the
  count of a concatenation is the sum of the counts; the source count is
  the number of N5 glyphs; the qutb flag is set exactly when Aa1 occurs.
- Master matrix: the invariant check is exactly the four invariant
  equalities; the master record satisfies all four.
- Kenoma/pleroma: kenoma exactly below 49, pleroma exactly at or above
  49; no time is in both.

The remaining theorems are computed instances of the definitions, proved
by `rfl` and stated as such: the Al-Hamid value 53, mirror dimension 106,
bifurcation order 7, threshold 49, Allah sum 66 and equilibrium 33, the
master constants 93/53/110/256/146/110/36/2056, digit root of 256 is 4,
pillar constants, and the kenoma/pleroma boundary at 48/49.

## The wafq finding (not weakened)

The Allah wafq rows and columns sum to 33, the main diagonal sums to 21,
the anti-diagonal sums to 45. The theorem `wafqAllah_verify_false` proves
the wafq verifies at NO constant sum: the rows force 33 while the main
diagonal forces 21. The Rust test `test_wafq_allah`, which asserts
verification, is therefore false — the same result as the Rust test run
itself (6 passed, 1 failed). The definition was not weakened to make the
test pass; the Lean development proves the test false.

## Files

- `GnosticArabic.lean` — root import.
- `GnosticArabic/AbjadMatrix.lean` — definitions and proofs.
- `SPEC.md` — independent mathematical specification.
- `LEDGER.md` — this record.
- `README.md` — what the code is and does.
- `rust/abjad_matrix.rs` — the owner's Rust source, verbatim.
- `lakefile.lean`, `lean-toolchain`, `.gitignore` — project scaffolding.
