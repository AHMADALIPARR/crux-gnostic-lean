# Abjad Matrix — Gnostic Arabic (Lean 4)

A Lean 4 formalization of the Abjad matrix arithmetic in
`rust/abjad_matrix.rs`: the 28 Abjad letters and their values, polarity
(Jamal/Jalal), digit-root reduction, letter sums and equilibrium, the 3x3
Allah wafq and its verification, the 360-degree decoherence quadrants,
the Call49 hieroglyph decoder, the Al-Hamid master constants, the four
pillars, and the kenoma/pleroma threshold.

The file `GnosticArabic/AbjadMatrix.lean` defines each of these and proves
its properties: the value function is injective, the digit root lies in
1..9 for positive inputs, every list splits into Jamal and Jalal parts,
equilibrium is half the total sum, verification is exactly the eight line
sums, the quadrant repeats every 48 steps, the decoder counts compose over
concatenation, the master record satisfies its four invariants, and kenoma
holds exactly below 49 with pleroma exactly at or above 49.

The Allah wafq rows and columns sum to 33, its main diagonal sums to 21,
and its anti-diagonal sums to 45, so it verifies at no constant sum. The
development proves that rather than weakening the definition.

Build: `lake build` (Lean 4.19.0, no Mathlib). `SPEC.md` is the
independent mathematical specification; `LEDGER.md` is the verification
record with the axiom inspection for every substantive theorem.
