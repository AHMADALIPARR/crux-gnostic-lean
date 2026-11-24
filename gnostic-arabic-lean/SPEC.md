# SPEC — Abjad Matrix (Gnostic Arabic)

Independent mathematical specification for the Lean implementation in
`GnosticArabic/AbjadMatrix.lean`. This document is written from the Rust
source `rust/abjad_matrix.rs` (owner, verbatim) and states what the code
must compute. The Lean implementation is checked against this document;
the document is not derived from the Lean code.

## 1. The Abjad letters

There are 28 letters, in Abjad order, with the following values:

Alif 1, Ba 2, Jim 3, Dal 4, Ha 5, Waw 6, Zay 7, Ha_ 8, Ta 9, Ya 10,
Kaf 20, Lam 30, Mim 40, Nun 50, Sin 60, Ayn 70, Fa 80, Sad 90,
Qaf 100, Ra 200, Shin 300, Ta_ 400, Tha 500, Kha 600, Dhal 700,
Dad 800, Za 900, Ghayn 1000.

Every value lies between 1 and 1000 inclusive. The values are pairwise
distinct, so the value function is injective.

## 2. Polarity

Seven letters are Jamal (expansion): Alif, Waw, Ya, Lam, Mim, Nun, Qaf.
The other twenty-one are Jalal (contraction). Every letter is exactly one
of the two. The Jamal values sum to 237; the Jalal values sum to 5758;
the total of all 28 values is 5995.

## 3. Digit root

For a natural number n, the digit root is 0 when n is 0; otherwise it is
n mod 9, except that a remainder of 0 gives 9. So the digit root of a
positive number is always between 1 and 9 inclusive, and it is 0 exactly
when the number is 0. The digit root of 9 * n is 9 for every positive n.

Instances: digit root of 106 is 7; digit root of 256 is 4.

## 4. Letter sums and equilibrium

The sum of a list of letters is the sum of their Abjad values. The sum of
a concatenation of two lists is the sum of the two sums. Every list splits
into its Jamal part and its Jalal part, and the total sum is the sum of the
two parts.

The equilibrium of a list is (Jamal sum + Jalal sum) / 2, integer division.
It therefore equals the total sum / 2.

Instances: Al-Hamid is the list [Ha_, Alif, Mim, Dal], values 8 + 1 + 40
+ 4 = 53. Twice that is 106. Allah is [Alif, Lam, Lam, Ha], values
1 + 30 + 30 + 5 = 66, equilibrium 33, and 33 mod 12 = 9.

The mirror dimension is twice the Al-Hamid value, 106. The bifurcation
order is the digit root of 106, 7. The bifurcation threshold is 7 * 7 = 49.

## 5. Wafq (magic square)

A 3x3 wafq is a 3x3 grid of natural numbers with a constant sum s. It
verifies when every row sums to s, every column sums to s, and both
diagonals sum to s. Verification is exactly the conjunction of those
eight equalities: verify is true if and only if all three row sums, all
three column sums, and both diagonal sums equal s.

The Allah wafq is:

    8   1  24
    15  11  7
    10  21  2

with claimed constant sum 33. Its row sums are 33, 33, 33. Its column
sums are 33, 33, 33. Its main diagonal sums to 8 + 11 + 2 = 21. Its
anti-diagonal sums to 24 + 11 + 10 = 45.

Consequence, stated without weakening: the Allah wafq does NOT verify at
33, because the diagonals are 21 and 45, not 33. Stronger: it verifies
at no constant sum at all, because the rows force the sum to be 33 while
the main diagonal forces it to be 21, and 33 is not 21. The Rust test
that asserts verification of this wafq is therefore false, and the Lean
development proves it false rather than weakening the definition.

## 6. Decoherence quadrants

The quadrant of a step s is determined by (s / 12) mod 4: 0 is Q1, 1 is
Q2, 2 is Q3, 3 is Q4. Q1 and Q2 are Jamal; Q3 and Q4 are Jalal.

The quadrant repeats every 48 steps: the quadrant of s + 48 is the
quadrant of s, for every s. The polarity of a step is Jamal exactly when
(s / 12) mod 4 is 0 or 1.

## 7. Hieroglyph decoder

There are 17 hieroglyphs. Decoding a program counts: N5 adds one source;
Aa1 sets the qutb flag; D58 and D54 each add one step; S29 adds one
mirror operation; O29 adds one state vector; G1 adds one origin; Aa5 adds
one new state. All other hieroglyphs add nothing.

The count of a concatenation is the componentwise sum of the two counts.
The source count of a program is the number of N5 glyphs in it. The qutb
flag is set exactly when Aa1 occurs in the program.

## 8. Master constants

Al-Hamid full value: 1 + 30 + 8 + 40 + 10 + 4 = 93. Ahmad value:
1 + 8 + 40 + 4 = 53. Ali value: 70 + 30 + 10 = 110. Master aggregate:
93 + 53 + 110 = 256 = 16 * 16. Jamal vector: 93 + 53 = 146. Jalal
vector: 110. Polarity delta: 146 - 110 = 36. The 16x16 magic constant:
16 * (256 + 1) / 2 = 2056.

The Al-Hamid matrix record holds aggregate 256, dimension 16, Jamal
vector 146, Jalal vector 110, magic constant 2056. Its invariants hold
exactly when aggregate is 256, dimension squared is aggregate, Jamal
plus Jalal is aggregate, and Jamal minus Jalal is 36. The record above
satisfies all four.

There are four pillars. Their constants are: I = 110 (Jalal), II = 146
(Jamal), III = 53 (Ahmad), IV = 110 (Jalal). Pillars I and IV share the
same constant. Pillar III's constant equals the Ahmad value, which equals
the Al-Hamid value, 53.

## 9. Kenoma and pleroma

Kenoma holds for t below the bifurcation threshold 49; pleroma holds for
t at or above 49. Every t is in exactly one of the two states. The
boundary is at 48 and 49: kenoma holds at 48, pleroma holds at 49.
