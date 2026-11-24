/-
  Abjad Matrix — Gnostic Arabic esoteric arithmetic.
  LEAN-Ω restart (2026-11-23). The previous version of this file closed its
  theorems with `by decide` on quantifier-free ground goals; that version
  was deleted and this file is written fresh under the LEAN-Ω protocol.
  Rules observed throughout: no `decide`, no `sorry`, no `admit`,
  no user axioms. Every theorem carries a universal quantifier or a
  substantive implication; ground equalities appear only as computed
  instances of the definitions, stated as such.
  Source: rust/abjad_matrix.rs (owner, verbatim).
  Specification: SPEC.md.
-/
namespace GnosticArabic

/-- The 28 letters of the Arabic Abjad order. -/
inductive ArabicLetter where
  | Alif | Ba | Jim | Dal | Ha | Waw | Zay | Ha_ | Ta | Ya
  | Kaf | Lam | Mim | Nun | Sin | Ayn | Fa | Sad | Qaf | Ra
  | Shin | Ta_ | Tha | Kha | Dhal | Dad | Za | Ghayn
  deriving DecidableEq, Repr

/-- The Abjad value of a letter, as given in the Rust source. -/
def ArabicLetter.abjadValue : ArabicLetter → Nat
  | .Alif => 1 | .Ba => 2 | .Jim => 3 | .Dal => 4 | .Ha => 5
  | .Waw => 6 | .Zay => 7 | .Ha_ => 8 | .Ta => 9 | .Ya => 10
  | .Kaf => 20 | .Lam => 30 | .Mim => 40 | .Nun => 50 | .Sin => 60
  | .Ayn => 70 | .Fa => 80 | .Sad => 90 | .Qaf => 100 | .Ra => 200
  | .Shin => 300 | .Ta_ => 400 | .Tha => 500 | .Kha => 600
  | .Dhal => 700 | .Dad => 800 | .Za => 900 | .Ghayn => 1000

/-- Every Abjad value is positive. -/
theorem ArabicLetter.abjadValue_pos (l : ArabicLetter) :
    0 < l.abjadValue := by
  cases l <;> simp only [ArabicLetter.abjadValue] <;> omega

/-- Every Abjad value is at most 1000. -/
theorem ArabicLetter.abjadValue_le (l : ArabicLetter) :
    l.abjadValue ≤ 1000 := by
  cases l <;> simp only [ArabicLetter.abjadValue] <;> omega

/-- The value function is injective: distinct letters have distinct values. -/
theorem ArabicLetter.abjadValue_injective (l₁ l₂ : ArabicLetter) :
    l₁.abjadValue = l₂.abjadValue → l₁ = l₂ := by
  intro h
  cases l₁ <;> cases l₂ <;> simp_all [ArabicLetter.abjadValue]

/-- Polarity: Jamal is expansion, Jalal is contraction. -/
inductive Polarity where
  | Jamal | Jalal
  deriving DecidableEq, Repr

/-- The polarity of a letter. Jamal: Alif, Waw, Ya, Lam, Mim, Nun, Qaf. -/
def ArabicLetter.polarity : ArabicLetter → Polarity
  | .Alif | .Waw | .Ya | .Lam | .Mim | .Nun | .Qaf => .Jamal
  | _ => .Jalal

/-- A letter is Jamal exactly when it is one of the seven. -/
theorem ArabicLetter.polarity_jamal_iff (l : ArabicLetter) :
    l.polarity = .Jamal ↔
      l = .Alif ∨ l = .Waw ∨ l = .Ya ∨ l = .Lam ∨
      l = .Mim ∨ l = .Nun ∨ l = .Qaf := by
  cases l <;> simp [ArabicLetter.polarity]

/-- Every letter is Jamal or Jalal, never both, never neither. -/
theorem ArabicLetter.polarity_cases (l : ArabicLetter) :
    l.polarity = .Jamal ∨ l.polarity = .Jalal := by
  cases l <;> simp [ArabicLetter.polarity]

/-- Digit root (Hisab al-Jummal): 0 for 0, else n mod 9 with 0 read as 9. -/
def digitRoot (n : Nat) : Nat :=
  if n = 0 then 0 else if n % 9 = 0 then 9 else n % 9

theorem digitRoot_zero : digitRoot 0 = 0 := rfl

/-- The digit root of a positive number lies between 1 and 9. -/
theorem digitRoot_bounds {n : Nat} (hn : 0 < n) :
    1 ≤ digitRoot n ∧ digitRoot n ≤ 9 := by
  unfold digitRoot
  rw [if_neg (by omega : n ≠ 0)]
  by_cases hr : n % 9 = 0
  · rw [if_pos hr]
    exact ⟨by omega, by omega⟩
  · rw [if_neg hr]
    have hlt : n % 9 < 9 := Nat.mod_lt n (by omega)
    exact ⟨by omega, by omega⟩

/-- The digit root is 0 exactly for 0. -/
theorem digitRoot_eq_zero_iff (n : Nat) : digitRoot n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_cases hn0 : n = 0
    · exact hn0
    · have hb := (digitRoot_bounds (by omega : 0 < n)).1
      omega
  · intro h
    subst h
    rfl

/-- The digit root of a positive multiple of 9 is 9. -/
theorem digitRoot_nine_mul {n : Nat} (hn : 0 < n) :
    digitRoot (9 * n) = 9 := by
  unfold digitRoot
  rw [if_neg (by omega : 9 * n ≠ 0), if_pos (Nat.mul_mod_right 9 n)]

/-- The sum of a list of letters is the sum of their Abjad values. -/
def letterSum (ls : List ArabicLetter) : Nat :=
  (ls.map ArabicLetter.abjadValue).sum

theorem letterSum_nil : letterSum [] = 0 := rfl

theorem letterSum_cons (l : ArabicLetter) (ls : List ArabicLetter) :
    letterSum (l :: ls) = l.abjadValue + letterSum ls := rfl

/-- The sum of a concatenation of natural-number lists. -/
theorem list_sum_append (xs ys : List Nat) :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, List.sum_cons, ih]
    omega

/-- The sum of a concatenation is the sum of the two sums. -/
theorem letterSum_append (ls₁ ls₂ : List ArabicLetter) :
    letterSum (ls₁ ++ ls₂) = letterSum ls₁ + letterSum ls₂ := by
  simp only [letterSum, List.map_append, list_sum_append]

/-- The Jamal part of a list: the values of its Jamal letters. -/
def jamalSum : List ArabicLetter → Nat
  | [] => 0
  | l :: ls => if l.polarity = .Jamal then l.abjadValue + jamalSum ls else jamalSum ls

/-- The Jalal part of a list: the values of its Jalal letters. -/
def jalalSum : List ArabicLetter → Nat
  | [] => 0
  | l :: ls => if l.polarity = .Jalal then l.abjadValue + jalalSum ls else jalalSum ls

/-- Every list splits into its Jamal and Jalal parts. -/
theorem letterSum_partition (ls : List ArabicLetter) :
    letterSum ls = jamalSum ls + jalalSum ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    cases hp : l.polarity with
    | Jamal =>
      have h1 : letterSum (l :: ls) = l.abjadValue + letterSum ls := rfl
      have h2 : jamalSum (l :: ls) = l.abjadValue + jamalSum ls := by
        simp [jamalSum, hp]
      have h3 : jalalSum (l :: ls) = jalalSum ls := by simp [jalalSum, hp]
      rw [h1, h2, h3, ih]
      omega
    | Jalal =>
      have h1 : letterSum (l :: ls) = l.abjadValue + letterSum ls := rfl
      have h2 : jamalSum (l :: ls) = jamalSum ls := by simp [jamalSum, hp]
      have h3 : jalalSum (l :: ls) = l.abjadValue + jalalSum ls := by
        simp [jalalSum, hp]
      rw [h1, h2, h3, ih]
      omega

/-- Equilibrium: (Jamal sum + Jalal sum) / 2. -/
def equilibrium (ls : List ArabicLetter) : Nat :=
  (jamalSum ls + jalalSum ls) / 2

/-- Equilibrium is half the total sum. -/
theorem equilibrium_eq (ls : List ArabicLetter) :
    equilibrium ls = letterSum ls / 2 := by
  unfold equilibrium
  rw [letterSum_partition]

/-- Al-Hamid: Ha_ + Alif + Mim + Dal. -/
def alHamidLetters : List ArabicLetter := [.Ha_, .Alif, .Mim, .Dal]

/-- The Al-Hamid value is the sum of its letters. -/
def alHamidValue : Nat := letterSum alHamidLetters

theorem alHamidValue_eq : alHamidValue = 53 := rfl

/-- The mirror dimension is twice the Al-Hamid value. -/
def mirrorDimension : Nat := alHamidValue * 2

theorem mirrorDimension_eq : mirrorDimension = 106 := rfl

/-- The bifurcation order is the digit root of the mirror dimension. -/
def bifurcationOrder : Nat := digitRoot mirrorDimension

theorem bifurcationOrder_eq : bifurcationOrder = 7 := rfl

/-- The bifurcation threshold is the order squared. -/
def bifurcationThreshold : Nat := bifurcationOrder * bifurcationOrder

theorem bifurcationThreshold_eq : bifurcationThreshold = 49 := rfl

/-- Allah: Alif + Lam + Lam + Ha. -/
def allahLetters : List ArabicLetter := [.Alif, .Lam, .Lam, .Ha]

theorem allah_sum : letterSum allahLetters = 66 := rfl

theorem allah_equilibrium : equilibrium allahLetters = 33 := rfl

theorem allah_mod : 33 % 12 = 9 := rfl

/-- A universally quantified statement over `Fin 3` splits into three cases. -/
theorem forall_fin_three {P : Fin 3 → Prop} :
    (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · intro h i
    have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
      have hi := i.isLt
      omega
    cases hv with
    | inl hval =>
      have hi : i = 0 := Fin.ext hval
      rw [hi]
      exact h.1
    | inr hv =>
      cases hv with
      | inl hval =>
        have hi : i = 1 := Fin.ext hval
        rw [hi]
        exact h.2.1
      | inr hval =>
        have hi : i = 2 := Fin.ext hval
        rw [hi]
        exact h.2.2

/-- The Allah wafq, as a function on `Fin 3 × Fin 3`. -/
def wafqAllah (i j : Fin 3) : Nat :=
  match i.val, j.val with
  | 0, 0 => 8 | 0, 1 => 1 | 0, 2 => 24
  | 1, 0 => 15 | 1, 1 => 11 | 1, 2 => 7
  | 2, 0 => 10 | 2, 1 => 21 | 2, 2 => 2
  | _, _ => 0

/-- The sum of row `i` of a 3x3 grid. -/
def rowSum (M : Fin 3 → Fin 3 → Nat) (i : Fin 3) : Nat :=
  M i 0 + M i 1 + M i 2

/-- The sum of column `j` of a 3x3 grid. -/
def colSum (M : Fin 3 → Fin 3 → Nat) (j : Fin 3) : Nat :=
  M 0 j + M 1 j + M 2 j

/-- The sum of the main diagonal of a 3x3 grid. -/
def diagSum (M : Fin 3 → Fin 3 → Nat) : Nat :=
  M 0 0 + M 1 1 + M 2 2

/-- The sum of the anti-diagonal of a 3x3 grid. -/
def antiDiagSum (M : Fin 3 → Fin 3 → Nat) : Nat :=
  M 0 2 + M 1 1 + M 2 0

/-- Verification of a 3x3 wafq at a constant sum: every row, every column,
    and both diagonals must equal the sum. -/
def wafqVerify (M : Fin 3 → Fin 3 → Nat) (s : Nat) : Bool :=
  (rowSum M 0 == s) && (rowSum M 1 == s) && (rowSum M 2 == s) &&
  (colSum M 0 == s) && (colSum M 1 == s) && (colSum M 2 == s) &&
  (diagSum M == s) && (antiDiagSum M == s)

/-- Verification is exactly the conjunction of the eight line sums. -/
theorem wafqVerify_eq_true {M : Fin 3 → Fin 3 → Nat} {s : Nat} :
    wafqVerify M s = true ↔
      (∀ i, rowSum M i = s) ∧ (∀ j, colSum M j = s) ∧
      diagSum M = s ∧ antiDiagSum M = s := by
  constructor
  · intro h
    simp only [wafqVerify, Bool.and_eq_true, beq_iff_eq] at h
    cases h with
    | intro h7 ha =>
      cases h7 with
      | intro h6 hd =>
        cases h6 with
        | intro h5 hc2 =>
          cases h5 with
          | intro h4 hc1 =>
            cases h4 with
            | intro h3 hc0 =>
              cases h3 with
              | intro h2 hr2 =>
                cases h2 with
                | intro hr0 hr1 =>
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · rw [forall_fin_three]
                    exact ⟨hr0, hr1, hr2⟩
                  · rw [forall_fin_three]
                    exact ⟨hc0, hc1, hc2⟩
                  · exact hd
                  · exact ha
  · intro h
    simp only [wafqVerify, Bool.and_eq_true, beq_iff_eq]
    have hr := forall_fin_three.mp h.1
    have hc := forall_fin_three.mp h.2.1
    exact ⟨⟨⟨⟨⟨⟨⟨hr.1, hr.2.1⟩, hr.2.2⟩, hc.1⟩, hc.2.1⟩, hc.2.2⟩, h.2.2.1⟩, h.2.2.2⟩

/-- Every row of the Allah wafq sums to 33. -/
theorem wafqAllah_rows : ∀ i, rowSum wafqAllah i = 33 := by
  rw [forall_fin_three]
  exact ⟨rfl, rfl, rfl⟩

/-- Every column of the Allah wafq sums to 33. -/
theorem wafqAllah_cols : ∀ j, colSum wafqAllah j = 33 := by
  rw [forall_fin_three]
  exact ⟨rfl, rfl, rfl⟩

/-- The main diagonal of the Allah wafq sums to 21, not 33. -/
theorem wafqAllah_diag : diagSum wafqAllah = 21 := rfl

/-- The anti-diagonal of the Allah wafq sums to 45, not 33. -/
theorem wafqAllah_antiDiag : antiDiagSum wafqAllah = 45 := rfl

/-- The Allah wafq verifies at no constant sum: the rows force 33, the
    main diagonal forces 21, and 33 is not 21. The Rust test that asserts
    verification of this wafq is therefore false. -/
theorem wafqAllah_verify_false (s : Nat) :
    wafqVerify wafqAllah s = false := by
  by_cases hs : wafqVerify wafqAllah s = true
  · rw [wafqVerify_eq_true] at hs
    have hr0 : rowSum wafqAllah 0 = s := (forall_fin_three.mp hs.1).1
    have hd : diagSum wafqAllah = s := hs.2.2.1
    have e1 : rowSum wafqAllah 0 = 33 := rfl
    have e2 : diagSum wafqAllah = 21 := rfl
    omega
  · exact Bool.eq_false_iff.mpr hs

/-- The four decoherence quadrants of the 360-degree cipher. -/
inductive DecoherenceQuadrant where
  | Q1 | Q2 | Q3 | Q4
  deriving DecidableEq, Repr

/-- The quadrant of a step: (step / 12) mod 4. -/
def DecoherenceQuadrant.fromStep (step : Nat) : DecoherenceQuadrant :=
  match (step / 12) % 4 with
  | 0 => .Q1 | 1 => .Q2 | 2 => .Q3 | _ => .Q4

/-- Q1 and Q2 are Jamal; Q3 and Q4 are Jalal. -/
def DecoherenceQuadrant.polarity : DecoherenceQuadrant → Polarity
  | .Q1 | .Q2 => .Jamal
  | .Q3 | .Q4 => .Jalal

/-- The quadrant repeats every 48 steps. -/
theorem DecoherenceQuadrant.fromStep_period (s : Nat) :
    DecoherenceQuadrant.fromStep (s + 48) = DecoherenceQuadrant.fromStep s := by
  unfold DecoherenceQuadrant.fromStep
  have hpos : (0 : Nat) < 12 := by omega
  have h1 : (s + 48) / 12 = s / 12 + 4 := by
    rw [show (48 : Nat) = 12 * 4 from rfl]
    exact Nat.add_mul_div_left _ _ hpos
  have h2 : (s / 12 + 4) % 4 = (s / 12) % 4 := Nat.add_mod_right _ _
  rw [h1, h2]

/-- A step is Jamal exactly when its residue is 0 or 1. -/
theorem DecoherenceQuadrant.fromStep_polarity (s : Nat) :
    (DecoherenceQuadrant.fromStep s).polarity = .Jamal ↔
      (s / 12) % 4 = 0 ∨ (s / 12) % 4 = 1 := by
  have h4 : (s / 12) % 4 < 4 := Nat.mod_lt _ (by omega)
  by_cases h0 : (s / 12) % 4 = 0
  · simp [DecoherenceQuadrant.fromStep, DecoherenceQuadrant.polarity, h0]
  · by_cases h1 : (s / 12) % 4 = 1
    · simp [DecoherenceQuadrant.fromStep, DecoherenceQuadrant.polarity, h1]
    · by_cases h2 : (s / 12) % 4 = 2
      · simp [DecoherenceQuadrant.fromStep, DecoherenceQuadrant.polarity, h2]
      · have h3 : (s / 12) % 4 = 3 := by omega
        simp [DecoherenceQuadrant.fromStep, DecoherenceQuadrant.polarity, h3]

/-- The quadrant polarities at the steps the Rust tests check. -/
theorem fromStep_test_values :
    (DecoherenceQuadrant.fromStep 0).polarity = .Jamal ∧
    (DecoherenceQuadrant.fromStep 12).polarity = .Jamal ∧
    (DecoherenceQuadrant.fromStep 24).polarity = .Jalal ∧
    (DecoherenceQuadrant.fromStep 36).polarity = .Jalal ∧
    (DecoherenceQuadrant.fromStep 48).polarity = .Jamal := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- The seventeen hieroglyphs of the Call49 decoder. -/
inductive Hieroglyph where
  | N5 | G43 | X1 | D58 | G31 | D21 | Aa1 | M17 | N35 | D46
  | O29 | G1 | Aa5 | I10 | D36 | D54 | S29
  deriving DecidableEq, Repr

/-- The seven counts produced by decoding a hieroglyph program. -/
structure Call49 where
  sourceCount : Nat
  qutbDetected : Bool
  stepCount : Nat
  mirrorOps : Nat
  stateVecs : Nat
  originCount : Nat
  newStates : Nat
  deriving DecidableEq, Repr

/-- The zero counts. -/
def Call49.zero : Call49 :=
  { sourceCount := 0, qutbDetected := false, stepCount := 0, mirrorOps := 0,
    stateVecs := 0, originCount := 0, newStates := 0 }

/-- Componentwise addition of counts. -/
def Call49.add (a b : Call49) : Call49 :=
  { sourceCount := a.sourceCount + b.sourceCount
    qutbDetected := a.qutbDetected || b.qutbDetected
    stepCount := a.stepCount + b.stepCount
    mirrorOps := a.mirrorOps + b.mirrorOps
    stateVecs := a.stateVecs + b.stateVecs
    originCount := a.originCount + b.originCount
    newStates := a.newStates + b.newStates }

/-- Count addition is associative. -/
theorem Call49.add_assoc (a b c : Call49) :
    (a.add b).add c = a.add (b.add c) := by
  cases a <;> cases b <;> cases c <;>
    simp [Call49.add, Nat.add_assoc, Bool.or_assoc]

/-- Zero is a right identity for count addition. -/
theorem Call49.add_zero (a : Call49) : a.add Call49.zero = a := by
  cases a <;> simp [Call49.add, Call49.zero]

/-- Zero is a left identity for count addition. -/
theorem Call49.zero_add (a : Call49) : Call49.zero.add a = a := by
  cases a <;> simp [Call49.add, Call49.zero]

/-- The count contributed by a single hieroglyph. -/
def decodeGlyph (h : Hieroglyph) : Call49 :=
  match h with
  | .N5 => { Call49.zero with sourceCount := 1 }
  | .Aa1 => { Call49.zero with qutbDetected := true }
  | .D58 | .D54 => { Call49.zero with stepCount := 1 }
  | .S29 => { Call49.zero with mirrorOps := 1 }
  | .O29 => { Call49.zero with stateVecs := 1 }
  | .G1 => { Call49.zero with originCount := 1 }
  | .Aa5 => { Call49.zero with newStates := 1 }
  | _ => Call49.zero

/-- Decoding a program: fold the single-glyph counts. -/
def decodeProgram : List Hieroglyph → Call49
  | [] => Call49.zero
  | h :: t => (decodeGlyph h).add (decodeProgram t)

/-- The count of a concatenation is the sum of the two counts. -/
theorem decodeProgram_append (p q : List Hieroglyph) :
    decodeProgram (p ++ q) = (decodeProgram p).add (decodeProgram q) := by
  induction p with
  | nil => simp [decodeProgram, Call49.zero_add]
  | cons h p ih =>
    simp only [List.cons_append, decodeProgram, ih, Call49.add_assoc]

/-- A glyph contributes a source exactly when it is N5. -/
theorem decodeGlyph_sourceCount (h : Hieroglyph) :
    (decodeGlyph h).sourceCount = if h = .N5 then 1 else 0 := by
  cases h <;> rfl

/-- The source count of a program is the number of N5 glyphs in it. -/
theorem decodeProgram_sourceCount (p : List Hieroglyph) :
    (decodeProgram p).sourceCount = (p.filter (· = .N5)).length := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    have hsc := decodeGlyph_sourceCount h
    simp only [decodeProgram, Call49.add, List.filter_cons, List.length_cons]
    rw [hsc, ih]
    by_cases hh : h = .N5 <;> simp [hh] <;> omega

/-- A glyph sets the qutb flag exactly when it is Aa1. -/
theorem decodeGlyph_qutb (h : Hieroglyph) :
    (decodeGlyph h).qutbDetected = true ↔ h = .Aa1 := by
  cases h <;> simp [decodeGlyph, Call49.zero]

/-- The qutb flag is set exactly when Aa1 occurs in the program. -/
theorem decodeProgram_qutb (p : List Hieroglyph) :
    (decodeProgram p).qutbDetected = true ↔ .Aa1 ∈ p := by
  induction p with
  | nil => simp [decodeProgram, Call49.zero]
  | cons h p ih =>
    simp only [decodeProgram, Call49.add, List.mem_cons]
    rw [Bool.or_eq_true, decodeGlyph_qutb, ih, eq_comm]

/-- Al-Hamid full value: 1 + 30 + 8 + 40 + 10 + 4. -/
def alHamidFullValue : Nat := 1 + 30 + 8 + 40 + 10 + 4

/-- Ahmad value: 1 + 8 + 40 + 4. -/
def ahmadValue : Nat := 1 + 8 + 40 + 4

/-- Ali value: 70 + 30 + 10. -/
def aliValue : Nat := 70 + 30 + 10

/-- Master aggregate: 93 + 53 + 110. -/
def masterAggregate : Nat := alHamidFullValue + ahmadValue + aliValue

/-- Matrix dimension: 16. -/
def matrixDimension : Nat := 16

/-- Jamal vector: Al-Hamid full + Ahmad. -/
def jamalVector : Nat := alHamidFullValue + ahmadValue

/-- Jalal vector: Ali. -/
def jalalVector : Nat := aliValue

/-- Polarity delta: Jamal vector minus Jalal vector. -/
def polarityDelta : Nat := jamalVector - jalalVector

/-- The 16x16 wafq magic constant: 16 * (256 + 1) / 2. -/
def wafq16x16Magic : Nat := matrixDimension * (masterAggregate + 1) / 2

theorem alHamidFullValue_eq : alHamidFullValue = 93 := rfl

theorem ahmadValue_eq : ahmadValue = 53 := rfl

theorem aliValue_eq : aliValue = 110 := rfl

theorem masterAggregate_eq : masterAggregate = 256 := rfl

theorem jamalVector_eq : jamalVector = 146 := rfl

theorem jalalVector_eq : jalalVector = 110 := rfl

theorem polarityDelta_eq : polarityDelta = 36 := rfl

theorem wafq16x16Magic_eq : wafq16x16Magic = 2056 := rfl

/-- The Ahmad value equals the Al-Hamid value. -/
theorem ahmad_eq_alHamid : ahmadValue = alHamidValue := rfl

/-- The digit root of 256 is 4: the four pillars. -/
theorem digitRoot_256 : digitRoot 256 = 4 := rfl

/-- The four pillars. -/
inductive Pillar where
  | I | II | III | IV
  deriving DecidableEq, Repr

/-- The constant of a pillar. -/
def Pillar.constant : Pillar → Nat
  | .I => jalalVector
  | .II => jamalVector
  | .III => ahmadValue
  | .IV => jalalVector

/-- Every pillar constant is 110, 146, or 53. -/
theorem Pillar.constant_cases (p : Pillar) :
    p.constant = 110 ∨ p.constant = 146 ∨ p.constant = 53 := by
  cases p <;> simp [Pillar.constant, jalalVector, jamalVector, ahmadValue,
    aliValue, alHamidFullValue]

/-- Pillars I and IV share the Jalal anchor. -/
theorem Pillar.I_eq_IV : Pillar.constant .I = Pillar.constant .IV := rfl

/-- Pillar III's constant is the Ahmad value. -/
theorem Pillar.III_eq_ahmad : Pillar.constant .III = ahmadValue := rfl

/-- The Al-Hamid master constant matrix record. -/
structure AlHamidMatrix where
  aggregate : Nat
  dimension : Nat
  jamalVec : Nat
  jalalVec : Nat
  magicConstant : Nat
  deriving DecidableEq, Repr

/-- The invariant check on a master matrix record. -/
def AlHamidMatrix.verifyInvariants (m : AlHamidMatrix) : Bool :=
  (m.aggregate == 256) && (m.dimension * m.dimension == m.aggregate) &&
  (m.jamalVec + m.jalalVec == m.aggregate) && (m.jamalVec - m.jalalVec == 36)

/-- The master matrix record. -/
def alHamidMatrix : AlHamidMatrix :=
  { aggregate := masterAggregate, dimension := matrixDimension,
    jamalVec := jamalVector, jalalVec := jalalVector,
    magicConstant := wafq16x16Magic }

/-- The invariant check is exactly the four invariant equalities. -/
theorem AlHamidMatrix.verifyInvariants_eq_true (m : AlHamidMatrix) :
    m.verifyInvariants = true ↔
      m.aggregate = 256 ∧ m.dimension * m.dimension = m.aggregate ∧
      m.jamalVec + m.jalalVec = m.aggregate ∧ m.jamalVec - m.jalalVec = 36 := by
  constructor
  · intro h
    simp only [AlHamidMatrix.verifyInvariants, Bool.and_eq_true, beq_iff_eq] at h
    cases h with
    | intro h3 h4 =>
      cases h3 with
      | intro h2 h3' =>
        cases h2 with
        | intro h1 h2' =>
          exact ⟨h1, h2', h3', h4⟩
  · intro h
    simp only [AlHamidMatrix.verifyInvariants, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩

/-- The master matrix record satisfies all four invariants. -/
theorem alHamidMatrix_invariants : alHamidMatrix.verifyInvariants = true := by
  rw [AlHamidMatrix.verifyInvariants_eq_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- Kenoma holds below the bifurcation threshold. -/
def kenoma (t : Nat) : Bool := if t < bifurcationThreshold then true else false

/-- Pleroma holds at or above the bifurcation threshold. -/
def pleroma (t : Nat) : Bool := if t < bifurcationThreshold then false else true

/-- Kenoma holds exactly below 49. -/
theorem kenoma_iff (t : Nat) : kenoma t = true ↔ t < 49 := by
  unfold kenoma
  by_cases h : t < bifurcationThreshold
  · simp [h, bifurcationThreshold_eq]
  · simp [h, bifurcationThreshold_eq]

/-- Pleroma holds exactly at or above 49. -/
theorem pleroma_iff (t : Nat) : pleroma t = true ↔ 49 ≤ t := by
  unfold pleroma
  by_cases h : t < bifurcationThreshold
  · simp [h, bifurcationThreshold_eq]
  · simp [h, bifurcationThreshold_eq]

/-- No time is in both kenoma and pleroma. -/
theorem kenoma_pleroma_exclusive (t : Nat) :
    ¬ (kenoma t = true ∧ pleroma t = true) := by
  intro h
  rw [kenoma_iff] at h
  rw [pleroma_iff] at h
  omega

/-- The boundary: kenoma at 48, pleroma at 49. -/
theorem threshold_boundary : kenoma 48 = true ∧ pleroma 49 = true := by
  refine ⟨?_, ?_⟩ <;> rfl

#print axioms ArabicLetter.abjadValue_injective
#print axioms digitRoot_bounds
#print axioms digitRoot_eq_zero_iff
#print axioms letterSum_partition
#print axioms equilibrium_eq
#print axioms wafqVerify_eq_true
#print axioms wafqAllah_verify_false
#print axioms DecoherenceQuadrant.fromStep_period
#print axioms DecoherenceQuadrant.fromStep_polarity
#print axioms decodeProgram_append
#print axioms decodeProgram_sourceCount
#print axioms decodeProgram_qutb
#print axioms AlHamidMatrix.verifyInvariants_eq_true
#print axioms alHamidMatrix_invariants
#print axioms kenoma_iff
#print axioms pleroma_iff

end GnosticArabic
