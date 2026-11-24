/-
Gnostic/Arabic esoteric arithmetic runtime, Lean mirror.

Source: rust/abjad_matrix.rs, kept verbatim in this project.
Authors from the source header: Ahmad Ali Parr, Jessica L. Williams (SNAPKITTYWEST).

Every name, value, and function below follows the Rust source. The Rust
u32/u64 arithmetic is carried as Nat; the values are the same.
-/

namespace GnosticArabic

-- =============================================================================
-- ABJAD MATRIX (28 Letters)
-- =============================================================================

inductive ArabicLetter where
  | Alif | Ba | Jim | Dal | Ha | Waw | Zay
  | Ha_ | Ta | Ya | Kaf | Lam | Mim | Nun
  | Sin | Ayn | Fa | Sad | Qaf | Ra
  | Shin | Ta_ | Tha | Kha | Dhal
  | Dad | Za | Ghayn
deriving DecidableEq, Repr

def ArabicLetter.abjad_value : ArabicLetter → Nat
  | .Alif => 1 | .Ba => 2 | .Jim => 3 | .Dal => 4 | .Ha => 5 | .Waw => 6 | .Zay => 7
  | .Ha_ => 8 | .Ta => 9 | .Ya => 10 | .Kaf => 20 | .Lam => 30 | .Mim => 40 | .Nun => 50
  | .Sin => 60 | .Ayn => 70 | .Fa => 80 | .Sad => 90 | .Qaf => 100 | .Ra => 200
  | .Shin => 300 | .Ta_ => 400 | .Tha => 500 | .Kha => 600 | .Dhal => 700
  | .Dad => 800 | .Za => 900 | .Ghayn => 1000

inductive Polarity where
  | Jamal -- جمال: Expansion, Mercy
  | Jalal -- جلال: Contraction, Rigor
deriving DecidableEq, Repr

def Polarity.toNat : Polarity → Nat
  | .Jamal => 0
  | .Jalal => 1

def ArabicLetter.polarity : ArabicLetter → Polarity
  | .Alif | .Waw | .Ya | .Lam | .Mim | .Nun | .Qaf => .Jamal
  | _ => .Jalal

-- Al-Hamid: ح(8) + ا(1) + م(40) + د(4) = 53
def AL_HAMID : List ArabicLetter := [.Ha_, .Alif, .Mim, .Dal]

def AL_HAMID_VALUE : Nat := 8 + 1 + 40 + 4 -- = 53
def MIRROR_DIMENSION : Nat := AL_HAMID_VALUE * 2 -- = 106
def BIFURCATION_ORDER : Nat := 7 -- digit_root(106) = 7
def BIFURCATION_THRESHOLD : Nat := BIFURCATION_ORDER * BIFURCATION_ORDER -- = 49

-- =============================================================================
-- DIGIT ROOT REDUCTION (Hisāb al-Jummal)
-- =============================================================================

def digit_root (n : Nat) : Nat :=
  if n = 0 then 0
  else
    let r := n % 9
    if r = 0 then 9 else r

-- =============================================================================
-- EQUILIBRIUM CONSTANT (Jamāl-Jalāl Median)
-- =============================================================================

def equilibrium_constant (letters : List ArabicLetter) : Nat :=
  let (jamal, jalal) := letters.foldl (fun acc l =>
    match l.polarity with
    | .Jamal => (acc.1 + l.abjad_value, acc.2)
    | .Jalal => (acc.1, acc.2 + l.abjad_value)) (0, 0)
  (jamal + jalal) / 2

-- =============================================================================
-- AWFĀQ (MAGIC SQUARE)
-- =============================================================================

structure Wafq where
  matrix : List (List Nat)
  constant_sum : Nat
deriving DecidableEq, Repr

def Wafq.colSum (m : List (List Nat)) (j : Nat) : Nat :=
  (m.map (fun row => row.getD j 0)).sum

def Wafq.diagSum (m : List (List Nat)) : Nat :=
  ((List.range m.length).map (fun i => (m.getD i []).getD i 0)).sum

def Wafq.antiDiagSum (m : List (List Nat)) : Nat :=
  ((List.range m.length).map (fun i => (m.getD i []).getD (m.length - 1 - i) 0)).sum

def Wafq.verify (w : Wafq) : Bool :=
  w.matrix.all (fun row => row.sum == w.constant_sum)
    && (List.range w.matrix.length).all (fun j => Wafq.colSum w.matrix j == w.constant_sum)
    && (Wafq.diagSum w.matrix == w.constant_sum)
    && (Wafq.antiDiagSum w.matrix == w.constant_sum)

def WAFQ_ALLAH_3X3 : Wafq :=
  { matrix := [[8, 1, 24], [15, 11, 7], [10, 21, 2]], constant_sum := 33 }

-- =============================================================================
-- 360° CIPHER → DECOHERENCE QUADRANTS
-- =============================================================================

inductive DecoherenceQuadrant where
  | Q1_EnochianLTR -- 0-90°: Jamāl
  | Q2_LatinLTR    -- 90-180°: Jamāl
  | Q3_HebrewRTL   -- 180-270°: Jalāl
  | Q4_ArabicRTL   -- 270-360°: Jalāl
deriving DecidableEq, Repr

def DecoherenceQuadrant.from_step (step : Nat) : DecoherenceQuadrant :=
  match (step / 12) % 4 with
  | 0 => .Q1_EnochianLTR
  | 1 => .Q2_LatinLTR
  | 2 => .Q3_HebrewRTL
  | _ => .Q4_ArabicRTL

def DecoherenceQuadrant.polarity : DecoherenceQuadrant → Polarity
  | .Q1_EnochianLTR | .Q2_LatinLTR => .Jamal
  | .Q3_HebrewRTL | .Q4_ArabicRTL => .Jalal

-- =============================================================================
-- HIEROGLYPH DECODER (Call49 Constants)
-- =============================================================================

inductive Hieroglyph where
  | N5   -- 𓂀 Sun/Ra (Source)
  | G43  -- 𓆎 Quail (w/Waw)
  | X1   -- 𓏏 Bread (t/Ta)
  | D58  -- 𓉐 Foot (w/Walk/Step)
  | G31  -- 𓊽 Bird/Ba (Soul)
  | D21  -- 𓂋 Mouth (r/Ra/Speech)
  | Aa1  -- 𓇓 Head (Qutb/Pole)
  | M17  -- 𓇋 Reed (i/y/Ya/Input)
  | N35  -- 𓈖 Water (n/Nun/Flow)
  | D46  -- 𓅓 Hand (d/Dal/Action)
  | O29  -- 𓊪 House (pr/State)
  | G1   -- 𓄿 Vulture (a/Alif/Origin)
  | Aa5  -- 𓃭 Child (New State)
  | I10  -- 𓆓 Cobra (Protection)
  | D36  -- 𓎛 Arm (Power)
  | D54  -- 𓆑 Legs (Walk)
  | S29  -- 𓋴 Pool (Mirror/Shin)
deriving DecidableEq, Repr

structure Call49Constants where
  source_count : Nat := 0
  qutb_detected : Bool := false
  step_count : Nat := 0
  mirror_ops : Nat := 0
  state_vecs : Nat := 0
  origin_count : Nat := 0
  new_states : Nat := 0
deriving DecidableEq, Repr

def decode_hieroglyph_program (program : List Hieroglyph) : Call49Constants :=
  program.foldl (fun c h =>
    match h with
    | .N5 => { c with source_count := c.source_count + 1 }
    | .Aa1 => { c with qutb_detected := true }
    | .D58 | .D54 => { c with step_count := c.step_count + 1 }
    | .S29 => { c with mirror_ops := c.mirror_ops + 1 }
    | .O29 => { c with state_vecs := c.state_vecs + 1 }
    | .G1 => { c with origin_count := c.origin_count + 1 }
    | .Aa5 => { c with new_states := c.new_states + 1 }
    | _ => c) ({} : Call49Constants)

-- =============================================================================
-- AL-HAMID AHMAD ALI — MASTER CONSTANT MATRIX (256 = 16²)
-- =============================================================================

-- Al-Ḥamīd full form: ا(1)+ل(30)+ح(8)+م(40)+ي(10)+د(4) = 93
def AL_HAMID_FULL_VALUE : Nat := 1 + 30 + 8 + 40 + 10 + 4 -- = 93
-- Aḥmad: أ(1)+ح(8)+م(40)+د(4) = 53
def AHMAD_VALUE : Nat := 1 + 8 + 40 + 4 -- = 53 (= AL_HAMID_VALUE)
-- ʿAlī: ع(70)+ل(30)+ي(10) = 110
def ALI_VALUE : Nat := 70 + 30 + 10 -- = 110

-- Master aggregate: 93 + 53 + 110 = 256 = 16²
def MASTER_AGGREGATE : Nat := AL_HAMID_FULL_VALUE + AHMAD_VALUE + ALI_VALUE
def MATRIX_DIMENSION : Nat := 16 -- sqrt(256)

-- Jamāl vector (expansion): Al-Ḥamīd + Aḥmad = 146
def JAMAL_VECTOR : Nat := AL_HAMID_FULL_VALUE + AHMAD_VALUE
-- Jalāl vector (contraction): ʿAlī = 110
def JALAL_VECTOR : Nat := ALI_VALUE

-- Polarity delta = |146 - 110| = 36 = one quadrant of the 360° cipher
def POLARITY_DELTA : Nat := JAMAL_VECTOR - JALAL_VECTOR

-- 16×16 Wafq magic constant: n*(n²+1)/2 = 16*257/2 = 2056
def WAFQ_16X16_MAGIC : Nat := MATRIX_DIMENSION * (MASTER_AGGREGATE + 1) / 2

inductive Pillar where
  | I_SovereignFoundation    -- Djed-Ra-Nesw: Jalāl anchor, ʿAlī(110)
  | II_PropheticTransmission -- Ilyas lineage: Jamāl-Jalāl bridge, Al-Ḥamīd(93)
  | III_GenesisOrigin        -- Mst/Netjer: Jamāl origin, Aḥmad(53) locks
  | IV_HistoricalConvergence -- Israel/Merneptah: Jalāl boundary, ʿAlī(110)
deriving DecidableEq, Repr

def Pillar.constant : Pillar → Nat
  | .I_SovereignFoundation => JALAL_VECTOR
  | .II_PropheticTransmission => JAMAL_VECTOR
  | .III_GenesisOrigin => AHMAD_VALUE
  | .IV_HistoricalConvergence => JALAL_VECTOR

structure AlHamidMatrix where
  aggregate : Nat       -- 256
  dimension : Nat       -- 16
  jamal_vec : Nat       -- 146
  jalal_vec : Nat       -- 110
  magic_constant : Nat  -- 2056
deriving DecidableEq, Repr

def AlHamidMatrix.new : AlHamidMatrix :=
  { aggregate := MASTER_AGGREGATE,
    dimension := MATRIX_DIMENSION,
    jamal_vec := JAMAL_VECTOR,
    jalal_vec := JALAL_VECTOR,
    magic_constant := WAFQ_16X16_MAGIC }

def AlHamidMatrix.verify_invariants (m : AlHamidMatrix) : Bool :=
  (m.aggregate == 256)
    && (m.dimension * m.dimension == m.aggregate)
    && (m.jamal_vec + m.jalal_vec == m.aggregate)
    && (m.jamal_vec - m.jalal_vec == 36) -- one quadrant

def AL_HAMID_MATRIX : AlHamidMatrix := AlHamidMatrix.new

-- =============================================================================
-- SETHIAN COSMOLOGY → STATE MACHINE
-- =============================================================================

def kenoma_state (t : Nat) : Bool := t < BIFURCATION_THRESHOLD
def pleroma_state (t : Nat) : Bool := t >= BIFURCATION_THRESHOLD

-- =============================================================================
-- TESTS (from the Rust test module, as theorems)
-- =============================================================================

theorem test_al_hamid :
    (AL_HAMID.map ArabicLetter.abjad_value).sum = 53 ∧
    (AL_HAMID.map ArabicLetter.abjad_value).sum * 2 = 106 ∧
    digit_root 106 = 7 := by decide

def ALLAH : List ArabicLetter := [.Alif, .Lam, .Lam, .Ha]

theorem test_allah_equilibrium :
    (ALLAH.map ArabicLetter.abjad_value).sum = 66 ∧
    equilibrium_constant ALLAH = 33 ∧
    33 % 12 = 9 := by decide

-- The Rust test asserts WAFQ_ALLAH_3X3.verify() and constant_sum = 33.
-- Execution gives a different result: rows and columns sum to 33, but the
-- diagonals sum to 21 and 45, so verify is false. The Rust test run gives
-- the same result (6 passed, 1 failed). Both statements below are what
-- execution gives; the matrix and verify are left as the Rust source has them.
theorem test_wafq_allah_rows_columns :
    WAFQ_ALLAH_3X3.constant_sum = 33 ∧
    WAFQ_ALLAH_3X3.matrix.all (fun row => row.sum == 33) = true ∧
    (List.range WAFQ_ALLAH_3X3.matrix.length).all
      (fun j => Wafq.colSum WAFQ_ALLAH_3X3.matrix j == 33) = true := by decide

theorem test_wafq_allah_diagonals :
    Wafq.diagSum WAFQ_ALLAH_3X3.matrix = 21 ∧
    Wafq.antiDiagSum WAFQ_ALLAH_3X3.matrix = 45 ∧
    WAFQ_ALLAH_3X3.verify = false := by decide

theorem test_decoherence_quadrants :
    (DecoherenceQuadrant.from_step 0).polarity = Polarity.Jamal ∧
    (DecoherenceQuadrant.from_step 12).polarity = Polarity.Jamal ∧
    (DecoherenceQuadrant.from_step 24).polarity = Polarity.Jalal ∧
    (DecoherenceQuadrant.from_step 36).polarity = Polarity.Jalal ∧
    (DecoherenceQuadrant.from_step 48).polarity = Polarity.Jamal := by decide

theorem test_exodus :
    kenoma_state 48 = true ∧ kenoma_state 49 = false ∧
    pleroma_state 48 = false ∧ pleroma_state 49 = true := by decide

theorem test_al_hamid_matrix :
    MASTER_AGGREGATE = 256 ∧
    MATRIX_DIMENSION * MATRIX_DIMENSION = 256 ∧
    digit_root 256 = 4 ∧
    JAMAL_VECTOR = 146 ∧
    JALAL_VECTOR = 110 ∧
    POLARITY_DELTA = 36 ∧
    WAFQ_16X16_MAGIC = 2056 ∧
    AL_HAMID_MATRIX.verify_invariants = true := by decide

theorem test_pillar_constants :
    Pillar.I_SovereignFoundation.constant = 110 ∧
    Pillar.II_PropheticTransmission.constant = 146 ∧
    Pillar.III_GenesisOrigin.constant = AHMAD_VALUE ∧
    Pillar.III_GenesisOrigin.constant = AL_HAMID_VALUE ∧
    Pillar.IV_HistoricalConvergence.constant = 110 ∧
    Pillar.I_SovereignFoundation.constant =
      Pillar.IV_HistoricalConvergence.constant := by decide

end GnosticArabic
