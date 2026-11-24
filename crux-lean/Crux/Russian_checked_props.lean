-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Properties of the checked Russian parser (Crux/Russian_checked.lean).
-- No `sorry`, no new axioms; `#print axioms` output is at the end.

import Crux.Russian_checked

namespace Crux
namespace RussianCheckedProps

/-! ## Reach: a successful parse returns a position of at least `lo` -/

structure Reach {α : Type} (lo : Nat) (r : Except String (α × Nat)) : Prop where
  out : ∀ v q, r = .ok (v, q) → lo ≤ q

theorem Reach.error {α : Type} {lo : Nat} {e : String} : Reach (α := α) lo (.error e) :=
  ⟨fun _ _ h => by cases h⟩

theorem Reach.ok {α : Type} {lo q : Nat} {v : α} (h : lo ≤ q) : Reach lo (.ok (v, q)) :=
  ⟨fun _ _ h' => by cases h'; exact h⟩

theorem Reach.bind {α β : Type} {lo lo1 : Nat} {m : Except String (α × Nat)}
    {f : α × Nat → Except String (β × Nat)}
    (hm : Reach lo1 m) (hf : ∀ a q, lo1 ≤ q → Reach lo (f (a, q))) :
    Reach lo (m >>= f) := by
  refine ⟨fun v q h => ?_⟩
  cases hm' : m with
  | error e => rw [hm'] at h; cases h
  | ok x =>
    rw [hm'] at h
    obtain ⟨a, q1⟩ := x
    exact (hf a q1 (hm.out a q1 hm')).out v q h

theorem Reach.bindExpect {β : Type} {lo pos : Nat} {tokens : List Token} {e : Token}
    {f : Nat → Except String (β × Nat)} (hf : Reach lo (f (pos + 1))) :
    Reach lo (expectTok tokens pos e >>= f) := by
  refine ⟨fun v q h => ?_⟩
  unfold expectTok at h
  by_cases hc : (peekTok tokens pos == e) = true
  · simp only [hc, if_true] at h; exact hf.out v q h
  · simp only [hc] at h; cases h

theorem Reach.mono {α : Type} {lo lo' : Nat} {r : Except String (α × Nat)}
    (h : lo ≤ lo') (hr : Reach lo' r) : Reach lo r :=
  ⟨fun v q hq => Nat.le_trans h (hr.out v q hq)⟩

theorem Reach.bare {lo pos : Nat} {lhs : Term} (h : lo ≤ pos) :
    Reach lo (bareTermFormula lhs pos) := by
  unfold bareTermFormula
  split
  · exact Reach.ok h
  · exact Reach.error

set_option hygiene false in
/-- Goal-directed `Reach` prover over the parser bodies; uses hypotheses
`h1` ... `h15` (the progress facts at the previous fuel). -/
macro "reach_auto" : tactic => `(tactic|
  repeat' (first
    | with_reducible exact Reach.error
    | (with_reducible apply Reach.ok; omega)
    | (with_reducible apply Reach.bare; omega)
    | (with_reducible refine Reach.bindExpect ?_)
    | with_reducible refine Reach.bind Reach.error ?_
    | with_reducible refine Reach.bind (Reach.ok (Nat.le_refl _)) ?_
    | with_reducible refine Reach.bind (h1 _ _) ?_
    | with_reducible refine Reach.bind (h2 _ _ _) ?_
    | with_reducible refine Reach.bind (h3 _ _) ?_
    | with_reducible refine Reach.bind (h4 _ _ _) ?_
    | with_reducible refine Reach.bind (h5 _ _ _ _) ?_
    | with_reducible refine Reach.bind (h6 _ _) ?_
    | with_reducible refine Reach.bind (h7 _ _ _) ?_
    | with_reducible refine Reach.bind (h8 _ _) ?_
    | with_reducible refine Reach.bind (h9 _ _) ?_
    | with_reducible refine Reach.bind (h10 _ _ _) ?_
    | with_reducible refine Reach.bind (h11 _ _) ?_
    | with_reducible refine Reach.bind (h12 _ _ _) ?_
    | with_reducible refine Reach.bind (h13 _ _) ?_
    | with_reducible refine Reach.bind (h14 _ _ _) ?_
    | with_reducible refine Reach.bind (h15 _ _) ?_
    | refine Reach.bind Reach.error ?_
    | (refine ⟨fun _ _ h => ?_⟩; cases h)
    | (intro _ _ _)
    | dsimp only
    | split
    | with_reducible exact Reach.mono (by omega) (h1 _ _)
    | with_reducible exact Reach.mono (by omega) (h2 _ _ _)
    | with_reducible exact Reach.mono (by omega) (h3 _ _)
    | with_reducible exact Reach.mono (by omega) (h4 _ _ _)
    | with_reducible exact Reach.mono (by omega) (h5 _ _ _ _)
    | with_reducible exact Reach.mono (by omega) (h6 _ _)
    | with_reducible exact Reach.mono (by omega) (h7 _ _ _)
    | with_reducible exact Reach.mono (by omega) (h8 _ _)
    | with_reducible exact Reach.mono (by omega) (h9 _ _)
    | with_reducible exact Reach.mono (by omega) (h10 _ _ _)
    | with_reducible exact Reach.mono (by omega) (h11 _ _)
    | with_reducible exact Reach.mono (by omega) (h12 _ _ _)
    | with_reducible exact Reach.mono (by omega) (h13 _ _)
    | with_reducible exact Reach.mono (by omega) (h14 _ _ _)
    | with_reducible exact Reach.mono (by omega) (h15 _ _)))

/-- Every parser that must consume input returns a position strictly past
its start; the loops (`...Loop`, `parseSortArrows`) never move backwards.
Together: no successful parse, and no successful repetition, makes zero
progress except a loop that stops at once. -/
theorem progress : ∀ n : Nat,
    (∀ tokens pos, Reach (pos + 1) (parseSort tokens pos n)) ∧
    (∀ tokens base pos, Reach pos (parseSortArrows tokens base pos n)) ∧
    (∀ tokens pos, Reach (pos + 1) (parseTerm tokens pos n)) ∧
    (∀ tokens pos mp, Reach (pos + 1) (parseTermBinop tokens pos mp n)) ∧
    (∀ tokens lhs pos mp, Reach pos (parseTermBinopLoop tokens lhs pos mp n)) ∧
    (∀ tokens pos, Reach (pos + 1) (parseTermAtom tokens pos n)) ∧
    (∀ tokens elems pos, Reach (pos + 1) (parseTupleRest tokens elems pos n)) ∧
    (∀ tokens pos, Reach (pos + 1) (parseFormula tokens pos n)) ∧
    (∀ tokens pos, Reach (pos + 1) (parseFormulaImplies tokens pos n)) ∧
    (∀ tokens lhs pos, Reach pos (parseFormulaImpliesLoop tokens lhs pos n)) ∧
    (∀ tokens pos, Reach (pos + 1) (parseFormulaOr tokens pos n)) ∧
    (∀ tokens lhs pos, Reach pos (parseFormulaOrLoop tokens lhs pos n)) ∧
    (∀ tokens pos, Reach (pos + 1) (parseFormulaAnd tokens pos n)) ∧
    (∀ tokens lhs pos, Reach pos (parseFormulaAndLoop tokens lhs pos n)) ∧
    (∀ tokens pos, Reach (pos + 1) (parseFormulaAtom tokens pos n)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      intros <;> exact Reach.error
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp only [parseSort, parseSortArrows, parseTerm, parseTermBinop, parseTermBinopLoop,
        parseTermAtom, parseTupleRest, parseFormula, parseFormulaImplies,
        parseFormulaImpliesLoop, parseFormulaOr, parseFormulaOrLoop, parseFormulaAnd,
        parseFormulaAndLoop, parseFormulaAtom, advanceTok] <;>
      reach_auto

/-! ## Fuel monotonicity -/

/-- `Mono a b`: whenever `a` succeeds, `b` succeeds with the same value. -/
structure Mono {α : Type} (a b : Except String α) : Prop where
  out : ∀ r, a = .ok r → b = .ok r

theorem Mono.refl {α : Type} {a : Except String α} : Mono a a := ⟨fun _ h => h⟩

theorem Mono.error {α : Type} {e : String} {b : Except String α} : Mono (.error e) b :=
  ⟨fun _ h => by cases h⟩

theorem Mono.trans {α : Type} {a b c : Except String α} (h1 : Mono a b) (h2 : Mono b c) :
    Mono a c := ⟨fun r h => h2.out r (h1.out r h)⟩

theorem Mono.bind {α β : Type} {m m' : Except String α} {f f' : α → Except String β}
    (hm : Mono m m') (hf : ∀ x, Mono (f x) (f' x)) : Mono (m >>= f) (m' >>= f') := by
  refine ⟨fun r h => ?_⟩
  cases hm1 : m with
  | error e => rw [hm1] at h; cases h
  | ok x =>
    rw [hm1] at h
    have h2 := hm.out x hm1
    rw [h2]
    exact (hf x).out r h

theorem Mono.ite {α : Type} {c : Prop} [Decidable c] {a a' b b' : Except String α}
    (h1 : c → Mono a a') (h2 : ¬c → Mono b b') :
    Mono (if c then a else b) (if c then a' else b') := by
  by_cases hc : c
  · simp only [hc, if_true]; exact h1 hc
  · simp only [hc, if_false]; exact h2 hc

/-- More fuel never changes a successful parse: success with fuel `n`
gives the same value and position with fuel `n + 1`. -/
theorem fuel_mono_succ : ∀ n : Nat,
    (∀ tokens pos, Mono (parseSort tokens pos n) (parseSort tokens pos (n + 1))) ∧
    (∀ tokens base pos, Mono (parseSortArrows tokens base pos n) (parseSortArrows tokens base pos (n + 1))) ∧
    (∀ tokens pos, Mono (parseTerm tokens pos n) (parseTerm tokens pos (n + 1))) ∧
    (∀ tokens pos mp, Mono (parseTermBinop tokens pos mp n) (parseTermBinop tokens pos mp (n + 1))) ∧
    (∀ tokens lhs pos mp, Mono (parseTermBinopLoop tokens lhs pos mp n) (parseTermBinopLoop tokens lhs pos mp (n + 1))) ∧
    (∀ tokens pos, Mono (parseTermAtom tokens pos n) (parseTermAtom tokens pos (n + 1))) ∧
    (∀ tokens elems pos, Mono (parseTupleRest tokens elems pos n) (parseTupleRest tokens elems pos (n + 1))) ∧
    (∀ tokens pos, Mono (parseFormula tokens pos n) (parseFormula tokens pos (n + 1))) ∧
    (∀ tokens pos, Mono (parseFormulaImplies tokens pos n) (parseFormulaImplies tokens pos (n + 1))) ∧
    (∀ tokens lhs pos, Mono (parseFormulaImpliesLoop tokens lhs pos n) (parseFormulaImpliesLoop tokens lhs pos (n + 1))) ∧
    (∀ tokens pos, Mono (parseFormulaOr tokens pos n) (parseFormulaOr tokens pos (n + 1))) ∧
    (∀ tokens lhs pos, Mono (parseFormulaOrLoop tokens lhs pos n) (parseFormulaOrLoop tokens lhs pos (n + 1))) ∧
    (∀ tokens pos, Mono (parseFormulaAnd tokens pos n) (parseFormulaAnd tokens pos (n + 1))) ∧
    (∀ tokens lhs pos, Mono (parseFormulaAndLoop tokens lhs pos n) (parseFormulaAndLoop tokens lhs pos (n + 1))) ∧
    (∀ tokens pos, Mono (parseFormulaAtom tokens pos n) (parseFormulaAtom tokens pos (n + 1))) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      intros <;> exact Mono.error
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      (first
        | rw [parseSort.eq_2, parseSort.eq_2]
        | rw [parseSortArrows.eq_2, parseSortArrows.eq_2]
        | rw [parseTerm.eq_2, parseTerm.eq_2]
        | rw [parseTermBinop.eq_2, parseTermBinop.eq_2]
        | rw [parseTermBinopLoop.eq_2, parseTermBinopLoop.eq_2]
        | rw [parseTermAtom.eq_2, parseTermAtom.eq_2]
        | rw [parseTupleRest.eq_2, parseTupleRest.eq_2]
        | rw [parseFormula.eq_2, parseFormula.eq_2]
        | rw [parseFormulaImplies.eq_2, parseFormulaImplies.eq_2]
        | rw [parseFormulaImpliesLoop.eq_2, parseFormulaImpliesLoop.eq_2]
        | rw [parseFormulaOr.eq_2, parseFormulaOr.eq_2]
        | rw [parseFormulaOrLoop.eq_2, parseFormulaOrLoop.eq_2]
        | rw [parseFormulaAnd.eq_2, parseFormulaAnd.eq_2]
        | rw [parseFormulaAndLoop.eq_2, parseFormulaAndLoop.eq_2]
        | rw [parseFormulaAtom.eq_2, parseFormulaAtom.eq_2]) <;>
      (try simp only [advanceTok]) <;>
      repeat' (first
        | with_reducible exact Mono.refl
        | with_reducible exact Mono.error
        | with_reducible exact h1 _ _
        | with_reducible exact h2 _ _ _
        | with_reducible exact h3 _ _
        | with_reducible exact h4 _ _ _
        | with_reducible exact h5 _ _ _ _
        | with_reducible exact h6 _ _
        | with_reducible exact h7 _ _ _
        | with_reducible exact h8 _ _
        | with_reducible exact h9 _ _
        | with_reducible exact h10 _ _ _
        | with_reducible exact h11 _ _
        | with_reducible exact h12 _ _ _
        | with_reducible exact h13 _ _
        | with_reducible exact h14 _ _ _
        | with_reducible exact h15 _ _
        | with_reducible refine Mono.ite (fun _ => ?_) (fun _ => ?_)
        | with_reducible refine Mono.bind (h1 _ _) ?_
        | with_reducible refine Mono.bind (h2 _ _ _) ?_
        | with_reducible refine Mono.bind (h3 _ _) ?_
        | with_reducible refine Mono.bind (h4 _ _ _) ?_
        | with_reducible refine Mono.bind (h5 _ _ _ _) ?_
        | with_reducible refine Mono.bind (h6 _ _) ?_
        | with_reducible refine Mono.bind (h7 _ _ _) ?_
        | with_reducible refine Mono.bind (h8 _ _) ?_
        | with_reducible refine Mono.bind (h9 _ _) ?_
        | with_reducible refine Mono.bind (h10 _ _ _) ?_
        | with_reducible refine Mono.bind (h11 _ _) ?_
        | with_reducible refine Mono.bind (h12 _ _ _) ?_
        | with_reducible refine Mono.bind (h13 _ _) ?_
        | with_reducible refine Mono.bind (h14 _ _ _) ?_
        | with_reducible refine Mono.bind (h15 _ _) ?_
        | with_reducible refine Mono.bind Mono.refl ?_
        | (intro _)
        | dsimp only
        | split)

/-! ## Fuel exhaustion: fuel `0` is a defined failure, never an AST -/

theorem parseSort_fuel_zero (tokens : List Token) (pos : Nat) :
    parseSort tokens pos 0 = .error "recursion limit reached in parse_sort" := rfl

theorem parseSortArrows_fuel_zero (tokens : List Token) (base : «Sort») (pos : Nat) :
    parseSortArrows tokens base pos 0 = .error "recursion limit reached in parse_sort" := rfl

theorem parseTerm_fuel_zero (tokens : List Token) (pos : Nat) :
    parseTerm tokens pos 0 = .error "recursion limit reached in parse_term" := rfl

theorem parseTermBinop_fuel_zero (tokens : List Token) (pos : Nat) (mp : Nat) :
    parseTermBinop tokens pos mp 0 = .error "recursion limit reached in parse_term_binop" := rfl

theorem parseTermBinopLoop_fuel_zero (tokens : List Token) (lhs : Term) (pos : Nat) (mp : Nat) :
    parseTermBinopLoop tokens lhs pos mp 0 = .error "recursion limit reached in parse_term_binop" := rfl

theorem parseTermAtom_fuel_zero (tokens : List Token) (pos : Nat) :
    parseTermAtom tokens pos 0 = .error "recursion limit reached in parse_term_atom" := rfl

theorem parseTupleRest_fuel_zero (tokens : List Token) (elems : List Term) (pos : Nat) :
    parseTupleRest tokens elems pos 0 = .error "recursion limit reached in parse_tuple" := rfl

theorem parseFormula_fuel_zero (tokens : List Token) (pos : Nat) :
    parseFormula tokens pos 0 = .error "recursion limit reached in parse_formula" := rfl

theorem parseFormulaImplies_fuel_zero (tokens : List Token) (pos : Nat) :
    parseFormulaImplies tokens pos 0 = .error "recursion limit reached in parse_formula_implies" := rfl

theorem parseFormulaImpliesLoop_fuel_zero (tokens : List Token) (lhs : Formula) (pos : Nat) :
    parseFormulaImpliesLoop tokens lhs pos 0 = .error "recursion limit reached in parse_formula_implies" := rfl

theorem parseFormulaOr_fuel_zero (tokens : List Token) (pos : Nat) :
    parseFormulaOr tokens pos 0 = .error "recursion limit reached in parse_formula_or" := rfl

theorem parseFormulaOrLoop_fuel_zero (tokens : List Token) (lhs : Formula) (pos : Nat) :
    parseFormulaOrLoop tokens lhs pos 0 = .error "recursion limit reached in parse_formula_or" := rfl

theorem parseFormulaAnd_fuel_zero (tokens : List Token) (pos : Nat) :
    parseFormulaAnd tokens pos 0 = .error "recursion limit reached in parse_formula_and" := rfl

theorem parseFormulaAndLoop_fuel_zero (tokens : List Token) (lhs : Formula) (pos : Nat) :
    parseFormulaAndLoop tokens lhs pos 0 = .error "recursion limit reached in parse_formula_and" := rfl

theorem parseFormulaAtom_fuel_zero (tokens : List Token) (pos : Nat) :
    parseFormulaAtom tokens pos 0 = .error "recursion limit reached in parse_formula_atom" := rfl

theorem parseState_fuel_zero (tokens : List Token) (pos : Nat) :
    parseState tokens pos 0 = .error "recursion limit reached in parse_state" := rfl

theorem parseRussianForm_fuel_zero (tokens : List Token) (pos : Nat) :
    parseRussianForm tokens pos 0 = .error "recursion limit reached in parse_russian_form" := rfl

/-! ## Determinism: equal inputs and fuel give equal results -/

theorem parse_russian_deterministic (s t : String) (h : s = t) :
    parse_russian s = parse_russian t := by rw [h]
theorem parse_formula_deterministic (s t : String) (h : s = t) :
    parse_formula s = parse_formula t := by rw [h]
theorem parse_term_deterministic (s t : String) (h : s = t) :
    parse_term s = parse_term t := by rw [h]
theorem parseFormula_deterministic (tokens : List Token) (pos fuel : Nat)
    (r₁ r₂ : Except String (Formula × Nat))
    (h₁ : parseFormula tokens pos fuel = r₁) (h₂ : parseFormula tokens pos fuel = r₂) :
    r₁ = r₂ := h₁ ▸ h₂ ▸ rfl

/-! ## Fuel monotonicity for any amount of extra fuel -/

theorem parseFormula_fuel_mono {n m : Nat} (h : n ≤ m) (tokens : List Token) (pos : Nat) :
    Mono (parseFormula tokens pos n) (parseFormula tokens pos m) := by
  induction h with
  | refl => exact Mono.refl
  | step _ ih => exact ih.trans ((fuel_mono_succ _).2.2.2.2.2.2.2.1 tokens pos)

theorem parseTerm_fuel_mono {n m : Nat} (h : n ≤ m) (tokens : List Token) (pos : Nat) :
    Mono (parseTerm tokens pos n) (parseTerm tokens pos m) := by
  induction h with
  | refl => exact Mono.refl
  | step _ ih => exact ih.trans ((fuel_mono_succ _).2.2.1 tokens pos)

theorem parseSort_fuel_mono {n m : Nat} (h : n ≤ m) (tokens : List Token) (pos : Nat) :
    Mono (parseSort tokens pos n) (parseSort tokens pos m) := by
  induction h with
  | refl => exact Mono.refl
  | step _ ih => exact ih.trans ((fuel_mono_succ _).1 tokens pos)

theorem parseState_fuel_mono_succ (n : Nat) (tokens : List Token) (pos : Nat) :
    Mono (parseState tokens pos n) (parseState tokens pos (n + 1)) := by
  cases n with
  | zero => exact Mono.error
  | succ n => exact Mono.refl

theorem parseRussianForm_fuel_mono_succ (n : Nat) (tokens : List Token) (pos : Nat) :
    Mono (parseRussianForm tokens pos n) (parseRussianForm tokens pos (n + 1)) := by
  cases n with
  | zero => exact Mono.error
  | succ n =>
    have hf := (fuel_mono_succ n).2.2.2.2.2.2.2.1
    have ht := (fuel_mono_succ n).2.2.1
    have hs := parseState_fuel_mono_succ n
    rw [parseRussianForm.eq_2, parseRussianForm.eq_2]
    (try simp only [advanceTok])
    repeat' (first
      | with_reducible exact Mono.refl
      | with_reducible exact Mono.error
      | with_reducible refine Mono.bind (hf _ _) ?_
      | with_reducible refine Mono.bind (ht _ _) ?_
      | with_reducible refine Mono.bind (hs _ _) ?_
      | with_reducible refine Mono.bind Mono.refl ?_
      | (intro _)
      | dsimp only
      | split)

theorem parseRussianForm_fuel_mono {n m : Nat} (h : n ≤ m) (tokens : List Token) (pos : Nat) :
    Mono (parseRussianForm tokens pos n) (parseRussianForm tokens pos m) := by
  induction h with
  | refl => exact Mono.refl
  | step _ ih => exact ih.trans (parseRussianForm_fuel_mono_succ _ tokens pos)

/-! ## No zero-progress repetition

A loop either stops at once (returning its accumulator and position
unchanged) or consumes at least an operator and an operand. -/

theorem Reach.of {α : Type} {lo q : Nat} {v : α} {r : Except String (α × Nat)}
    (hr : Reach lo r) (h : r = .ok (v, q)) : lo ≤ q := hr.out v q h

theorem parseFormulaAndLoop_no_zero_progress (n : Nat) (tokens : List Token) (lhs : Formula) (pos : Nat) (v : Formula) (q : Nat)
    (h : parseFormulaAndLoop tokens lhs pos n = .ok (v, q)) : (v = lhs ∧ q = pos) ∨ pos + 2 ≤ q := by
  cases n with
  | zero => cases h
  | succ n =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := progress n
    rw [parseFormulaAndLoop.eq_2] at h
    simp only [advanceTok] at h
    repeat' split at h
    all_goals first
      | (left; cases h; exact ⟨rfl, rfl⟩)
      | (right; refine Reach.of ?_ h; reach_auto)

theorem parseFormulaOrLoop_no_zero_progress (n : Nat) (tokens : List Token) (lhs : Formula) (pos : Nat) (v : Formula) (q : Nat)
    (h : parseFormulaOrLoop tokens lhs pos n = .ok (v, q)) : (v = lhs ∧ q = pos) ∨ pos + 2 ≤ q := by
  cases n with
  | zero => cases h
  | succ n =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := progress n
    rw [parseFormulaOrLoop.eq_2] at h
    simp only [advanceTok] at h
    repeat' split at h
    all_goals first
      | (left; cases h; exact ⟨rfl, rfl⟩)
      | (right; refine Reach.of ?_ h; reach_auto)

theorem parseFormulaImpliesLoop_no_zero_progress (n : Nat) (tokens : List Token) (lhs : Formula) (pos : Nat) (v : Formula) (q : Nat)
    (h : parseFormulaImpliesLoop tokens lhs pos n = .ok (v, q)) : (v = lhs ∧ q = pos) ∨ pos + 2 ≤ q := by
  cases n with
  | zero => cases h
  | succ n =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := progress n
    rw [parseFormulaImpliesLoop.eq_2] at h
    simp only [advanceTok] at h
    repeat' split at h
    all_goals first
      | (left; cases h; exact ⟨rfl, rfl⟩)
      | (right; refine Reach.of ?_ h; reach_auto)

theorem parseTermBinopLoop_no_zero_progress (n : Nat) (tokens : List Token) (lhs : Term) (pos : Nat) (mp : Nat) (v : Term) (q : Nat)
    (h : parseTermBinopLoop tokens lhs pos mp n = .ok (v, q)) : (v = lhs ∧ q = pos) ∨ pos + 2 ≤ q := by
  cases n with
  | zero => cases h
  | succ n =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := progress n
    rw [parseTermBinopLoop.eq_2] at h
    simp only [advanceTok] at h
    repeat' split at h
    all_goals first
      | (left; cases h; exact ⟨rfl, rfl⟩)
      | (right; refine Reach.of ?_ h; reach_auto)

theorem parseSortArrows_no_zero_progress (n : Nat) (tokens : List Token) (base : «Sort») (pos : Nat) (v : «Sort») (q : Nat)
    (h : parseSortArrows tokens base pos n = .ok (v, q)) : (v = base ∧ q = pos) ∨ pos + 2 ≤ q := by
  cases n with
  | zero => cases h
  | succ n =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := progress n
    rw [parseSortArrows.eq_2] at h
    simp only [advanceTok] at h
    repeat' split at h
    all_goals first
      | (left; cases h; exact ⟨rfl, rfl⟩)
      | (right; refine Reach.of ?_ h; reach_auto)

/-! ## Axioms used (printed at build time) -/

#print axioms progress
#print axioms fuel_mono_succ
#print axioms parseFormula_fuel_mono
#print axioms parseTerm_fuel_mono
#print axioms parseSort_fuel_mono
#print axioms parseRussianForm_fuel_mono
#print axioms parseFormulaAndLoop_no_zero_progress
#print axioms parseFormulaOrLoop_no_zero_progress
#print axioms parseFormulaImpliesLoop_no_zero_progress
#print axioms parseTermBinopLoop_no_zero_progress
#print axioms parseSortArrows_no_zero_progress
#print axioms parseFormula_fuel_zero
#print axioms parseRussianForm_fuel_zero
#print axioms parse_formula_deterministic
#print axioms parseFormula_deterministic
#print axioms Crux.parse_russian
#print axioms Crux.parse_formula
#print axioms Crux.parse_term
#print axioms Crux.parseFormula

end RussianCheckedProps
end Crux
