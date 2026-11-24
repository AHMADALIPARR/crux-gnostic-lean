/- 
Lean 4 Backend (fsl/src/crux/lean_backend.rs).
Builds Lean goals, expands tactic macros, proves via reflection.

Note on serializer strings: the Lean output strings here use the correct
characters the Rust code means (→, ∧, ∨, ↔, ∀, ∃, ≤, ≥, ≠, Сила, S₀, ·),
not the mojibake in the pasted Rust file.
-/

import Crux.Ast

namespace Crux

-- ---------------------------------------------------------------------------
-- 1. Lean Prover
-- ---------------------------------------------------------------------------

/-- The Lean prover carries no state; it is a unit structure in the Rust. -/
structure LeanProver where
deriving DecidableEq, Repr

def LeanProver.new : LeanProver := {}

/-- Debug-style rendering of a state, used for the generated goal name.
    The Rust formats the state with {:?}; this uses the Lean repr rendering. -/
def State.debugString (s : State) : String := toString (repr s)

def LeanProver.build_goal (_ : LeanProver) (state : State) (formula : Formula) : LeanGoal :=
  { kind := .Theorem,
    name := "sila_goal_" ++ state.debugString,
    formula := .Sila state formula,
    tactics := [.Macro "crux_close"] }

inductive LeanResult where
  | Proved | Timeout | Unknown
deriving DecidableEq, Repr

mutual

def LeanProver.try_decide (_ : LeanProver) (formula : Formula) : Bool :=
  match formula with
  | .Atomic .True => true
  | .Atomic .False => false
  | .Not inner => !LeanProver.new.try_decide inner
  | .And fs => tryDecideAll fs
  | .Or fs => tryDecideAny fs
  | .Eq (.Var a) (.Var b) => a == b
  | .Eq (.Const (.Number a)) (.Const (.Number b)) => a == b
  | .Paren inner => LeanProver.new.try_decide inner
  | _ => false

def tryDecideAll : List Formula → Bool
  | [] => true
  | f :: rest => LeanProver.new.try_decide f && tryDecideAll rest

def tryDecideAny : List Formula → Bool
  | [] => false
  | f :: rest => LeanProver.new.try_decide f || tryDecideAny rest

end

mutual

/-- Fuel-bounded worker for try_tactic. The macro call graph in try_macro
    is acyclic but not structurally decreasing in its arguments, so the
    mutual try_tactic / try_macro pair runs on explicit fuel. The wrappers
    below start with fuel 16; the longest macro chain is 3 hops, so the
    fuel never runs out on reachable inputs. -/
def tryTacticFueled (p : LeanProver) (tactic : LeanTactic) (formula : Formula) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    match tactic with
    | .Macro name => tryMacroFueled p name formula fuel
    | .Simpl _ => true
    | .Omega => true
    | .Decide => p.try_decide formula
    | .Ring => true
    | .Linarith => true
    | .Aesop => true
    | .Sorry => false
    | .Seq ts => tryTacticsAllFueled p ts formula fuel
    | .Try inner => tryTacticFueled p inner formula fuel || true
    | .Repeat inner => tryTacticFueled p inner formula fuel
    | _ => false

def tryTacticsAllFueled (p : LeanProver) : List LeanTactic → Formula → Nat → Bool
  | [], _, _ => true
  | _, _, 0 => false
  | t :: ts, formula, fuel + 1 =>
    tryTacticFueled p t formula fuel && tryTacticsAllFueled p ts formula fuel

def tryMacroFueled (p : LeanProver) (name : String) (formula : Formula) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    match name with
    | "sila_auto" =>
      tryTacticFueled p (.Simpl []) formula fuel
        || tryTacticFueled p .Omega formula fuel
        || tryTacticFueled p .Decide formula fuel
    | "omega_smash" =>
      tryTacticFueled p .Omega formula fuel
        || tryTacticFueled p .Linarith formula fuel
    | "crux_close" =>
      tryMacroFueled p "sila_auto" formula fuel
        || tryMacroFueled p "omega_smash" formula fuel
        || tryTacticFueled p .Decide formula fuel
    | "z3_decide" => p.try_decide formula
    | "sas_prove" => true
    | "blast" => tryTacticFueled p .Constructor formula fuel
    | "finish" =>
      tryMacroFueled p "sila_auto" formula fuel
        || tryMacroFueled p "omega_smash" formula fuel
    | "crush" => tryMacroFueled p "sila_auto" formula fuel
    | _ => false

end

def LeanProver.try_tactic (p : LeanProver) (tactic : LeanTactic) (formula : Formula) : Bool :=
  tryTacticFueled p tactic formula 16

def LeanProver.try_macro (p : LeanProver) (name : String) (formula : Formula) : Bool :=
  tryMacroFueled p name formula 16

def LeanProver.prove (p : LeanProver) (goal : LeanGoal) : LeanResult :=
  if goal.tactics.any (fun t => p.try_tactic t goal.formula) then
    .Proved
  else
    .Unknown

-- ---------------------------------------------------------------------------
-- 2. Lean 4 serialization
-- ---------------------------------------------------------------------------

def term_to_lean4 (t : Term) : String :=
  match t with
  | .Var name => name
  | .Const (.Number n) => s!"{n}"
  | .Const (.Bool true) => "true"
  | .Const (.Bool false) => "false"
  | .BinOp op lhs rhs =>
    let op_str := match op with
      | .Add => "+" | .Sub => "-" | .Mul => "*" | .Div => "/" | .Mod => "%"
      | .Eq => "=" | .Ne => "≠"
      | .Lt => "<" | .Le => "≤" | .Gt => ">" | .Ge => "≥"
    s!"({term_to_lean4 lhs} {op_str} {term_to_lean4 rhs})"
  | .Paren inner => s!"({term_to_lean4 inner})"
  | .App func arg => s!"({term_to_lean4 func} {term_to_lean4 arg})"
  | _ => "sorry"

def sort_to_lean4 (s : «Sort») : String :=
  match s with
  | .Prop => "Prop"
  | .Type => "Type"
  | .Nat => "Nat"
  | .Int => "Int"
  | .Bool => "Bool"
  | .BitVec w => s!"BitVec {w}"
  | .List inner => s!"List {sort_to_lean4 inner}"
  | .Arrow a b => s!"{sort_to_lean4 a} → {sort_to_lean4 b}"
  | .User name => name
  | _ => "Type"

def state_to_lean4 (s : State) : String :=
  match s with
  | .S => "S"
  | .S0 => "S₀"
  | .Sn n => s!"S{n}"
  | .Prime inner => s!"({state_to_lean4 inner}')"
  | _ => "S"

mutual

def tactic_to_lean4 (t : LeanTactic) : String :=
  match t with
  | .Exact term => s!"exact {term_to_lean4 term}"
  | .Apply term => s!"apply {term_to_lean4 term}"
  | .Intro ids => s!"intro {String.intercalate " " ids}"
  | .Simpl _ => "simp"
  | .SimplAll => "simp_all"
  | .Omega => "omega"
  | .Decide => "decide"
  | .Ring => "ring"
  | .Linarith => "linarith"
  | .Aesop => "aesop"
  | .Constructor => "constructor"
  | .Left => "left"
  | .Right => "right"
  | .Exfalso => "exfalso"
  | .Macro name => name
  | .Sorry => "sorry"
  | .Try inner => s!"try {tactic_to_lean4 inner}"
  | .Repeat inner => s!"repeat {tactic_to_lean4 inner}"
  | .AllGoals inner => s!"all_goals {tactic_to_lean4 inner}"
  | .Focus ts => s!"· {String.intercalate " <;> " (tacticListToLean4 ts)}"
  | .Seq ts => String.intercalate " <;> " (tacticListToLean4 ts)
  | _ => "sorry"

def tacticListToLean4 : List LeanTactic → List String
  | [] => []
  | t :: ts => tactic_to_lean4 t :: tacticListToLean4 ts

end

mutual

def formula_to_lean4 (f : Formula) : String :=
  match f with
  | .Atomic .True => "True"
  | .Atomic .False => "False"
  | .Not inner => s!"Not {formula_to_lean4 inner}"
  | .And fs => String.intercalate " ∧ " (formulaListToLean4 fs)
  | .Or fs => String.intercalate " ∨ " (formulaListToLean4 fs)
  | .Implies a b => s!"{formula_to_lean4 a} → {formula_to_lean4 b}"
  | .Iff a b => s!"{formula_to_lean4 a} ↔ {formula_to_lean4 b}"
  | .Eq a b => s!"{term_to_lean4 a} = {term_to_lean4 b}"
  | .Forall var sort body => s!"∀ ({var} : {sort_to_lean4 sort}), {formula_to_lean4 body}"
  | .Exists var sort body => s!"∃ ({var} : {sort_to_lean4 sort}), {formula_to_lean4 body}"
  | .Paren inner => s!"({formula_to_lean4 inner})"
  | .Sila state formula => s!"Сила({state_to_lean4 state}, {formula_to_lean4 formula})"
  | _ => "True"

def formulaListToLean4 : List Formula → List String
  | [] => []
  | f :: fs => formula_to_lean4 f :: formulaListToLean4 fs

end

def LeanProver.goal_to_lean4 (_ : LeanProver) (goal : LeanGoal) : String :=
  let kind := match goal.kind with
    | .Theorem => "theorem"
    | .Lemma => "lemma"
    | .Example => "example"
  let tactics := goal.tactics.map tactic_to_lean4
  s!"{kind} {goal.name} : {formula_to_lean4 goal.formula} := by\n  {String.intercalate "\n  " tactics}"

theorem build_goal_tactics :
    (LeanProver.new.build_goal .S0 (.Atomic .True)).tactics = [.Macro "crux_close"] := rfl

theorem prove_true_goal :
    LeanProver.new.prove (LeanProver.new.build_goal .S0 (.Atomic .True)) = .Proved := by decide

theorem state_to_lean4_s0 : state_to_lean4 .S0 = "S₀" := rfl

theorem formula_to_lean4_sila :
    formula_to_lean4 (.Sila .S0 (.Atomic .True)) = "Сила(S₀, True)" := rfl

theorem formula_to_lean4_and :
    formula_to_lean4 (.And [.Atomic .True, .Atomic .False]) = "True ∧ False" := rfl

end Crux
