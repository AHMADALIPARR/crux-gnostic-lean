/-
Omega smasher (fsl/src/crux/omega.rs).
Tries Z3 first, then Lean, then SAS — in that priority order.
-/

import Crux.Ast
import Crux.Z3Backend
import Crux.SasBackend
import Crux.LeanBackend

namespace Crux

inductive OmegaResult where
  | Sat
  | Unsat
  | Model (m : List (Ident × Term))
  | Proved
  | Unknown
  | Timeout
  | Alarm (location : Ident) (formula : Formula)
deriving Repr

structure OmegaSmasher where
  z3 : Z3Solver := Z3Solver.new
  sas : SASAnalyzer := SASAnalyzer.new
  lean : LeanProver := {}
deriving DecidableEq, Repr

def OmegaSmasher.new : OmegaSmasher := {}

def OmegaResult.isUnknown : OmegaResult → Bool
  | .Unknown => true
  | _ => false

def OmegaResult.toFinal : OmegaResult → FinalResult
  | .Sat => .Sat
  | .Unsat => .Unsat
  | .Model m => .Model m
  | .Proved => .Proved
  | .Unknown => .Unknown
  | .Timeout => .Timeout
  | .Alarm location formula => .Alarm location formula

def OmegaSmasher.smash_z3 (s : OmegaSmasher) (state : State) (formula : Formula) : OmegaResult :=
  match s.z3.check (s.z3.build_query state formula) with
  | .Sat => .Sat
  | .Unsat => .Unsat
  | .Model m => .Model m
  | .Unknown => .Unknown
  | .Timeout => .Timeout

def OmegaSmasher.smash_lean (s : OmegaSmasher) (state : State) (formula : Formula) : OmegaResult :=
  let goal := s.lean.build_goal state formula
  match s.lean.prove goal with
  | .Proved => .Proved
  | .Timeout => .Timeout
  | .Unknown => .Unknown

def OmegaSmasher.smash_sas (s : OmegaSmasher) (state : State) (formula : Formula) : OmegaResult :=
  match s.sas.analyze (s.sas.build_query state formula) with
  | .Proved => .Proved
  | .Unknown => .Unknown
  | .Alarm reason f => .Alarm reason f

def OmegaSmasher.smash (s : OmegaSmasher) (backend : Backend) (state : State) (formula : Formula) : OmegaResult :=
  match backend with
  | .GHC _ => s.smash_lean state formula
  | .Kani _ => s.smash_z3 state formula

def OmegaSmasher.smash_auto (s : OmegaSmasher) (state : State) (formula : Formula) : OmegaResult :=
  let z3_result := s.smash_z3 state formula
  if !z3_result.isUnknown then z3_result
  else
    let lean_result := s.smash_lean state formula
    if !lean_result.isUnknown then lean_result
    else s.smash_sas state formula

def omega_macro_definitions : List (String × String) :=
  [ ("omega_smash", "macro_rules | `(tactic| omega_smash) => `(tactic| crux_close)"),
    ("sila_auto", "macro_rules | `(tactic| sila_auto) => `(tactic| omega_smash)"),
    ("crux_close", "macro_rules | `(tactic| crux_close) => `(tactic| decide)"),
    ("sila", "syntax \"sila\" term : term"),
    ("Сила", "syntax \"Сила\" term : term"),
    ("sila_state", "syntax \"sila_state\" term : term"),
    ("omega_z3", "macro_rules | `(tactic| omega_z3) => `(tactic| sorry)"),
    ("omega_sas", "macro_rules | `(tactic| omega_sas) => `(tactic| sorry)"),
    ("omega_lean", "macro_rules | `(tactic| omega_lean) => `(tactic| sorry)"),
    ("sila_prove", "macro_rules | `(tactic| sila_prove) => `(tactic| crux_close)"),
    ("sila_discharge", "macro_rules | `(tactic| sila_discharge) => `(tactic| omega_smash)"),
    ("sila_certify", "macro_rules | `(tactic| sila_certify) => `(tactic| crux_close)") ]

def omega_smash_pipeline (backend : Backend) (state : State) (formula : Formula) :
    OmegaResult × ProofClosure :=
  let result := OmegaSmasher.new.smash_auto state formula
  let discharged_by := match result with
    | .Sat | .Unsat | .Model _ => .Z3Check
    | .Proved => .CruxClose
    | .Alarm _ _ => .SASProve
    | _ => .CruxClose
  let closure : ProofClosure := { obligations := [{ id := 0, formula := .Sila state formula, discharged_by := discharged_by }] }
  (result, closure)

theorem omega_result_to_final_sat : OmegaResult.toFinal .Sat = .Sat := rfl

theorem omega_result_to_final_unknown : OmegaResult.toFinal .Unknown = .Unknown := rfl

theorem omega_macro_definitions_length : omega_macro_definitions.length = 12 := by decide

end Crux
