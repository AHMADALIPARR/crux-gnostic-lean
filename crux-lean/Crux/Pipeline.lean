/-
Crux pipeline (fsl/src/crux/pipeline.rs).
Parse → lower → backend → omega → close.
-/

import Crux.Ast
import Crux.Russian
import Crux.Omega
import Crux.Pcc

namespace Crux

inductive PipelineStage where
  | Parsed (form : RussianForm)
  | Lowered (state : State) (formula : Formula)
  | BackendSelected (backend : Backend)
  | OmegaSmashed (result : OmegaResult)
  | ProofClosed (closure : ProofClosure)
  | Final (result : CruxResult)
deriving Repr

inductive CruxResult where
  | Sat
  | Unsat
  | Model (m : List (Ident × Term))
  | Proved
  | Unknown
  | Timeout
  | Alarm (location : Ident) (formula : Formula)
  | Error (msg : String)
deriving Repr

def CruxResult.toFinal : CruxResult → FinalResult
  | .Sat => .Sat
  | .Unsat => .Unsat
  | .Model m => .Model m
  | .Proved => .Proved
  | .Unknown => .Unknown
  | .Timeout => .Timeout
  | .Alarm location formula => .Alarm location formula
  | .Error _ => .Unknown

def CruxResult.toString : CruxResult → String
  | .Sat => "SAT"
  | .Unsat => "UNSAT"
  | .Model m => "MODEL{ " ++ String.intercalate ", " (m.map (fun (name, val) => s!"{name} = {repr val}")) ++ " }"
  | .Proved => "PROVED"
  | .Unknown => "UNKNOWN"
  | .Timeout => "TIMEOUT"
  | .Alarm location formula => s!"ALARM at {location}: {repr formula}"
  | .Error e => s!"ERROR: {e}"

instance : ToString CruxResult where
  toString := CruxResult.toString

structure CruxPipeline where
  input : String
  stages : List PipelineStage := []
deriving Repr

def default_kani : KaniMIR :=
  { name := "harness", params := [], return_sort := .Bool, body := [] }

def lower_russian_form (form : RussianForm) : State × Formula × Backend :=
  match form with
  | .Ravnostvo a b => (.S0, .Eq a b, .Kani default_kani)
  | .Implikatsiya a b => (.S0, .Implies a b, .Kani default_kani)
  | .Konyunktsiya a b => (.S0, .And [a, b], .Kani default_kani)
  | .Dizyunktsiya a b => (.S0, .Or [a, b], .Kani default_kani)
  | .Otritsanie a => (.S0, .Not a, .Kani default_kani)
  | .DlyaVsekh var sort body => (.S0, .Forall var sort body, .Kani default_kani)
  | .Sushchestvuet var sort body => (.S0, .Exists var sort body, .Kani default_kani)
  | .Sila state formula => (state, formula, .Kani default_kani)
  | .Omega backend state formula => (state, formula, backend)
  | .Sostoyanie state => (state, .Atomic .True, .Kani default_kani)
  | .Rekursiya var body => (.S0, .Mu var body, .Kani default_kani)
  | .Dokazatelstvo _ => (.S0, .Atomic .True, .Kani default_kani)

def omega_result_to_crux : OmegaResult → CruxResult
  | .Sat => .Sat
  | .Unsat => .Unsat
  | .Model m => .Model m
  | .Proved => .Proved
  | .Unknown => .Unknown
  | .Timeout => .Timeout
  | .Alarm loc f => .Alarm loc f

structure CruxPipelineResult where
  stages : List PipelineStage
  result : CruxResult
deriving Repr

def run_crux_pipeline (input : String) : CruxPipelineResult :=
  match parse_russian input with
  | .error e => { stages := [], result := .Error s!"parse error: {e}" }
  | .ok form =>
    let (state, formula, backend) := lower_russian_form form
    let (omega_result, closure) := omega_smash_pipeline backend state formula
    let result := omega_result_to_crux omega_result
    { stages := [.Parsed form, .Lowered state formula, .BackendSelected backend,
                 .OmegaSmashed omega_result, .ProofClosed closure, .Final result],
      result := result }

def CruxPipelineResult.report (r : CruxPipelineResult) : String :=
  let (out, _) := r.stages.foldl (fun (acc : String × Nat) stage =>
    let i := acc.2
    let line := match stage with
      | .Parsed f => s!"Stage {i}: Parsed → {repr f}\n"
      | .Lowered state formula => s!"Stage {i}: Lowered → state={repr state}, formula={repr formula}\n"
      | .BackendSelected b => s!"Stage {i}: Backend → {repr b}\n"
      | .OmegaSmashed res => s!"Stage {i}: OMEGA → {repr res}\n"
      | .ProofClosed c => s!"Stage {i}: ProofClosure → {c.obligations.length} obligations\n"
      | .Final res => s!"Stage {i}: Result → {res}\n"
    (acc.1 ++ line, acc.2 + 1))
    ("=== CRUX · SILA · OMEGA-SMASHER Pipeline ===\n\n", 0)
  out ++ s!"\nFinal: {r.result.toFinal}\n"

def run_crux_direct (state : State) (formula : Formula) (backend : Backend) : CruxResult :=
  omega_result_to_crux (omega_smash_pipeline backend state formula).1

def run_crux_auto (state : State) (formula : Formula) : CruxResult :=
  omega_result_to_crux (OmegaSmasher.new.smash_auto state formula)

theorem crux_result_to_final_error :
    (.Error "x").toFinal = .Unknown := rfl

theorem crux_result_to_final_sat :
    CruxResult.toFinal .Sat = .Sat := rfl

end Crux
