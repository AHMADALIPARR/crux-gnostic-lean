/-
SAS backend (fsl/src/crux/sas_backend.rs).
Abstract interpretation over interval domains. The fixpoint loop in
`analyze` is bounded by `loop_bound` (default 10) via explicit fuel.
`transfer` is the identity, as written in the source.
-/

import Crux.Ast

namespace Crux

inductive SASResult where
  | Proved
  | Unknown
  | Alarm (reason : String) (formula : Formula)
deriving Repr

def i64Min : Int := -9223372036854775808

def i64Max : Int := 9223372036854775807

structure SASAnalyzer where
  default_config : SASConfig := SASConfig.default
deriving DecidableEq, Repr

def SASAnalyzer.new : SASAnalyzer := {}

def SASAnalyzer.eval_binop (_ : SASAnalyzer) (op : BinOp) (l r : AbsVal) : AbsVal :=
  match op, l, r with
  | .Add, .Interval ll lh, .Interval rl rh => .Interval (ll + rl) (lh + rh)
  | .Sub, .Interval ll lh, .Interval rl rh => .Interval (ll - rh) (lh - rl)
  | .Mul, .Interval ll lh, .Interval rl rh =>
    .Interval
      (min (min (ll * rl) (ll * rh)) (min (lh * rl) (lh * rh)))
      (max (max (ll * rl) (ll * rh)) (max (lh * rl) (lh * rh)))
  | .Lt, _, _ | .Le, _, _ | .Gt, _, _ | .Ge, _, _ => .Interval 0 1
  | .Eq, _, _ | .Ne, _, _ => .Interval 0 1
  | _, _, _ => .Top

def SASAnalyzer.join (_ : SASAnalyzer) (x y : AbsVal) : AbsVal :=
  match x, y with
  | .Top, _ | _, .Top => .Top
  | .Bottom, v | v, .Bottom => v
  | .Interval al ah, .Interval bl bh => .Interval (min al bl) (max ah bh)
  | _, _ => .Top

def AbsVal.tag : AbsVal → Nat
  | .Interval .. => 0
  | .Top => 1
  | .Bottom => 2
  | .Join .. => 3
  | .Meet .. => 4
  | .PointsTo .. => 5
  | .Null => 6
  | .Dangling => 7

def SASAnalyzer.subsumes (_ : SASAnalyzer) (larger smaller : AbsVal) : Bool :=
  match larger, smaller with
  | .Top, _ => true
  | _, .Bottom => true
  | .Interval ll lh, .Interval sl sh => ll ≤ sl && lh ≥ sh
  | _, _ => larger.tag == smaller.tag

def SASAnalyzer.abstract_term (a : SASAnalyzer) (t : Term) : AbsVal :=
  match t with
  | .Const (.Number n) => .Interval n n
  | .Const (.Bool true) => .Interval 1 1
  | .Const (.Bool false) => .Interval 0 0
  | .Var _ => .Top
  | .BinOp op lhs rhs => a.eval_binop op (a.abstract_term lhs) (a.abstract_term rhs)
  | .IfThenElse _ then_ else_ => a.join (a.abstract_term then_) (a.abstract_term else_)
  | _ => .Top

def SASAnalyzer.abstract_state (a : SASAnalyzer) (state : State) : SASState :=
  match state with
  | .S | .S0 => { bindings := [] }
  | .Sn n => { bindings := [("iter", .Interval 0 (n : Int))] }
  | .Update _ var value => { bindings := [(var, a.abstract_term value)] }
  | .Prime inner => a.abstract_state inner
  | .Bind base binding => { bindings := (a.abstract_state base).bindings ++ [(binding.var, a.abstract_term binding.value)] }
  | .Recursive var _ => { bindings := [(var, .Top)] }

mutual
def SASAnalyzer.eval_formula_in_state (a : SASAnalyzer) (f : Formula) (state : SASState) : Bool :=
  match f with
  | .Atomic .True => true
  | .Atomic .False => false
  | .Not inner => !a.eval_formula_in_state inner state
  | .And fs => evalFormulaAll a fs state
  | .Or fs => evalFormulaAny a fs state
  | .Eq (.Var name) term =>
    let lookup : Bool :=
      match state.bindings.find? (fun (n, _) => n == name) with
      | some (_, aval) => a.subsumes aval (a.abstract_term term)
      | none => true
    match term with
    | .Var name2 => if name == name2 then true else lookup
    | _ => lookup
  | .Paren inner => a.eval_formula_in_state inner state
  | _ => true

def evalFormulaAll (a : SASAnalyzer) : List Formula → SASState → Bool
  | [], _ => true
  | f :: fs, state => a.eval_formula_in_state f state && evalFormulaAll a fs state

def evalFormulaAny (a : SASAnalyzer) : List Formula → SASState → Bool
  | [], _ => false
  | f :: fs, state => a.eval_formula_in_state f state || evalFormulaAny a fs state
end

def SASAnalyzer.satisfies (a : SASAnalyzer) (state : SASState) (prop : SASProperty) : Bool :=
  match prop with
  | .Safe f | .Invariant f => a.eval_formula_in_state f state
  | .Termination => true
  | _ => true

def SASAnalyzer.leq (a : SASAnalyzer) (x y : SASState) : Bool :=
  x.bindings.all fun (name, aval) =>
    match y.bindings.find? (fun (n, _) => n == name) with
    | some (_, bval) => a.subsumes bval aval
    | none => false

def SASAnalyzer.transfer (_ : SASAnalyzer) (state : SASState) (_ : SASProperty) : SASState :=
  -- identity transfer, as written in the source
  state

def SASAnalyzer.widen_vals (_ : SASAnalyzer) (x y : AbsVal) : AbsVal :=
  match x, y with
  | .Interval al ah, .Interval bl bh =>
    let low := if bl < al then i64Min else bl
    let high := if bh > ah then i64Max else bh
    .Interval low high
  | _, _ => .Top

def SASAnalyzer.widen (a : SASAnalyzer) (x y : SASState) : SASState :=
  y.bindings.foldl (fun acc (name, bval) =>
    match acc.bindings.find? (fun (n, _) => n == name) with
    | some (_, aval) =>
      { bindings := acc.bindings.map (fun (n, v) => if n == name then (n, a.widen_vals aval bval) else (n, v)) }
    | none => { bindings := acc.bindings ++ [(name, bval)] }) x

def SASAnalyzer.extract_violation (_ : SASAnalyzer) (_ : SASState) (prop : SASProperty) : Formula :=
  match prop with
  | .Safe f => f
  | .Assertion f => f
  | _ => .Atomic .True

def SASAnalyzer.build_query (a : SASAnalyzer) (state : State) (formula : Formula) : SASQuery :=
  { config := a.default_config, state := a.abstract_state state, property := .Safe formula }

def SASAnalyzer.analyzeAux (a : SASAnalyzer) (query : SASQuery) (current : SASState) : Nat → SASResult
  | 0 => .Unknown
  | fuel + 1 =>
    let next := a.transfer current query.property
    if a.leq next current then
      if a.satisfies next query.property then .Proved
      else .Alarm "fixpoint" (a.extract_violation next query.property)
    else a.analyzeAux query (a.widen current next) fuel

def SASAnalyzer.analyze (a : SASAnalyzer) (query : SASQuery) : SASResult :=
  a.analyzeAux query query.state query.config.loop_bound

theorem abstract_term_number :
    SASAnalyzer.new.abstract_term (.Const (.Number 5)) = .Interval 5 5 := rfl

theorem widen_vals_to_extremes :
    SASAnalyzer.new.widen_vals (.Interval 0 10) (.Interval (-5) 20) =
      .Interval (-9223372036854775808) 9223372036854775807 := rfl

end Crux
