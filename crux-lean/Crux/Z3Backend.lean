/-
Z3 backend (fsl/src/crux/z3_backend.rs).
Builds SMT-LIB queries from the AST. `check` is ported exactly as
written: it builds the SMT-LIB string and falls back to Unknown (the
source has no Z3 process behind it; the actual call is a TODO there).
-/

import Crux.Ast

namespace Crux

inductive Z3CheckResult where
  | Sat
  | Unsat
  | Model (m : List (Ident × Term))
  | Unknown
  | Timeout
deriving Repr

structure Z3Solver where
  context : Z3Context := {}
deriving DecidableEq, Repr

def Z3Solver.new : Z3Solver := {}

def sort_to_smt : «Sort» → String
  | .Bool => "Bool"
  | .Int => "Int"
  | .BitVec 32 => "(_ BitVec 32)"
  | .BitVec 64 => "(_ BitVec 64)"
  | _ => "(_ BitVec 32)"

mutual
def expr_to_smt : Z3Expr → String
  | .Const name => name
  | .Lit value (.BitVec w) => s!"(_ bv{value} {w})"
  | .Lit value _ => s!"{value}"
  | .And es => s!"(and {String.intercalate " " (z3ExprListToSmt es)})"
  | .Or es => s!"(or {String.intercalate " " (z3ExprListToSmt es)})"
  | .Not e => s!"(not {expr_to_smt e})"
  | .Implies a b => s!"(=> {expr_to_smt a} {expr_to_smt b})"
  | .Eq a b => s!"(= {expr_to_smt a} {expr_to_smt b})"
  | .Distinct es => s!"(distinct {String.intercalate " " (z3ExprListToSmt es)})"
  | .Lt a b => s!"(bvult {expr_to_smt a} {expr_to_smt b})"
  | .Le a b => s!"(bvule {expr_to_smt a} {expr_to_smt b})"
  | .Gt a b => s!"(bvugt {expr_to_smt a} {expr_to_smt b})"
  | .Ge a b => s!"(bvuge {expr_to_smt a} {expr_to_smt b})"
  | .BvAdd a b => s!"(bvadd {expr_to_smt a} {expr_to_smt b})"
  | .BvSub a b => s!"(bvsub {expr_to_smt a} {expr_to_smt b})"
  | .BvMul a b => s!"(bvmul {expr_to_smt a} {expr_to_smt b})"
  | .BvAnd a b => s!"(bvand {expr_to_smt a} {expr_to_smt b})"
  | .BvOr a b => s!"(bvor {expr_to_smt a} {expr_to_smt b})"
  | .BvXor a b => s!"(bvxor {expr_to_smt a} {expr_to_smt b})"
  | .BvNot a => s!"(bvnot {expr_to_smt a})"
  | .Ite cond then_ else_ => s!"(ite {expr_to_smt cond} {expr_to_smt then_} {expr_to_smt else_})"
  | .App func args => s!"({func} {String.intercalate " " (z3ExprListToSmt args)})"
  | .Select a i => s!"(select {expr_to_smt a} {expr_to_smt i})"
  | .Store a i v => s!"(store {expr_to_smt a} {expr_to_smt i} {expr_to_smt v})"
  | .Forall vars body =>
    let bindings := String.intercalate " " (vars.map (fun (n, s) => s!"({n} {sort_to_smt s})"))
    s!"(forall ({bindings}) {expr_to_smt body})"
  | .Exists vars body =>
    let bindings := String.intercalate " " (vars.map (fun (n, s) => s!"({n} {sort_to_smt s})"))
    s!"(exists ({bindings}) {expr_to_smt body})"

def z3ExprListToSmt : List Z3Expr → List String
  | [] => []
  | e :: es => expr_to_smt e :: z3ExprListToSmt es
end

def term_to_z3 : Term → Z3Expr
  | .Var name => .Const name
  | .Const (.Number n) => .Lit n (.BitVec 32)
  | .Const (.Bool true) => .Const "true"
  | .Const (.Bool false) => .Const "false"
  | .BinOp op lhs rhs =>
    let l := term_to_z3 lhs
    let r := term_to_z3 rhs
    match op with
    | .Add => .BvAdd l r
    | .Sub => .BvSub l r
    | .Mul => .BvMul l r
    | .Eq => .Eq l r
    | .Ne => .Distinct [l, r]
    | .Lt => .Lt l r
    | .Le => .Le l r
    | .Gt => .Gt l r
    | .Ge => .Ge l r
    | .Div => .App "bvudiv" [l, r]
    | .Mod => .App "bvurem" [l, r]
  | .App func arg => .App (toString (repr func)) [term_to_z3 arg]
  | .Paren inner => term_to_z3 inner
  | _ => .Const "nil"

mutual
def formula_to_z3 : Formula → Z3Expr
  | .Atomic .True => .Const "true"
  | .Atomic .False => .Const "false"
  | .Not inner => .Not (formula_to_z3 inner)
  | .And fs => .And (formulaListToZ3 fs)
  | .Or fs => .Or (formulaListToZ3 fs)
  | .Implies a b => .Implies (formula_to_z3 a) (formula_to_z3 b)
  | .Iff a b =>
    let la := formula_to_z3 a
    let lb := formula_to_z3 b
    .And [.Implies la lb, .Implies lb la]
  | .Eq a b => .Eq (term_to_z3 a) (term_to_z3 b)
  | .Forall var sort body => .Forall [(var, sort)] (formula_to_z3 body)
  | .Exists var sort body => .Exists [(var, sort)] (formula_to_z3 body)
  | .Paren inner => formula_to_z3 inner
  | .Sila _ formula => formula_to_z3 formula
  | .Mu var body | .Nu var body => .App var [formula_to_z3 body]
  | _ => .Const "true"

def formulaListToZ3 : List Formula → List Z3Expr
  | [] => []
  | f :: fs => formula_to_z3 f :: formulaListToZ3 fs
end

mutual
def collect_vars (f : Formula) (vars : List Ident) : List Ident :=
  match f with
  | .Atomic (.Predicate _ args) => collectTermVarsList args vars
  | .Atomic _ => vars
  | .Not inner => collect_vars inner vars
  | .And fs | .Or fs => collectVarsList fs vars
  | .Implies a b => collect_vars b (collect_vars a vars)
  | .Iff a b => collect_vars b (collect_vars a vars)
  | .Eq a b => collect_term_vars b (collect_term_vars a vars)
  | .Forall var _ _ | .Exists var _ _ | .Mu var _ | .Nu var _ => vars ++ [var]
  | .Sila _ formula => collect_vars formula vars
  | .Paren inner => collect_vars inner vars

def collectVarsList : List Formula → List Ident → List Ident
  | [], vars => vars
  | f :: fs, vars => collectVarsList fs (collect_vars f vars)

def collect_term_vars (t : Term) (vars : List Ident) : List Ident :=
  match t with
  | .Var name => if vars.contains name then vars else vars ++ [name]
  | .BinOp _ lhs rhs => collect_term_vars rhs (collect_term_vars lhs vars)
  | .App func arg => collect_term_vars arg (collect_term_vars func vars)
  | .Paren inner => collect_term_vars inner vars
  | _ => vars

def collectTermVarsList : List Term → List Ident → List Ident
  | [], vars => vars
  | t :: ts, vars => collectTermVarsList ts (collect_term_vars t vars)
end

def Z3Solver.build_query (s : Z3Solver) (_state : State) (formula : Formula) : Z3Query :=
  let vars := collect_vars formula []
  let commands :=
    (vars.map fun v => Z3Command.DeclareConst v (.BitVec 32)) ++
    [.Assert (formula_to_z3 formula), .CheckSat, .GetModel]
  { context := s.context, commands := commands }

def Z3Solver.query_to_smtlib (_ : Z3Solver) (query : Z3Query) : String :=
  let header := "(set-logic QF_BV)\n"
    ++ (match query.context.timeout with
        | some t => s!"(set-option :timeout {t})\n"
        | none => "")
    ++ (if query.context.model then "(set-option :produce-models true)\n" else "")
    ++ (if query.context.unsat_core then "(set-option :produce-unsat-cores true)\n" else "")
  header ++ String.join (query.commands.map z3CommandToSmt)
where
  z3CommandToSmt : Z3Command → String
    | .DeclareConst name sort => s!"(declare-const {name} {sort_to_smt sort})\n"
    | .DeclareFun name arg_sorts ret_sort =>
      let args := String.intercalate " " (arg_sorts.map sort_to_smt)
      s!"(declare-fun {name} ({args}) {sort_to_smt ret_sort})\n"
    | .DefineFun .. => ""
    | .Assert expr => s!"(assert {expr_to_smt expr})\n"
    | .AssertAndTrack .. => ""
    | .CheckSat => "(check-sat)\n"
    | .GetModel => "(get-model)\n"
    | .GetUnsatCore => "(get-unsat-core)\n"
    | .GetProof => "(get-proof)\n"
    | .Push n => s!"(push {n})\n"
    | .Pop n => s!"(pop {n})\n"
    | .Tactic .. => ""

def Z3Solver.check (s : Z3Solver) (query : Z3Query) : Z3CheckResult :=
  let _smt := s.query_to_smtlib query
  .Unknown

theorem sort_to_smt_bool : sort_to_smt .Bool = "Bool" := rfl

theorem expr_to_smt_const : expr_to_smt (.Const "true") = "true" := rfl

theorem formula_to_z3_true : formula_to_z3 (.Atomic .True) = .Const "true" := rfl

end Crux
