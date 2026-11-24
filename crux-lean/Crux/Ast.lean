/-
CRUX Core AST Types (fsl/src/crux/ast.rs).
Formula, Term, Sort, State, Backend, Proof Closure.

Note: Lean 4.19's `deriving DecidableEq` does not support nested recursion
through List, so it is derived only for types without list-recursive fields
(Literal, BinOp, Sort, BindingKind, GHCConstructor, Z3Tactic, Z3ParamValue,
SASConfig, AbsDomain, Widening, AbsVal, LeanGoalKind, Z3Context, SASState).
The other types carry `deriving Repr` only; no code path needs to compare
them for equality (matches are used instead).
-/

namespace Crux

-- ---------------------------------------------------------------------------
-- 1. Identifiers & Literals
-- ---------------------------------------------------------------------------

/-- Identifier: a name. -/
abbrev Ident := String

inductive Literal where
  | Number (n : Int)
  | Str (s : String)
  | Bool (b : Bool)
  | BitVecLit (value : Nat) (width : Nat)
  | Nil
  | Unit
deriving DecidableEq, Repr

-- ---------------------------------------------------------------------------
-- 2. Sorts (types / kinds)
-- ---------------------------------------------------------------------------

inductive «Sort» where
  | Prop
  | Type
  | Nat
  | Int
  | Bool
  | BitVec (width : Nat)
  | List (inner : «Sort»)
  | Array (key : «Sort») (value : «Sort»)
  | Arrow (dom : «Sort») (cod : «Sort»)
  | State
  | Formula
  | Term
  | MIR
  | Core
  | Haskell
  | Rust
  | Z3Expr
  | LeanTerm
  | SASAbs
  | User (id : Ident)
deriving DecidableEq, Repr

def «Sort».toString : «Sort» → String
  | .Prop => "Prop"
  | .Type => "Type"
  | .Nat => "Nat"
  | .Int => "Int"
  | .Bool => "Bool"
  | .BitVec w => s!"BitVec {w}"
  | .List s => s!"List {«Sort».toString s}"
  | .Array k v => s!"Array {«Sort».toString k} {«Sort».toString v}"
  | .Arrow a b => s!"{«Sort».toString a} → {«Sort».toString b}"
  | .State => "State"
  | .Formula => "Formula"
  | .Term => "Term"
  | .MIR => "MIR"
  | .Core => "Core"
  | .Haskell => "Haskell"
  | .Rust => "Rust"
  | .Z3Expr => "Z3Expr"
  | .LeanTerm => "LeanTerm"
  | .SASAbs => "SASAbs"
  | .User id => id

instance : ToString «Sort» where
  toString := «Sort».toString

-- ---------------------------------------------------------------------------
-- 3. Terms
-- ---------------------------------------------------------------------------

inductive BinOp where
  | Add | Sub | Mul | Div | Mod
  | Eq | Ne | Lt | Le | Gt | Ge
deriving DecidableEq, Repr

inductive Pattern where
  | Var (name : Ident)
  | Const (lit : Literal)
  | Wildcard
  | Cons (head : Pattern) (tail : Pattern)
  | Tuple (elems : List Pattern)
deriving Repr

inductive BindingKind where
  | Assign | Arrow | Let
deriving DecidableEq, Repr

mutual

inductive Term where
  | Var (name : Ident)
  | Const (lit : Literal)
  | Lambda (param : Ident) (sort : «Sort») (body : Term)
  | App (func : Term) (arg : Term)
  | BinOp (op : BinOp) (lhs : Term) (rhs : Term)
  | Cons (head : Term) (tail : Term)
  | Nil
  | Concat (a : Term) (b : Term)
  | IfThenElse (cond : Formula) (then_ : Term) (else_ : Term)
  | Match (scrutinee : Term) (arms : List MatchArm)
  | Fold (init : Term) (step : Term)
  | Rec (name : Ident) (body : Term)
  | Tuple (elems : List Term)
  | Field (base : Term) (field : Ident)
  | Paren (inner : Term)
deriving Repr

inductive Formula where
  | Atomic (a : Atomic)
  | Not (inner : Formula)
  | And (fs : List Formula)
  | Or (fs : List Formula)
  | Implies (a : Formula) (b : Formula)
  | Iff (a : Formula) (b : Formula)
  | Forall (var : Ident) (sort : «Sort») (body : Formula)
  | Exists (var : Ident) (sort : «Sort») (body : Formula)
  | Mu (var : Ident) (body : Formula)
  | Nu (var : Ident) (body : Formula)
  | Eq (a : Term) (b : Term)
  | Sila (state : State) (formula : Formula)
  | Paren (inner : Formula)
deriving Repr

inductive Atomic where
  | Predicate (name : Ident) (args : List Term)
  | Member (elem : Term) (set : Term)
  | Predecessor (less : Term) (greater : Term)
  | True
  | False
deriving Repr

inductive State where
  | S
  | S0
  | Sn (n : Nat)
  | Prime (inner : State)
  | Update (base : State) (var : Ident) (value : Term)
  | Bind (base : State) (binding : Binding)
  | Recursive (var : Ident) (body : Formula)
deriving Repr

structure Binding where
  var : Ident
  value : Term
  kind : BindingKind
deriving Repr

structure MatchArm where
  pattern : Pattern
  body : Term
deriving Repr

end

-- ---------------------------------------------------------------------------
-- 6. Backends
-- ---------------------------------------------------------------------------

structure GHCConstructor where
  name : Ident
  arg_sorts : List «Sort»
deriving DecidableEq, Repr

inductive GHCDecl where
  | Data (name : Ident) (constructors : List GHCConstructor)
  | Type (name : Ident) (target : «Sort»)
  | Function (name : Ident) (sort : «Sort») (body : Term)
deriving Repr

structure GHCIR where
  module_name : Ident
  decls : List GHCDecl
deriving Repr

mutual

inductive MIRStatement where
  | Let (name : Ident) (value : Term)
  | AssertEq (lhs : Term) (rhs : Term)
  | Assert (cond : Formula)
  | Expr (t : Term)
  | Return (t : Term)
  | IfThenElse (cond : Formula) (then_ : List MIRStatement) (else_ : List MIRStatement)
  | Loop (body : List MIRStatement)
  | Match (scrutinee : Term) (arms : List MIRMatchArm)
  | Unsafe (body : List MIRStatement)
  | KaniProof (body : List MIRStatement)
  | KaniUnwind (n : Nat)
deriving Repr

structure MIRMatchArm where
  pattern : Pattern
  body : List MIRStatement
deriving Repr

end

structure KaniMIR where
  name : Ident
  params : List (Ident × «Sort»)
  return_sort : «Sort»
  body : List MIRStatement
deriving Repr

inductive Backend where
  | GHC (ir : GHCIR)
  | Kani (mir : KaniMIR)
deriving Repr

-- ---------------------------------------------------------------------------
-- 7. OMEGA SMASHER
-- ---------------------------------------------------------------------------

structure Z3Context where
  timeout : Option Nat := none
  model : Bool := true
  unsat_core : Bool := false
  proof : Bool := false
deriving DecidableEq, Repr

def Z3Context.default : Z3Context := {}

inductive Z3ParamValue where
  | Str (s : String)
  | Num (n : Nat)
  | Bool (b : Bool)
deriving DecidableEq, Repr

structure Z3Tactic where
  name : Ident
  params : List (Ident × Z3ParamValue)
deriving DecidableEq, Repr

inductive Z3Expr where
  | Const (name : Ident)
  | Lit (value : Int) (sort : «Sort»)
  | App (func : Ident) (args : List Z3Expr)
  | And (es : List Z3Expr)
  | Or (es : List Z3Expr)
  | Not (e : Z3Expr)
  | Implies (a : Z3Expr) (b : Z3Expr)
  | Ite (cond : Z3Expr) (then_ : Z3Expr) (else_ : Z3Expr)
  | Eq (a : Z3Expr) (b : Z3Expr)
  | Distinct (es : List Z3Expr)
  | Lt (a : Z3Expr) (b : Z3Expr)
  | Le (a : Z3Expr) (b : Z3Expr)
  | Gt (a : Z3Expr) (b : Z3Expr)
  | Ge (a : Z3Expr) (b : Z3Expr)
  | BvAdd (a : Z3Expr) (b : Z3Expr)
  | BvSub (a : Z3Expr) (b : Z3Expr)
  | BvMul (a : Z3Expr) (b : Z3Expr)
  | BvAnd (a : Z3Expr) (b : Z3Expr)
  | BvOr (a : Z3Expr) (b : Z3Expr)
  | BvXor (a : Z3Expr) (b : Z3Expr)
  | BvNot (a : Z3Expr)
  | Select (a : Z3Expr) (i : Z3Expr)
  | Store (a : Z3Expr) (i : Z3Expr) (v : Z3Expr)
  | Forall (vars : List (Ident × «Sort»)) (body : Z3Expr)
  | Exists (vars : List (Ident × «Sort»)) (body : Z3Expr)
deriving Repr

inductive Z3Command where
  | DeclareConst (name : Ident) (sort : «Sort»)
  | DeclareFun (name : Ident) (arg_sorts : List «Sort») (ret_sort : «Sort»)
  | DefineFun (name : Ident) (params : List (Ident × «Sort»)) (sort : «Sort») (body : Z3Expr)
  | Assert (expr : Z3Expr)
  | AssertAndTrack (expr : Z3Expr) (label : Ident)
  | CheckSat
  | GetModel
  | GetUnsatCore
  | GetProof
  | Push (n : Nat)
  | Pop (n : Nat)
  | Tactic (tactic : Z3Tactic)
deriving Repr

structure Z3Query where
  context : Z3Context
  commands : List Z3Command
deriving Repr

-- ---------------------------------------------------------------------------
-- 8. SAS (Symbolic Abstract Semantics)
-- ---------------------------------------------------------------------------

inductive AbsDomain where
  | Intervals | Octagons | Polyhedra | Zones | Congruences | Signs
  | Constants | Predicate | Shape | Heap
  | Combined (a : AbsDomain) (b : AbsDomain)
deriving DecidableEq, Repr

inductive Widening where
  | Standard
  | Delayed (n : Nat)
  | Threshold
  | Localized
deriving DecidableEq, Repr

structure SASConfig where
  domain : AbsDomain
  widening : Widening
  narrowing : Nat
  threshold : Nat
  loop_bound : Nat
  track_pointers : Bool
  track_arrays : Bool
  relational : Bool
deriving DecidableEq, Repr

def SASConfig.default : SASConfig :=
  { domain := AbsDomain.Intervals,
    widening := Widening.Standard,
    narrowing := 1,
    threshold := 16,
    loop_bound := 10,
    track_pointers := true,
    track_arrays := false,
    relational := false }

inductive AbsVal where
  | Interval (low : Int) (high : Int)
  | Top
  | Bottom
  | Join (a : AbsVal) (b : AbsVal)
  | Meet (a : AbsVal) (b : AbsVal)
  | PointsTo (name : Ident)
  | Null
  | Dangling
deriving DecidableEq, Repr

structure SASState where
  bindings : List (Ident × AbsVal)
deriving DecidableEq, Repr

inductive SASProperty where
  | Safe (f : Formula)
  | Reach (f : Formula)
  | Invariant (f : Formula)
  | Assertion (f : Formula)
  | Termination
  | NonTermination
deriving Repr

structure SASQuery where
  config : SASConfig
  state : SASState
  property : SASProperty
deriving Repr

-- ---------------------------------------------------------------------------
-- 9. Lean 4 Goal
-- ---------------------------------------------------------------------------

inductive LeanGoalKind where
  | Theorem | Lemma | Example
deriving DecidableEq, Repr

inductive SimpArg where
  | Term (t : Term)
  | Neg (t : Term)
  | Star
deriving Repr

inductive RwArg where
  | Term (t : Term)
  | Rev (t : Term)
deriving Repr

inductive LeanTactic where
  | Exact (t : Term)
  | Apply (t : Term)
  | Refine (t : Term)
  | Intro (ids : List Ident)
  | Cases (t : Term)
  | Induction (t : Term)
  | Simpl (args : List SimpArg)
  | SimplAll
  | Rewrite (args : List RwArg)
  | Ring
  | Linarith
  | Nlinarith
  | Omega
  | Decide
  | NativeDecide
  | Aesop
  | Trivial
  | Constructor
  | Left
  | Right
  | Exfalso
  | Have (name : Ident) (formula : Formula) (proof : LeanTactic)
  | LetBind (name : Ident) (value : Term)
  | ByCases (name : Ident) (cond : Formula)
  | Macro (name : Ident)
  | Focus (tactics : List LeanTactic)
  | Seq (tactics : List LeanTactic)
  | Try (tactic : LeanTactic)
  | Repeat (tactic : LeanTactic)
  | AllGoals (tactic : LeanTactic)
  | Sorry
deriving Repr

structure LeanGoal where
  kind : LeanGoalKind
  name : Ident
  formula : Formula
  tactics : List LeanTactic
deriving Repr

inductive OmegaTarget where
  | Z3 (query : Z3Query)
  | SAS (query : SASQuery)
  | Lean (goal : LeanGoal)
deriving Repr

-- ---------------------------------------------------------------------------
-- 10. Proof Closure
-- ---------------------------------------------------------------------------

inductive DischargeMethod where
  | Z3Check
  | SASProve
  | LeanTactic (tactic : LeanTactic)
  | CruxClose
  | Assumption (name : Ident)
deriving Repr

structure Obligation where
  id : Nat
  formula : Formula
  discharged_by : DischargeMethod
deriving Repr

structure ProofClosure where
  obligations : List Obligation
deriving Repr

-- ---------------------------------------------------------------------------
-- 11. Final Result
-- ---------------------------------------------------------------------------

inductive FinalResult where
  | Sat
  | Unsat
  | Model (bindings : List (Ident × Term))
  | Unknown
  | Timeout
  | Alarm (location : Ident) (formula : Formula)
  | Proved
deriving Repr

def FinalResult.toString : FinalResult → String
  | .Sat => "SAT"
  | .Unsat => "UNSAT"
  | .Model bindings =>
    "MODEL{ " ++
      String.intercalate ", " (bindings.map (fun (name, val) => s!"{repr name} ↦ {repr val}")) ++
      " }"
  | .Unknown => "UNKNOWN"
  | .Timeout => "TIMEOUT"
  | .Alarm location formula => s!"ALARM at {location}: {repr formula}"
  | .Proved => "PROVED"

instance : ToString FinalResult where
  toString := FinalResult.toString

-- ---------------------------------------------------------------------------
-- 12. Russian Forms (parsed but lowered to AST above)
-- ---------------------------------------------------------------------------

inductive RussianForm where
  | Ravnostvo (a : Term) (b : Term)
  | Implikatsiya (a : Formula) (b : Formula)
  | Konyunktsiya (a : Formula) (b : Formula)
  | Dizyunktsiya (a : Formula) (b : Formula)
  | Otritsanie (a : Formula)
  | DlyaVsekh (var : Ident) (sort : «Sort») (body : Formula)
  | Sushchestvuet (var : Ident) (sort : «Sort») (body : Formula)
  | Rekursiya (var : Ident) (body : Formula)
  | Sostoyanie (state : State)
  | Sila (state : State) (formula : Formula)
  | Omega (backend : Backend) (state : State) (formula : Formula)
  | Dokazatelstvo (closure : ProofClosure)
deriving Repr

end Crux
