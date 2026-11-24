/-
Lean 4 Monad Stack Reference Types (fsl/src/crux/lean_monad_stack.rs).
Port of the Rust-side type definitions matching the Lean 4 grammar.
-/

namespace Crux

-- ---------------------------------------------------------------------------
-- 1. Monad Hierarchy (Lean 4 stack positions)
-- ---------------------------------------------------------------------------

inductive MonadLayer where
  | CoreM | MetaM | ElabM | TermElabM | TacticM | CommandElabM
  | MacroM | MacroT | QuotationM | IO
deriving DecidableEq, Repr

-- ---------------------------------------------------------------------------
-- 2. MetaM API surface — key operations
-- ---------------------------------------------------------------------------

structure MVarId where
  val : Nat
deriving DecidableEq, Repr

structure FVarId where
  val : Nat
deriving DecidableEq, Repr

inductive BinderInfo where
  | Default | Implicit | StrictImplicit | Instance | OutParam
deriving DecidableEq, Repr

inductive LeanLevel where
  | Zero
  | Succ (level : LeanLevel)
  | Max (a : LeanLevel) (b : LeanLevel)
  | Param (name : String)
deriving DecidableEq, Repr

inductive LeanExpr where
  | Sort (level : Nat)
  | Const (name : String) (levels : List LeanLevel)
  | App (func : LeanExpr) (arg : LeanExpr)
  | Lambda (name : String) (type : LeanExpr) (body : LeanExpr)
  | Pi (name : String) (type : LeanExpr) (body : LeanExpr)
  | Let (name : String) (type : LeanExpr) (value : LeanExpr) (body : LeanExpr)
  | MVar (id : MVarId)
  | FVar (id : FVarId)
deriving DecidableEq, Repr

inductive TransparencyMode where
  | All | Default | Reducible | Instances | None
deriving DecidableEq, Repr

inductive LOption (α : Type) where
  | None
  | Some (x : α)
  | Undef
deriving DecidableEq, Repr

structure LocalContext where
  decl_names : List String := []
deriving DecidableEq, Repr

def LocalContext.default : LocalContext := {}

structure MetavarContext where
  mvar_count : Nat := 0
deriving DecidableEq, Repr

def MetavarContext.default : MetavarContext := {}

-- ---------------------------------------------------------------------------
-- 3. TacticM — state, context, config
-- ---------------------------------------------------------------------------

structure TacticState where
  goals : List MVarId := []
  aux_goals : List MVarId := []
deriving DecidableEq, Repr

def TacticState.default : TacticState := {}

inductive NewGoals where
  | GoalsFirst | GoalsLast | GoalsIndep
deriving DecidableEq, Repr

inductive TacticLocation where
  | Everywhere | Target | Hypotheses | Wildcard
deriving DecidableEq, Repr

structure TacticConfig where
  transparent : TransparencyMode
  new_goals : NewGoals
  location : TacticLocation
deriving DecidableEq, Repr

def TacticConfig.default : TacticConfig :=
  { transparent := TransparencyMode.Default,
    new_goals := NewGoals.GoalsFirst,
    location := TacticLocation.Everywhere }

structure TacticContext where
  main : Option MVarId
  elaborator : String
  recover : Bool
  config : TacticConfig
deriving DecidableEq, Repr

-- ---------------------------------------------------------------------------
-- 4. Lean tactic operations (user-facing enum)
-- ---------------------------------------------------------------------------

inductive LeanTacticOp where
  | GetGoals
  | SetGoals (goals : List MVarId)
  | GetMainGoal
  | GetMainTarget
  | ReplaceMainGoal (goals : List MVarId)
  | Done
  | Intro (name : String)
  | IntroN (n : Nat)
  | Intros
  | Apply (e : LeanExpr)
  | Exact (e : LeanExpr)
  | Assumption
  | Cases (e : LeanExpr)
  | Induction (e : LeanExpr)
  | Simp
  | SimpAll
  | Left
  | Right
  | Constructor
  | Exfalso
  | Decide
  | Omega
  | Ring
  | Focus (op : LeanTacticOp)
  | AllGoals (op : LeanTacticOp)
  | Try (op : LeanTacticOp)
  | Repeat (op : LeanTacticOp)
  | Seq (ops : List LeanTacticOp)
  | Failure
deriving Repr

-- ---------------------------------------------------------------------------
-- 5. MacroM — hygiene engine
-- ---------------------------------------------------------------------------

structure MacroScope where
  val : Nat
deriving DecidableEq, Repr

structure HygienicName where
  base : String
  scopes : List MacroScope
deriving DecidableEq, Repr

-- ---------------------------------------------------------------------------
-- 6. Recursive goal stack
-- ---------------------------------------------------------------------------

structure RecGoal where
  id : MVarId
  parent : Option MVarId
  children : List MVarId
  layer : Nat
  tag : String
deriving DecidableEq, Repr

structure RecTacticState where
  root_goals : List RecGoal := []
  focus_path : List MVarId := []
  depth : Nat := 0
  aux : List MVarId := []
deriving DecidableEq, Repr

def RecTacticState.default : RecTacticState := {}

-- ---------------------------------------------------------------------------
-- 7. Lean tactic macro definitions (from grammar)
-- ---------------------------------------------------------------------------

def lean_tactic_macros : List (String × String × String) :=
  [ ("sila_tac", "tactic",
     "withMainContext do let goal <- getMainTarget; let goal' <- liftMetaM (DUP goal); evalTactic (<- `(tactic| DUP <;> sila_auto <;> try omega))"),
    ("crux_tac", "tactic",
     "withFreshMacroScope do `(tactic| sila_tac <;> crux_dup <;> try z3_decide <;> try aesop)"),
    ("dup_at", "tactic",
     "evalTactic (<- `(tactic| DUP at loc))"),
    ("let!", "term",
     "do let x <- mkFreshIdent x; `(let $x := $v; $body)"),
    ("have!", "tactic",
     "withFreshMacroScope do let n <- mkFreshIdent n; `(tactic| have $n : $t := $v)"),
    ("quote_hygienic", "term",
     "do let stx <- Quote.quote t; let stx' <- withFreshMacroScope (quote stx); elabTerm stx'") ]

-- ---------------------------------------------------------------------------
-- 8. MetaM key operations (reference surface)
-- ---------------------------------------------------------------------------

def meta_m_operations : List (String × String) :=
  [ ("getLCtx", "MetaM LocalContext"),
    ("withLCtx", "LocalContext -> MetaM a -> MetaM a"),
    ("mkFreshExprMVar", "Option Expr -> MetaM Expr"),
    ("assignExprMVar", "MVarId -> Expr -> MetaM Unit"),
    ("isDefEq", "Expr -> Expr -> MetaM Bool"),
    ("whnf", "Expr -> MetaM Expr"),
    ("reduce", "Expr -> MetaM Expr"),
    ("inferType", "Expr -> MetaM Expr"),
    ("synthInstance", "Expr -> MetaM Expr"),
    ("isTypeCorrect", "Expr -> MetaM Bool"),
    ("instantiateMVars", "Expr -> MetaM Expr"),
    ("withMVarContext", "MVarId -> MetaM a -> MetaM a"),
    ("getEnv", "MetaM Environment"),
    ("modifyEnv", "(Environment -> Environment) -> MetaM Unit"),
    ("trace", "Name -> (Unit -> MessageData) -> MetaM Unit"),
    ("throwError", "MessageData -> MetaM a"),
    ("orElse", "MetaM a -> (Unit -> MetaM a) -> MetaM a"),
    ("tryCatch", "MetaM a -> (Exception -> MetaM a) -> MetaM a") ]

-- ---------------------------------------------------------------------------
-- 9. TacticM key operations (reference surface)
-- ---------------------------------------------------------------------------

def tactic_m_operations : List (String × String) :=
  [ ("getGoals", "TacticM (List MVarId)"),
    ("setGoals", "List MVarId -> TacticM Unit"),
    ("getMainGoal", "TacticM MVarId"),
    ("getMainTarget", "TacticM Expr"),
    ("replaceMainGoal", "List MVarId -> TacticM Unit"),
    ("done", "TacticM Unit"),
    ("intro", "Name -> TacticM Unit"),
    ("intros", "TacticM Unit"),
    ("apply", "Expr -> TacticM Unit"),
    ("exact", "Expr -> TacticM Unit"),
    ("assumption", "TacticM Unit"),
    ("cases", "Expr -> TacticM Unit"),
    ("induction", "Expr -> TacticM Unit"),
    ("simp", "SimpConfig -> List SimpArg -> Location -> TacticM Unit"),
    ("left", "TacticM Unit"),
    ("right", "TacticM Unit"),
    ("constructor", "TacticM Unit"),
    ("exfalso", "TacticM Unit"),
    ("decide", "TacticM Unit"),
    ("omega", "TacticM Unit"),
    ("ring", "TacticM Unit"),
    ("allGoals", "TacticM Unit -> TacticM Unit"),
    ("anyGoals", "TacticM Unit -> TacticM Unit"),
    ("focus", "TacticM a -> TacticM a"),
    ("try", "TacticM a -> TacticM (Option a)"),
    ("repeat'", "TacticM Unit -> TacticM Unit"),
    ("first", "List (TacticM a) -> TacticM a"),
    ("liftMetaM", "MetaM a -> TacticM a"),
    ("liftMetaTactic", "(MVarId -> MetaM (List MVarId)) -> TacticM Unit"),
    ("evalTactic", "Syntax -> TacticM Unit"),
    ("withMainContext", "TacticM a -> TacticM a") ]

-- ---------------------------------------------------------------------------
-- 10. MonadQuotation operations
-- ---------------------------------------------------------------------------

def monad_quotation_operations : List (String × String) :=
  [ ("getCurrMacroScope", "m MacroScope"),
    ("getMainModule", "m Name"),
    ("withFreshMacroScope", "m a -> m a"),
    ("quote", "Syntax -> m Syntax"),
    ("quoteTerm", "Expr -> m Syntax"),
    ("mkIdent", "Name -> m Syntax"),
    ("mkFreshIdent", "Syntax -> m Syntax"),
    ("withAntiquote", "m a -> m a"),
    ("withRef", "Syntax -> m a -> m a") ]

theorem tactic_config_default :
    TacticConfig.default =
      { transparent := TransparencyMode.Default,
        new_goals := NewGoals.GoalsFirst,
        location := TacticLocation.Everywhere } := rfl

theorem lean_tactic_macros_length : lean_tactic_macros.length = 6 := by decide

theorem meta_m_operations_length : meta_m_operations.length = 18 := by decide

theorem tactic_m_operations_length : tactic_m_operations.length = 31 := by decide

theorem monad_quotation_operations_length : monad_quotation_operations.length = 9 := by decide

end Crux
