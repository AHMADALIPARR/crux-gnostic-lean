/-
Lean 4 Tactic Infrastructure (appended sections 4-7 of fsl/src/crux/lean_backend.rs).
Goal management, combinators, recursive goal stack, macro hygiene helpers.

Modeling note: the Rust takes &mut state and closures. Lean is pure, so
the state-taking operations return the updated state, and the combinators
take explicit function values: tactic_try takes a (Unit → Option T) thunk,
tactic_first takes a List of (Unit → Option T) thunks, tactic_repeat takes
a (Unit → Bool) thunk.
-/

import Crux.LeanMonadStack

namespace Crux

-- ---------------------------------------------------------------------------
-- 4. TacticM goal management operations
-- ---------------------------------------------------------------------------

def tactic_get_goals (state : TacticState) : List MVarId :=
  state.goals

def tactic_set_goals (state : TacticState) (goals : List MVarId) : TacticState :=
  { state with goals := goals }

def tactic_get_main_goal (state : TacticState) : Option MVarId :=
  state.goals.head?

def tactic_replace_main_goal (state : TacticState) (new_goals : List MVarId) : TacticState :=
  match state.goals with
  | [] => state
  | _ :: rest => { state with goals := new_goals ++ rest }

def tactic_done (state : TacticState) : Bool :=
  state.goals.isEmpty

def tactic_prune_solved (state : TacticState) : TacticState :=
  -- In real Lean 4 this checks if mvar is assigned; here we keep all
  state

-- ---------------------------------------------------------------------------
-- 5. Tactic combinators (pure, matching Lean 4 semantics)
-- ---------------------------------------------------------------------------

def tactic_try {T : Type} (f : Unit → Option T) : Option T :=
  f ()

def tactic_first {T : Type} (tactics : List (Unit → Option T)) : Option T :=
  match tactics with
  | [] => none
  | t :: ts =>
    match t () with
    | some result => some result
    | none => tactic_first ts

def tactic_repeat (tactic : Unit → Bool) (max_iter : Nat) : Nat :=
  go max_iter 0
where
  go : Nat → Nat → Nat
    | 0, count => count
    | fuel + 1, count =>
      if tactic () then go fuel (count + 1) else count

-- ---------------------------------------------------------------------------
-- 6. Recursive goal stack operations
-- ---------------------------------------------------------------------------

def push_focus (state : RecTacticState) (goal : MVarId) : RecTacticState :=
  { state with focus_path := state.focus_path ++ [goal], depth := state.depth + 1 }

def pop_focus (state : RecTacticState) : RecTacticState :=
  { state with
    focus_path := state.focus_path.dropLast,
    depth := if state.depth > 0 then state.depth - 1 else 0 }

def current_depth (state : RecTacticState) : Nat :=
  state.depth

def make_rec_goal (id : MVarId) (parent : Option MVarId) (layer : Nat) (tag : String) : RecGoal :=
  { id := id, parent := parent, children := [], layer := layer, tag := tag }

-- ---------------------------------------------------------------------------
-- 7. Macro hygiene helpers
-- ---------------------------------------------------------------------------

def add_macro_scope (base : String) (scope : MacroScope) : HygienicName :=
  { base := base, scopes := [scope] }

def erase_macro_scopes (hname : HygienicName) : String :=
  hname.base

def has_macro_scopes (hname : HygienicName) : Bool :=
  !hname.scopes.isEmpty

theorem replace_main_goal_example :
    tactic_replace_main_goal
      { goals := [⟨1⟩, ⟨2⟩], aux_goals := [] }
      [⟨7⟩, ⟨8⟩]
      = { goals := [⟨7⟩, ⟨8⟩, ⟨2⟩], aux_goals := [] } := rfl

theorem tactic_first_example :
    tactic_first [fun _ => (none : Option Nat), fun _ => some 3] = some 3 := rfl

theorem pop_focus_depth :
    current_depth (pop_focus (push_focus RecTacticState.default ⟨1⟩)) = 0 := rfl

end Crux
