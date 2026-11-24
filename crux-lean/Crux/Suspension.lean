/-
Suspension store (fsl/src/crux/suspension.rs).
Suspended constraints that wake when a watched variable changes.

`propagate_store` loops until a full pass fires nothing. In Lean it is
a recursive function with fuel bounded by (number of entries + 1)
passes: wake only ever flips `fired` false → true and never back, so
at most one firing pass per entry can occur; the next pass then fires
nothing and the loop stops. The domain store does not change during
propagation, so a pass that fires nothing is followed by identical
passes.
-/

import Crux.Domain
import Crux.Arithmetic

namespace Crux

structure SuspensionEntry where
  id : Nat
  constraint : Constraint
  priority : Int
  watch_vars : List String
  fired : Bool := false
deriving DecidableEq, Repr

structure SuspensionStore where
  entries : List SuspensionEntry := []
  next_id : Nat := 0
deriving DecidableEq, Repr

def SuspensionStore.new : SuspensionStore := {}

def SuspensionStore.suspend (s : SuspensionStore) (c : Constraint) (priority : Int)
    (watch_vars : List String) : SuspensionStore × Nat :=
  let id := s.next_id
  ({ entries := s.entries ++ [{ id := id, constraint := c, priority := priority,
                                watch_vars := watch_vars, fired := false }],
     next_id := s.next_id + 1 }, id)

def SuspensionStore.wake (s : SuspensionStore) (var : String) (store : DomainStore) :
    SuspensionStore × List Nat :=
  let (entries, fired) := s.entries.foldl (fun (acc : List SuspensionEntry × List Nat) entry =>
    if !entry.fired && entry.watch_vars.contains var then
      match eval_constraint entry.constraint store with
      | .Entailed | .Failed => (acc.1 ++ [{ entry with fired := true }], acc.2 ++ [entry.id])
      | .Unknown => (acc.1 ++ [entry], acc.2)
    else (acc.1 ++ [entry], acc.2)) ([], [])
  ({ entries := entries, next_id := s.next_id }, fired)

def SuspensionStore.active_count (s : SuspensionStore) : Nat :=
  (s.entries.filter (fun e => !e.fired)).length

def SuspensionStore.clear (_ : SuspensionStore) : SuspensionStore :=
  { entries := [], next_id := 0 }

def suspend_goal (s : SuspensionStore) (c : Constraint) (priority : Int)
    (watch_vars : List String) : SuspensionStore × Nat :=
  s.suspend c priority watch_vars

def wake_var (s : SuspensionStore) (var : String) (store : DomainStore) :
    SuspensionStore × List Nat :=
  s.wake var store

def propagate_pass (s : SuspensionStore) (store : DomainStore) : SuspensionStore × Bool :=
  store.vars.foldl (fun (acc : SuspensionStore × Bool) var =>
    let (s', fired) := acc.1.wake var store
    (s', acc.2 || !fired.isEmpty)) (s, false)

def propagate_store_fueled (s : SuspensionStore) (store : DomainStore) (fuel : Nat) :
    SuspensionStore × DomainStore :=
  match fuel with
  | 0 => (s, store)
  | fuel + 1 =>
    let (s', any_fired) := propagate_pass s store
    if any_fired then propagate_store_fueled s' store fuel else (s', store)

def propagate_store (s : SuspensionStore) (store : DomainStore) : SuspensionStore × DomainStore :=
  propagate_store_fueled s store (s.entries.length + 1)

theorem test_suspend_and_wake :
    let ds0 := DomainStore.new.set_domain "x" (.Range 1 10)
    let (ss1, id) := SuspensionStore.new.suspend (.eq "x" 5) 1 ["x"]
    let ds1 := ds0.set_value "x" 5
    let (ss2, fired) := ss1.wake "x" ds1
    ss1.active_count = 1 ∧ fired.contains id ∧ ss2.active_count = 0 := by decide

theorem test_propagate :
    let ds0 := (DomainStore.new.set_domain "x" (.Range 1 10)).set_domain "y" (.Range 1 10)
    let (ss1, _) := SuspensionStore.new.suspend (.eq "x" 3) 1 ["x"]
    let (ss2, _) := ss1.suspend (.lt "x" "y") 2 ["x", "y"]
    let ds1 := ds0.set_value "x" 3
    let (ss3, _) := propagate_store ss2 ds1
    ss3.active_count ≤ 1 := by decide

end Crux
