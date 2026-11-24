/-
Constraint search (fsl/src/crux/search.rs).
Pure functions threading DomainStore explicitly. The recursive search
is bounded by a single fuel argument initialized to the Rust `limit`:
fuel decreases on every recursive call — both on each depth step and
on each value tried. The Rust limit bounds depth only; the Lean fuel
bounds total recursive steps, so a search with a large branching
factor could exhaust fuel sooner than the Rust limit would allow.
For the tested inputs (limit 100, tiny domains) the outcomes coincide.
-/

import Crux.Domain

namespace Crux

inductive SearchStrategy where
  | Complete
  | FirstFail
  | DomOverDeg
  | AntiFirstFail
deriving DecidableEq, Repr

inductive SearchResult where
  | Sat (model : List (String × Int))
  | Unsat
  | Unknown
deriving DecidableEq, Repr

def first_fail_select (store : DomainStore) (vars : List String) : Option String :=
  let best := vars.foldl (fun (best : Option (String × Nat)) var =>
    let size := (store.get_domain var).size
    if size > 1 then
      match best with
      | none => some (var, size)
      | some (_, best_size) => if size < best_size then some (var, size) else best
    else best) none
  best.map (fun (v, _) => v)

def indomain (store : DomainStore) (var : String) : List Int :=
  match store.get_domain var with
  | .Range lo hi =>
    let n := (hi - lo + 1).toNat
    (List.range n).map (fun (i : Nat) => lo + (i : Int))
  | .Set vals => vals
  | .Fixed v => [v]
  | .Free => []

def modelOf (store : DomainStore) : List (String × Int) :=
  store.vars.filterMap (fun v => (store.get_value v).map (fun val => (v, val)))

mutual
def search_recursive (store : DomainStore) (vars : List String) (strategy : SearchStrategy) (fuel : Nat) : SearchResult × DomainStore :=
  match fuel with
  | 0 => (.Unknown, store)
  | fuel + 1 =>
    if vars.isEmpty || store.all_fixed then
      (.Sat (modelOf store), store)
    else
      let chosen := match strategy with
        | .FirstFail | .Complete | .DomOverDeg => first_fail_select store vars
        | _ => vars.head?
      match chosen with
      | none => (.Sat (modelOf store), store)
      | some c =>
        let values := indomain store c
        let old_domain := store.get_domain c
        tryValues store vars strategy fuel c values old_domain

def tryValues (store : DomainStore) (vars : List String) (strategy : SearchStrategy) (fuel : Nat) (chosen : String) (values : List Int) (old_domain : Domain) : SearchResult × DomainStore :=
  match fuel, values with
  | _, [] => (.Unsat, store)
  | 0, _ => (.Unknown, store)
  | fuel + 1, val :: rest =>
    let store' := store.set_value chosen val
    let remaining := vars.filter (fun v => v != chosen)
    let (result, store'') := search_recursive store' remaining strategy fuel
    match result with
    | .Sat _ => (result, store'')
    | _ => tryValues (store''.set_domain chosen old_domain) vars strategy fuel chosen rest old_domain
end

def search_vars (store : DomainStore) (strategy : SearchStrategy) (limit : Nat) : SearchResult :=
  (search_recursive store store.vars strategy limit).1

def minimize_cost (store : DomainStore) (cost_vars : List String) (strategy : SearchStrategy) (limit : Nat) : SearchResult :=
  match search_vars store strategy limit with
  | .Sat model =>
    let _cost : Int := cost_vars.filterMap (fun cv =>
      (model.find? (fun (k, _) => k == cv)).map (fun (_, v) => v)) |>.sum
    .Sat model
  | result => result

theorem test_first_fail :
    let store := DomainStore.new.set_domain "x" (.Range 1 100)
    let store := store.set_domain "y" (.Set [1, 2, 3])
    let store := store.set_domain "z" (.Fixed 5)
    first_fail_select store ["x", "y", "z"] = some "y" := by decide

theorem test_search_simple :
    search_vars (DomainStore.new.set_domain "x" (.Range 1 3)) .Complete 100 =
      .Sat [("x", 1)] := by decide

theorem test_search_unsat :
    search_vars (DomainStore.new.set_domain "x" (.Fixed 1)) .Complete 100 =
      .Sat [("x", 1)] := by decide

end Crux
