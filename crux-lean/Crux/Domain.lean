/-
Domain store (fsl/src/crux/../domain.rs, referenced as super::domain).
Intervals, sets, fixed values, and the store that maps variables to them.

Modeling note: the Rust uses HashMap<String, Domain> and
HashMap<String, i64>. This project has no Mathlib and no Batteries, so
the two maps are modeled as association lists (List (String × Domain)
and List (String × Int)) with lookup/insert helpers. Lookup is by first
matching key; insert replaces an existing key in place.
-/

namespace Crux

inductive Domain where
  | Range (lo : Int) (hi : Int)
  | Set (vals : List Int)
  | Fixed (v : Int)
  | Free
deriving DecidableEq, Repr

def Domain.size : Domain → Nat
  | .Range lo hi => (hi - lo + 1).toNat
  | .Set vals => vals.length
  | .Fixed _ => 1
  | .Free => 0

def Domain.contains : Domain → Int → Bool
  | .Range lo hi, val => lo ≤ val && val ≤ hi
  | .Set vals, val => vals.contains val
  | .Fixed v, val => v == val
  | .Free, _ => true

def Domain.intersect : Domain → Domain → Option Domain
  | .Range a_lo a_hi, .Range b_lo b_hi =>
    let lo := max a_lo b_lo
    let hi := min a_hi b_hi
    if lo ≤ hi then some (.Range lo hi) else none
  | .Range lo hi, .Set vals | .Set vals, .Range lo hi =>
    let filtered := vals.filter (fun v => lo ≤ v && v ≤ hi)
    if filtered.isEmpty then none else some (.Set filtered)
  | .Set a, .Set b =>
    let filtered := a.filter (fun v => b.contains v)
    if filtered.isEmpty then none else some (.Set filtered)
  | .Fixed v, other | other, .Fixed v =>
    if other.contains v then some (.Fixed v) else none
  | _, _ => none

def Domain.remove (d : Domain) (val : Int) : Option Domain :=
  match d with
  | .Range lo hi =>
    if val < lo || val > hi then some (.Range lo hi)
    else if lo == hi then none
    else if val == lo then some (.Range (lo + 1) hi)
    else if val == hi then some (.Range lo (hi - 1))
    else
      let n := (hi - lo + 1).toNat
      let vals := (List.range n).map (fun (i : Nat) => lo + (i : Int)) |>.filter (fun v => v != val)
      some (.Set vals)
  | .Set vals =>
    let filtered := vals.filter (fun v => v != val)
    if filtered.isEmpty then none else some (.Set filtered)
  | .Fixed v =>
    if v == val then none else some (.Fixed v)
  | .Free => some .Free

def Domain.min : Domain → Option Int
  | .Range lo _ => some lo
  | .Set vals => vals.foldl (fun acc v => match acc with | none => some v | some m => some (if m ≤ v then m else v)) none
  | .Fixed v => some v
  | .Free => none

def Domain.max : Domain → Option Int
  | .Range _ hi => some hi
  | .Set vals => vals.foldl (fun acc v => match acc with | none => some v | some m => some (if m ≤ v then v else m)) none
  | .Fixed v => some v
  | .Free => none

def assocLookup {α : Type} (l : List (String × α)) (key : String) : Option α :=
  (l.find? (fun (k, _) => k == key)).map (fun (_, v) => v)

def assocInsert {α : Type} (l : List (String × α)) (key : String) (v : α) : List (String × α) :=
  match l with
  | [] => [(key, v)]
  | (k, x) :: rest => if k == key then (key, v) :: rest else (k, x) :: assocInsert rest key v

structure DomainStore where
  domains : List (String × Domain) := []
  values : List (String × Int) := []
deriving DecidableEq, Repr

def DomainStore.new : DomainStore := {}

def DomainStore.set_domain (store : DomainStore) (var : String) (dom : Domain) : DomainStore :=
  let values := match dom with
    | .Fixed v => assocInsert store.values var v
    | _ => store.values
  { domains := assocInsert store.domains var dom, values := values }

def DomainStore.get_domain (store : DomainStore) (var : String) : Domain :=
  (assocLookup store.domains var).getD .Free

def DomainStore.get_value (store : DomainStore) (var : String) : Option Int :=
  assocLookup store.values var

def DomainStore.set_value (store : DomainStore) (var : String) (val : Int) : DomainStore :=
  { domains := assocInsert store.domains var (.Fixed val),
    values := assocInsert store.values var val }

def DomainStore.get_bounds (store : DomainStore) (var : String) : Option Int × Option Int :=
  let dom := store.get_domain var
  (dom.min, dom.max)

def DomainStore.vars (store : DomainStore) : List String :=
  store.domains.map (fun (k, _) => k)

def DomainStore.any_empty (store : DomainStore) : Bool :=
  store.domains.any (fun (_, d) => match d with | .Free => true | _ => false)

def DomainStore.all_fixed (store : DomainStore) : Bool :=
  store.domains.all (fun (_, d) => match d with | .Fixed _ => true | _ => false)

def DomainStore.reset_statuses (store : DomainStore) : DomainStore :=
  -- no-op for DomainStore; constraint statuses live elsewhere
  store

def set_domain_decl (store : DomainStore) (var : String) (dom : Domain) : DomainStore :=
  store.set_domain var dom

def get_domain_decl (store : DomainStore) (var : String) : Domain :=
  store.get_domain var

def get_bounds (store : DomainStore) (var : String) : Option Int × Option Int :=
  store.get_bounds var

theorem test_domain_range :
    (Domain.Range 1 10).size = 10 ∧
    (Domain.Range 1 10).contains 5 = true ∧
    (Domain.Range 1 10).contains 11 = false := by decide

theorem test_domain_intersect :
    (Domain.Range 1 5).intersect (Domain.Range 3 8) = some (Domain.Range 3 5) := by decide

theorem test_domain_remove :
    (Domain.Range 1 3).remove 2 = some (Domain.Set [1, 3]) ∧
    (Domain.Range 1 3).remove 1 = some (Domain.Range 2 3) ∧
    (Domain.Range 1 3).remove 4 = some (Domain.Range 1 3) := by decide

theorem test_domain_store :
    let store := DomainStore.new.set_domain "x" (.Range 1 10)
    store.get_domain "x" = .Range 1 10 ∧
    (store.set_value "x" 5).get_value "x" = some 5 ∧
    (store.set_value "x" 5).get_domain "x" = .Fixed 5 := by decide

end Crux
