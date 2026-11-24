/-
Constraint evaluation (fsl/src/crux/arithmetic.rs, formerly constraint.rs).

PARTIAL: the source file as sent ends mid-function inside the Lt arm
(the last line sent is `match dom_b.min()`), and no remainder is coming.
Only the Eq and Neq arms are complete in the source. This port covers
exactly those arms; the remaining arms return Unknown so the function
is total. The Lt arm — and everything after it — awaits the rest of the
file, which the user confirms does not exist.
-/

import Crux.Domain

namespace Crux

inductive Constraint where
  | Eq (var : String) (val : Int)
  | Neq (var : String) (val : Int)
  | Lt (a : String) (b : String)
  | Le (a : String) (b : String)
  | Gt (a : String) (b : String)
  | Ge (a : String) (b : String)
  | Linear (terms : List (String × Int)) (rhs : Int)
  | Reified (c : Constraint) (name : String)
deriving DecidableEq, Repr

def Constraint.eq (var : String) (val : Int) : Constraint :=
  .Eq var val

def Constraint.neq (var : String) (val : Int) : Constraint :=
  .Neq var val

def Constraint.lt (a : String) (b : String) : Constraint :=
  .Lt a b

def Constraint.le (a : String) (b : String) : Constraint :=
  .Le a b

def Constraint.gt (a : String) (b : String) : Constraint :=
  .Gt a b

def Constraint.ge (a : String) (b : String) : Constraint :=
  .Ge a b

def Constraint.linear (terms : List (String × Int)) (rhs : Int) : Constraint :=
  .Linear terms rhs

inductive EvalResult where
  | Entailed | Failed | Unknown
deriving DecidableEq, Repr

def eval_constraint (c : Constraint) (store : DomainStore) : EvalResult :=
  match c with
  | .Eq var val =>
    match store.get_value var with
    | some v => if v == val then .Entailed else .Failed
    | none =>
      let dom := store.get_domain var
      if !dom.contains val then .Failed else .Unknown
  | .Neq var val =>
    match store.get_value var with
    | some v => if v != val then .Entailed else .Failed
    | none =>
      let dom := store.get_domain var
      if dom == .Fixed val then .Failed else .Unknown
  | _ => .Unknown

theorem eval_constraint_eq_entailed :
    eval_constraint (.Eq "x" 5) (DomainStore.new.set_value "x" 5) = .Entailed := by decide

theorem eval_constraint_eq_failed :
    eval_constraint (.Eq "x" 5) (DomainStore.new.set_value "x" 6) = .Failed := by decide

theorem eval_constraint_lt_unknown :
    eval_constraint (.Lt "x" "y")
      ((DomainStore.new.set_domain "x" (.Range 1 10)).set_domain "y" (.Range 1 10)) = .Unknown := by decide

end Crux
