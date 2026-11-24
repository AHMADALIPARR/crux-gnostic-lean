/-
Proof-carrying code (fsl/src/crux/pcc.rs).
Derivations, certificates, and certified states.
-/

import Crux.Ast
import Crux.Omega

namespace Crux

mutual
structure SilaDerivation where
  state : State
  formula : Formula
  rules : List DerivationRule := []
deriving Repr

inductive DerivationRule where
  | Axiom (formula : Formula)
  | ModusPonens (imp : SilaDerivation) (ant : SilaDerivation)
  | Generalization (inner : SilaDerivation) (var : Ident)
  | RecursiveUnfold (inner : SilaDerivation)
  | StateUpdate (inner : SilaDerivation) (binding : Binding)
  | OmegaConfirmed (formula : Formula)
deriving Repr
end

mutual
def SilaDerivation.is_validFuel : SilaDerivation → Nat → Bool
  | _, 0 => false
  | d, fuel + 1 => validRulesFuel d.rules fuel
termination_by _d fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _

def validRulesFuel : List DerivationRule → Nat → Bool
  | [], _ => true
  | _, 0 => false
  | r :: rs, fuel + 1 => (r.is_validFuel fuel) && (validRulesFuel rs fuel)
termination_by _rs fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _

def DerivationRule.is_validFuel : DerivationRule → Nat → Bool
  | _, 0 => false
  | .Axiom _, _ => true
  | .ModusPonens imp ant, fuel + 1 => (imp.is_validFuel fuel) && (ant.is_validFuel fuel)
  | .Generalization inner _, fuel + 1 => inner.is_validFuel fuel
  | .RecursiveUnfold inner, fuel + 1 => inner.is_validFuel fuel
  | .StateUpdate inner _, fuel + 1 => inner.is_validFuel fuel
  | .OmegaConfirmed _, _ => true
termination_by _r fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _
end

/-- Fuel bound for `SilaDerivation.is_valid`. The Rust `is_valid` is total
over any derivation depth; the Lean port threads an explicit fuel (the same
pattern as the Russian parser) and the public wrapper supplies a fixed
bound. Derivations deeper than this bound evaluate to `false`. -/
def SilaDerivation.is_validFuelBound : Nat := 1000000

def SilaDerivation.is_valid (d : SilaDerivation) : Bool :=
  d.is_validFuel SilaDerivation.is_validFuelBound

def SilaDerivation.axiom (state : State) (formula : Formula) : SilaDerivation :=
  { state := state, formula := formula, rules := [.Axiom formula] }

def SilaDerivation.modus_ponens (state : State) (imp_formula : Formula) (imp_deriv : SilaDerivation)
    (ant_formula : Formula) (ant_deriv : SilaDerivation) : SilaDerivation :=
  let result_formula := match imp_formula with
    | .Implies _ consequent => consequent
    | _ => imp_formula
  { state := state, formula := result_formula,
    rules := [.ModusPonens imp_deriv ant_deriv] }

def SilaDerivation.state_update (state : State) (formula : Formula) (binding : Binding)
    (inner : SilaDerivation) : SilaDerivation :=
  { state := state, formula := formula, rules := [.StateUpdate inner binding] }

def SilaDerivation.omega_confirmed (state : State) (formula : Formula) : SilaDerivation :=
  { state := state, formula := formula, rules := [.OmegaConfirmed formula] }

inductive ProofCertificate where
  | Z3Cert (model : String)
  | SASCert (invariant : String)
  | LeanCert (expr : String)
  | SilaCert (deriv : SilaDerivation)
  | Compose (a b : ProofCertificate)
  | Reflect (formula : Formula)
deriving Repr

structure ProofCarrying (α : Type) where
  value : α
  proof : ProofCertificate

def ProofCarrying.certify {α : Type} (value : α) (proof : ProofCertificate) : ProofCarrying α :=
  { value := value, proof := proof }

def ProofCarrying.extract {α : Type} (p : ProofCarrying α) : α × ProofCertificate :=
  (p.value, p.proof)

structure CertifiedState where
  state : State
  formula : Formula
  derivation : SilaDerivation
  pcc : ProofCarrying Unit

def CertifiedState.new (state : State) (formula : Formula) : CertifiedState :=
  { state := state, formula := formula,
    derivation := SilaDerivation.axiom state formula,
    pcc := ProofCarrying.certify () (.SilaCert (SilaDerivation.axiom state formula)) }

def CertifiedState.lift (c : CertifiedState) (rule : DerivationRule) : CertifiedState :=
  { c with derivation := { state := c.state, formula := c.formula, rules := c.derivation.rules ++ [rule] } }

def CertifiedState.is_proved (c : CertifiedState) : Bool :=
  c.derivation.is_valid

def compose_pcc (a b : ProofCertificate) : ProofCertificate :=
  .Compose a b

def reflect_pcc (formula : Formula) : ProofCertificate :=
  .Reflect formula

def omega_to_derivation (state : State) (formula : Formula) : SilaDerivation :=
  SilaDerivation.omega_confirmed state formula

theorem axiom_valid :
    (SilaDerivation.axiom .S0 (.Atomic .True)).is_valid = true := by
  simp [SilaDerivation.is_valid, SilaDerivation.is_validFuelBound,
    SilaDerivation.is_validFuel, validRulesFuel,
    DerivationRule.is_validFuel, SilaDerivation.axiom]

end Crux
