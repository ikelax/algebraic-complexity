import Mathlib
import AlgebraicComplexity.Formulas

/-!

## Circuits

Circuits are directed acyclic graphs. They differ from formulas in that nodes can have an out-degree greater than 1.
This means that they needn't have multiple copies of the same circuit whose output is used as input to multiple nodes. Further,  we explicitly want to use only one copy of a circuit where possible since this can affect the size of the circuit
!-/

namespace AlgebraicComplexity

namespace Circuits

open MvPolynomial

-- Lambda calculus values. Basically formulas with
-- additional BVar constructor
inductive CTerm (α : Type u) (ID : Type v) where
  | CVar (x: ID) -- Circuit input nodes. important to keep separate.
  | BVar (n : ℕ)
  | Add (g h: CTerm α ID): CTerm α ID
  | Mult (g h: CTerm α ID): CTerm α ID
  | Neg (g : CTerm α ID): CTerm α ID
  | Const (c : α): CTerm α ID

/-- This Lambda calculus is meant to be a safe substitution mechanism. Whence the separation between CTerms and Circuits.
 You can always distinguish between the lambda calculus stuff
and the purely circuit stuff. This matters for several stuff -/
inductive Circuit (α : Type u) (ID : Type v) where
  | Pure (t : CTerm α ID) -- Pure Termsthose
  | Abs (t : Circuit α ID) -- Lambda abstraction. De Bruijn indices. No free variables. Disallow loose BVars.
  | App (c₁ c₂ : Circuit α ID) -- Apply

variable {α : Type u} {ID : Type v}

def isPureCircuit (c : Circuit α ID) : Prop :=
  match c with
  | .Pure _ => True
  | _ => False

def hasCTermLooseBVarsAux (c : CTerm α ID) (binderDepth : Nat) : Prop :=
  match c with
  | .CVar _ => True
  | .Const _ => True
  | .BVar x =>
      if x > binderDepth then
        False
      else
        True
  | .Add f g => hasCTermLooseBVarsAux f binderDepth ∧ hasCTermLooseBVarsAux g binderDepth
  | .Mult f g => hasCTermLooseBVarsAux f binderDepth ∧
  hasCTermLooseBVarsAux g binderDepth
  | .Neg c => hasCTermLooseBVarsAux c binderDepth

def hasLooseBVarsAux (c : Circuit α ID) (binderDepth : Nat) : Prop :=
  match c with
  | .Pure circ =>
      hasCTermLooseBVarsAux circ binderDepth
  | .Abs c =>
      hasLooseBVarsAux c (binderDepth + 1)
  | .App c₁ c₂ =>
      hasLooseBVarsAux c₁ binderDepth ∧ hasLooseBVarsAux c₂ binderDepth

def hasLooseBVars (c : Circuit α ID) : Prop :=
  hasLooseBVarsAux c 0

def isPureCTerm (c : CTerm α ID) : Prop :=
  match c with
  | .CVar _ => True
  | .Const _ => True
  | .BVar _ => False
  | .Add f g => isPureCTerm f ∧ isPureCTerm g
  | .Mult f g => isPureCTerm f ∧ isPureCTerm g
  | .Neg c => isPureCTerm c

theorem noBindersNoBVars (c : CTerm α ID) :
  isPureCTerm c → ∀ x, c ≠ .BVar x := by
  intro h x
  cases c with (simp_all[isPureCTerm])

theorem noBinderAddSubTerm (g h : CTerm α ID) :
  isPureCTerm (.Add g h) → isPureCTerm g ∧ isPureCTerm h := by
  intro hyp
  constructor
  all_goals {
    unfold isPureCTerm at hyp
    tauto
  }


instance [Ring α]: Zero (CTerm α ID) where
  zero := .Const 0

instance [Ring α]: One (CTerm α ID) where
  one := .Const 1

instance : Add (CTerm α ID) where
  add := .Add

instance : Neg (CTerm α ID) where
  neg := .Neg

instance : Sub (CTerm α ID) where
  sub a b := a + (- b)

instance : Mul (CTerm α ID) where
  mul := .Mult

instance [Ring α]: Zero (Circuit α ID) where
  zero := .Pure 0

instance [Ring α]: One (Circuit α ID) where
  one := .Pure 1



def sizeCTerm (f: CTerm α ID) : ℕ :=
match f with
| .CVar _ => 1
| .BVar _ => 1 -- this I doubt can be decided until it is substituted. But I am also not sure matching the textbook definition makes much sense. What happens if a Lambda is unapplied?
| .Add g h => sizeCTerm g + sizeCTerm h + 1
| .Mult g h => sizeCTerm g + sizeCTerm h + 1
| .Neg g => sizeCTerm g + 1
| .Const _ => 0

def depthCTerm (f: CTerm α ID) : ℕ :=
match f with
| .CVar _ => 0
| .BVar _ => 0
| .Add g h => max (depthCTerm g) (depthCTerm h) + 1
| .Mult g h => max (depthCTerm g) (depthCTerm h) + 1
| .Neg g => depthCTerm g + 1
| .Const _ => 0

def sizeCircuit (c : Circuit α ID) : ℕ :=
  match c with
  | .Pure t => sizeCTerm t
  | .Abs c => sizeCircuit c
  | .App c₁ c₂ => sizeCircuit c₁ + sizeCircuit c₂
open Formulas
noncomputable def pureCTermToFormula
  (f: CTerm α ID) (hyp : isPureCTerm f):  Formula α ID :=
match f with
| .CVar x => .CVar x
| .Add g h => .Add (pureCTermToFormula g (by unfold isPureCTerm at hyp; tauto)) (pureCTermToFormula h (by unfold isPureCTerm at hyp; tauto))
| .Mult g h => .Mult (pureCTermToFormula g (by unfold isPureCTerm at hyp; tauto)) (pureCTermToFormula h (by unfold isPureCTerm at hyp; tauto))
| .Neg g => - (pureCTermToFormula g hyp)
| .Const c => .Const c
| .BVar n => nomatch hyp

noncomputable def evalToPolynomial [CommRing α] (c : CTerm α ID) (hyp : isPureCTerm c) : MvPolynomial ID α :=
  let form := pureCTermToFormula c hyp
  Formulas.evalToPolynomial form

end Circuits

end AlgebraicComplexity
