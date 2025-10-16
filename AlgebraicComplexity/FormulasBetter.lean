/-
Copyright (c) 2025 Shreyas Srinivas, Alexander Ikonomou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Ikonomou, Shreyas Srinivas
-/
import Mathlib


namespace AlgebraicComplexity

namespace Formulas

open MvPolynomial

inductive Formula (α : Type u) (Idx : Type v) where
| Var (x: Idx)
| Add (g h: Formula α Idx): Formula α Idx
| Mult (g h: Formula α Idx): Formula α Idx
| Neg (g : Formula α Idx): Formula α Idx
| Const (c : α): Formula α Idx

notation "C[" val "]" => Formula.Const val
notation "V[" name "]" =>  Formula.Var ⟨name, by grind⟩

variable {α : Type u} {Idx : Type v}

instance zero [Ring α]: Zero (Formula α Idx) where
  zero := .Const 0

instance one [Ring α]: One (Formula α Idx) where
  one := .Const 1

instance add [Ring α]: Add (Formula α Idx) where
  add := .Add

instance neg [Ring α] : Neg (Formula α Idx) where
  neg := .Neg

instance sub [Ring α] : Sub (Formula α Idx) where
  sub a b := a + (- b)

instance mul' [Ring α] : Mul (Formula α Idx) where
  mul := .Mult

def inputSize [Fintype Idx] (_ : Formula α Idx) := Fintype.card Idx

def size (f: Formula α Idx) : ℕ :=
match f with
| .Var _ => 1
| .Add g h => size g + size h + 1
| .Mult g h => size g + size h + 1
| .Neg g => size g + 1
| .Const _ => 1

def depth (f: Formula α Idx) : ℕ :=
match f with
| .Var _ => 0
| .Add g h => max (depth g) (depth h) + 1
| .Mult g h => max (depth g) (depth h) + 1
| .Neg g => depth g + 1
| .Const _ => 0

@[simp]
noncomputable def evalToPolynomial [CommRing α] (f: Formula α Idx) : (MvPolynomial Idx α) :=
match f with
| .Var x => X x ^ 1
| .Add g h => evalToPolynomial g + evalToPolynomial h
| .Mult g h => evalToPolynomial g * evalToPolynomial h
| .Neg g => - evalToPolynomial g
| .Const c => MvPolynomial.C c

lemma size_zero_const_or_var (f: Formula α Idx) :
  size f = 0 → (∃ x, f = .Var x) ∨ (∃ c, f = .Const c) := by
  intro h
  cases f with (simp_all [size])

lemma size_highest_degree [CommRing α] [Nontrivial α] :
  ∀ f: Formula α Idx, size f ≥ MvPolynomial.totalDegree (evalToPolynomial f) - 1 := by
    intro f
    induction f with (simp_all[evalToPolynomial])
      | Add g h ihg ihh => {
        rw[size]
        have h : (evalToPolynomial g + evalToPolynomial h).totalDegree - 1 ≤ max (size g) (size h) := by
          have t := totalDegree_add (evalToPolynomial g) (evalToPolynomial h)
          omega
        grind
      }
      | Mult g h ihg ihh => {
        rw[size]
        have m := totalDegree_mul (evalToPolynomial g) (evalToPolynomial h)
        grind
      }
      | Neg g ih => {
        rw [size]
        grind
      }


/--
`coerce_up f` coerces a formula `f` in `n` variables to a formula in `n + 1` variables.
-/
def coeFormula [Coe Idx₁ Idx₂] (f : Formula α Idx₁) : Formula α Idx₂ :=
  match f with
    | .Var x => .Var ↑x
    | .Add g h => .Add (coeFormula g) (coeFormula h)
    | .Mult g h => .Mult (coeFormula g) (coeFormula h)
    | .Neg p => .Neg (coeFormula p)
    | .Const c => .Const c

/--
This is the Coe typeclass instance for the above coercion. T
-/
instance [Coe Idx₁ Idx₂]: Coe (Formula α Idx₁) (Formula α Idx₂) where
  coe f := coeFormula f

#print MvPolynomial.rename
#print MvPolynomial


theorem coeFormula_composes_rename
  [CommRing α]
  [instCoe : Coe Idx₁ Idx₂]
  (f : Formula α Idx₁)
  (p : MvPolynomial Idx₁ α)
  (heval : evalToPolynomial  f = p)
  : (evalToPolynomial (coeFormula f)) = MvPolynomial.rename instCoe.coe p := by
    induction f generalizing p with (
      simp_all [coeFormula]
      rw [←heval]
      simp only [rename_X, map_add, map_mul, map_neg, algHom_C, algebraMap_eq]
    )


/--
The complexity of a polynomial `p`, denoted `L p` is the size of the smallest formula that evaluates to it
-/
def FormulaComplexityUpperBound
  [CommRing α]
  (p : MvPolynomial ID α) (size_bound : ℕ): Prop :=
    ∃ formula, evalToPolynomial formula = p
    ∧ size formula = size_bound

def FormulaComplexityLowerBound
  [CommRing α]
  (p : MvPolynomial ID α) (size_bound : ℕ) : Prop :=
    (∀ other_formula, evalToPolynomial other_formula = p
      → size_bound ≤ size other_formula)


theorem complexity_UB_monomial
  [CommRing α] [Nontrivial α]
  (deg: ℕ) :
  let my_monomial (x : ID) : MvPolynomial ID α := (X x) ^ deg
  ∀ x : ID, FormulaComplexityUpperBound (my_monomial x) (2*deg + 1) := by
  extract_lets monom
  intro x
  have hmonom_x:  monom x = (X x)^deg := by
    simp [monom]
  induction deg with (simp[FormulaComplexityUpperBound])
  | zero =>
      simp_all only [pow_zero]
      use C[1]
      constructor
      · simp [evalToPolynomial]
      · simp [size]
  | succ n ih =>
      simp_all only [forall_const]
      unfold FormulaComplexityUpperBound at ih
      obtain ⟨formula, ⟨h₁, h₂⟩⟩ := ih
      exists (formula * (.Var x))
      simp [evalToPolynomial, h₁]
      constructor
      · ring
      · simp[size]
        rw [h₂]
        ring

end Formulas

end AlgebraicComplexity
