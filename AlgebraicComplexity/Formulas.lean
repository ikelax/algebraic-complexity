import Mathlib

open MvPolynomial

inductive Formula (α : Type u) (n : ℕ) where
| Var (x: Fin n)
| Add (g h: Formula α n): Formula α n
| Mult (g h: Formula α n): Formula α n
| Neg (g : Formula α n): Formula α n
| Const (c : α): Formula α n

notation "C[" val "]" => Formula.Const val
notation "V[" name "]" =>  Formula.Var ⟨name, by decide⟩
instance zero [Ring α]: Zero (Formula α n) where
  zero := .Const 0

instance one [Ring α]: One (Formula α n) where
  one := .Const 1

instance add [Ring α]: Add (Formula α n) where
  add := .Add

instance neg [Ring α] : Neg (Formula α n) where
  neg := .Neg

instance sub [Ring α] : Sub (Formula α n) where
  sub a b := a + (- b)

instance mul' [Ring α] : Mul (Formula α n) where
  mul := .Mult

def size (f: Formula α n) : ℕ :=
match f with
| .Var _ => 0
| .Add g h => size g + size h + 1
| .Mult g h => size g + size h + 1
| .Neg g => size g + 1
| .Const _ => 0

def depth (f: Formula α n) : ℕ :=
match f with
| .Var _ => 0
| .Add g h => max (depth g) (depth h) + 1
| .Mult g h => max (depth g) (depth h) + 1
| .Neg g => depth g + 1
| .Const _ => 0

@[simp]
noncomputable def evalToPolynomial [CommRing α] (f: Formula α n) :  (MvPolynomial (Fin n) α) :=
match f with
| .Var x => X x
| .Add g h => evalToPolynomial g + evalToPolynomial h
| .Mult g h => evalToPolynomial g * evalToPolynomial h
| .Neg g => - evalToPolynomial g
| .Const c => MvPolynomial.C c

lemma add_ge_size_one : size (.Add g h) ≥ 1 := by
  rw [size]
  simp

lemma mul_ge_size_one : size (.Mult g h) ≥ 1 := by
  rw [size]
  simp

lemma neg_ge_size_one : size (.Neg g) ≥ 1 := by
  rw [size]
  simp
