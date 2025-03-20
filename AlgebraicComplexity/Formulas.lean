import Mathlib

inductive Formula (α : Type u) where
| Var (n: String)
| Add (g h: Formula α): Formula α
| Mult (g h: Formula α): Formula α
| Neg (g : Formula α): Formula α
| Const (c : α): Formula α

notation "C[" val "]" => Formula.Const val
notation "V[" name "]" =>  Formula.Var name
instance zero [Ring α]: Zero (Formula α) where
  zero := .Const 0

instance one [Ring α]: One (Formula α) where
  one := .Const 1

instance add [Ring α]: Add (Formula α) where
  add := .Add

instance neg [Ring α] : Neg (Formula α) where
  neg := .Neg

instance sub [Ring α] : Sub (Formula α) where
  sub a b := a + (- b)

instance mul' [Ring α] : Mul (Formula α) where
  mul := .Mult

def size (f: Formula α) : ℕ :=
match f with
| .Var _ => 0
| .Add g h => size g + size h + 1
| .Mult g h => size g + size h + 1
| .Neg g => size g + 1
| .Const _ => 0

def depth (f: Formula α) : ℕ :=
match f with
| .Var _ => 1
| .Add g h => max (depth g) (depth h) + 1
| .Mult g h => max (depth g) (depth h) + 1
| .Neg g => depth g + 1
| .Const _ => 1
