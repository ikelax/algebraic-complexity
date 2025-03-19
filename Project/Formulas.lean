import Mathlib

inductive Formula (α : Type u) where
| Var (n: String)
| Add (g h: Formula α): Formula α
| Mult (g h: Formula α): Formula α
| Neg (g : Formula α): Formula α
| Const (c : α): Formula α

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

def size : Formula → ℕ
| Var => 0
| Add g h => size g + size h + 1
| Mult g h => size g + size h + 1
| Neg g => size g + 1
| Const => 0

-- def depth : Formula → ℕ
