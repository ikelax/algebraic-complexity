import Mathlib


/-!

## Circuits

Circuits are directed acyclic graphs. They differ from formulas in that nodes can have an out-degree greater than 1.
This means that they needn't have multiple copies of the same circuit whose output is used as input to multiple nodes. Further,  we explicitly want to use only one copy of a circuit where possible since this can affect the size of the circuit
!-/

inductive Formula (α : Type u) (n : ℕ) where
| Var (x: Fin n)
| BVar (m : ℕ) -- This constructor exists to allow us to label internal nodes. We can define as many of these as we like in-principle. Substitution only happens at BVars. They act as pointers into a context. Each `MVar` points to a circuit in a context.
| Add (g h: Formula α n): Formula α n
| Mult (g h: Formula α n): Formula α n
| Neg (g : Formula α n): Formula α n
| Const (c : α): Formula α n
