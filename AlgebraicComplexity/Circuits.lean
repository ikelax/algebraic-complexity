import Mathlib

/-!

## Circuits

Circuits are directed acyclic graphs. They differ from formulas in that nodes can have an out-degree greater than 1.
This means that they needn't have multiple copies of the same circuit whose output is used as input to multiple nodes. Further,  we explicitly want to use only one copy of a circuit where possible since this can affect the size of the circuit
!-/

namespace AlgebraicComplexity

namespace Circuits

open MvPolynomial
inductive Circuit (α : Type u) (ID : Type v) where
| Var (x: ID)
| BVar (m : ℕ) -- This constructor exists to allow us to label internal nodes. We can define as many of these as we like in-principle. Substitution only happens at BVars. They act as pointers into a context. Each `MVar` points to a circuit in a context.
| Add (g h: Circuit α ID): Circuit α ID
| Mult (g h: Circuit α ID): Circuit α ID
| Neg (g : Circuit α ID): Circuit α ID
| Const (c : α): Circuit α ID

variable {α : Type u} {ID : Type v}

notation "C[" val "]" => Circuit.Const val
notation "V[" name "]" =>  Circuit.Var ⟨name, by grind⟩

instance zero [Ring α]: Zero (Circuit α ID) where
  zero := .Const 0

instance one [Ring α]: One (Circuit α ID) where
  one := .Const 1

instance add : Add (Circuit α ID) where
  add := .Add

instance neg : Neg (Circuit α ID) where
  neg := .Neg

instance sub : Sub (Circuit α ID) where
  sub a b := a + (- b)

instance mul [Ring α] : Mul (Circuit α ID) where
  mul := .Mult

def size (f: Circuit α ID) : ℕ :=
match f with
| .Var _ => 1
| .BVar _ => 1
| .Add g h => size g + size h + 1
| .Mult g h => size g + size h + 1
| .Neg g => size g + 1
| .Const _ => 0

def depth (f: Circuit α ID) : ℕ :=
match f with
| .Var _ => 0
| .BVar _ => 0
| .Add g h => max (depth g) (depth h) + 1
| .Mult g h => max (depth g) (depth h) + 1
| .Neg g => depth g + 1
| .Const _ => 0


noncomputable def evalToPolynomial
  [CommRing α] (ctx : ℕ → (Option <| Circuit α ID)) (f: Circuit α ID) : Option (MvPolynomial ID α) :=
match f with
| .Var x => do
    return (X x) ^ 1
| .BVar n => do
    let getn ← ctx n
    let evalN ← evalToPolynomial ctx getn
    return evalN
| .Add g h => do
    let g' ← evalToPolynomial ctx g
    let h' ← evalToPolynomial ctx h
    return g' + h'
| .Mult g h => do
    let g' ← evalToPolynomial ctx g
    let h' ← evalToPolynomial ctx h
    return g' * h'
| .Neg g => do
    let g' ← (evalToPolynomial ctx g)
    return -g'
| .Const c => do
    return MvPolynomial.C c

end Circuits

end AlgebraicComplexity
