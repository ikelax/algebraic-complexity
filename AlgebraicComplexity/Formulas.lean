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
noncomputable def evalToPolynomial [CommRing α] (f: Formula α n) : (MvPolynomial (Fin n) α) :=
match f with
| .Var x => X x
| .Add g h => evalToPolynomial g + evalToPolynomial h
| .Mult g h => evalToPolynomial g * evalToPolynomial h
| .Neg g => - evalToPolynomial g
| .Const c => MvPolynomial.C c

lemma size_zero_const_or_var (f: Formula α n) :
  size f = 0 → (∃ x, f = .Var x) ∨ (∃ c, f = .Const c) := by
  intro h
  cases f with (simp_all[size, h])
  done

def coerce_up (f : Formula α n) : Formula α (n + 1) :=
  match f with
    | .Var x => .Var x
    | .Add g h => .Add (coerce_up g) (coerce_up h)
    | .Mult g h => .Mult (coerce_up g) (coerce_up h)
    | .Neg p => .Neg (coerce_up p)
    | .Const c => .Const c

instance : Coe (Formula α n) (Formula α (n + 1)) where
  coe f := coerce_up f

#print MvPolynomial.rename
#print MvPolynomial
#print AddMonoidAlgebra

noncomputable def incrVar [CommSemiring α]
  (p : MvPolynomial (Fin n) α) : MvPolynomial (Fin (n + 1)) α :=
  MvPolynomial.rename Fin.castSucc p

@[simp]
lemma incrVar_composes_add [CommSemiring α]: ∀ f g : MvPolynomial (Fin n) α,
  (incrVar f) + (incrVar g) = incrVar (f + g) := by
  intro f g
  simp [incrVar]


@[simp]
lemma incrVar_composes_mult [CommSemiring α] : ∀ f g : MvPolynomial (Fin n) α,
  (incrVar f) * (incrVar g) = incrVar (f * g) := by
  intro f g
  simp [incrVar]

@[simp]
lemma incrVar_composes_neg [CommRing α] : ∀ f : MvPolynomial (Fin n) α,
  - (incrVar f) = incrVar (- f) := by
  intro f
  simp [incrVar]

noncomputable instance[CommSemiring α] :
  Coe (MvPolynomial (Fin n) α) (MvPolynomial (Fin <| n + 1) α) where
  coe p := incrVar p



lemma coerce_up_preserves_incrVar_eval [CommRing α]
  (f : Formula α n) :
  ∀ p : MvPolynomial (Fin n) α,
    evalToPolynomial f = p →
    evalToPolynomial (coerce_up f) = incrVar p := by
  intro p hp_eval
  induction f generalizing p with
      (
        simp_all [incrVar, coerce_up, Fin.castSucc, Fin.castAdd];
        subst hp_eval
        simp_all only [algHom_C, algebraMap_eq, rename_X, map_add, map_mul, map_neg]
      )
  done



def L (n: ℕ) (α : Type u) [CommRing α] (p: MvPolynomial (Fin n) α) (k: ℕ): Prop :=
  ∃ f, evalToPolynomial f = p
  ∧ (∀ g, evalToPolynomial g = p → k ≤ size g)
  ∧ size f = k

theorem complexity_monomial_le [iCR: CommRing α] (n d: ℕ) (hn_pos : n > 0):
  ∃ k: ℕ, L n α ((X ⟨0, by omega⟩ : MvPolynomial (Fin n) α) ^ d) k ∧ k ≤ d-1 := by
  induction n generalizing d with
  | zero =>
      cases hn_pos
  | succ n ih =>
      by_cases hb : n > 0 <;> simp [hb, L]
      · specialize ih (d - 1) hb
        simp [L] at ih
        obtain ⟨kn, ⟨circ_h, eval_h⟩, size_h⟩ := ih
        let new_circ : Formula α (n + 1) := Formula.Mult circ_h (.Var (n + 1))
        use (kn + 1)
        constructor
        · 
          done
        · done
      ·
        sorry
