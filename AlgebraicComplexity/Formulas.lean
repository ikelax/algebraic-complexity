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

/--
`coerce_up f` coerces a formula `f` in `n` variables to a formula in `n + 1` variables.
-/
def coerce_up (f : Formula α n) : Formula α (n + 1) :=
  match f with
    | .Var x => .Var x
    | .Add g h => .Add (coerce_up g) (coerce_up h)
    | .Mult g h => .Mult (coerce_up g) (coerce_up h)
    | .Neg p => .Neg (coerce_up p)
    | .Const c => .Const c

/--
This is the Coe typeclass instance for the above coercion. T
-/
instance : Coe (Formula α n) (Formula α (n + 1)) where
  coe f := coerce_up f

#print MvPolynomial.rename
#print MvPolynomial
#print AddMonoidAlgebra

/--
`incrVar p` coerces an `n` variable `MvPolynomial` to an `n + 1` variable `MvPolynomial`
-/
noncomputable def incrVar [CommSemiring α]
  (p : MvPolynomial (Fin n) α) : MvPolynomial (Fin (n + 1)) α :=
  MvPolynomial.rename Fin.castSucc p


/--
The three lemmas below show that the `incrVar` function respects ring operations
on the polynomial.
-/
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

-- Why do we need hn_pos and hd_pos? n and d are in ℕ.
-- ℕ starts from 0 (see induction). So, we ensure that d-1 is in ℕ.
theorem complexity_monomial_le [CommRing α] (n d: ℕ) (hn_pos : n > 0) (hd_pos : d > 0):
  -- What does ⟨0, by omega⟩?
  ∃ k: ℕ, L (n+1) α ((X ⟨0, by omega⟩ : MvPolynomial (Fin (n + 1)) α) ^ d) k ∧ k ≤ d-1 := by
  -- Proof by induction over n
  induction d  with
  | zero =>
      -- Done because 0 > 0 is a contradiction.
      cases hd_pos
  | succ d ih => -- Why ∀ in ih
      -- What does <;>
      -- Case distinction over n > 0
      by_cases hb : d > 0 <;> simp [hb, L]
      -- Specialize removes ∀ n > 0. We already assume this with hb.
      · specialize ih hb
        simp [L] at ih
        -- What does obtain? Rename stuff?
        obtain ⟨kn, ⟨circ_h, eval_h⟩, size_h⟩ := ih
        -- The formula for n+1
        let new_circ : Formula α (n + 1) := Formula.Mult circ_h (.Var (n + 1))
        -- Replaces k with kn + 1 in goal
        use (kn + 1)
        -- Split ∧. First prove left side and then right side.
        constructor
        -- Prove that new_circ satisfies the statement.
        · use new_circ
          constructor
          · simp_all [new_circ, evalToPolynomial]
            ring_nf
            -- have eval_h' := eval_h.left
            -- have coerce_pres_incr := coerce_up_preserves_incrVar_eval circ_h (X 0 ^ d) eval_h'
            -- rw[coerce_pres_incr]
            -- simp [incrVar]
            -- ring_nf
            -- apply mul_pow_sub_one ?_ (X 0)
            -- done
          · constructor
            . intro h1
              intro h2
              sorry
            . rw [size]
              have evalToPolynomial_h := eval_h.left
              have eval_h_right := eval_h.right
              have size_circ_h := eval_h_right.right
              rw [size_circ_h]
              rw [size]
        · omega
      · sorry


example {α} (hn : n > 0) [iCR: CommRing α]: @X α (Fin n) iCR.toCommSemiring ⟨0, by omega⟩ ^ (d - 1) * X ⟨0, by omega⟩ = (X ⟨0, by omega⟩) ^ d := by
  sorry
