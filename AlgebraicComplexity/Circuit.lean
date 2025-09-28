import Mathlib
import Std.Data.HashMap

set_option linter.unusedTactic false

--        x
-- +          *
-- x1    x2   1

-- inductive Operation where
--   | Sum
--   | Prod
--   | None
--
-- inductive MetaVar (n : ℕ) where
--   | Elem (e: ℝ)
--   | Var (x: Fin n)
--
-- abbrev Context (n : ℕ) := Std.HashMap (Fin n) (MetaVar n)
--
-- structure Circuit (n : ℕ) (C : Context n) where
--   identifier : Fin n
--   operation : Operation
--   operands : List (Fin n)
--
-- def x1 : MetaVar 3 := MetaVar.Var (1)
-- def x2 : MetaVar 3 := MetaVar.Var (2)
-- def one : MetaVar 3 := MetaVar.Elem (1)
--
-- def context : Context 3 := Std.HashMap.empty
--   |>.insert 1 x1
--   |>.insert 2 x2
--   |>.insert 3 one
--
-- def x1_plus_x2 : Circuit 3 context := {
--   identifier := 4,
--   operation := Operation.Sum,
--   operands := [1, 2]
-- }
--
-- def x2_plus_1 : Circuit 3 context := {
--   identifier := 5,
--   operation := Operation.Sum,
--   operands := [2, 3]
-- }
--
-- def circuit : Circuit 3 context := {
--   identifier := 6,
--   operation := Operation.Prod,
--   operands := [2, 4, 5]
-- }
--
-- @[simp]
-- noncomputable def evalCircuit (n : ℕ)
--                               (Γ : Context n)
--                               (c : Circuit n Γ)
--                             : (MvPolynomial (Fin n) ℝ) :=
--   1

-- inductive Formula (α : Type u) (n : ℕ) where
-- | Var (x: Fin n)
-- | Add (g h: Formula α n): Formula α n
-- | Mult (g h: Formula α n): Formula α n
-- | Neg (g : Formula α n): Formula α n
-- | Const (c : α): Formula α n

inductive MetaVar (n : ℕ) where
  | Var (x: Fin n)

--  (Γ : List (Sigma (ℕ -> (MetaVar n))))

inductive Gate (α : Type) where
  | pair : α -> α -> Gate α
  | cons : α -> Gate α -> Gate α


def g1 : Gate ℕ := .pair 1 2
def g2 : Gate ℕ := .pair 1 2

inductive Circuit (n : ℕ) where
  -- We want to keep our input variables separate for now.
  | Var (x : Fin n)
  | MetaVar (x : ℕ)
  | Sum (c d : Circuit n)
  | Prod (c d : Circuit n)
  | Const (c : ℝ)
  | Neg (g : Circuit n)

def size (c: Circuit n) : ℕ :=
  match c with
  | .Var _ => 0
  | .MetaVar _ => 0
  | .Sum c d => size c + size d + 1
  | .Prod c d => size c + size d + 1
  | .Const _ => 0
  | .Neg d => size d + 1

def depth (c: Circuit n) : ℕ :=
  match c with
  | .Var _ => 0
  | .MetaVar _ => 0
  | .Sum c d => max (depth c) (depth d) + 1
  | .Prod c d => max (depth c) (depth d) + 1
  | .Const _ => 0
  | .Neg d => depth d + 1
