import AlgebraicComplexity.Formulas

def formula1 : Formula ℝ :=
  Formula.Const 0

def formula2 : Formula ℝ :=
  Formula.Const 1

def formula3 : Formula ℝ :=
  Formula.Var "variable"

def formula4 : Formula ℝ :=
  Formula.Add (.Const 1) (.Mult (.Const 1) (.Var "x"))

def formula5 : Formula ℝ :=
  Formula.Neg (.Const 1)

def formula6 : Formula ℝ :=
  - (.Const 1) * (.Var "x") + (.Var "y")

-- def formula7 : Formula ℝ :=
  -- -1 * 3 + 5

-- strings and identifiers

example : size (.Const 1) = 0 := by rfl
example : size (.Var "") = 0 := by rfl
example : size (.Add (.Const 1) (.Const 0)) = 1 := by rfl
example : size (.Add (.Mult (.Const (-3.4)) (.Add (.Const 0) (.Var "y"))) (.Add (.Var "x") (.Const 1))) = 4 := by rfl
-- example : size - (Formula.Const 1) * (Formula.Var "x") + (Formula.Var "y") = 2 := by rfl

example : depth (.Const 1) = 1 := by rfl
example : depth (.Var "x") = 1 := by rfl
example : depth (.Add (.Const 1) (.Const 1)) = 2 := by rfl
example : depth (.Add (.Mult (.Const (-3.4)) (.Add (.Const 0) (.Var "y"))) (.Add (.Var "x") (.Const 1))) = 4 := by rfl
