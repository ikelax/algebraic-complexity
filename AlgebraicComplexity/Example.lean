import AlgebraicComplexity.Formulas

def formula1 : Formula ℝ := C[0]

def formula2 : Formula ℝ := C[1]

def formula3 : Formula ℝ :=
  Formula.Var "variable"

def formula4 : Formula ℝ :=
  C[1] + C[1] * V["x"]

def formula5 : Formula ℝ :=
  -C[1]

def formula6 : Formula ℝ :=
  -C[1] * V["x"] + V["y"]

-- def formula7 : Formula ℝ :=
  -- -1 * 3 + 5

-- strings and identifiers

example : size C[1] = 0 := by rfl
example : @size Real V["x"] = 0 := by rfl
example : @size ℤ (-C[1]) = 1 := by rfl
example : @size ℚ (C[1] + C[0]) = 1 := by rfl
example : size (.Add (.Mult (.Const (-3.4)) (.Add (.Const 0) (.Var "y"))) (.Add (.Var "x") (.Const 1))) = 4 := by rfl
-- example : size - (Formula.Const 1) * (Formula.Var "x") + (Formula.Var "y") = 2 := by rfl

example : depth (.Const 1) = 1 := by rfl
example : @depth Int (.Var "x") = 1 := by rfl
example : depth (.Neg (.Const 1)) = 2 := by rfl
example : depth (.Add (.Const 1) (.Const 1)) = 2 := by rfl
example : depth (.Add (.Mult (.Const (-3.4)) (.Add (.Const 0) (.Var "y"))) (.Add (.Var "x") (.Const 1))) = 4 := by rfl
