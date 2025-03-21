import AlgebraicComplexity.Formulas

open MvPolynomial

def formula1 : Formula ℝ := C[0]

def formula2 : Formula ℝ := C[1]

def formula3 : Formula ℝ := V["variable"]

def formula4 : Formula ℝ := C[1] + C[1] * V["x"]

def formula5 : Formula ℝ := -C[1]

def formula6 : Formula ℝ := -C[1] * V["x"] + V["y"]

def formula7 : Formula ℝ := -C[1] * C[3] + C[5]

example : size C[1] = 0 := by rfl
example : @size Real V["x"] = 0 := by rfl
example : @size ℤ (-C[1]) = 1 := by rfl
example : @size ℚ (V["x"] + C[1]) = 1 := by rfl
example : @size ℚ (C[1] + C[0]) = 1 := by rfl
example : @size ℝ (C[-3.4] * (C[0] + V["y"]) + V["x"] + C[1]) = 4 := by rfl
example : @size ℝ (C[-3.4] * (C[0] + V["y"]) + (V["x"] + C[1])) = 4 := by rfl
example : @size ℤ (-C[3] * (V["x"] + V["y"])) = 3 := by rfl

example : depth C[1] = 0 := by rfl
example : @depth Real V["x"] = 0 := by rfl
example : @depth ℤ (-C[1]) = 1 := by rfl
example : @depth ℚ (V["x"] + C[1]) = 1 := by rfl
example : @depth ℚ (C[1] + C[0]) = 1 := by rfl
example : @depth ℝ (C[-3.4] * (C[0] + V["y"]) + V["x"] + C[1]) = 4 := by rfl
example : @depth ℝ (C[-3.4] * (C[0] + V["y"]) + (V["x"] + C[1])) = 3 := by rfl
example : @depth ℤ (-C[3] * (V["x"] + V["y"])) = 2 := by rfl

-- TODO: fix them after evalToPolynomial works
example : @evalToPolynomial ℝ (C[1]) = 1 := by rfl
example : @evalToPolynomial Real V["x"] = X "x" := by rfl
example : @evalToPolynomial ℤ (-C[1]) = -1 := by rfl
example : @evalToPolynomial ℚ (V["x"] + C[1]) = X "x" + 1 := by rfl
example : @evalToPolynomial ℚ (C[1] + C[0]) = 1 + 0 := by rfl
example : @evalToPolynomial ℝ (C[-3.4] * (C[0] + V["y"]) + V["x"] + C[1]) = -3.4 * (0 + X "y") + X "x" + 1 := by rfl
example : @evalToPolynomial ℝ (C[-3.4] * (C[0] + V["y"]) + (V["x"] + C[1])) = -3.4 * (0 + X "y") + (X "x" + 1) := by rfl
example : @evalToPolynomial ℤ (-C[3] * (V["x"] + V["y"])) = -3 * (X "x" + X "y") := by rfl
