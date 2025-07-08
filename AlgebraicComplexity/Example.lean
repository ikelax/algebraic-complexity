import AlgebraicComplexity.Formulas
import Mathlib

open MvPolynomial

def formula1 : Formula ℝ 3 := C[0]

def formula2 : Formula ℝ 0 := C[1]

def formula3 : Formula ℝ 1 := V[0]

def formula4 : Formula ℝ 1 := C[1] + C[1] * V[0]

def formula5 : Formula ℝ 5 := -C[1]

def formula6 : Formula ℝ 21 := -C[1] * V[4] + V[20] + V[0]

def formula7 : Formula ℝ 7 := -C[1] * C[3] + C[5]

example : @size ℝ 1 C[1] = 0 := by rfl
example : @size Real 1 V[0] = 0 := by rfl
example : @size ℤ 2 (-C[1]) = 1 := by rfl
example : @size ℚ 2 (V[0] + C[1]) = 1 := by rfl
example : @size ℚ 2 (C[1] + C[0]) = 1 := by rfl
example : @size ℝ 3 (C[-3.4] * (C[0] + V[2]) + V[1] + C[1]) = 4 := by rfl
example : @size ℝ 3 (C[-3.4] * (C[0] + V[2]) + (V[1] + C[1])) = 4 := by rfl
example : @size ℤ 3 (-C[3] * (V[1] + V[2])) = 3 := by rfl

example : @depth ℝ 1 C[1] = 0 := by rfl
example : @depth Real 1 V[0] = 0 := by rfl
example : @depth ℤ 2 (-C[1]) = 1 := by rfl
example : @depth ℚ 2 (V[1] + C[1]) = 1 := by rfl
example : @depth ℚ 2 (C[1] + C[0]) = 1 := by rfl
example : @depth ℝ 3 (C[-3.4] * (C[0] + V[2]) + V[1] + C[1]) = 4 := by rfl
example : @depth ℝ 3 (C[-3.4] * (C[0] + V[2]) + (V[1] + C[1])) = 3 := by rfl
example : @depth ℤ 3 (-C[3] * (V[1] + V[2])) = 2 := by rfl

example : @evalToPolynomial ℝ 1 _ (C[1]) = 1 := by rfl
example : @evalToPolynomial Real 1 _ V[0] = X 1 ^ 1 := by rfl
example : @evalToPolynomial ℤ 2 _ (-C[1]) = -1 := by rfl
example : @evalToPolynomial ℚ 2 _ (V[1] + C[1]) = X 1 ^ 1 + 1 := by rfl
example : @evalToPolynomial ℚ 2 _ (C[1] + C[0]) = 1 + 0 := by simp[evalToPolynomial]
example : @evalToPolynomial ℝ 3 _ (C[-3] * (C[0] + V[2]) + V[1] + C[1]) =
    (C (-3)) * (0 + (X 2)) + (X 1) + 1 := by simp
example : @evalToPolynomial ℚ  3 _ (C[-3] * (C[0] + V[2]) + (V[1] + C[1])) = (C (-3)) * (0 + (X 2)) + ((X 1) + 1) := by simp
example : @evalToPolynomial ℤ 3 _ (-C[3] * (V[1] + V[2])) = -3 * (X 1 ^ 1 + X 2 ^ 1) := by rfl
