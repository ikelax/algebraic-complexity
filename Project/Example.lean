import AlgebraicComplexity.Formulas

def formula1 : Formula ℝ :=
 Formula.Const 0

def formula2 : Formula ℝ :=
 Formula.Const 1

def formula3 : Formula ℝ :=
 Formula.Var "variable"

def formula4 : Formula ℝ :=
 Formula.Add (.Const 1) (.Mult (.Const 1) (.Var "x"))

example : size (.Const 1) = 0 := sorry
example : size (.Var "") = 0 := sorry
example : size (.Add (.Const 1) (.Const 0)) = 1 := sorry
example : size (.Add (.Mult (.Const (-3.4)) (.Add (.Const 0) (.Var "y"))) (.Add (.Var "x") (.Const 1))) = 4 := sorry
