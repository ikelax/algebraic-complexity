import AlgebraicComplexity.Formulas

#check Formula.Const 0
#check Formula.Const 1
#check Formula.Var "variable"
#check Formula.Add (.Const 1) (.Mult (.Const 1) (.Var "x"))

example : size (.Const 1) = 0 := sorry
example : size (.Var "") = 0 := sorry
example : size (.Add (.Const 1) (.Const 0)) = 1 := sorry
example : size (.Add (.Mult (.Const (-3.4)) (.Add (.Const 0) (.Var "y"))) (.Add (.Var "x") (.Const 1))) = 4 := sorry
