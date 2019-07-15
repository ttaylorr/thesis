theory Eval_Preservation
  imports Main
begin

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int"  where
"eval Var x = x" |
"eval (Const m) _ = m" |
"eval (Add e1 e2) x = (eval e1 x) + (eval e2 x)" |
"eval (Mult e1 e2) x = (eval e1 x) * (eval e2 x)"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int"  where
"evalp [] _ = 0" |
"evalp (x # xs) v = x + v * (evalp xs v)"

fun add_coeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list"  where
"add_coeffs [] [] = []" |
"add_coeffs [] ys = ys" |
"add_coeffs xs [] = xs" |
"add_coeffs (x # xs) (y # ys) = (x + y) # (add_coeffs xs ys)"

lemma evalp_add [simp] : "evalp (add_coeffs xs ys) a = (evalp xs a) + (evalp ys a)"
  apply (induction xs arbitrary: a rule: add_coeffs.induct)
     apply (auto simp add: algebra_simps)
  done

fun mult :: "int \<Rightarrow> int list \<Rightarrow> int list"  where
"mult _ [] = []" |
"mult m (x # xs) = (m * x) # (mult m xs)"

lemma evalp_mul [simp] : "evalp (mult c xs) a = c * (evalp xs a)"
  apply (induction xs arbitrary: a c)
   apply (auto simp add: algebra_simps)
  done

fun mult_coeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list"  where
"mult_coeffs [] ys = []" |
"mult_coeffs (x # xs) ys = add_coeffs (mult x ys) (0 # (mult_coeffs xs ys))"

lemma evalp_mult [simp] : "evalp (mult_coeffs xs ys) a = (evalp xs a) * (evalp ys a)"
  apply (induction xs)
     apply (auto simp add: algebra_simps)
  done

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0,1]" |
"coeffs (Const m) = [m]" |
"coeffs (Add e1 e2) = add_coeffs (coeffs e1) (coeffs e2)" |
"coeffs (Mult e1 e2) = mult_coeffs (coeffs e1) (coeffs e2)"

theorem preservation : "eval e x = evalp (coeffs e) x"
  apply (induction e)
     apply (auto)
  done

value "eval Var 5"
value "evalp (coeffs Var) 5"

value "eval (Const 7) 5"
value "evalp (coeffs (Const 7)) 5"

value "eval (Add (Const 7) (Const 3)) 5"
value "evalp (coeffs (Add (Const 7) (Const 3))) 5"

value "eval (Mult (Const 7) (Const 3)) 5"
value "evalp (coeffs (Mult (Const 7) (Const 3))) 5"

end