theory Programming_and_Proving
  imports Main
begin

(* Exercise 2.1 *)
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(* Exercise 2.2 *)
lemma add_assoc : "(x::nat) + (y + z) = (x + y) + z"
  apply(induction x)
   apply(auto)
  done

lemma add_commut : "(x::nat) + y = y + x"
  apply(induction x)
   apply(auto)
  done

(* Exercise 2.3 *)
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat"  where
"count x [] = 0" |
"count x (y#xs) = (if x = y then 1 else 0) + count x xs"

lemma count_ub : "count x xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done

(* Exercise 2.4 *)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list"  where
"snoc [] y = y#[]" |
"snoc (x#xs) y = x # (snoc xs y)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x#xs) = snoc (reverse xs) x"

value "reverse ((1::nat)#(2#(3#[])))"

lemma rev_snoc [simp] : "reverse (snoc xs a) = a # (reverse xs)"
  apply (induction xs)
   apply (auto)
  done

lemma reverse_reverse_ident : "reverse (reverse xs) = xs"
  apply (induction xs)
   apply (auto)
  done

(* Exercise 2.5 *)
fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto n = (sum_upto (n - 1)) + n"

lemma sum_euler : "sum_upto n = n * (n + 1) div 2"
  apply (induction n)
   apply (auto)
  done

end