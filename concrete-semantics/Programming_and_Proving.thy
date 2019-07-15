theory Programming_and_Proving
  imports Main
begin

(* Exercise 2.1 *)
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat"  where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

(* Exercise 2.2 *)
lemma add_assoc : "(x::nat) + (y + z) = (x + y) + z"
  apply(induction x)
   apply(auto)
  done

lemma add_commut : "(x::nat) + y = y + x"
  apply(induction x)
   apply(auto)
  done

lemma add_mSn_Smn : "add m (Suc n) = add (Suc m) n"
  apply (induction m)
   apply (auto)
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

(* Exercise 2.6 *)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l x r) = x # (contents l) @ (contents r)"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l n r) = n + (sum_tree l) + (sum_tree r)"

lemma sum_tree_list_equiv : "sum_tree t = sum_list (contents t)"
  apply (induction t)
   apply (auto)
  done

(* Exercise 2.7 *)
datatype 'a tree2 = Tip "'a" | Node "'a tree2" "'a" "'a tree2"

fun mirror2 :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror2 (Tip x) = (Tip x)" |
"mirror2 (Node l x r) = (Node (mirror2 r) x (mirror2 l))"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Tip n) = n # []" |
"pre_order (Node l n r) = n # (pre_order l) @ (pre_order r)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Tip n) = n # []" |
"post_order (Node l n r) = (post_order l) @ (post_order r) @ [n]"

lemma order_pre_post : "pre_order (mirror2 t) = rev (post_order t)"
  apply (induction t)
   apply (auto)
  done

(* Exercise 2.8 *)
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"  where
"intersperse a [] = []" |
"intersperse a (x # []) = [x]" |
"intersperse a (x # xs) = x # [a] @ (intersperse a xs)"

(* note: must use intersperse's induction rule as above *)
lemma map_intersperse : "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs rule: intersperse.induct)
    apply (auto)
  done

(* Exercise 2.9 *)
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat"  where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

theorem add_itadd: "itadd m n = add m n"
  apply (induction m arbitrary: n)
   apply (auto)
   apply (simp add: add_mSn_Smn)
  done

datatype tree0 = Tip | Node "tree0" "tree0"

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 1" |
"nodes (Node l r) = 1 + (nodes l) + (nodes r)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0"  where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

lemma "nodes(explode n t) = (2 ^ n) * (nodes t + 1) - 1"
  apply (induction n arbitrary: t)
  apply (auto)
  apply (simp add: algebra_simps)
  done