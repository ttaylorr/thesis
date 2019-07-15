theory Arith
  imports Main
begin

type_synonym vname = string

datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val"  where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a_1 a_2) s = aval a_1 s + aval a_2 s"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus a_1 a_2) =
  (case (asimp_const a_1, asimp_const a_2) of
    (N n_1, N n_2) \<Rightarrow> N (n_1 + n_2) |
    (b_1, b_2) \<Rightarrow> Plus b_1 b_2)"

lemma asimp_const_preservation [simp] : "aval (asimp_const a) s = aval a s"
  apply (induction a)
    apply (auto split: aexp.split)
  done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp"  where
"plus (N i_1) (N i_2) = N (i_1 + i_2)" |
"plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
"plus a (N i) = (if i = 0 then a else Plus a (N i))" |
"plus a_1 a_2 = Plus a_1 a_2"

lemma aval_plus [simp] : "aval (plus a_1 a_2) s = aval a_1 s + aval a_2 s"
  apply (induction a_1 a_2 rule: plus.induct)
              apply (simp_all)
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" | 
"asimp (V x) = V x" |
"asimp (Plus a_1 a_2) = plus a_1 a_2"

lemma asimp_preservation : "aval (asimp a) s = aval a s"
  apply (induction a)
    apply auto
  done

(* Exercise 3.1 *)
fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N _) = True" |
"optimal (V _) = True" |
"optimal (Plus (N _) (N _)) = False" |
"optimal (Plus a_1 a_2) = ((optimal a_1) \<and> optimal a_2)"

lemma asimp_optimal : "optimal (asimp_const a)"
  apply (induction a)
    apply (auto split: aexp.split)
  done

end