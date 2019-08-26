theory IMP_Expressions
  imports Main
begin

type_synonym vname = "string"
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = "int"
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val"  where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s"

value "aval (Plus (N 3) (N 4)) (\<lambda>x. 0)"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus a1 a2) =
  (case (asimp_const a1, asimp_const a2) of 
    (N n1, N n2) \<Rightarrow> N (n1 + n2) |
    (a1, a2) \<Rightarrow> Plus a1 a2)"

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp"  where
"plus (N n1) (N n2) = N (n1 + n2)" |
"plus (N n) a = (if n = 0 then a else Plus (N n) a)" |
"plus a (N n) = (if n = 0 then a else Plus a (N n))" |
"plus a1 a2 = Plus a1 a2"

lemma aval_plus [simp] : "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction a1 a2 rule: plus.induct)
  apply (auto)
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

lemma aval_asimp_const [simp] :  "aval (asimp_const a) s = aval a s"
  apply (induction a)
    (*
      this proof is annoying without the splitting hint, which instructs Isabelle to split the
      case expression into sub-goals that can be inducted upon.
    *)
    apply (auto split: aexp.split)
  done

lemma "aval (asimp a) s = aval a s"
  apply (induction a)
  apply (auto)
  done

(* Exercise 3.1 *)
fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N n) = True" |
"optimal (V v) = True" |
"optimal (Plus (N _ ) (N _)) = False" |
"optimal (Plus a1 a2) = ((optimal a1) \<and> (optimal a2))"

lemma "optimal (asimp_const a)"
  apply (induction a)
  apply (auto split: aexp.split)
  done

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp (N n) = N n" |
"full_asimp (V x) = V x" |
"full_asimp (Plus a1 a2) =
  (case (full_asimp a1, full_asimp a2) of
      (Plus x (N n1), Plus y (N n2)) \<Rightarrow> Plus (Plus x y) (N (n1 + n2)) |
      (N n1, N n2) \<Rightarrow> N (n1 + n2) |
      (Plus x (N n1), (N n2)) \<Rightarrow> Plus x (N (n1 + n2)) |
      (N n1, Plus x (N n2)) \<Rightarrow> Plus x (N (n1 + n2)) |
      (Plus x (N n), y) \<Rightarrow> Plus (Plus x y) (N n) |
      (x, Plus y (N n)) \<Rightarrow> Plus (Plus x y) (N n) |
      (N n, x) \<Rightarrow> Plus x (N n) |
      (x, y) \<Rightarrow> Plus x y)"

lemma "aval (full_asimp a) s = aval a s"
  apply (induction a)
  apply (auto split: aexp.split)
  done

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp"  where
"subst x e (N n) = N n" |
"subst x e (V v) = (if v = x then e else (V v))" |
"subst x e (Plus l r) = Plus (subst x e l) (subst x e r)"

lemma "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply (induction e)
  apply (auto)
  done

end