theory IMP_Expressions_Times
  imports Main
begin

type_synonym vname = "string"
datatype aexp = N int | V vname | Plus aexp aexp | Times aexp aexp

type_synonym val = "int"
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val"  where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s" |
"aval (Times a1 a2) s = aval a1 s * aval a2 s"

value "aval (Plus (N 3) (N 4)) (\<lambda>x. 0)"

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp"  where
"plus (N n1) (N n2) = N (n1 + n2)" |
"plus (N n) a = (if n = 0 then a else Plus (N n) a)" |
"plus a (N n) = (if n = 0 then a else Plus a (N n))" |
"plus a1 a2 = Plus a1 a2"

fun times :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp"  where
"times (N n1) (N n2) = N (n1 * n2)" |
"times (N n) a =
  (if n = 0 then (N 0) else (if n = 1 then a else Times (N n) a))" |
"times a (N n) =
  (if n = 0 then (N 0) else (if n = 1 then a else Times a (N n)))" |
"times a1 a2 = Times a1 a2"

lemma aval_plus [simp] : "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction a1 a2 rule: plus.induct)
  apply (auto)
  done

lemma aval_times [simp] : "aval (times a1 a2) s = aval a1 s * aval a2 s"
  apply (induction a1 a2 rule: times.induct)
  apply (auto)
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)" |
"asimp (Times a1 a2) = times (asimp a1) (asimp a2)"

lemma "aval (asimp a) s = aval a s"
  apply (induction a)
  apply (auto)
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
      (x, y) \<Rightarrow> Plus x y)" |
"full_asimp (Times a1 a2) = Times (full_asimp a1) (full_asimp a2)"

lemma "aval (full_asimp a) s = aval a s"
  apply (induction a)
  apply (auto split: aexp.split)
  done

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp"  where
"subst x e (N n) = N n" |
"subst x e (V v) = (if v = x then e else (V v))" |
"subst x e (Plus l r) = Plus (subst x e l) (subst x e r)" |
"subst x e (Times l r) = Times (subst x e l) (subst x e r)"

lemma "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply (induction e)
  apply (auto)
  done


datatype aexp2 = N int | V vname | Plus aexp2 aexp2 | Times aexp2 aexp2 | Div aexp2 aexp2 | PlusPlus vname

(*
fun aval2_bin :: "aexp2 \<Rightarrow> aexp2 \<Rightarrow> state \<Rightarrow> (val \<Rightarrow> val \<Rightarrow> val option) \<Rightarrow> (val * state) option"  
and aval2     :: "aexp2 \<Rightarrow> state \<Rightarrow> (val * state) option" 
where
  "aval2_bin l r s fn =
    (case (aval2 l s) of
        (Some (v1, s1)) \<Rightarrow>
           (case (aval2 r s1) of
              (Some (v2, s2)) \<Rightarrow> (case (fn v1 v2) of (Some v3) \<Rightarrow> (Some (v3, s2)) | None \<Rightarrow> None) |
              None \<Rightarrow> None) |
         None \<Rightarrow> None)" |
  "aval2 (N n) s = Some (n, s)" |
  "aval2 (V x) s = Some (s x, s)" |
  "aval2 (Plus l r) s = aval2_bin l r s (\<lambda> x y. Some (x + y))" |
  "aval2 (Times l r) s = aval2_bin l r s (\<lambda> x y. Some (x * y))" |
  "aval2 (Div l r) s = aval2_bin l r s (\<lambda> x y. (if y = 0 then None else Some (x div y)))" |
  "aval2 (PlusPlus x) s = Some (s x, s(x := (s x) + 1))"
  by pat_completness auto

*)

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> val"  where
"lval (Nl n) s = n" |
"lval (Vl x) s = s x" |
"lval (Plusl l1 l2) s = (lval l1 s) + (lval l2 s)" |
"lval (LET x l1 l2) s = (lval l2 (s(x := (lval l1 s))))"

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl n) = (N n)" |
"inline (Vl v) = (V v)" |
"inline (Plusl l1 l2) = (Plus (inline l1) (inline l2))" |
"inline (LET x l1 l2) = 


end