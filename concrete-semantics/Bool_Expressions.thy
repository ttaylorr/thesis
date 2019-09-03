theory Bool_Expressions
  imports Main IMP_Expressions
begin

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool"  where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)" |
"bval (Less a1 a2) s = (aval a1 s < aval a2 s)"

fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False" |
"not (Bc False) = Bc True" | 
"not b = Not b"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp"  where
"and (Bc True) b = b" |
"and b (Bc True) = b" |
"and (Bc False) b = Bc False" |
"and b (Bc False) = Bc False" |
"and b1 b2 = And b1 b2"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp"  where
"less (N n1) (N n2) = Bc (n1 < n2)" |
"less a1 a2 = Less a1 a2"

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc v) = Bc v" |
"bsimp (Not b) = not (bsimp b)" |
"bsimp (And b1 b2) = and (bsimp b1) (bsimp b2)" |
"bsimp (Less a1 a2) = less (asimp a1) (asimp a2)"

fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp"  where
"Eq a1 a2 = And (Not (Less a1 a2)) (Not (Less a2 a1))"

fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp"  where
"Le a1 a2 = Not (Less a2 a1)"

lemma "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  apply (induction a1 a2 rule: Eq.induct)
  apply (auto)
  done

lemma "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
  apply (induction a2 a2 rule: Le.induct)
  apply (auto)
  done

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool"  where
"ifval (Bc2 v) s = v" |
"ifval (If c e1 e2) s =
  (if (ifval c s) then (ifval e1 s) else (ifval e2 s))" |
"ifval (Less2 a1 a2) s = (aval a1 s < aval a2 s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc v) = (Bc2 v)" |
"b2ifexp (Not b) = (If (b2ifexp b) (Bc2 False) (Bc2 True))" |
"b2ifexp (And b1 b2) = (If (b2ifexp b1) (b2ifexp b2) (Bc2 False))" |
"b2ifexp (Less a1 a2) = (Less2 a1 a2)"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 b) = (Bc b)" |
(* ugh; this case checked with https://github.com/okaduki/ConcreteSemantics/blob/master/chapter3/ex3_08.thy *)
"if2bexp (If c b1 b2) = (Not (And (Not (And (if2bexp c) (if2bexp b1))) (Not (And (Not (if2bexp c)) (if2bexp b2)))))" |
"if2bexp (Less2 a1 a2) = (Less a1 a2)" 

lemma "bval e s = ifval (b2ifexp e) s"
  apply (induction e)
  apply (auto)
  done

lemma "ifval e s = bval (if2bexp e) s"
  apply (induction e)
    apply (auto)
  done

datatype pbexp = VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool"  where
"pbval (VAR x) s = s x" |
"pbval (NOT b) s = (\<not> pbval b s)" |
"pbval (AND b1 b2) s = ((pbval b1 s) \<and> (pbval b2 s))" |
"pbval (OR b1 b2) s = ((pbval b1 s) \<or> (pbval b2 s))"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR x) = True" |
"is_nnf (NOT (VAR x)) = True"  |
"is_nnf (NOT _) = False"  |
"is_nnf (AND b1 b2) = (is_nnf b1 \<and> is_nnf b2)" |
"is_nnf (OR b1 b2) = (is_nnf b1 \<and> is_nnf b2)"

fun nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf (VAR x) = (VAR x)" |
"nnf (AND b1 b2) = (AND (nnf b1) (nnf b2))" |
"nnf (OR b1 b2) = (OR (nnf b1) (nnf b2))" |
"nnf (NOT (VAR x)) = (NOT (VAR x))" |
"nnf (NOT (NOT x)) = nnf x" |
"nnf (NOT (AND b1 b2)) = (OR (nnf (NOT b1)) (nnf (NOT b2)))" |
"nnf (NOT (OR b1 b2)) = (AND (nnf (NOT b1)) (nnf (NOT b2)))"

lemma "pbval (nnf b) s = pbval b s"
  apply (induction b rule: nnf.induct)
  apply (auto)
  done

lemma "is_nnf (nnf b)"
  apply (induction b rule: nnf.induct)
  apply (auto)
  done

fun is_dnf_and :: "pbexp \<Rightarrow> bool"  where
"is_dnf_and (VAR _) = True" |
"is_dnf_and (NOT x) = is_dnf_and x" |
"is_dnf_and (OR _ _) = False" |
"is_dnf_and (AND b1 b2) = (is_dnf_and b1 \<and> is_dnf_and b2)"

fun is_dnf :: "pbexp \<Rightarrow> bool" where
"is_dnf (VAR x) = True" |
"is_dnf (NOT (VAR x)) = True" |
"is_dnf (NOT _) = False" |
"is_dnf (OR b1 b2) = (is_nnf (OR b1 b2) \<and> is_dnf b1 \<and> is_dnf b2)" |
"is_dnf (AND b1 b2) = (is_nnf (AND b1 b2) \<and> is_dnf_and b1 \<and> is_dnf_and b2)"

fun dist :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp"  where
"dist (OR b1 b2) b3 = (OR (dist b1 b3) (dist b2 b3))" |
"dist b1 (OR b2 b3) = (OR (dist b1 b2) (dist b1 b3))" |
"dist b1 b2 = AND b1 b2"
 
fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
"dnf_of_nnf (VAR x) = VAR x" |
"dnf_of_nnf (NOT x) = NOT x" |
"dnf_of_nnf (OR b1 b2) = OR (dnf_of_nnf b1) (dnf_of_nnf b2)" |
"dnf_of_nnf (AND b1 b2) = dist (dnf_of_nnf b1) (dnf_of_nnf b2)"

lemma [simp] : "pbval (dist b1 b2) s = pbval (AND b1 b2) s"
  apply (induction b1 b2 rule: dist.induct)
  apply (auto)
  done

lemma [simp] : "(pbval (dnf_of_nnf b) s = pbval b s)"
  apply (induction b)
  apply (auto)
  done

lemma [simp] : "is_dnf x \<Longrightarrow> is_nnf x" 
  apply (induction x rule: is_nnf.induct)
  apply (auto)
  done

lemma "(is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b))"
  apply (induction b rule: dnf_of_nnf.induct)
  apply (auto)
  (* using is_nnf.elims(2) by fastforce ? ? ? *)
  sorry

end