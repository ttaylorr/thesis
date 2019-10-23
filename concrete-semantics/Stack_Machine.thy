theory Stack_Machine
  imports Main IMP_Expressions Bool_Expressions
begin

datatype instr = LOADI val | LOAD vname | ADD 

type_synonym stack = \<open>val list\<close>

fun exec1 :: \<open>instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option \<close> where
\<open>exec1 (LOADI n) _ stk = Some(n # stk)\<close> |
\<open>exec1 (LOAD x) s stk = Some(s(x) # stk)\<close> |
\<open>exec1 ADD _ (j # i # stk) = Some((j + i) # stk)\<close> |
\<open>exec1 ADD _ _ = None\<close>

fun exec :: \<open>instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option  \<close> where
\<open>exec [] _ stk = Some(stk)\<close> |
\<open>exec (i#is) s stk = (case (exec1 i s stk) of
  Some stk' \<Rightarrow> exec is s stk'
  | _ \<Rightarrow> None) \<close>

fun comp :: \<open>aexp \<Rightarrow> instr list\<close> where
"comp (N n) = [LOADI n]" | 
"comp (V x) = [LOAD x]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

lemma [simp] : "(exec is1 s stk) = Some stk1 \<Longrightarrow> exec (is1 @ is2) s stk = exec is2 s stk1"
  apply (induction is1 arbitrary: stk)
  apply (auto)
  by (metis option.case_eq_if option.distinct(1))

lemma "exec (comp a) s stk = Some (aval a s # stk)"
  apply (induction a arbitrary: stk)
  apply (auto)
  done

type_synonym reg = nat
type_synonym cpu = "reg \<Rightarrow> int"

datatype rinstr = LDI int reg | LD vname reg | ADD reg reg

fun rexec1 :: "rinstr => state => cpu => cpu" where
"rexec1 (LDI n r) _ c = c(r := n)" |
"rexec1 (LD x r) s c = c(r := s(x))" |
"rexec1 (ADD r1 r2) _ c = c(r1 := c(r1) + c(r2))"

fun rexec :: "rinstr list => state => cpu => cpu" where
"rexec [] _ c = c" |
"rexec (i#is) s c = rexec is s (rexec1 i s c)"

lemma [simp] : "rexec (is1@is2) s c = rexec is2 s (rexec is1 s c)"
  apply (induction is1 arbitrary: c)
  apply (auto)
  done

fun rcomp :: "aexp => reg => rinstr list" where
"rcomp (N n) r = [LDI n r]" |
"rcomp (V x) r = [LD x r]" |
"rcomp (Plus e1 e2) r = rcomp e1 r @ rcomp e2 (r+1) @ [ADD r (r+1)]"

(* from @okaduki's solutions *) 
lemma [simp] : "r' < r \<Longrightarrow> rexec (rcomp a r) s rs r' = rs r'"
  apply(induction a arbitrary: rs r)
  apply auto
  done

lemma "rexec (rcomp a r) s rs r = aval a s"
  apply (induction a arbitrary: s rs r)
  apply (auto)
  done

end