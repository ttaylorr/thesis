theory
  DeltaGCounter
imports
  Network
begin

type_synonym ('id) state = "'id \<Rightarrow> int option"
type_synonym ('id) operation = "'id state"

fun option_max :: "int option \<Rightarrow> int option \<Rightarrow> int option"  where
"option_max (Some a) (Some b) = Some (max a b)" |
"option_max x None = x" |
"option_max None y = y"

fun inc :: "'id \<Rightarrow> ('id state) \<Rightarrow> ('id operation)" where
"inc who st = (\<lambda>j. if who = j
                   then Some (1 + (case (st who) of None \<Rightarrow> 0 | Some (x) \<Rightarrow> x))
                   else None)"


fun delta_gcounter_op :: "('id operation) \<Rightarrow> ('id state) \<rightharpoonup> ('id state)" where
"delta_gcounter_op theirs ours = Some (\<lambda> x. option_max (theirs x) (ours x))"

locale delta_gcounter = network_with_ops _ delta_gcounter_op "\<lambda> x. None"

lemma (in delta_gcounter) option_max_assoc:
  "option_max a (option_max b c) = option_max (option_max a b) c"
  apply (induction a; induction b; induction c)
  apply (auto)
  done

lemma (in delta_gcounter) option_max_commut: "option_max a b = option_max b a"
  apply (induction a; induction b)
  apply (auto)
  done

lemma (in delta_gcounter) [simp] : "delta_gcounter_op x \<rhd> delta_gcounter_op y = delta_gcounter_op y \<rhd> delta_gcounter_op x"
  apply (auto simp add: kleisli_def option_max_assoc)
  apply (simp add: option_max_commut)
  done

lemma (in delta_gcounter) concurrent_operations_commute:
  assumes "xs prefix of i"
  shows "hb.concurrent_ops_commute (node_deliver_messages xs)"
  using assms
  apply(clarsimp simp: hb.concurrent_ops_commute_def)
  apply(unfold interp_msg_def, simp)
  done

corollary (in delta_gcounter) counter_convergence:
  assumes "set (node_deliver_messages xs) = set (node_deliver_messages ys)"
      and "xs prefix of i"
      and "ys prefix of j"
    shows "apply_operations xs = apply_operations ys"
using assms by(auto simp add: apply_operations_def intro: hb.convergence_ext concurrent_operations_commute
                node_deliver_messages_distinct hb_consistent_prefix)

context delta_gcounter begin

sublocale sec: strong_eventual_consistency weak_hb hb interp_msg
  "\<lambda>ops. \<exists>xs i. xs prefix of i \<and> node_deliver_messages xs = ops" "\<lambda> x. None"
  apply(standard; clarsimp)
      apply(auto simp add: hb_consistent_prefix drop_last_message node_deliver_messages_distinct concurrent_operations_commute)
   apply(metis (full_types) interp_msg_def delta_gcounter_op.elims)
  using drop_last_message apply blast
  done
end

end