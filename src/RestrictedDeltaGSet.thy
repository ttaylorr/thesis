theory
  RestrictedDeltaGSet
imports
  Network
begin

type_synonym ('a) state = "'a set"
type_synonym ('a) operation = "'a"

fun insert :: "'a \<Rightarrow> ('a state) \<Rightarrow> ('a operation)" where
"insert a _ = a "

fun delta_gset_op :: "('a operation) \<Rightarrow> ('a state) \<rightharpoonup> ('a state)" where
"delta_gset_op a as = Some ( as \<union> { a })"

locale delta_gset = network_with_ops _ delta_gset_op "{}"

lemma (in delta_gset) [simp] : "delta_gset_op x \<rhd> delta_gset_op y = delta_gset_op y \<rhd> delta_gset_op x"
  apply (auto simp add: kleisli_def)
done

lemma (in delta_gset) concurrent_operations_commute:
  assumes "xs prefix of i"
  shows "hb.concurrent_ops_commute (node_deliver_messages xs)"
  using assms
  apply(clarsimp simp: hb.concurrent_ops_commute_def)
  apply(unfold interp_msg_def, simp)
done

corollary (in delta_gset) set_convergence:
  assumes "set (node_deliver_messages xs) = set (node_deliver_messages ys)"
      and "xs prefix of i"
      and "ys prefix of j"
    shows "apply_operations xs = apply_operations ys"
using assms by(auto simp add: apply_operations_def intro: hb.convergence_ext concurrent_operations_commute
                node_deliver_messages_distinct hb_consistent_prefix)

context delta_gset begin

sublocale sec: strong_eventual_consistency weak_hb hb interp_msg
  "\<lambda>ops. \<exists>xs i. xs prefix of i \<and> node_deliver_messages xs = ops" "{}"
  apply(standard; clarsimp)
      apply(auto simp add: hb_consistent_prefix drop_last_message node_deliver_messages_distinct concurrent_operations_commute)
   apply(metis (full_types) interp_msg_def delta_gset_op.elims)
  using drop_last_message apply blast
  done
end

end