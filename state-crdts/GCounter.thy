theory
  GCounter
imports
  Network
begin

datatype ('id) operation = Increment 'id | Decrement 'id

type_synonym ('id) state = "'id \<Rightarrow> int option"

fun update :: "'id state => 'id => (int => int) => ('id state) option" where
  "update x i fn = (case (x i) of
      None       => Some(x(i := Some(fn 0)))
    | Some (x_i) => Some(x(i := Some(fn x_i)))
  )"

fun gcounter_op :: "('id operation) \<Rightarrow> ('id state) \<rightharpoonup> ('id state)" where
  "gcounter_op (Increment i) x = update x i (\<lambda> y. y + 1)" |
  "gcounter_op (Decrement i) x = update x i (\<lambda> y. y - 1)"

locale gcounter = network_with_ops _ gcounter_op "\<lambda> x. None"

lemma (in gcounter) "gcounter_op x \<rhd> gcounter_op y = gcounter_op y \<rhd> gcounter_op x"
  sorry
  (* by(case_tac x; case_tac y; auto simp add: kleisli_def) *)

lemma (in gcounter) concurrent_operations_commute:
  assumes "xs prefix of i"
  shows "hb.concurrent_ops_commute (node_deliver_messages xs)"
  using assms
  apply(clarsimp simp: hb.concurrent_ops_commute_def)
  apply(unfold interp_msg_def, simp)
  apply(case_tac "b"; case_tac "ba")
   apply(auto simp add: kleisli_def)
  sorry

corollary (in gcounter) counter_convergence:
  assumes "set (node_deliver_messages xs) = set (node_deliver_messages ys)"
      and "xs prefix of i"
      and "ys prefix of j"
    shows "apply_operations xs = apply_operations ys"
using assms by(auto simp add: apply_operations_def intro: hb.convergence_ext concurrent_operations_commute
                node_deliver_messages_distinct hb_consistent_prefix)

context gcounter begin
(* 
sublocale sec: strong_eventual_consistency weak_hb hb interp_msg
  "\<lambda>ops. \<exists>xs i. xs prefix of i \<and> node_deliver_messages xs = ops" "\<lambda> x. None"
  apply(standard; clarsimp)
      apply(auto simp add: hb_consistent_prefix drop_last_message node_deliver_messages_distinct concurrent_operations_commute)
   apply(metis (full_types) interp_msg_def counter_op.elims)
  using drop_last_message apply blast
done
 *)
end
end
