theory
  GCounter
imports
  Network
begin

type_synonym ('id) state = "'id \<Rightarrow> int option"
type_synonym ('id) operation = "'id state"

fun option_max :: "int option \<Rightarrow> int option \<Rightarrow> int option"  where
"option_max (Some x) (Some y) = Some (max x y)" |
"option_max (Some x) None = Some x" | 
"option_max None (Some y) = Some y" | 
"option_max None None = None"

fun update :: "'id state => 'id => (int => int) => ('id operation)" where
  "update x i fn = (case (x i) of
      None       => x(i := Some(fn 0))
    | Some (x_i) => x(i := Some(fn x_i)))"

fun inc :: "'id \<Rightarrow> ('id state) \<Rightarrow> ('id operation)"  where
"inc who st = update st who (\<lambda>x. x + 1)"

fun dec :: "'id \<Rightarrow> ('id state) \<Rightarrow> ('id operation)"  where
"dec who st = update st who (\<lambda>x. x - 1)"

fun gcounter_op :: "('id operation) \<Rightarrow> ('id state) \<rightharpoonup> ('id state)" where
"gcounter_op theirs ours = Some (\<lambda> x. option_max (theirs x) (ours x))"

locale gcounter = network_with_ops _ gcounter_op "\<lambda> x. None"

lemma (in gcounter) "gcounter_op x \<rhd> gcounter_op y = gcounter_op y \<rhd> gcounter_op x"
  sorry

lemma (in gcounter) concurrent_operations_commute:
  assumes "xs prefix of i"
  shows "hb.concurrent_ops_commute (node_deliver_messages xs)"
  using assms
  sorry
  
corollary (in gcounter) counter_convergence:
  assumes "set (node_deliver_messages xs) = set (node_deliver_messages ys)"
      and "xs prefix of i"
      and "ys prefix of j"
    shows "apply_operations xs = apply_operations ys"
using assms by(auto simp add: apply_operations_def intro: hb.convergence_ext concurrent_operations_commute
                node_deliver_messages_distinct hb_consistent_prefix)

context gcounter begin

sublocale sec: strong_eventual_consistency weak_hb hb interp_msg
  "\<lambda>ops. \<exists>xs i. xs prefix of i \<and> node_deliver_messages xs = ops" "\<lambda> x. None"
  apply(standard; clarsimp)
      apply(auto simp add: hb_consistent_prefix drop_last_message node_deliver_messages_distinct concurrent_operations_commute)
   apply(metis (full_types) interp_msg_def gcounter_op.elims)
  using drop_last_message apply blast
  done
end

end