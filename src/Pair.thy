theory
  Pair
imports
  Network
  GCounter
begin

locale pair =
  fixes interp_l :: "'a_op \<Rightarrow> 'a_state \<rightharpoonup> 'a_state"
    and interp_r :: "'b_op \<Rightarrow> 'b_state \<rightharpoonup> 'b_state"

context pair begin
  type_synonym ('a, 'b) state = "'a option * 'b option"
  type_synonym ('a, 'b) operation = "('a * 'b)"

  fun pair_op :: "(('a_op, 'b_op) operation) \<Rightarrow> (('a_state, 'b_state) state) \<rightharpoonup> (('a_state, 'b_state) state)" where
    "pair_op _ (None, None) = Some (None, None)" |
    "pair_op (op_lhs, _) (Some state_lhs, None) = Some (interp_l op_lhs state_lhs, None)" | 
    "pair_op (_, op_rhs) (None, Some state_rhs) = Some (None, interp_r op_rhs state_rhs)" |
    "pair_op (op_lhs, op_rhs) (Some state_lhs, Some state_rhs) = Some (interp_l op_lhs state_lhs,
                                                                       interp_r op_rhs state_rhs)"
end

locale delta_pair = network_with_ops _ pair.pair_op

end