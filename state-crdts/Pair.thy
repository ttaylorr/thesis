theory
  Pair
imports
  Network
begin

locale pair =
  fixes op_l :: "'a_op \<Rightarrow> 'a_state \<rightharpoonup> 'a_state"
    and op_r :: "'b_op \<Rightarrow> 'b_state \<rightharpoonup> 'b_state"
    and st_init_l :: "'a_state"
    and st_init_r :: "'b_state"

context pair begin
  type_synonym ('a, 'b) state = "'a * 'b"
  type_synonym ('a, 'b) operation = "('a, 'b) state"
  
  fun option_merge :: "'a option \<Rightarrow> 'b option \<rightharpoonup> ('a * 'b)" where
      "option_merge _ None = None"
    | "option_merge None _ = None"
    | "option_merge (Some a) (Some b) = Some (a, b)"

  define pair_init where "(st_init_l, st_init_r)"

  fun pair_op :: "('a_op, 'b_op) operation \<Rightarrow> ('a_state, 'b_state) state \<rightharpoonup> ('a_state, 'b_state) state" where
     "pair_op (op_lhs, op_rhs) (state_lhs, state_rhs) = option_merge (op_l op_lhs state_lhs)
                                                                     (op_r op_rhs state_rhs)"
end

locale delta_pair = network_with_ops _ pair.pair_op pair.st_init_l

end