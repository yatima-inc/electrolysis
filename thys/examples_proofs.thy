theory examples
imports examples_export Binomial
begin

lemma fac: "examples_fac (n::u32) = fact n"
proof-
  note Let_def[simp]
  note core_iter_ops_Range_A__Iterator_next_def[simp] core_cmp_PartialOrd_lt_def[simp] core_ops_Add_add_def[simp] core_num_One_one_def[simp]
  {
    fix x2c x2
    assume asm: "Suc x2c = core_ops_Range_start x2"
    have "fact x2c * core_ops_Range_start x2 = fact (core_ops_Range_start x2)"
    by (auto simp: asm[symmetric])
  }
  note 1 = this
  show ?thesis
  oops
  unfolding examples_fac_def
  apply (auto simp: core_iter_I_IntoIterator_into_iter_def ops.core_ops_Range.defs)
  apply (rule loop_rule[where P="\<lambda>s. case s of (res, rng) \<Rightarrow>
    let l = core_ops_Range_start rng in
    let r = core_ops_Range_end rng in
    case l of Suc l \<Rightarrow> res = fact l \<and> (n = 0 \<and> l = 1 \<or> l < r) \<and> r = n+1 | _ \<Rightarrow> False"])
  unfolding examples_fac_16_def
  apply auto[1]
  apply (auto simp add: 1 le_less_Suc_eq simp del: mult_Suc_right split:prod.splits split_if_asm nat.splits)[2]
  apply (rule wf_measure[of "\<lambda>s. case s of (_,rng) \<Rightarrow> core_ops_Range_end rng - core_ops_Range_start rng"])
  by (auto split:split_if_asm)
qed

end
