theory examples
imports examples_export Binomial
begin

declare split_def[simp] Let_def[simp]

lemma fac: "examples_fac TYPE(_) (n::u32) = fact n"
proof-
  {
    fix x2c x2
    assume asm: "Suc x2c = core_ops_Range_start x2"
    have "fact x2c * core_ops_Range_start x2 = fact (core_ops_Range_start x2)"
    by (auto simp: asm[symmetric])
  }
  note 1 = this
  show ?thesis
  apply simp
  apply (rule loop_rule[where P="\<lambda>s. case s of (res, rng) \<Rightarrow>
    let l = core_ops_Range_start rng in
    let r = core_ops_Range_end rng in
    case l of Suc l \<Rightarrow> res = fact l \<and> (n = 0 \<and> l = 1 \<or> l < r) \<and> r = n+1 | _ \<Rightarrow> False"])
      apply (auto simp: core_ops_Range.make_def)[1]
     apply (clarsimp split: prod.splits nat.splits split_if_asm)
     unfolding examples_fac_4_def
     apply (auto simp add: 1 le_less_Suc_eq simp del: mult_Suc_right split:prod.splits split_if_asm nat.splits)[1]
  apply (rule wf_measure[of "\<lambda>s. case s of (_,rng) \<Rightarrow> core_ops_Range_end rng - core_ops_Range_start rng"])
  by (auto split:split_if_asm)
qed

end
