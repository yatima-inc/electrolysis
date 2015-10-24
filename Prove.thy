theory Prove
imports Export Binomial
begin

lemma fac: "fac (n::u32) = fact n"
proof-
  show ?thesis
  unfolding fac_def
  apply auto
  apply (rule loop_rule[where P="\<lambda>s. case s of (res,core_ops_Range (Suc l) r) \<Rightarrow> res = fact l \<and> (n = 0 \<and> l = 1 \<or> l < r) \<and> r = n+1 | _ \<Rightarrow> False"])
  unfolding fac_16_def
  apply auto[1]
  apply (auto simp add: le_less_Suc_eq split:prod.splits core_ops_Range.splits split_if_asm option.splits nat.splits)[2]
  apply (rule wf_measure[of "\<lambda>s. case s of (_,core_ops_Range l r) \<Rightarrow> r-l"])
  by (auto simp add: le_less_Suc_eq split:prod.splits core_ops_Range.splits split_if_asm option.splits nat.splits)
qed

end