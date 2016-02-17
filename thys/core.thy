theory core
imports
  core_export
begin

lemma loop_rule:
  assumes "P s"
  assumes "\<And>s s'. P s \<Longrightarrow> l s = (s',True) \<Longrightarrow> P s'" "\<And>s s'. P s \<Longrightarrow> l s = (s',False) \<Longrightarrow> Q s'"
  assumes "wf r" "\<And>s s'. P s \<Longrightarrow> l s = (s',True) \<Longrightarrow> (s', s) \<in> r"
  shows "Q (loop l s)"
proof-
  let ?r' = "{((s\<^sub>1, l s\<^sub>1), (s\<^sub>2, l s\<^sub>2)) | s\<^sub>1 s\<^sub>2. (s\<^sub>1,s\<^sub>2) \<in> r}"
  have "wf ?r'"
    by (rule compat_wf[where f=fst, OF _ assms(4)]) (auto simp: compat_def)
  show ?thesis
    unfolding loop_def
    by (rule while_rule[where P="\<lambda>(s,s'). P s \<and> s' = l s" and r="?r'", OF _ _ _ `wf ?r'`]) (auto simp: assms)
qed

declare split_def[simp] Let_def[simp]

lemma loop_range_u32:
  assumes "P l res\<^sub>0"
  assumes "\<And>i res. \<lbrakk>l \<le> i; i < r; P i res\<rbrakk> \<Longrightarrow> P (Suc i) (f i res)"
  shows "P (max l r) (fst (loop (\<lambda>(res, iter).
                  let (t6, iter) = core_iter_ops_Range_A__Iterator_next core_num_u32_One core_iter_u32_Step core_ops___b_u32_Add___a_u32 iter
                  in case t6 of core_option_Option_None \<Rightarrow> ((res, iter), False)
                     | core_option_Option_Some i \<Rightarrow> ((f i res, iter), True))
         (res\<^sub>0, core_ops_Range.make l r)))"
apply (rule loop_rule[where P="\<lambda>s. case s of (res, iter) \<Rightarrow>
    let i = core_ops_Range_start iter in
    l \<le> i \<and> i \<le> max l r \<and> core_ops_Range_end iter = r \<and> P i res"])
    apply (auto simp: core_ops_Range.make_def assms(1))[1]
   apply (auto split: option.splits split_if_asm intro!: assms(2))[1]
  apply (auto simp: max_absorb1 max_absorb2 le_max_iff_disj not_less split: option.splits split_if_asm)[1]
 apply (rule wf_measure[of "\<lambda>s. case s of (_,iter) \<Rightarrow> core_ops_Range_end iter - core_ops_Range_start iter"])
apply (auto split: split_if_asm)
done

lemma loop_range_u32':
  assumes "body = (\<lambda>(res, iter).
                  let (t6, iter) = core_iter_ops_Range_A__Iterator_next core_num_u32_One core_iter_u32_Step core_ops___b_u32_Add___a_u32 iter
                  in case t6 of core_option_Option_None \<Rightarrow> ((res, iter), False)
                     | core_option_Option_Some i \<Rightarrow> ((f i res, iter), True))"
  assumes "P (max l r) (fst (loop body (res\<^sub>0, core_ops_Range.make l r))) \<Longrightarrow> P'"
  assumes "P l res\<^sub>0"
  assumes "\<And>i res. \<lbrakk>l \<le> i; i < r; P i res\<rbrakk> \<Longrightarrow> P (Suc i) (f i res)"
  shows "P'"
apply (rule assms(2))
unfolding assms(1)
by (rule loop_range_u32; rule assms(3-4); assumption)

end