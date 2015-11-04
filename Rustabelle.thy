theory Rustabelle
imports Main "~~/src/HOL/Library/While_Combinator"
begin

definition loop :: "('state \<Rightarrow> 'state \<times> bool) \<Rightarrow> 'state \<Rightarrow> 'state" where
  "loop l s = (let (s,s',c) = while (\<lambda>(s,s',c). c) (\<lambda>(s,s',c). (s',(l s'))) (s,(l s)) in s')"

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


type_synonym u32 = nat

abbreviation "core_iter_I_IntoIterator_into_iter \<equiv> id"

datatype core_ops_Range = core_ops_Range u32 u32
abbreviation "core_iter_ops_Range_A__Iterator_next r \<equiv> case r of core_ops_Range l r \<Rightarrow> (if l < r then Some l else None, core_ops_Range (l+1) r)"

type_synonym core_option_Option = "u32 option"
abbreviation "core_option_Option_None \<equiv> None"
abbreviation "core_option_Option_Some \<equiv> Some"

end