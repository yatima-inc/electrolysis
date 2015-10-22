theory Rustabelle
imports Main "~~/src/HOL/Library/While_Combinator"
begin

type_synonym ('state, 'ans) cont = "'state \<Rightarrow> 'ans"
type_synonym ('state, 'ans) sem = "('state, 'ans) cont \<Rightarrow> ('state, 'ans) cont"

abbreviation seq :: "('state, 'ans) sem \<Rightarrow> ('state, 'ans) sem \<Rightarrow> ('state, 'ans) sem" (infixl ";" 80) where
  "seq s1 s2 \<equiv> s1 \<circ> s2"

(*definition loop :: "('state \<Rightarrow> 'state \<times> ('state, 'ans) cont option) \<Rightarrow> 'state \<Rightarrow> 'ans" where
  "loop l s = (let (s,s',c) = while (\<lambda>(s,s',c). c = None) (\<lambda>(s,s',c). (s',(l s'))) (s,(l s)) in the c s')"

lemma loop_rule:
  assumes "P s"
  assumes "\<And>s s'. P s \<Longrightarrow> l s = (s',None) \<Longrightarrow> P s'" "\<And>s s' c. P s \<Longrightarrow> l s = (s',Some c) \<Longrightarrow> Q (c s')"
  assumes "wf r" "\<And>s s'. P s \<Longrightarrow> l s = (s',None) \<Longrightarrow> (s', s) \<in> r"
  shows "Q (loop l s)"
sorry
proof-
  let ?r' = "{((s\<^sub>1,s\<^sub>1',c\<^sub>1), (s\<^sub>2,s\<^sub>2',c\<^sub>2)) | s\<^sub>1 s\<^sub>1' c\<^sub>1 s\<^sub>2 s\<^sub>2' c\<^sub>2. (s\<^sub>1,s\<^sub>2) \<in> r}"
  have "\<And>a aa b P. \<forall>a. (\<forall>aa. (aa, a) \<in> r \<longrightarrow> (\<forall>a b. P (aa, a, b))) \<longrightarrow> (\<forall>aa b. P (a, aa, b)) \<Longrightarrow> P (a, aa, b)"
  thm wf_def[THEN iffD1, OF assms(4), rule_format]
  apply (rule wf_def[THEN iffD1, OF assms(4), rule_format])
  sorry
  have "wf ?r'"
  apply (rule wf_def[THEN iffD2, rule_format])
  apply (rule wf_def[THEN iffD1, OF assms(4), rule_format])
  apply (rule wfI)
  apply auto
  have "\<And>s. (P \<circ> fst) s \<Longrightarrow> \<not> (case s of (s, c) \<Rightarrow> c = None) \<Longrightarrow> Q (let a = s in case a of (s, c) \<Rightarrow> the c s)"
  by (auto intro!:assms(3))
  show ?thesis
  unfolding loop_def
  term "{((s\<^sub>1,s\<^sub>1',c\<^sub>1), (s\<^sub>2,s\<^sub>2',c\<^sub>2)) | s\<^sub>1 s\<^sub>1' c\<^sub>1 s\<^sub>2 s\<^sub>2' c\<^sub>2. (s\<^sub>1,s\<^sub>2) \<in> r}"
  apply (rule while_rule[where P="\<lambda>(s,s',c). P s \<and> (s',c) = l s" and r=?r'])
  apply (auto simp: assms)[3]
  apply (rule assms(4))*)

definition loop :: "('state \<Rightarrow> 'state \<times> bool) \<Rightarrow> 'state \<Rightarrow> 'state" where
  "loop l s = (let (s,s',c) = while (\<lambda>(s,s',c). c) (\<lambda>(s,s',c). (s',(l s'))) (s,(l s)) in s')"

lemma loop_rule:
  assumes "P s"
  assumes "\<And>s s'. P s \<Longrightarrow> l s = (s',True) \<Longrightarrow> P s'" "\<And>s s' c. P s \<Longrightarrow> l s = (s',False) \<Longrightarrow> Q s'"
  assumes "wf r" "\<And>s s'. P s \<Longrightarrow> l s = (s',True) \<Longrightarrow> (s', s) \<in> r"
  shows "Q (loop l s)"
sorry


type_synonym u32 = nat

abbreviation "core_iter_I_IntoIterator_into_iter \<equiv> id"

datatype core_ops_Range = core_ops_Range u32 u32
abbreviation "core_iter_ops_Range_A__Iterator_next r \<equiv> case r of core_ops_Range l r \<Rightarrow> (if l < r then Some (l+1) else None, core_ops_Range (l+1) r)"

type_synonym core_option_Option = "u32 option"
abbreviation "core_option_Option_None \<equiv> None"
abbreviation "core_option_Option_Some \<equiv> Some"

end