theory core_pre
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
type_synonym usize = nat

definition "core_num_u32_checked_add x y= Some (x+y)"

type_synonym 'a core_option_Option = "'a option"
abbreviation "core_option_Option_Some \<equiv> Some"
abbreviation "core_option_Option_None \<equiv> None"

class core_marker_Sized
class core_num_One = one
class core_ops_Add = plus
class core_cmp_PartialOrd = ord
definition (in core_num_One) "core_num_One_one \<equiv> 1"
definition (in core_ops_Add) "core_ops_Add_add \<equiv> op +"
definition (in core_cmp_PartialOrd) "core_cmp_PartialOrd_lt \<equiv> op <"

instantiation nat :: core_num_One
begin
  instance ..
end
instantiation nat :: core_ops_Add
begin
  instance ..
end
instantiation nat :: core_cmp_PartialOrd
begin
  instance ..
end

abbreviation core_mem_swap :: "'T \<Rightarrow> 'T \<Rightarrow> unit \<times> 'T \<times> 'T" where
  "core_mem_swap x y \<equiv> ((),y,x)"

end