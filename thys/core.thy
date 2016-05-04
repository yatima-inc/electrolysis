section \<open> Proofs about the \emph{core} crate \<close>

text_raw \<open> \label{sec:core} \<close>

theory core
imports
  core_export
begin

subsection \<open> Lemmas that should be in HOL/Library \<close>

definition "all_option P = case_option False P"

lemma all_option_Some [simp]: "all_option P (Some x) = P x"
by (simp add: all_option_def)

lemma all_option_None [simp]: "\<not>all_option P None"
by (simp add: all_option_def)

lemma all_optionE [elim!]:
  assumes "all_option P x"
  obtains x' where "x = Some x'" "P x'"
using assms by (cases x; simp)

lemma all_option_comp: "all_option (P \<circ> f) x = all_option P (map_option f x)"
by (cases x; simp)

lemma all_option_eq: "all_option (\<lambda>x. x = y) x \<longleftrightarrow> x = Some y"
by (cases x; simp)
 
theorem while_opt_rule_lemma:
  assumes invariant: "!!s. P s ==> b s ==> P (c s)"
    and terminate: "!!s. P s ==> \<not> b s ==> Q s"
    and wf: "wf {(t, s). P s \<and> b s \<and> t = c s}"
  shows "P s \<Longrightarrow> all_option Q (while_option b c s)"
  using wf
  apply (induct s)
  apply simp
  apply (subst while_option_unfold)
  apply (simp add: invariant terminate all_option_def)
  done

theorem while_opt_rule:
  "[| P s;
      !!s. [| P s; b s  |] ==> P (c s);
      !!s. [| P s; \<not> b s  |] ==> Q s;
      wf r;
      !!s. [| P s; b s  |] ==> (c s, s) \<in> r |] ==>
   all_option Q (while_option b c s)"
  apply (rule while_opt_rule_lemma)
     prefer 4 apply assumption
    apply blast
   apply blast
  apply (erule wf_subset)
  apply blast
  done

subsection \<open> Lemmas about @{term loop} \<close>

lemma loop_rule:
  assumes "P s"
  assumes "\<And>s s'. P s \<Longrightarrow> l s = Inl s' \<Longrightarrow> P s'" "\<And>s r. P s \<Longrightarrow> l s = Inr r \<Longrightarrow> Q r"
  assumes "wf R" "\<And>s s'. P s \<Longrightarrow> l s = Inl s' \<Longrightarrow> (s', s) \<in> R"
  shows "all_option Q (loop l s)"
proof-
  let ?R' = "{(Inr r, Inl s) | r s. True} \<union> {(Inl s\<^sub>1, Inl s\<^sub>2) | s\<^sub>1 s\<^sub>2. (s\<^sub>1,s\<^sub>2) \<in> R}"
  have "wf ?R'"
  apply (rule wf_Un)
    apply (rule wfI_pf; auto)
   apply (rule compat_wf[where f="\<lambda>x. case x of Inl y \<Rightarrow> y", OF _ assms(4)])
  by (auto simp: compat_def)

  show ?thesis
  unfolding loop_def all_option_comp[symmetric]
  apply (rule while_opt_rule[where P="\<lambda>x. case x of Inl s' \<Rightarrow> P s' | Inr r \<Rightarrow> Q r", OF _ _ _ `wf ?R'`])
     apply (auto simp: assms pred_option_def split: sum.splits)[3]
  apply (case_tac s)
   apply (rename_tac s')
   apply (case_tac "l s'")
  by (auto simp: assms(5))
qed

lemma loop'_rule:
  assumes "P s"
  assumes "\<And>s. P s \<Longrightarrow> l s \<noteq> None" "\<And>s s'. P s \<Longrightarrow> l s = Some (Inl s') \<Longrightarrow> P s'" "\<And>s r. P s \<Longrightarrow> l s = Some (Inr r) \<Longrightarrow> Q r"
  assumes "wf R" "\<And>s s'. P s \<Longrightarrow> l s = Some (Inl s') \<Longrightarrow> (s', s) \<in> R"
  shows "all_option Q (loop' l s)"
by (cut_tac loop_rule[where P="P" and Q="all_option Q" and s="s", OF _ _ _ `wf R`])
   (auto simp: loop'_def all_option_def pred_option_def Option.bind_def assms(1,2,6) intro: assms(3,4) split: option.splits sum.splits)

declare Let_def[simp] Option.bind_eq_Some_conv[simp] Option.bind_eq_None_conv[simp]
declare not_None_eq[iff del]

(*
subsection \<open> Loops over @{verbatim u32} ranges \<close>

text \<open> Because the following lemmas reference specific trait implementations for @{verbatim u32}, it is not
  clear how they could be generalized to other numeric types. \<close>

lemma loop_range_u32:
  assumes "P l res\<^sub>0"
  assumes "\<And>i res iter. \<lbrakk>l \<le> i; i < r; P i res\<rbrakk> \<Longrightarrow> f i res iter = Some ((g i res, iter), Continue)"
  assumes "\<And>i res iter. \<lbrakk>l \<le> i; i < r; P i res\<rbrakk> \<Longrightarrow> P (Suc i) (g i res)"
  shows "all_option (P (max l r) \<circ> fst) (loop' (\<lambda>(res, iter).
                  do (t6, iter) \<leftarrow> (core_iter_ops_Range_A__Iterator_next (core_num_u32_One) (core_iter_u32_Step) (core_ops___b_u32_Add___a_u32) iter);
                  case t6 of core_option_Option_None \<Rightarrow> Some ((res, iter), Break)
                     | core_option_Option_Some i \<Rightarrow> f i res iter)
         (res\<^sub>0, core_ops_Range.make l r))"
apply (rule loop'_rule[where P="\<lambda>s. case s of (res, iter) \<Rightarrow>
    let i = core_ops_Range_start iter in
    l \<le> i \<and> i \<le> max l r \<and> core_ops_Range_end iter = r \<and> P i res"])
     apply (auto simp: core_ops_Range.make_def assms(1,2))[1]
    apply (auto simp: assms(2) split: split_if_asm)[1]
   apply (auto simp: max_absorb1 max_absorb2 assms(2,3) split: if_splits)[1]
  apply (auto simp: max_absorb1 max_absorb2 le_max_iff_disj assms(2) split: option.splits split_if_asm)[1]
 apply (rule wf_measure[of "\<lambda>s. case s of (_,iter) \<Rightarrow> core_ops_Range_end iter - core_ops_Range_start iter"])
apply (auto simp: assms(2) split: split_if_asm)
done

text \<open> A variant of @{text loop_range_u32} that is easier to unify with a goal \<close>

lemma loop_range_u32':
  assumes "body = (\<lambda>(res, iter).
                  do (t6, iter) \<leftarrow> core_iter_ops_Range_A__Iterator_next core_num_u32_One core_iter_u32_Step core_ops___b_u32_Add___a_u32 iter;
                  case t6 of core_option_Option_None \<Rightarrow> Some ((res, iter), Break)
                     | core_option_Option_Some i \<Rightarrow> f i res iter)"
  assumes "\<And>i res iter. \<lbrakk>l \<le> i; i < r; P i res\<rbrakk> \<Longrightarrow> f i res iter = Some ((g i res, iter), Continue) \<and> P (Suc i) (g i res)"
  assumes "\<And>x. P (max l r) (fst x) \<Longrightarrow> P' (Some x)"
  assumes "P l res\<^sub>0"
  shows "P' (loop' body (res\<^sub>0, core_ops_Range.make l r))"
by (cut_tac loop_range_u32[of P l res\<^sub>0 r f g]) (auto simp: assms[unfolded assms(2)])
*)

section \<open> core::slice \<close>

lemma option_all[simp]: "all_option (\<lambda>x. True) x \<longleftrightarrow> x \<noteq> None"
by (auto simp: all_option_def split: option.split)

declare core_ops_Range.defs[simp] core_ops_RangeFrom.defs[simp] core_ops_RangeTo.defs[simp]
declare core_slice__T__SliceExt_def[simp]

lemma binarySearch_by_terminates:
  assumes "\<And>f x. core_ops_FnMut_call_mut f_impl f x \<noteq> None"
  assumes "length (pointer_data (core_raw_Slice_data s)) \<ge> core_raw_Slice_len s + pointer_pos (core_raw_Slice_data s)"
  shows "core_slice__T__SliceExt_binary_search_by f_impl s f \<noteq> None"
proof-
  note div_le_dividend[simplified not_less[symmetric], simp]
  have[simp]: "\<And>b s. (if b then Some s else None) = None \<longleftrightarrow> \<not>b"
    by (auto split: split_if_asm)

  show ?thesis
  apply (simp add: core_slice__T__SliceExt_binary_search_by_def)
  apply (rule loop'_rule[where P="\<lambda>(f,base,s). length (pointer_data (core_raw_Slice_data s)) \<ge> core_raw_Slice_len s + pointer_pos (core_raw_Slice_data s)" and Q="\<lambda>x. True", simplified])
     apply (auto simp: assms(2))[1]
    apply safe
    apply (simp add: core_slice__T__SliceExt_split_at_def core_slice__T__ops_Index_ops_RangeTo_usize___index_def
           core_slice__T__ops_Index_ops_Range_usize___index_def nat_int_add core_ptr__const_T_offset_def checked_sub_def core_slice_from_raw_parts_def
           core_slice__T__ops_Index_ops_RangeFrom_usize___index_def core_slice_SliceExt_is_empty_def core_raw_Slice.defs
           split: split_if_asm)
     apply (simp add: core_slice__T__SliceExt_get_unchecked_def core_ptr__const_T_offset_def assms(1))
     apply safe
qed


end

section \<open> Transpilation of the \emph{examples} crate \<close>

text \<open> Original code:

  \begin{lstlisting}
fn fac(n: u32) -> u32 {
    let mut res = 1;
    for i in 2..n+1 {
        res *= i;
    }
    res
}
  \end{lstlisting}

  Expanded code:

  \begin{lstlisting}
fn fac(n: u32) -> u32 {
    let mut res = 1;
    {
        let _result =
            match ::core::iter::IntoIterator::into_iter(2..n + 1) {
                mut iter =>
                loop  {
                    match ::core::iter::Iterator::next(&mut iter) {
                        ::core::option::Option::Some(i) => { res *= i; }
                        ::core::option::Option::None => break ,
                    }
                },
            };
        _result
    }
    res
}
  \end{lstlisting}

\<close>