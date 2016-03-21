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

lemma not_loop_control [simp]: "l \<noteq> Continue \<Longrightarrow> l = Break" "l \<noteq> Break \<Longrightarrow> l = Continue"
  by (cases l, simp_all)+

lemma loop_rule:
  assumes "P s"
  assumes "\<And>s s'. P s \<Longrightarrow> l s = (s',Continue) \<Longrightarrow> P s'" "\<And>s s'. P s \<Longrightarrow> l s = (s',Break) \<Longrightarrow> Q s'"
  assumes "wf r" "\<And>s s'. P s \<Longrightarrow> l s = (s',Continue) \<Longrightarrow> (s', s) \<in> r"
  shows "all_option Q (loop l s)"
proof-
  let ?r' = "{((s\<^sub>1, l s\<^sub>1), (s\<^sub>2, l s\<^sub>2)) | s\<^sub>1 s\<^sub>2. (s\<^sub>1,s\<^sub>2) \<in> r}"
  have "wf ?r'"
    by (rule compat_wf[where f=fst, OF _ assms(4)]) (auto simp: compat_def)

  show ?thesis
  unfolding loop_def all_option_comp[symmetric]
  by (rule while_opt_rule[where P="\<lambda>(s,s'). P s \<and> l s = s'", OF _ _ _ `wf ?r'`])
     (auto simp: assms pred_option_def)
qed

lemma loop'_rule:
  assumes "P s"
  assumes "\<And>s. P s \<Longrightarrow> l s \<noteq> None" "\<And>s s'. P s \<Longrightarrow> l s = Some (s',Continue) \<Longrightarrow> P s'" "\<And>s s'. P s \<Longrightarrow> l s = Some (s',Break) \<Longrightarrow> Q s'"
  assumes "wf r" "\<And>s s'. P s \<Longrightarrow> l s = Some (s',Continue) \<Longrightarrow> (s', s) \<in> r"
  shows "all_option Q (loop' l s)"
proof-
  let ?r' = "{(Some s\<^sub>1, Some s\<^sub>2) | s\<^sub>1 s\<^sub>2. (s\<^sub>1,s\<^sub>2) \<in> r}"
  have "wf ?r'"
    by (rule compat_wf[where f=the, OF _ assms(5)]) (auto simp: compat_def)

  show ?thesis
  by (cut_tac loop_rule[where P="all_option P" and Q="all_option Q" and s="Some s", OF _ _ _ `wf ?r'`])
     (auto simp: loop'_def all_option_def pred_option_def Option.bind_def assms(1,2,6) intro: assms(3,4) split: option.splits)
qed

declare Let_def[simp] Option.bind_eq_Some_conv[simp] Option.bind_eq_None_conv[simp]
declare not_None_eq[iff del]

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