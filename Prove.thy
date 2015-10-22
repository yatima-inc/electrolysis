theory Prove
imports Export Binomial
begin

(*
lemma fac_16:
  assumes "s 3 = core_option_Option_Some (Any_3 (core_ops_Range 2 n))"
  shows "fac_16 (\<lambda>s. case s (Suc 0) of Some (Any_1 xa) \<Rightarrow> xa) s = fact n"
proof-
  have "fac_16_dom (\<lambda>a. fac_16 (\<lambda>s. case s (Suc 0) of Some (Any_1 xa) \<Rightarrow> xa) a = fact n, s)"
  thm fac_16.domintros
  apply (rule fac_16.domintros)
  apply (auto split:option.splits)

  
  apply (rule fac_16.pinduct)
*)

lemma "(s(1:=1,2:=2,3:=3)) 2 = 2" by simp
find_theorems "_(?x:=_,?y := _ )"
lemma "(case if b then Some x else None of Some x \<Rightarrow> P x | None \<Rightarrow> Q) = P x" by simp
lemma fac: "fac (n::u32) = fact n"
proof-
  let ?s = "
     (Map.empty(0 := core_option_Option_Some (Any_0 n), Suc 0 := core_option_Option_Some (Any_1 (Suc 0)), 8 := core_option_Option_Some (Any_8 core_iter_I_IntoIterator_into_iter),
                10 := core_option_Option_Some (Any_10 n), 9 := core_option_Option_Some (Any_9 (core_ops_Range 2 n)), 7 := core_option_Option_Some (Any_7 (core_ops_Range 2 n)),
                3 := core_option_Option_Some (Any_3 (core_ops_Range 2 n))))"
  show ?thesis
  unfolding fac_def
  apply auto
  apply (rule loop_rule[where P="\<lambda>s. \<exists>k. s 9 = Some (Any_9 (core_ops_Range k n))"])
  apply (auto simp: fac_16_def)[1]
  apply (simp add: fac_16_def split:prod.splits core_ops_Range.splits)
  apply (cases "2<n")
  apply auto[1]
qed

end