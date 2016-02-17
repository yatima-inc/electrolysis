theory examples
imports core examples_export Binomial
begin

lemma fac: "examples_fac (n::u32) = fact n"
apply simp
apply (rule loop_range_u32'[where body=examples_fac_4 and P="\<lambda>i res. res = fact (i-1)"])
   apply (auto simp: examples_fac_4_def)[1]
   apply (erule trans)
proof-
  show "fact (max 2 (Suc n) - 1) = fact n"
  apply (cases "n > 1")
   apply (cases n; auto)
  by (cases n; auto)

  show "\<And>i res. 2 \<le> i \<Longrightarrow> res = fact (i - 1) \<Longrightarrow> res * i = fact (Suc i - 1)"
  by (case_tac i; auto)
qed simp

end
