theory examples
imports core examples_export Binomial
begin

lemma fac: "examples_fac n = Some (fact n)"
apply simp
apply (rule loop_range_u32'[where P="\<lambda>i res. res = fact (i-1)"])
   apply (auto simp: examples_fac_4_def)[1]
  apply clarsimp
proof-
  show "fact (max (Suc 0) n) = fact n"
  by (cases n; auto)

  show "\<And>i res. 2 \<le> i \<Longrightarrow> res = fact (i - 1) \<Longrightarrow> res * i = fact (Suc i - 1)"
  by (case_tac i; auto)
qed simp

end
