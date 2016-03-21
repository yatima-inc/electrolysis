section \<open> Finally, a trivial proof of the correctness of the Fibonacci function \<close>

theory examples
imports core examples_export Binomial
begin

lemma fac: "examples_fac n = Some (fact n)"
proof-
  have "\<And>i. 2 \<le> i \<Longrightarrow> fact (i - Suc 0) * i = fact i"
    by (case_tac i, auto)

  moreover have "fact (max (Suc 0) n) = fact n"
    by (cases n, auto)

  ultimately show ?thesis
  apply simp
  apply (rule loop_range_u32'[where body=examples_fac_loop_4 and P="\<lambda>i res. res = fact (i-1)"])
     apply (auto simp: examples_fac_loop_4_def)[1]
    apply auto
  done
qed

end
