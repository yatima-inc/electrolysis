section \<open> Finally, a trivial proof of the correctness of the Fibonacci function \<close>

theory examples
imports core examples_export Binomial
begin

declare semiring_numeral_class.power_numeral [simp del]
 
lemma fac:
  assumes "fact n < (2::int)^32"
  shows "examples_fac (u32 (int n)) = Some (u32 (fact n))"
proof-
  have int_n: "int n < 2^32"
  apply (cases "n > 2")
   using fact_ge_self[of n, simplified zle_int[symmetric]] assms
   apply auto[1]
  by (smt numeral_eq_one_iff of_nat_less_imp_less one_less_power power_inject_exp power_one_right semiring_norm(85) transfer_int_nat_numerals(3) zero_less_numeral)

  have 0: "\<And>i. i > 0 \<Longrightarrow> fact (i - Suc 0) * int i = fact i"
    by (case_tac i; auto)

  have 1: "\<And>i. i > 0 \<Longrightarrow> fact (nat i - Suc 0) * i = fact (nat i)"
    by (case_tac i; simp add: 0)

  have 2: "\<And>(i::u32) j. i < j \<Longrightarrow> unat (i + 1) - Suc 0 = unat i"
    by unat_arith

  have 3: "\<And>i. 2 \<le> i \<Longrightarrow> i < u32 (int n) + 1 \<Longrightarrow> fact (unat i-1) < (2::int)^32 \<Longrightarrow> fact (unat i) < (2::int)^32"
  apply (rule le_less_trans[of _ "fact n"])
   apply (rule fact_mono)
   unfolding unat_def
   apply uint_arith
   apply (simp add: int_word_uint int_mod_eq' int_n)
  using assms
  apply simp
  done

  have 4: "\<And>i. 2 \<le> i \<Longrightarrow> i < u32 (int n) + 1 \<Longrightarrow> fact (unat i-1) < (2::int)^32 \<Longrightarrow> checked_mul (u32 (fact (unat i - Suc 0))) i = Some (u32 (fact (unat i)))"
  apply (clarsimp simp: checked_mul word_mult_def uint_word_of_int int_mod_eq' unat_def)
  apply safe
   apply (subst 1)
    apply uint_arith
   apply simp
  apply (subst 1)
   apply uint_arith
  apply (rule 3[unfolded unat_def]; simp)
  done

  have 5: "u32 (int n) < u32 (2^32-1)"
    sorry

  have 6: "\<not> 2 \<le> u32 (int n) + 1 \<Longrightarrow> u32 (fact n) = 1"
    sorry

  show ?thesis
  apply simp
  apply (rule loop_range_u32'[where P="\<lambda>i res. fact (unat i-1) < 2^32 \<and> res = u32 (fact (unat i-1))"])
      apply (auto simp: examples_fac_loop_5_def)[1]
     apply (auto simp: bind_eq_Some_conv)[1]
     apply (subst 4; simp add: 2)
    apply (simp only: 2)
    apply (rule 3; simp)
   using 5
   apply (auto simp: max_def unat_def uint_word_of_int int_mod_eq' int_n 6 simp: 2[OF 5, simplified unat_def])
  done
qed

end
