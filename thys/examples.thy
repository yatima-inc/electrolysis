theory examples
imports core examples_export Binomial
begin

lemma fact_greater_arg: "n > 2 \<Longrightarrow> n < fact n"
proof (induction n)
  case (Suc n)
  show ?case
  proof (cases "n > 2")
    case False
    with Suc show ?thesis
    apply (cases n)
     apply simp
    apply (rename_tac pn)
    apply (case_tac pn)
    by auto
  next
    case True
    hence "Suc n < n + n" by simp
    also have "\<dots> \<le> fact n + n" using True Suc by simp
    also have "\<dots> \<le> fact (Suc n)" by simp
    finally show ?thesis by simp
  qed
qed simp

declare semiring_numeral_class.power_numeral [simp del]

lemma fac:
  assumes "fact n < (2::int)^32"
  shows "examples_fac (u32 (int n)) = Some (u32 (fact n))"
proof-
  have [simp]: "Suc n < 2^32"
    using fact_greater_arg[of n] assms
    by (cases "n > 2") auto

  have 0: "\<And>i. i > 0 \<Longrightarrow> fact (i - Suc 0) * int i = fact i"
    by (case_tac i; auto)

  have 1: "\<And>i. i > 0 \<Longrightarrow> fact (nat i - Suc 0) * i = fact (nat i)"
    by (case_tac i; simp add: 0)

  have 3: "\<And>i. i < u32 (int n) + 1 \<Longrightarrow> unat i < n"
    sorry

  have [simp]: "\<And>(i::u32) j. 2 \<le> i \<Longrightarrow> i < j \<Longrightarrow> unat (i + 1) - Suc 0 = unat i"
    by unat_arith

  have 3: "\<And>i. 2 \<le> i \<Longrightarrow> i < u32 (int n) + 1 \<Longrightarrow> fact (unat i-1) < (2::int)^32 \<Longrightarrow> fact (unat i) < (2::int)^32"
  apply (rule less_trans[of _ "fact n"])
   apply (rule fact_less_mono)
    apply unat_arith
   apply (erule 3)
  using assms
  apply simp
  done

  have 2: "\<And>i. 2 \<le> i \<Longrightarrow> i < u32 (int n) + 1 \<Longrightarrow> fact (unat i-1) < (2::int)^32 \<Longrightarrow> checked_mul (u32 (fact (unat i - Suc 0))) i = Some (u32 (fact (unat i)))"
  apply (clarsimp simp: checked_mul word_mult_def uint_word_of_int int_mod_eq' unat_def)
  apply safe
   apply (subst 1)
    apply uint_arith
   apply simp
  apply (subst 1)
   apply uint_arith
  apply (rule 3[unfolded unat_def]; simp)
  done
   
  show ?thesis
  apply simp
  apply (rule loop_range_u32'[where P="\<lambda>i res. fact (unat i-1) < 2^32 \<and> res = u32 (fact (unat i-1))"])
      apply (auto simp: examples_fac_4_def)[1]
     apply (auto simp: bind_eq_Some_conv)[1]
     apply (subst 2; simp)
    apply (rule 3; simp)
   apply (auto)[1]
  sorry
qed

end
