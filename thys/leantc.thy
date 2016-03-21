theory leantc
imports core leantc_export
begin

fun Level_eval :: "(leantc_name_Name \<rightharpoonup> nat) \<Rightarrow> leantc_level_Level \<Rightarrow> nat option" where
  "Level_eval \<sigma> (leantc_level_Level (alloc_rc_Rc leantc_level_LevelCell_Zero)) = Some 0"
| "Level_eval \<sigma> (leantc_level_Level (alloc_rc_Rc (leantc_level_LevelCell_Succ l))) = map_option Suc (Level_eval \<sigma> l)"
| "Level_eval \<sigma> (leantc_level_Level (alloc_rc_Rc (leantc_level_LevelCell_Max l l'))) =
    (do el \<leftarrow> Level_eval \<sigma> l; do el' \<leftarrow> Level_eval \<sigma> l'; Some (max el el'))"
| "Level_eval \<sigma> (leantc_level_Level (alloc_rc_Rc (leantc_level_LevelCell_IMax l l'))) =
    (do el \<leftarrow> Level_eval \<sigma> l; do el' \<leftarrow> Level_eval \<sigma> l'; Some (if el' = 0 then 0 else max el el'))"
| "Level_eval \<sigma> (leantc_level_Level (alloc_rc_Rc (leantc_level_LevelCell_Param n))) = \<sigma> n"
| "Level_eval \<sigma> (leantc_level_Level (alloc_rc_Rc (leantc_level_LevelCell_Global n))) = \<sigma> n"


termination leantc_level_Level_is_definitely_not_zero
  by (relation "measure size") (auto split: leantc_level_Level.splits alloc_rc_Rc.splits)

declare leantc_level_Level_is_definitely_not_zero.simps [simp del]

lemma is_definitely_not_zero_terminating [simp]:
  "leantc_level_Level_is_definitely_not_zero (leantc_level_Level (alloc_rc_Rc lc)) \<noteq> None"
by (induction lc) (auto simp: leantc_level_Level_is_definitely_not_zero.simps[of "leantc_level_Level _"] split: alloc_rc_Rc.splits)

lemma is_definitely_not_zero: "leantc_level_Level_is_definitely_not_zero l = Some True \<Longrightarrow> (\<forall>\<sigma>. Level_eval \<sigma> l \<noteq> Some 0)"
  "leantc_level_Level_is_definitely_not_zero (leantc_level_Level (alloc_rc_Rc lc)) = Some True \<Longrightarrow> (\<forall>\<sigma>. Level_eval \<sigma> (leantc_level_Level (alloc_rc_Rc lc)) \<noteq> Some 0)"
apply (induction l and lc)
      apply (case_tac x; case_tac xa; auto split: alloc_rc_Rc.splits leantc_level_LevelCell.splits)
     apply (auto simp: leantc_level_Level_is_definitely_not_zero.simps[of "leantc_level_Level _"])[2]
   apply (auto simp: bind_eq_Some_conv max_def leantc_level_Level_is_definitely_not_zero.simps[of "leantc_level_Level _"] split: if_splits)[1]
     apply (drule_tac x=\<sigma> in spec; auto)+
  apply (auto simp: bind_eq_Some_conv max_def leantc_level_Level_is_definitely_not_zero.simps[of "leantc_level_Level _"] split: if_splits)
done

end