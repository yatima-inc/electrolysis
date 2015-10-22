theory Rustabelle
imports Main
begin

type_synonym ('state, 'ans) cont = "'state \<Rightarrow> 'ans"
type_synonym ('state, 'ans) sem = "('state, 'ans) cont \<Rightarrow> ('state, 'ans) cont"

type_synonym u32 = nat

abbreviation "core_iter_I_IntoIterator_into_iter \<equiv> id"

datatype core_ops_Range = core_ops_Range u32 u32
abbreviation "core_iter_ops_Range_A__Iterator_next r \<equiv> case r of core_ops_Range l r \<Rightarrow> (if l < r then Some (l+1) else None, core_ops_Range (l+1) r)"

type_synonym core_option_Option = "u32 option"
abbreviation "core_option_Option_None \<equiv> None"
abbreviation "core_option_Option_Some \<equiv> Some"

abbreviation seq :: "('state, 'ans) sem \<Rightarrow> ('state, 'ans) sem \<Rightarrow> ('state, 'ans) sem" (infixl ";" 80) where
  "seq s1 s2 \<equiv> s1 \<circ> s2"

end