theory Rustabelle
imports Main
begin

type_synonym ('state, 'res, 'ans) cont = "'state \<Rightarrow> 'res \<Rightarrow> 'ans"
type_synonym ('state, 'res, 'ans) sem = "('state, 'res, 'ans) cont \<Rightarrow> 'state \<Rightarrow> 'ans"

type_synonym u32 = nat

abbreviation seq :: "('state, unit, 'ans) sem \<Rightarrow> ('state, 'res, 'ans) sem \<Rightarrow> ('state, 'res, 'ans) sem" (infix ";" 20) where
  "s1; s2 \<equiv> \<lambda>c. s1 (\<lambda>s _. s2 c s)"

abbreviation lift2 :: "('res \<Rightarrow> 'res \<Rightarrow> 'res) \<Rightarrow> ('state, 'res, 'ans) sem \<Rightarrow> ('state, 'res, 'ans) sem \<Rightarrow> ('state, 'res, 'ans) sem" where
  "lift2 f s1 s2 \<equiv> \<lambda>c. s1 (\<lambda>s r\<^sub>1. s2 (\<lambda>s r\<^sub>2. c s (f r\<^sub>1 r\<^sub>2)) s)"

end