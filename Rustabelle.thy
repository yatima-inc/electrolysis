theory Rustabelle
imports Main
begin

type_synonym ('state, 'res, 'ans) cont = "'state \<Rightarrow> 'res \<Rightarrow> 'ans"
type_synonym ('state, 'res, 'ans) sem = "('state, 'res, 'ans) cont \<Rightarrow> 'state \<Rightarrow> 'ans"

type_synonym u32 = nat

abbreviation lift :: "('r1 \<Rightarrow> 'r2) \<Rightarrow> ('state, 'r1, 'ans) sem \<Rightarrow> ('state, 'r2, 'ans) sem" where
  "lift f s \<equiv> \<lambda>c. s (\<lambda>s r. c s (f r))"

abbreviation lift2 :: "('r1 \<Rightarrow> 'r2 \<Rightarrow> 'r3) \<Rightarrow> ('state, 'r1, 'ans) sem \<Rightarrow> ('state, 'r2, 'ans) sem \<Rightarrow> ('state, 'r3, 'ans) sem" where
  "lift2 f s1 s2 \<equiv> \<lambda>c. s1 (\<lambda>s r\<^sub>1. s2 (\<lambda>s r\<^sub>2. c s (f r\<^sub>1 r\<^sub>2)) s)"

abbreviation "seq s1 s2 \<equiv> lift2 (\<lambda>_ r2. r2) s1 s2"
end