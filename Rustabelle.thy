theory Rustabelle
imports Main
begin

type_synonym ('state, 'ans) cont = "'state \<Rightarrow> 'ans"
type_synonym ('state, 'ans) sem = "('state, 'ans) cont \<Rightarrow> ('state, 'ans) cont"

type_synonym u32 = nat

abbreviation seq :: "('state, 'ans) sem \<Rightarrow> ('state, 'ans) sem \<Rightarrow> ('state, 'ans) sem" (infixl ";" 80) where
  "seq s1 s2 \<equiv> s1 \<circ> s2"

end