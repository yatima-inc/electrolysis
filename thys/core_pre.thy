theory core_pre
imports Main "~~/src/HOL/Library/While_Combinator"
begin

definition loop :: "('state \<Rightarrow> 'state \<times> bool) \<Rightarrow> 'state \<Rightarrow> 'state" where
  "loop l s = (let (s,s',c) = while (\<lambda>(s,s',c). c) (\<lambda>(s,s',c). (s',(l s'))) (s,(l s)) in s')"


type_synonym u32 = nat
type_synonym usize = nat

definition[simp]: "u32_to_usize = id"

definition[simp]: "core_num_u32_overflowing_add x y = (x + y, False)"

definition[simp]: "core_mem_swap x y = ((),y,x)"

end