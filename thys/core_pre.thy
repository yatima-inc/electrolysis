theory core_pre
imports Main "~~/src/HOL/Library/While_Combinator"
begin

nonterminal dobinds and dobind
syntax
  "_bind"       :: "[pttrn, 'a] => dobind"              ("(2_ \<leftarrow>/ _)" 10)
  "_Do"         :: "[dobind, 'a] => 'a"                 ("(do (_)/; (_))" [0, 10] 10)

translations
  "do x \<leftarrow> a; e"        == "CONST Option.bind a (%x. e)"

definition loop :: "('state \<Rightarrow> 'state \<times> bool) \<Rightarrow> 'state \<Rightarrow> 'state option" where
  "loop l s \<equiv> map_option (\<lambda>(s,s',c). s')
    (while_option (\<lambda>(s,s',c). c) (\<lambda>(s,s',c). (s',(l s'))) (s,(l s)))"

definition loop' :: "('state \<Rightarrow> ('state \<times> bool) option) \<Rightarrow> 'state \<Rightarrow> 'state option" where
  "loop' l s = Option.bind (
    loop (\<lambda>s. case s of
      None \<Rightarrow> (None, False)
    | Some s \<Rightarrow> (case l s of
        None \<Rightarrow> (Some s, False)
      | Some (s',c) \<Rightarrow> (Some s',c)))
    (Some s)
  ) id"

type_synonym u32 = nat
type_synonym usize = nat

definition[simp]: "u32_to_usize = id"

definition[simp]: "core_num_u32_overflowing_add x y = Some (x + y, False)"

definition[simp]: "core_mem_swap x y = Some ((),y,x)"

end