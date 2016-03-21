section {* Language Primitives *}

theory core_pre
imports
  Main
  "~~/src/HOL/Word/Word"
  "~~/src/HOL/Library/While_Combinator"
begin

subsection {* Control Flow *}

subsubsection {* Succinct Monadic Bind Notation *}

text {* A simple notation for @{term Option.bind} that does not need a surrounding do block. *}

nonterminal dobinds and dobind
syntax
  "_bind"       :: "[pttrn, 'a] => dobind"              ("(2_ \<leftarrow>/ _)" 10)
  "_Do"         :: "[dobind, 'a] => 'a"                 ("(do (_);/ (_))" [0, 10] 10)

translations
  "do x \<leftarrow> a; e"        == "CONST Option.bind a (%x. e)"

subsubsection {* Generalized While Combinator *}

text {* In the Rust intermediate representation, every loop is represented by the unconditional
  @{verbatim loop} control structure. We accordingly generalize Isabelle's While combinator. *}

datatype loop_control = Continue | Break

definition loop :: "('state \<Rightarrow> 'state \<times> loop_control) \<Rightarrow> 'state \<Rightarrow> 'state option" where
  "loop l s \<equiv> map_option (\<lambda>(s,s',c). s')
    (while_option (\<lambda>(s,s',c). c = Continue) (\<lambda>(s,s',c). (s',(l s'))) (s,(l s)))"

text {* Extend @{term loop} to partial loop body functions. *}

definition loop' :: "('state \<Rightarrow> ('state \<times> loop_control) option) \<Rightarrow> 'state \<Rightarrow> 'state option" where
  "loop' l s = Option.bind (
    loop (\<lambda>s. case l (the s) of
        None \<Rightarrow> (Some (the s), Break)
      | Some (s',c) \<Rightarrow> (Some s',c))
    (Some s)
  ) id"

subsection {* Types *}

subsubsection {* Machine Types *}

type_synonym u8 = nat
type_synonym u16 = nat
type_synonym u32 = nat
type_synonym u64 = nat
type_synonym usize = nat

definition checked_sub :: "nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "checked_sub n m \<equiv> if n \<ge> m then Some (n - m) else None"

definition "checked_div n m \<equiv> if m \<noteq> 0 then Some (n div m) else None"
definition "checked_mod n m \<equiv> if m \<noteq> 0 then Some (n mod m) else None"

(* TODO
definition "unsigned_checked_shl (a::'a::len word) b = Some (a << (unat b))"
definition "unsigned_checked_shr (a::'a::len word) b = Some (a >> (unat b))"
*)

(*
subsubsection {* Manually-Translated Types *}

typedef 'a slice = "{xs::'a list. length xs < 2^native_bs}"
by (rule exI[where x="[]"], simp)
*)

subsection {* Functions *}

subsubsection {* Intrinsics *}

abbreviation "core_intrinsics_add_with_overflow n m \<equiv> Some (n + m, False)"

subsubsection {* Manually-Translated Functions *}

text {* The original implementation of @{verbatim "core::mem::swap"} uses (via unsafe code) the @{verbatim uninitialized}
  intrinsic. Since it is not clear whether or how we want to support uninitialized memory, we instead
  give a straight-forward manual implementation. *}

definition [simp]: "core_mem_swap x y = Some ((),y,x)"

end

section {* Transpilation of the \emph{core} crate *}

text {* This section merely contains the (transitive) dependencies of the single for loop we want to verify. Still, you might want
  to skip to the \hyperref[sec:core]{next section}. *}
