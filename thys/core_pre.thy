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

text {* Isabelle's Word library provides some nice support for fixed-size integers. *}

type_synonym u8 = "8 word"
type_synonym u16 = "16 word"
type_synonym u32 = "32 word"
type_synonym u64 = "64 word"

abbreviation "u8 n \<equiv> word_of_int n::u8"
abbreviation "u16 n \<equiv> word_of_int n::u16"
abbreviation "u32 n \<equiv> word_of_int n::u32"
abbreviation "u64 n \<equiv> word_of_int n::u64"

lift_definition unsigned_with_overflow :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> 'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word \<times> bool" is "\<lambda>f n m.
  let i = f (uint n) (uint m) in
  (i, uint (word_of_int i::'a word) \<noteq> i)" .

text {* In Rust, overflowing arithmetic operations are undefined behavior, which we model as returning @{term None}. *}

lift_definition unsigned_checked :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> 'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word option" is "\<lambda>f n m. case unsigned_with_overflow f n m of
  (n, False) \<Rightarrow> Some n
| (_, True)  \<Rightarrow> None" .

abbreviation "checked_add \<equiv> unsigned_checked (op +)"
abbreviation "checked_sub \<equiv> unsigned_checked (op -)"
abbreviation "checked_mul \<equiv> unsigned_checked (op *)"
abbreviation "checked_div \<equiv> unsigned_checked (op div)"
abbreviation "checked_mod \<equiv> unsigned_checked (op mod)"

(* TODO
definition "unsigned_checked_shl (a::'a::len word) b = Some (a << (unat b))"
definition "unsigned_checked_shr (a::'a::len word) b = Some (a >> (unat b))"
*)

subsubsection {* Machine-Dependent Integer Types *}

text {* We model the target system's native byte size as an axiomatic constant with a reasonable
  lower bound (met by all target architectures currently supported by @{verbatim rustc}). *}

consts native_bs :: nat

specification (native_bs) native_bs_min: "native_bs \<ge> 32"
by auto

typedef native_bs = "UNIV :: unit set" ..

instantiation native_bs :: len
begin
  definition "len_of_native_bs (_ :: native_bs itself) = native_bs"

  instance 
  using native_bs_min
  by intro_classes (simp add: len_of_native_bs_def)
end

type_synonym usize = "native_bs word"

abbreviation "usize n \<equiv> word_of_int n::usize"

(*
subsubsection {* Manually-Translated Types *}

typedef 'a slice = "{xs::'a list. length xs < 2^native_bs}"
by (rule exI[where x="[]"], simp)
*)

subsection {* Functions *}

subsubsection {* Intrinsics *}

abbreviation "core_intrinsics_add_with_overflow n m \<equiv> Some (unsigned_with_overflow (op +) n m)"
abbreviation "core_intrinsics_sub_with_overflow n m \<equiv> Some (unsigned_with_overflow (op -) n m)"
abbreviation "core_intrinsics_mul_with_overflow n m \<equiv> Some (unsigned_with_overflow (op *) n m)"

subsubsection {* Manually-Translated Functions *}

text {* The original implementation of @{verbatim "core::mem::swap"} uses (via unsafe code) the @{verbatim uninitialized}
  intrinsic. Since it is not clear whether or how we want to support uninitialized memory, we instead
  give a straight-forward manual implementation. *}

definition [simp]: "core_mem_swap x y = Some ((),y,x)"

end

section {* Transpilation of the \emph{core} crate *}

text {* This section merely contains the (transitive) dependencies of the single for loop we want to verify. Still, you might want
  to skip to the \hyperref[sec:core]{next section}. *}
