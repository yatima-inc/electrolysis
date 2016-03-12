section {* Language Primitives *}

theory core_pre
imports
  Main
  "~~/src/HOL/Word/Word"
  "~~/src/HOL/Library/While_Combinator"
begin

subsection {* Control Flow *}

subsubsection {* Succinct Monadic Bind Notation *}

nonterminal dobinds and dobind
syntax
  "_bind"       :: "[pttrn, 'a] => dobind"              ("(2_ \<leftarrow>/ _)" 10)
  "_Do"         :: "[dobind, 'a] => 'a"                 ("(do (_);/ (_))" [0, 10] 10)

translations
  "do x \<leftarrow> a; e"        == "CONST Option.bind a (%x. e)"

subsubsection {* Generalized While Combinator *}

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

subsection {* Types *}

subsubsection {* Machine Types *}

type_synonym u8 = "8 word"
type_synonym u16 = "16 word"
type_synonym u32 = "32 word"
type_synonym u64 = "64 word"

abbreviation "u8 n \<equiv> word_of_int n::u8"
abbreviation "u16 n \<equiv> word_of_int n::u16"
abbreviation "u32 n \<equiv> word_of_int n::u32"
abbreviation "u64 n \<equiv> word_of_int n::u64"

lift_definition uint_with_overflow :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> 'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word \<times> bool" is "\<lambda>f n m.
  let i = f (uint n) (uint m)in
  (i, uint (word_of_int i::'a word) \<noteq> i)" .

lift_definition uint_checked :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> 'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word option" is "\<lambda>f n m. case uint_with_overflow f n m of
  (n, False) \<Rightarrow> Some n
| (_, True)  \<Rightarrow> None" .

abbreviation "checked_add \<equiv> uint_checked (op +)"
abbreviation "checked_sub \<equiv> uint_checked (op -)"
abbreviation "checked_mul \<equiv> uint_checked (op *)"
abbreviation "checked_div \<equiv> uint_checked (op div)"
abbreviation "checked_mod \<equiv> uint_checked (op mod)"

(* TODO *)
definition "checked_shl (a::'a::len word) b = Some (a << (unat b))"
definition "checked_shr (a::'a::len word) b = Some (a >> (unat b))"

subsubsection {* Machine-Dependent Integer Types *}

consts native_bs :: nat

(* let's be somewhat realistic *)
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

subsubsection {* Manually-Translated Types *}

typedef 'a slice = "{xs::'a list. length xs < 2^native_bs}"
by (rule exI[where x="[]"], simp)

subsection {* Functions *}

subsubsection {* Intrinsics *}

abbreviation "core_intrinsics_add_with_overflow n m \<equiv> Some (uint_with_overflow (op +) n m)"
abbreviation "core_intrinsics_sub_with_overflow n m \<equiv> Some (uint_with_overflow (op -) n m)"
abbreviation "core_intrinsics_mul_with_overflow n m \<equiv> Some (uint_with_overflow (op *) n m)"

subsubsection {* Manually-Translated Functions *}

definition[simp]: "core_mem_swap x y = Some ((),y,x)"

end