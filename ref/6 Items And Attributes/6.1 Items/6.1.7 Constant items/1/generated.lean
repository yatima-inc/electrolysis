import core.generated

noncomputable theory

open [class] classical
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit

namespace test

definition BIT1 : u32 :=
let' ret ← (1 : nat);
ret

definition BIT2 : u32 :=
let' ret ← (2 : nat);
ret

definition BITS : (vector u32 2) :=
let' ret ← [BIT1, BIT2];
ret

definition STRING : string :=
let' ret ← "bitstring";
ret

structure BitsNStrings := mk {} ::
(mybits : (vector u32 2))
(mystring : string)

definition BITS_N_STRINGS : (BitsNStrings) :=
let' t1 ← STRING;
let' t0 ← t1;
let' ret ← BitsNStrings.mk BITS t0;
ret

end test