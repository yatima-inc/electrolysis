import core.generated

noncomputable theory

open bool
open [class] classical
open [notation] function
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit

namespace test

definition BIT1 : u32 :=
let' ret ← ((1 : nat));
ret

definition BIT2 : u32 :=
let' ret ← ((2 : nat));
ret

definition BITS : (list u32) :=
let' ret ← ([(BIT1), (BIT2)]);
ret

definition STRING : string :=
let' ret ← ("bitstring");
ret

structure BitsNStrings := mk {} ::
(mybits : (list u32))
(mystring : string)

definition BITS_N_STRINGS : (BitsNStrings) :=
let' t2 ← (STRING);
let' t1 ← (t2);
let' ret ← (BitsNStrings.mk (BITS) (t1));
ret

end test