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

definition test.BIT1 : sem u32 :=
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.shls u32.bits (1 : nat) (0 : int));
let' t1 ← «$tmp0»;
let' ret ← t1.1;
return (ret)


definition test.BIT2 : sem u32 :=
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.shls u32.bits (1 : nat) (1 : int));
let' t1 ← «$tmp0»;
let' ret ← t1.1;
return (ret)


definition test.BITS : sem (array u32 2) :=
do «$tmp0» ← do «$tmp0» ← test.BIT1;
do «$tmp1» ← test.BIT2;
return ([«$tmp0», «$tmp1»]);
let' ret ← «$tmp0»;
return (ret)


definition test.STRING : sem string :=
let' ret ← "bitstring";
return (ret)


structure test.BitsNStrings := mk {} ::
(mybits : (array u32 2))
(mystring : string)

definition test.BITS_N_STRINGS : sem (test.BitsNStrings) :=
do «$tmp0» ← test.STRING;
let' t2 ← «$tmp0»;
let' t1 ← t2;
do «$tmp0» ← do «$tmp0» ← test.BITS;
return (test.BitsNStrings.mk «$tmp0» t1);
let' ret ← «$tmp0»;
return (ret)


