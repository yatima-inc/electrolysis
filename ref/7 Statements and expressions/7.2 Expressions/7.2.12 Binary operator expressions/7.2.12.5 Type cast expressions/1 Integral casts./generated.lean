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

definition test.foo (xₐ : isize) : sem (u32) :=
let' x ← xₐ;
let' t3 ← x;
do «$tmp0» ← (signed_to_unsigned u32.bits t3);
let' ret ← «$tmp0»;
return (ret)


