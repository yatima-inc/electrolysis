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

definition test.foo (xₐ : i32) (yₐ : i32) (zₐ : u32) (bₐ : bool) : sem (unit) :=
let' x ← xₐ;
let' y ← yₐ;
let' z ← zₐ;
let' b ← bₐ;
let' t10 ← x;
let' t11 ← t10 =ᵇ (-2147483648 : int);
do «$tmp0» ← checked.neg i32.bits t10;
let' t9 ← «$tmp0»;
let' t13 ← y;
let' t12 ← t13;
let' t15 ← b;
let' t14 ← bool.bnot t15;
let' t17 ← z;
let' t16 ← bitnot t17;
let' t18 ← x;
let' t19 ← @lens.id i32;
do «$tmp» ← lens.get t19 x;
let' ret ← ⋆;
return (ret)


