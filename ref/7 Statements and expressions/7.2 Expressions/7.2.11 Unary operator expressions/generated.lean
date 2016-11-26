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

definition test.foo (xₐ : i32) (yₐ : i32) (bₐ : bool) : sem (unit) :=
let' x ← xₐ;
let' y ← yₐ;
let' b ← bₐ;
let' t8 ← x;
let' t9 ← t8 =ᵇ (-2147483648 : int);
do «$tmp0» ← checked.neg i32.bits t8;
let' t7 ← «$tmp0»;
let' t11 ← x;
let' t10 ← sbitnot i32.bits t11;
let' t13 ← y;
let' t12 ← t13;
let' t15 ← b;
let' t14 ← bool.bnot t15;
let' t16 ← x;
let' t17 ← @lens.id i32;
do «$tmp» ← lens.get t17 x;
let' ret ← ⋆;
return (⋆)


