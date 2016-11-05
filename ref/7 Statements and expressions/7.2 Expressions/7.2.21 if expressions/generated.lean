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

definition test.foo (bₐ : bool) (cₐ : bool) : sem (i32) :=
let' b ← bₐ;
let' c ← cₐ;
let' x ← (0 : int);
let' t7 ← b;
if t7 = bool.tt then
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sadd i32.bits x (1 : int));
let' t8 ← «$tmp0»;
let' x ← t8.1;
let' t10 ← c;
if t10 = bool.tt then
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sadd i32.bits x (1 : int));
let' t11 ← «$tmp0»;
let' x ← t11.1;
let' t12 ← x;
let' ret ← t12;
return (ret)
else
let' t9 ← ⋆;
let' t12 ← x;
let' ret ← t12;
return (ret)
else
let' t6 ← ⋆;
let' t10 ← c;
if t10 = bool.tt then
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sadd i32.bits x (1 : int));
let' t11 ← «$tmp0»;
let' x ← t11.1;
let' t12 ← x;
let' ret ← t12;
return (ret)
else
let' t9 ← ⋆;
let' t12 ← x;
let' ret ← t12;
return (ret)


