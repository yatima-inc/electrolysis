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

definition test.unsigned (xₐ : u32) (yₐ : u32) : sem (unit) :=
let' «x$3» ← xₐ;
let' «y$4» ← yₐ;
let' t6 ← «x$3»;
let' t7 ← «y$4»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add u32.bits t6 t7);
let' t8 ← «$tmp0»;
let' t5 ← t8.1;
let' t10 ← «x$3»;
let' t11 ← «y$4»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sub u32.bits t10 t11);
let' t12 ← «$tmp0»;
let' t9 ← t12.1;
let' t14 ← «x$3»;
let' t15 ← «y$4»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.mul u32.bits t14 t15);
let' t16 ← «$tmp0»;
let' t13 ← t16.1;
let' t18 ← «x$3»;
let' t19 ← «y$4»;
let' t20 ← t19 =ᵇ (0 : nat);
do «$tmp0» ← checked.div u32.bits t18 t19;
let' t17 ← «$tmp0»;
let' t22 ← «x$3»;
let' t23 ← «y$4»;
let' t24 ← t23 =ᵇ (0 : nat);
do «$tmp0» ← checked.rem u32.bits t22 t23;
let' t21 ← «$tmp0»;
let' ret ← ⋆;
return (⋆)


definition test.signed (xₐ : i32) (yₐ : i32) : sem (unit) :=
let' «x$3» ← xₐ;
let' «y$4» ← yₐ;
let' t6 ← «x$3»;
let' t7 ← «y$4»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sadd i32.bits t6 t7);
let' t8 ← «$tmp0»;
let' t5 ← t8.1;
let' t10 ← «x$3»;
let' t11 ← «y$4»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.ssub i32.bits t10 t11);
let' t12 ← «$tmp0»;
let' t9 ← t12.1;
let' t14 ← «x$3»;
let' t15 ← «y$4»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.smul i32.bits t14 t15);
let' t16 ← «$tmp0»;
let' t13 ← t16.1;
let' t18 ← «x$3»;
let' t19 ← «y$4»;
let' t20 ← t19 =ᵇ (0 : int);
let' t21 ← t19 =ᵇ (-1 : int);
let' t22 ← t18 =ᵇ (-2147483648 : int);
let' t23 ← band t21 t22;
do «$tmp0» ← checked.sdiv i32.bits t18 t19;
let' t17 ← «$tmp0»;
let' t25 ← «x$3»;
let' t26 ← «y$4»;
let' t27 ← t26 =ᵇ (0 : int);
let' t28 ← t26 =ᵇ (-1 : int);
let' t29 ← t25 =ᵇ (-2147483648 : int);
let' t30 ← band t28 t29;
do «$tmp0» ← checked.srem i32.bits t25 t26;
let' t24 ← «$tmp0»;
let' ret ← ⋆;
return (⋆)


