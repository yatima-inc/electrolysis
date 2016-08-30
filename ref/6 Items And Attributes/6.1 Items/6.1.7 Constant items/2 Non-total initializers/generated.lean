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
do tmp__ ← sem.map (λx, (x, true)) (checked.shl (1 : nat) (0 : int));
let' t0 ← tmp__;
let' ret ← t0.1;
ret

definition BIT2 : u32 :=
do tmp__ ← sem.map (λx, (x, true)) (checked.shl (1 : nat) (1 : int));
let' t0 ← tmp__;
let' ret ← t0.1;
ret

end test