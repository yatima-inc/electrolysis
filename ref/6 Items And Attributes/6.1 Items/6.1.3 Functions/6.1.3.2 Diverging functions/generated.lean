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

definition my_err.FILE_LINE : (string × u32) :=
let' ret ← ((("ref/6 Items And Attributes/6.1 Items/6.1.3 Functions/6.1.3.2 Diverging functions/lib.rs"), ((3 : nat))));
ret

definition my_err (sₐ : string) : sem (empty) :=
let' s ← (sₐ);
let' t3 ← (my_err.FILE_LINE);
let' t2 ← (t3);
mzero


definition f (iₐ : i32) : sem (i32) :=
let' i ← (iₐ);
let' t1 ← (i);
let' t0 ← ((t1) =ᵈ ((42 : int)));
if (t0) = tt then
let' ret ← ((42 : int));
return (ret)
else
let' t8 ← ("Bad number!");
let' t7 ← (t8);
mzero


end test