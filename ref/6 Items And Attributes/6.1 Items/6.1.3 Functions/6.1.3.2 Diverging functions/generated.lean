import core.generated

noncomputable theory

open [class] classical
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit

namespace test

definition my_err.FILE_LINE : (string × u32) :=
let' ret ← ("ref/6 Items And Attributes/6.1 Items/6.1.3 Functions/6.1.3.2 Diverging functions/lib.rs", (3 : nat));
ret

definition my_err (s : string) : sem (empty) :=
let' t2 ← my_err.FILE_LINE;
let' t1 ← t2;
mzero


definition f (i : i32) : sem (i32) :=
let' t1 ← i;
let' t0 ← t1 = (42 : int);
if t0 then
let' ret ← (42 : int);
return (ret)
else
let' t5 ← "Bad number!";
let' t4 ← t5;
mzero


end test