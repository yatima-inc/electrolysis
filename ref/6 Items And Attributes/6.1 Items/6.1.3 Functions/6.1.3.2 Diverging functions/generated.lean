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

definition test.my_err.«$_FILE_LINE» : sem (string × u32) :=
let' ret ← ("ref/6 Items And Attributes/6.1 Items/6.1.3 Functions/6.1.3.2 Diverging functions/lib.rs", (3 : nat));
return (ret)


definition test.my_err (sₐ : string) : sem (empty) :=
let' «s$2» ← sₐ;
let' t6 ← test.my_err.«$_FILE_LINE»;
let' t5 ← t6;
mzero


definition test.f (iₐ : i32) : sem (i32) :=
let' «i$2» ← iₐ;
let' t4 ← «i$2»;
let' t3 ← t4 =ᵇ (42 : int);
if t3 = bool.tt then
let' ret ← (42 : int);
return (ret)
else
let' t11 ← "Bad number!";
let' t10 ← t11;
mzero


