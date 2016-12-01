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

definition test.f1 (xₐ : i32) : sem (string) :=
let' «x$2» ← xₐ;
match «x$2» with
| 1 :=
let' ret ← "one";
return (ret)
| 2 :=
let' ret ← "two";
return (ret)
| 3 :=
let' ret ← "three";
return (ret)
| 4 :=
let' ret ← "four";
return (ret)
| 5 :=
let' ret ← "five";
return (ret)
| _ :=
let' ret ← "something else";
return (ret)

end


definition test.f2 (xₐ : i32) : sem (string) :=
let' «x$2» ← xₐ;
let' t4 ← (1 : int) ≤ᵇ «x$2»;
if t4 = bool.tt then
let' t5 ← «x$2» ≤ᵇ (5 : int);
if t5 = bool.tt then
let' «e$3» ← «x$2»;
let' ret ← "got a range element";
return (ret)
else
let' ret ← "anything";
return (ret)
else
let' ret ← "anything";
return (ret)


definition test.f3 (xₐ : i32) : sem (unit) :=
let' «x$2» ← xₐ;
match «x$2» with
| 0 :=
let' «y$3» ← "zero";
match «x$2» with
| 0 :=
let' «z$4» ← "zero";
let' ret ← ⋆;
return (⋆)
| _ :=
let' «z$4» ← "some";
let' ret ← ⋆;
return (⋆)

end
| _ :=
let' «y$3» ← "some";
match «x$2» with
| 0 :=
let' «z$4» ← "zero";
let' ret ← ⋆;
return (⋆)
| _ :=
let' «z$4» ← "some";
let' ret ← ⋆;
return (⋆)

end

end


definition test.f4 (xₐ : i32) : sem (unit) :=
let' «x$2» ← xₐ;
match «x$2» with
| 0 :=
let' «message$3» ← "not many";
let' ret ← ⋆;
return (⋆)
| 1 :=
let' «message$3» ← "not many";
let' ret ← ⋆;
return (⋆)
| _ :=
let' t4 ← (2 : int) ≤ᵇ «x$2»;
if t4 = bool.tt then
let' t5 ← «x$2» ≤ᵇ (9 : int);
if t5 = bool.tt then
let' «message$3» ← "a few";
let' ret ← ⋆;
return (⋆)
else
let' «message$3» ← "lots";
let' ret ← ⋆;
return (⋆)
else
let' «message$3» ← "lots";
let' ret ← ⋆;
return (⋆)

end


definition test.f5.«$_FILE_LINE» : sem (string × u32) :=
let' ret ← ("ref/7 Statements and expressions/7.2 Expressions/7.2.22 Match expressions/lib.rs", (36 : nat));
return (ret)


definition test.f5 (xₐ : (core.option.Option i32)) : sem ((core.option.Option i32)) :=
let' «x$2» ← xₐ;
match «x$2» with
| core.option.Option.None :=
let' t10 ← test.f5.«$_FILE_LINE»;
let' t9 ← t10;
mzero
 | core.option.Option.Some «» :=
do «$tmp0» ← match «x$2» with
| core.option.Option.None :=
mzero | core.option.Option.Some «$0» :=
return «$0»end
;
let' «x$3» ← «$tmp0»;
let' t6 ← «x$3»;
let' t5 ← t6 <ᵇ (10 : int);
if t5 = bool.tt then
let' t7 ← «x$3»;
let' ret ← core.option.Option.Some t7;
return (ret)
else
do «$tmp0» ← match «x$2» with
| core.option.Option.None :=
mzero | core.option.Option.Some «$0» :=
return «$0»end
;
let' «x$4» ← «$tmp0»;
let' ret ← core.option.Option.None;
return (ret)
end


