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
let' x ← xₐ;
match x with
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
let' x ← xₐ;
let' t4 ← (1 : int) ≤ᵇ x;
if t4 = bool.tt then
let' t5 ← x ≤ᵇ (5 : int);
if t5 = bool.tt then
let' e ← x;
let' ret ← "got a range element";
return (ret)
else
let' ret ← "anything";
return (ret)
else
let' ret ← "anything";
return (ret)


definition test.f3 (xₐ : i32) : sem (unit) :=
let' x ← xₐ;
match x with
| 0 :=
let' y ← "zero";
match x with
| 0 :=
let' z ← "zero";
let' ret ← ⋆;
return (⋆)
| _ :=
let' z ← "some";
let' ret ← ⋆;
return (⋆)

end
| _ :=
let' y ← "some";
match x with
| 0 :=
let' z ← "zero";
let' ret ← ⋆;
return (⋆)
| _ :=
let' z ← "some";
let' ret ← ⋆;
return (⋆)

end

end


definition test.f4 (xₐ : i32) : sem (unit) :=
let' x ← xₐ;
match x with
| 0 :=
let' message ← "not many";
let' ret ← ⋆;
return (⋆)
| 1 :=
let' message ← "not many";
let' ret ← ⋆;
return (⋆)
| _ :=
let' t4 ← (2 : int) ≤ᵇ x;
if t4 = bool.tt then
let' t5 ← x ≤ᵇ (9 : int);
if t5 = bool.tt then
let' message ← "a few";
let' ret ← ⋆;
return (⋆)
else
let' message ← "lots";
let' ret ← ⋆;
return (⋆)
else
let' message ← "lots";
let' ret ← ⋆;
return (⋆)

end


definition test.f5.FILE_LINE : sem (string × u32) :=
let' ret ← ("ref/7 Statements and expressions/7.2 Expressions/7.2.22 Match expressions/lib.rs", (36 : nat));
return (ret)


definition test.f5 (xₐ : (core.option.Option i32)) : sem ((core.option.Option i32)) :=
let' x ← xₐ;
match x with
| core.option.Option.None :=
let' t10 ← test.f5.FILE_LINE;
let' t9 ← t10;
mzero
 | core.option.Option.Some discr_0 :=
let' x ← discr_0;
let' t6 ← x;
let' t5 ← t6 <ᵇ (10 : int);
if t5 = bool.tt then
let' t7 ← x;
let' ret ← core.option.Option.Some t7;
return (ret)
else
let' x ← discr_0;
let' ret ← core.option.Option.None;
return (ret)
end


