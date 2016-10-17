import collections.pre
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
open collections

namespace collections

definition «[T]».get {T : Type₁} (selfₐ : (slice T)) (indexₐ : usize) : sem ((core.option.Option T)) :=
let' self ← (selfₐ);
let' index ← (indexₐ);
let' t5 ← (self);
let' t6 ← (index);
dostep «$tmp» ← @core.«[T] as core.slice.SliceExt».get _ (t5) (t6);
let' ret ← «$tmp»;
return (ret)


end collections