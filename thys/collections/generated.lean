import alloc.generated
import core.generated

noncomputable theory

open [class] classical
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit

namespace collections

structure vec.Vec (T : Type₁) := «{{constructor}}» {} ::
(buf : (alloc.raw_vec.RawVec T))
(len : usize)

end collections