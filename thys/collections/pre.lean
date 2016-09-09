import core.generated

open function
open list
open option

open core.clone
open core.option

namespace collections
namespace vec

structure Vec (T : Type₁) := mk {} ::
(buf : list T) -- (alloc.raw_vec.RawVec T))
-- (len : usize) -- useless without uninitialized storage

definition from_elem {T : Type₁} [clone : Clone T] (elem : T) (n : usize) : sem (Vec T) :=
dostep c ← @Clone.clone T clone elem;
sem.return_incr (Vec.mk (replicate n c)) n

namespace «Vec<T>»

definition new {T : Type₁} : sem (Vec T) :=
return (Vec.mk [])

-- TODO: amortized complexity
definition push {T : Type₁} (self : Vec T) (value : T) : sem (Vec T) :=
sem.return_incr (Vec.mk (Vec.buf self ++ [value])) (list.length (Vec.buf self))

definition pop {T : Type₁} (self : Vec T) : sem (Vec T × Option T) :=
match reverse (Vec.buf self) with
| x :: xs := return (Vec.mk (reverse xs), Option.Some x)
| []      := return (self, Option.None)
end

definition clear {T : Type₁} (self : Vec T) : sem (Vec T) := new

definition len {T : Type₁} (self : Vec T) : sem (usize) :=
return (list.length (Vec.buf self))

end «Vec<T>»

end vec

open vec

definition «collections.vec.Vec<T> as core.ops.Deref».deref {T : Type₁} (self : (Vec T)) :
  sem (slice T) :=
return (Vec.buf self)


definition «collections.vec.Vec<T> as core.ops.DerefMut».deref_mut {T : Type₁} (self : (Vec T)) :
  sem (lens (Vec T) (slice T) × Vec T) :=
return (⦃lens, get := return ∘ Vec.buf, set := λ old, return ∘ Vec.mk⦄,
        self)

definition «[T]».get_unchecked_mut {T : Type₁} (self : slice T) (index : usize) :
  sem (lens (slice T) T × slice T) :=
return (lens.index _ index, self)

end collections
