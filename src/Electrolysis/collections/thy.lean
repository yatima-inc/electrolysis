import core.thy
import collections.generated

open core
open core.clone
open core.marker

namespace collections

namespace vec

  definition from_elem_Copy_eq {T : Type₁} [Copy' T] (elem : T) (n : usize) :
    sem.terminates_with (λ v, Vec.buf v = list.replicate n elem) (from_elem elem n) :=
  obtain e' k Hcopy He', from sem.terminates_with_eq (Copy'.perfect elem),
  by rewrite [↑from_elem, Hcopy, He', ▸*]

end vec

end collections
