import .generated

open int
open list
open prod.ops

example (x y : i32) : sem.terminates_with (λ r, lens.get r.1 [x, y] = return x) (test.foo [x, y]) := rfl
