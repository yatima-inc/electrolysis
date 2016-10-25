import .generated
import core.thy

open int

example (x y : i32) [is_i32 (x + y)] : sem.terminates_with (λ sum, x + y = sum) (test.add x y) :=
by rewrite [↑test.add, if_pos `is_i32 (x + y)`, ▸*]

example (x y : i32) : sem.terminates_with (λ z, z = x) (test.first (x, y)) :=
rfl
