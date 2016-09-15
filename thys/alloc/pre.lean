import data.list
import core.pre

open list

namespace alloc
namespace raw_vec
  definition RawVec (T : Type₁) := list (option T)

  /- Creates the biggest possible RawVec without allocating.
     If T has positive size, then this makes a RawVec with capacity 0. If T has 0 size,
     then it it makes a RawVec with capacity usize::MAX. Useful for implementing delayed allocation.
    -/
  -- Since we currently don't have `usize::MAX`, always return empty RawVec. This should work, I
  -- I think.
  definition «RawVec<T>».new {T : Type₁} : sem (RawVec T) := return []
end raw_vec
end alloc
