A trait object type `&Trait` can be interpreted as an existential type `∃ (T : Trait), T` or, generically for all traits in Lean, as a dependent record

[sourcecode:lean]
structure trait_obj (Trait : Type → Type) := -- `Trait` explicitly takes `Self` in Lean
(ActualType : Type)
(impl : Trait ActualType)
(self : ActualType)
[/sourcecode]

We could then specify that a trait object indeed implements its trait by generating an instance of type `Trait (trait_obj Trait)`. The instance would call the respective function on `impl` with `self`, and, in the case of `&mut self` methods, place the new value of `self` back into the trait object.

However, this wouldn't integrate well (or at all) currently because of technical reasons (`trait_obj Trait` living in `Type₂` and Lean's universe hierarchy being noncumulative, if you really want to know), so we simply don't touch that yet.
