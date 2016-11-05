Skeleton code that surrounds each transpilation, which will be hidden in all further examples. The crate name ('test' in these examples) becomes the root namespace.

Files inside a crate may freely reference items between them. On the other
hand, Lean files may only import other files non-recursively and declarations
must be strictly sorted in order of usage for termination checking. We therefore
translate a crate into a single Lean file and perform a topological sort on its
items.
