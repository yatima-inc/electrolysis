Rust `fn`s are translated to curried definitions. The return type is wrapped in a semantics monad, which in the simplest case is `option` for modelling nontermination.
