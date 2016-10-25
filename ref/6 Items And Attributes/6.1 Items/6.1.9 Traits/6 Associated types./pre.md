You would think that a language with awesome dependent types like Lean would not have any problem declaring a type as a type class member, and you would be right. What it *cannot* express, however, are *definitional type equalities* like in `Iterator<Item=T>`, which could be written as `Iterator::Item ~ T` in a more Haskell-y syntax. Therefore, we follow the original paper [1] on associated types in Haskell and desugar them into type parameters. This does weaken type class inference, which is another reason why we don't do that inference in generated code. We might be able to regain inference in a potential future version of Lean that supports functional dependencies.

[1] System F with Type Equality Coercions  
Martin Sulzmann, Manuel M. T. Chakravarty, Simon Peyton Jones, and Kevin Donnelly.  
In G. Necula, editor, Proceedings of The Third ACM SIGPLAN Workshop on Types in Language Design and Implementation, ACM Press, 2007.
