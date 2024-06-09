# Base Type Checker

This is the minimal complete base type checker.
It handles inferring base types (like `Int`s) and function types.
We constructed it in the first 3 parts (part 0-2) of the [making a language series](https://thunderseethe.dev/series/making-a-language/).
It will be built upon in the followup posts that extend our type checker with fancier types and new features.

The blog posts walks through the constraint generation and constraint solving, but does not cover the final substitution we do to tie everything together.
To see that code check out [substitute](https://github.com/thunderseethe/type-inference-example/blob/main/src/main.rs#L258) and [substitute_ast](https://github.com/thunderseethe/type-inference-example/blob/main/src/main.rs#L281).

If you want to play around with the code, everything is driven by [type_infer](https://github.com/thunderseethe/type-inference-example/blob/main/src/main.rs#L313). You can call it from `main` to type check any input AST.

Some tests are included to exercise the type inference.
