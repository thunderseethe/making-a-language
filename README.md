# Making a Language

Implementation code for: https://thunderseethe.dev/series/making-a-language/.

This project is divided up into a crate for each "stage" of the compiler.
Each crate has at least one associated article in the making a language series (some crates have multiple articles associated with them).
The stages in the compiler:

* [types](/types) - Type inference and checking
  * [base](/types/base) - The initial base type checker.
  * [rows](/types/rows) - Extends base with support for datatypes via row types.
  * [items](/types/items) - Extends rows with support for checking top level functions.
* [lowering](/lowering) - Lowering into our intermediate representation (IR)
  * [base](/lowering/base) - Lowering the AST of our base type checker.
  * [rows](/lowering/rows) - Lowering our rows type checker using evidence passing.
  * [items](/lowering/items) - Lowering top level items into our IR.
* [simplify](/simplify) - Simplify our IR to improve its performance.
  * [base](/simplify/base) - Simplifying our base IR.
* [monomorph](/monomorph) - Monomorphization removes polymorphism from our IR.
  * [base](/monomorph/base) - Monomorphizing our base IR.
* [closure_convert](/closure_convert) - Closure conversion removes functions from our IR.
  * [base](/closure_convert/base) - Closure convert our base IR.
* [emit](/emit) - Code emission targeting WebAssembly
  * [base](/emit/base) - Emit Wasm for our closure-converted base IR.
