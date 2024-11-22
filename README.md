# Type Inference Example

Implementation of Type Inference discussed in: https://thunderseethe.dev/series/making-a-language/.

This crate is divided up into a crate for each "stage" of the type checker.
The stages in the typechecker are:

* [types](/types) - Type inference and checking
  * [base](/base) - The initial base type checker.
  * [rows](/rows) - Extends base with support for datatypes via row types.
  * [items](/items) - Extends rows with support for checking top level functions.
* [lowering](/lowering) - Lowering into our IR
  * [base](/base) - Lowering our AST of our base type checker.
