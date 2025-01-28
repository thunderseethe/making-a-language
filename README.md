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
