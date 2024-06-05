# Type Inference Example

Implementation of Type Inference discussed in: https://thunderseethe.dev/series/making-a-language/.

This crate is divided up into a crate for each "stage" of the type checker.
Right now there's two stages in the typechecker:

* [base](/base) - The initial base type checker.
* [row](/row) - Extends base with support for datatypes via row types.

