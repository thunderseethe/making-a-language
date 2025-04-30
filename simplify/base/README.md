Simplifies the IR we introduce in [lowering/base](/lowering/base).
Simplification involves inlining variable definitions and optimizing the resulting IR to improve performance.
This is covered by [simplify[0].base](https://thunderseethe.dev/posts/simplify-base) of the series.

The main entrypoint is the `simplify` function.
