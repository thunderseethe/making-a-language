# Name Resolution Base

See the [accompanying blog post](https://thunderseethe.dev/post/nameres-base) for the full tutorial.

Name resolution is the pass where we assign a unique variable to each of our names.
It turns out `Ast<String>` into the `Ast<Var>` that type inference takes as input, completeing the compilation circle.
