# Emit Base

Covered by [Skipping the Backend by Emitting Wasm](https://thunderseethe.dev/posts/emit-base/) in the making a language series.
This pass sees us finally reaching executable code.
We convert our closure converted items into a Wasm module that can be interpreted.

Examples of this can be found in the tests for this crate, where we use `wasmtime` to execute our generated code.
