This is a very minimalistic test, containing just an empty module:
```wasm
(module)
```

An empty module is syntactically valid, but one can’t execute any function from it.
```sh
$ wasm_coq_interpreter mod.wasm main # Fails
wasm_interpreter: unknown function `main`
[123]
```

