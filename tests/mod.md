This is a very minimalistic test, containing just an empty module:
```wasm
(module)
```

An empty module is syntactically valid, but one can’t execute any function from it.
```sh
$ ../wasm_interpreter --vr mod.wasm test 1 # @negative
$ # Fails with error message: unknown function `test`
```

