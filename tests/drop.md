This test features dropping a value from the stack:
```wasm
i32.const 42
i32.const 123
drop
```

```sh
$ wasm_coq_interpreter drop.wasm main 100
i32.const 42

```
