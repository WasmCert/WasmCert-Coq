This test features the following addition:
```wasm
i32.const 40
i32.const 2
i32.add
```

```sh
$ wasm_coq_interpreter add.wasm -r main
i32.const 42

```
