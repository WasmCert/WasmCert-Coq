This test features an addition function taking arguments from the CLI.
```wasm
(module
  (func (export "main") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.add)
)

```

```sh
$ wasm_coq_interpreter add2.wasm -r main -a "i32.const 12_3" -a "i32.const -8_1"
i32.const 42

```
