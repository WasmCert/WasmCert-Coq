This test contains a function returning multiple values.

```wasm
(module
  (func (export "main") (result i32 i64)
    i32.const 42
    i64.const 10000
))
```

```sh
$ wasm_coq_interpreter multivalue.wasm -r main
i32.const 42
i64.const 10000

```
