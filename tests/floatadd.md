This test features an addition function for floats taking arguments from the CLI.
```wasm
(module
  (func (export "main") (param f32 f32) (result f32)
    local.get 0
    local.get 1
    f32.add)
)

```

```sh
$ wasm_coq_interpreter floatadd.wasm -r main -a "f32.const 12.3" -a "f32.const -1.6_4"
i32.const 42

```
