This test contains a few trunc instructions on floats.

```wasm
(module
  (func (export "main") (result i32 i32 i32)
    f32.const 42.69
    i32.trunc_f32_s
    f32.const -42.69
    i32.trunc_f32_s
    f64.const -42.69
    i32.trunc_f64_s
))


```

```sh
$ wasm_coq_interpreter trunc_float.wasm -r main
i32.const 42
i32.const -42
i32.const -42

```

