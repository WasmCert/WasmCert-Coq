This test contains some saturated trunc operations.

```wasm
(module
  (func (export "main") (result i32 i32 i32 i64 i64)
    f64.const 0x1.a0aa7ep+7 (;=208.333;)
    i32.trunc_sat_f64_s
    f32.const nan
    i32.trunc_sat_f32_u
    f32.const -inf
    i32.trunc_sat_f32_s
    f64.const 0x1.388p+7 (;=156.25;)
    i64.trunc_sat_f64_s
    f32.const inf
    i64.trunc_sat_f32_u
  )
)
```

```sh
$ wasm_coq_interpreter trunc_sat.wasm -r main
i32.const 208
i32.const 0
i32.const -2147483648
i64.const 156
i64.const -1

```

