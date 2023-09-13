This test contains an reinterpretation of f32.nan to a 32-bit integer.

```wasm
f32.const nan
i32.reinterpret_f32
```

```sh
$ wasm_coq_interpreter nan.wasm main 100
i32.const 2143289344

```
Note: 2143289344 = 0x7fc00000 = nan (exponent = 255, mantissa = 4194304).
