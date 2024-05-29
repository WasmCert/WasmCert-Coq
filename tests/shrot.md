This test contains a few numeric shifts/rotations.

```wasm
(module
  (func (export "main") (result i64 i64 i64 i64 i64)
    i64.const 1
    i64.const 65
    i64.shl
    i64.const 1
    i64.const 64
    i64.shr_u
    i64.const -1
    i64.const 67
    i64.shr_s
    i64.const 1
    i64.const 65
    i64.rotl
    i64.const 1
    i64.const 65
    i64.rotr
))


```

```sh
$ wasm_coq_interpreter shrot.wasm -r main
i64.const 2
i64.const 1
i64.const -1
i64.const 2
i64.const -9223372036854775808

```

