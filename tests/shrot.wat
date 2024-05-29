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
