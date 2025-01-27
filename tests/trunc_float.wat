(module
  (func (export "main") (result i32 i32 i32)
    f32.const 42.69
    i32.trunc_f32_s
    f32.const -42.69
    i32.trunc_f32_s
    f64.const -42.69
    i32.trunc_f64_s
))