(module
  (func (export "nan") (result i32)
    f32.const nan
    i32.reinterpret_f32
  )
)
