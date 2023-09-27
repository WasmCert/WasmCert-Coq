(module
  (memory 1)
  (func (export "main") (result i32)
    i32.const 37
    i32.const 42
    i32.store
    i32.const 37
    i32.load
  )
)
