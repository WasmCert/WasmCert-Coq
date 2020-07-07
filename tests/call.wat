(module
  (func $hello (result i32)
    i32.const 42
  )
  (func (export "hello") (result i32)
    call $hello)
)