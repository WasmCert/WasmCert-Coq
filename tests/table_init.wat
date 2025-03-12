(module
  (func $f (param i32 i32 i32)
    local.get 0
    local.get 1
    local.get 2
    table.init 0 1
  )
  (func (export "main")
    i32.const 0
    i32.const 0
    i32.const 0
    call $f
  )
  (table 2 funcref)
  (elem 1)
  (elem 5)
)

