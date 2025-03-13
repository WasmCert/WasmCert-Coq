(module
  (func (export "main") (result i32 i32 i32)
    i32.const 0
    i32.load
    i32.const 4
    i32.load
    i32.const 4
    i32.const 0
    i32.const 4
    memory.init $dat2
    i32.const 4
    i32.load
  )
  (memory $mem 2 3)
  (data $dat (memory $mem) (offset (i32.const 4)) "\03\03\03\03")
  (data $dat2 "\04\04\04\04")
)

