(module
  (type $addt (func (param i32 i32) (result i32)))
  (import "add2" "main" (func $add2 (type $addt)))
  (func (export "add3") (param i32 i32 i32) (result i32)
    local.get 0
    local.get 1
    call $add2
    local.get 2
    call $add2
  )
)

