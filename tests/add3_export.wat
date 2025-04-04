(module
  (type $add3t (func (param i32 i32 i32) (result i32)))
  (import "add3_import" "add3" (func $add3 (type $add3t)))
  (export "add3_export" (func $add3)))

