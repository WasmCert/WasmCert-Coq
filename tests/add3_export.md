This test features exporting an imported function.
```wasm
(module
  (type $add3t (func (param i32 i32 i32) (result i32)))
  (import "add3_import" "add3" (func $add3 (type $add3t)))
  (export "add3_export" (func $add3))
)

```

```sh
$ wasm_coq_interpreter add2.wasm add3_import.wasm add3_export.wasm -m add3_export -r add3_export -a "i32.const 12_3" -a "i32.const -8_3" -a "i32.const +2"
i32.const 42

```
