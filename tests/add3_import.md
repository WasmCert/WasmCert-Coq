This test features the import of a function from another module (`add2`).
```wasm
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

```

```sh
$ wasm_coq_interpreter add2.wasm add3_import.wasm -m add3_import -r add3 -a "i32.const 12_3" -a "i32.const -8_0" -a "i32.const -1"
i32.const 42

```
