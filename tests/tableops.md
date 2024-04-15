This test contains some composition of table and element-related operations.

```wasm
(module
  (type $type1 (func (result i32)))
  (table $t1 4 funcref)
  (func $f1 (result i32)
    i32.const 1)
  (func $f2 (result i32)
    i32.const 2)
  (func $f3 (result i32)
    i32.const 3)
  (elem $e1 $t1 (i32.const 1) $f1 $f2 $f3)
  (func (export "main") (result i32)
    i32.const 0
    i32.const 3
    table.get 0
    table.set 0
    i32.const 0
    call_indirect $t1 (type $type1)
  )
)
```

```sh
$ wasm_coq_interpreter tableops.wasm -r main
i32.const 3

```

