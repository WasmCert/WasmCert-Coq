This test contains a mixture of instructions testing the initialisation of tables using elem segments, as well as the start function invocation.

```wasm
(module
  (type $ft0 (func (param i32 i32) (result i32)))
  (type $ft1 (func (param i32 i32 i32) (result i32)))
  (func $addTwo (export "addTwo") (type $ft0)
    local.get 0
    local.get 1
    i32.add)
  (func $addThree (export "addThree") (type $ft1)
    local.get 0
    local.get 1
    local.get 2
    i32.add
    i32.add)
  (func $swap (export "swap")
    i32.const 2
    i32.const 1
    table.get 0
    table.set 0
    
    i32.const 1
    i32.const 0
    table.get 0
    table.set 0
    
    i32.const 0
    i32.const 2
    table.get 0
    table.set 0
  )
  (func $main (export "main")(result i32)
    i32.const 2
    i32.const 3
    i32.const 0
    call_indirect 0 (type $ft0)
  )
  (table $table0 (export "table0") 3 funcref)
  (elem $elem0 (table $table0) 
    			(offset (i32.const 0))
    			funcref (item (ref.func $addThree))
  )
  (elem $elem1 (table $table0) 
    			(offset (i32.const 1))
    			funcref (item (ref.func $addTwo))
  )
  (start $swap)
)


```

```sh
$ wasm_coq_interpreter table_elem_start.wasm -r main
i32.const 5

```

