This test features the parsing and printing of a large i32 numeric value::
```wasm
i32.const 2000000000
```

```sh
$ wasm_coq_interpreter big_const.wasm -r main
i32.const 2000000000

```
