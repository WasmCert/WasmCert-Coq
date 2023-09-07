This test contains an integer multiplication.

```wasm
(i32.mul
  (i32.const 7)
  (i32.const 3))
```

```sh
$ wasm_coq_interpreter mul.wasm main
i32.const 21

```
