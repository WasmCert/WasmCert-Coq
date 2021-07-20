This test features dropping a value from the stack:
```wasm
i32.const 42
i32.const 123
drop
```

```sh
$ wasm_interpreter --vr drop.wasm hello 1
i32.const 42
```
