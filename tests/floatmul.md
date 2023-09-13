This test contains a floating point multiplication.

Note: 0x46fe500f = 32552.029; 208.333 * 156.25 = 32552.0312.

```wasm
block
	br 0
```

```sh
$ wasm_coq_interpreter floatmul.wasm main 100
f32.const 46fe500f

```
