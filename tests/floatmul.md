This test contains a floating point multiplication.

Note: 0x46fe500f = 32552.029; 208.333 * 156.25 = 32552.0312.

```wasm
(f32.mul
   (f32.const 0x1.a0aa7ep+7 (;=208.333;))
   (f32.const 0x1.388p+7 (;=156.25;)))
```

```sh
$ wasm_coq_interpreter floatmul.wasm main 100
f32.const 46fe500f

```
