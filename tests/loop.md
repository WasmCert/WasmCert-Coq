This test contains three simple examples of the usage of `br`.

One is located in a loop, and exits it (`br 0` would infinitively loop):
```wasm
main
	br 1
```
The second one is located in a block, and also exits it:
```wasm
block
	br 0
```
Finally, the third one is located at the top-level:
```wasm
br 0
```

```sh
$ wasm_coq_interpreter loop.wasm -r main

$ wasm_coq_interpreter loop.wasm -r block_br

$ wasm_coq_interpreter loop.wasm -r br

```
