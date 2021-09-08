This test contains three simple examples of the usage of `br`.

One is located in a loop, and exits it (`br 0` would infinitively loop):
```wasm
loop
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
$ ../wasm_interpreter --vr loop.wasm loop_br 1

$ ../wasm_interpreter --vr loop.wasm block_br 1

$ ../wasm_interpreter --vr loop.wasm br 1

```
