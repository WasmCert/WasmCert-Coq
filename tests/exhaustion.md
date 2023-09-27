This test contains an infinite loop which is terminated at fuel exhaustion.

```wasm
(loop
	br 0
)

```

```sh
$ wasm_coq_interpreter exhaustion.wasm main 100
fuel exhaustion

```

