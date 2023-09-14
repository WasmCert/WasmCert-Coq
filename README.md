# wasm_coq
WebAssembly (aka Wasm) formalisation in Coq, based on the [official formalisation](https://www.w3.org/TR/wasm-core-1/).
Our definitions and proofs draw from those given in the [Isabelle mechanisation of Conrad Watt](https://www.isa-afp.org/entries/WebAssembly.html).

(C) M. Bodin, P. Gardner, J. Pichon, C. Watt, R. Xiaojia 2019-2020 - see LICENSE.txt

The quotes from the WebAssembly standard (starting with `std-doc`) are (C) their respective authors.

This work is in progress, comprising WasmCert, a Coq-Specification of the Wasm operational semantics, and WasmRef, a Coq-representation of the Wasm pseudo-code standard which yields an OCAML interpreter. While our initial work used the definitions published in PLDI'17, we have now adapted the mechanisation to Wasm 1.0., the specification as ratified by the W3C. 

# TODOs

- [x] Give core definitions of WasmCert and WasmRef.
- [x] Prove soundness result for WasmRef with respect to WasmCert.
- [x] Update the definition of WebAssembly's global store to match the 1.0 standard.
- [x] Update the function frame and related definitions to match the 1.0 standard.
- [x] Finish type soundness result.
- [ ] Validate WasmRef (conformance tests).
- [x] Verify executable type checker correctness.
- [x] Verify instantiation correctness properties.
- [ ] Link WasmCert to CompCert.
- [x] Provide Iris Wasm [iris branch](https://github.com/WasmCert/WasmCert-Coq/tree/iris-wasm-native).

This repository contains some experimental work on a binary parser and Iris integration. 

# Usage

## Installation and Compilation

The project can be installed using opam-build.

Compiling the dependencies requires having at least 4-8 GB of RAM on your computer.
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install .
```

## Testing the Installation

The project comes with a small set of tests for its extracted interpreter:
```bash
dune test
```

## Using the project

A file `wasm_coq_interpreter` will have been generated.
It takes as argument a list of Wasm files, followed by a function name, followed by the number of steps of execution (fuel).
For instance, to interpret the function `main` defined in [tests/floatmul.wasm](tests/floatmul.wasm), run:
```bash
dune exec -- wasm_coq_interpreter tests/floatmul.wasm main 10
```
The interpreter can display intermediate states of the operational semantics:
```bash
dune exec -- wasm_coq_interpreter tests/floatmul.wasm main 10 --vi
```
would produce:
```bash
parsing OK
instantiation OK
interpreting OK
step 0:

invoke 0
with values (empty)

step 1:
normal
  local 1
  with values (empty)
    block f32
        f32.const 4350553f
        f32.const 431c4000
        f32.mul
    end
  end local
with values (empty)
and store unchanged
step 2:
normal
  local 1
  with values (empty)
    label 1
    label_cont
      f32.const 4350553f
      f32.const 431c4000
      f32.mul
    end label
  end local
with values (empty)
and store unchanged
step 3:
normal
  local 1
  with values (empty)
    label 1
    label_cont
      f32.const 46fe500f
    end label
  end local
with values (empty)
and store unchanged
step 4:
normal
  local 1
  with values (empty)
    f32.const 46fe500f
  end local
with values (empty)
and store unchanged
step 5:
normal
  f32.const 46fe500f
with values (empty)
and store unchanged
```
