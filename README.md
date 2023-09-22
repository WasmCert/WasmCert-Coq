# wasm_coq
WebAssembly (aka Wasm) 1.0 formalisation in Coq, based on the [official formalisation](https://www.w3.org/TR/wasm-core-1/).
Our definitions and proofs draw from those given in the [Isabelle mechanisation of Conrad Watt](https://www.isa-afp.org/entries/WebAssembly.html).

(C) M. Bodin, P. Gardner, J. Pichon, C. Watt, X. Rao 2019-2023 - see LICENSE.txt

The quotes from the WebAssembly standard (starting with `std-doc`) are (C) their respective authors.

This work is in progress, comprising WasmCert-Coq, a Coq-Specification of the Wasm operational semantics, and WasmRef-Coq, a Coq-representation of the Wasm pseudo-code standard which yields an OCAML interpreter. While our initial work used the definitions published in PLDI'17, we have now adapted the mechanisation to Wasm 1.0., the specification as ratified by the W3C. 

# TODOs

- [x] Give core definitions of WasmCert-Coq and WasmRef-Coq.
- [x] Prove soundness results for WasmRef-Coq (interpreter) with respect to WasmCert-Coq.
- [x] Finish type soundness result.
- [ ] Validate WasmRef-Coq (conformance tests).
- [x] Verify executable type checker soundness.
- [x] Verify instantiation soundness properties.
- [x] Implement numerics using CompCert numerics.
- [x] Instantiate a Wasm program logic using Iris [iris branch](https://github.com/WasmCert-Coq/WasmCert-Coq/tree/iris-wasm-native).

This repository also contains some experimental work on a parser for the binary format which is currently unverified. 

# Usage

## Installation and Compilation

The project can be installed using dune/opam. 

Compiling the dependencies requires having at least 4-8 GB of RAM on your computer.
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install .
dune build
```

## Testing the Installation

The project comes with a small set of tests for the extracted interpreter:
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
