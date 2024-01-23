# wasm_coq
WebAssembly (aka Wasm) 1.0 formalisation in Coq, based on the [official formalisation](https://www.w3.org/TR/wasm-core-1/).
Our definitions and proofs initially drew from those given in the [Isabelle mechanisation of Conrad Watt](https://www.isa-afp.org/entries/WebAssembly.html).

(C) M. Bodin, P. Gardner, J. Pichon, C. Watt, X. Rao 2019-2023 - see LICENSE.txt

The quotes from the WebAssembly standard (starting with `std-doc`) are (C) their respective authors.

This work is in progress. While our initial work used the definitions published in PLDI'17, we have now adapted the mechanisation to Wasm 1.0., the specification as ratified by the W3C. A large part of the work has been published at [FM'21](https://link.springer.com/chapter/10.1007/978-3-030-90870-6_4), with more additions to the repository since then.

# Components of the Repository

## In Publication

- [x] Core definitions of WasmCert-Coq and WasmRef-Coq.
- [x] Soundness results for WasmRef-Coq (interpreter) with respect to WasmCert-Coq.
- [x] Type safety results for Wasm typing system.
- [x] Soundness and completeness results for the type checker with respect to the typing system.
- [x] Implementing Wasm numerics (via CompCert numerics).

## Merged
- [x] Soundness results for module instantiation.
- [x] Proof carrying interpreter deriving progress.
- [x] Interpreter with optimised context representations.

## Unmerged/Future Work
- [ ] Validate WasmRef-Coq (conformance tests).
- [ ] Updates for Wasm 2.0 (except SIMD).
- [ ] Updates for further extension proposals (SIMD, GC, tail calls, etc).

# Program Logic

This repository contains a mechanised Wasm program logic using the Iris framework: [iris branch](https://github.com/WasmCert/WasmCert-Coq/tree/iris-wasm-opam). 
This is migrated from an older build for the [artefact](https://zenodo.org/records/7808708) submitted along with the Iris-Wasm publication at [PLDI'23](https://dl.acm.org/doi/10.1145/3591265).

# Binary Parser (experimental)
This repository contains some experimental work on a parser for the binary format which is currently unverified.

# Usage

## Installation and Compilation

The project can be installed using opam.

Compiling the dependencies requires having at least 4-8 GB of RAM on your computer.
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install .
```

## Build Based on Esy

The previous esy-based build is now deprecated; it is moved to esy branch.

## Testing the Installation

The project comes with a small set of tests for the extracted interpreter:
```bash
dune test
```

## Using the project

A file `wasm_coq_interpreter` will have been generated under `_build/install`.
It takes as argument a list of Wasm files, followed by a function name to run (with the `-r` flag).
For instance, to interpret the function `main` defined in [tests/floatmul.wasm](tests/floatmul.wasm), run:
```bash
dune exec -- wasm_coq_interpreter tests/floatmul.wasm -r main
```
The interpreter can display intermediate states of the operational semantics:
```bash
dune exec -- wasm_coq_interpreter tests/floatmul.wasm -r main --vi
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
