# wasm_coq
A WebAssembly (aka Wasm) formalisation in Coq, based on the [official specification](https://webassembly.github.io/spec/core/).

(C) M. Bodin, P. Gardner, J. Pichon, C. Watt, X. Rao 2019-2025 - see LICENSE.txt

The quotes from the WebAssembly standard (starting with `std-doc`) are (C) their respective authors.

The current master branch formalises Wasm version 2.0, plus additional subtyping systems from the future funcref/GC extension proposals. A large part of the old Wasm 1.0 formalisation has been published at [FM'21](https://link.springer.com/chapter/10.1007/978-3-030-90870-6_4), with many additions to the repository since then.

# Components of the Repository

## In Publication

- [x] Core definitions of WasmCert-Coq and WasmRef-Coq.
- [x] Soundness results for WasmRef-Coq (interpreter) with respect to WasmCert-Coq.
- [x] Type safety results for Wasm typing system.
- [x] Soundness and completeness results for the type checker with respect to the typing system.
- [x] Implementing Wasm numerics (via CompCert numerics).
- [x] Soundness results for module instantiation.
- [x] Proof carrying interpreter deriving progress.
- [x] Interpreter with optimised context representations.

## Merged
- [x] Updates for Wasm 2.0 (except SIMD and new numerics ops) + subtyping systems.

## Ongoing
- [ ] Validate WasmRef-Coq (conformance tests).

# Program Logic

This repository contains a mechanised Wasm program logic using the Iris framework: [iris branch](https://github.com/WasmCert/WasmCert-Coq/tree/iris-wasm-opam).

This is migrated from an older build for the [artefact](https://zenodo.org/records/7808708) submitted along with the Iris-Wasm publication at [PLDI'23](https://dl.acm.org/doi/10.1145/3591265).

A new version working with `opam` can be found [here](https://github.com/logsem/iriswasm).

# Binary Parser (experimental)
This repository contains some experimental work on a parser for the binary format which is currently unverified.
As the parser forms a part of the extracted interpreter, any error in the parser would result in the interpreter reporting `syntax error` for some valid Wasm binaries. Bug reports are appreciated!

# Usage

## Installation and Compilation

The project can be installed using opam.

Compiling the dependencies and codebase requires having at least 8 GB of RAM on your computer.
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add -y wasm git+https://github.com/WasmCert/spec#interpreter_only
opam install .
```

## Testing the Installation

The project comes with a small set of tests for the extracted interpreter:
```bash
dune test
```

## Using the project

A file `wasm_coq_interpreter` will have been generated under `_build/install`.
It takes as argument a list of Wasm files, followed by a function name to run (with the `-r` flag).
For instance, to interpret the function `main` defined in [tests/add.wasm](tests/add.wasm), run:
```bash
dune exec -- wasm_coq_interpreter tests/add.wasm -r main
```

The project has experimental support on passing arguments to function calls in the CLI via the `-a` flag. For example:
```bash
dune exec -- wasm_coq_interpreter tests/add2.wasm -r main -a "i32.const 6" -a "i32.const 36"
```
would produce
```bash
i32.const 42
```

The interpreter can also display intermediate states of the operational semantics:
```bash
dune exec -- wasm_coq_interpreter tests/add.wasm -r main --vi
```
would produce:
```bash
parsing OK                            
instantiation OK

Post-instantiation stage for table and memory initialisers...
step 1:
(empty)

step 2:
Value:
(empty)
success after 2 steps

Instantiation success
interpreting OK
step 0:

Executing configuration:
frame 0
with values (empty)
  invoke 0
end frame

step 1:
frame 0
with values (empty)
  frame 1
  with values (empty)
    label 1
    label_cont
      i32.const 40
      i32.const 2
      i32.add
    end label
  end frame
end frame

step 2:
frame 0
with values (empty)
  frame 1
  with values (empty)
    label 1
    label_cont
      i32.const 42
    end label
  end frame
end frame

step 3:
frame 0
with values (empty)
  frame 1
  with values (empty)
    i32.const 42
  end frame
end frame

step 4:
frame 0
with values (empty)
  i32.const 42
end frame

step 5:
Value:
i32.const 42

success after 5 steps
```
