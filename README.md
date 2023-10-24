# coq_iris_wasm
This branch contains the work on the Iris-Wasm Program Logic, which is the artifact for the paper
*Iris-Wasm: Robust and Modular Verification of WebAssembly Programs* on PLDI'23.

This version is slightly adapted from the submitted artefact, providing an `opam` build instead of the submitted `esy` build. 
The old `esy` build can still be found on the branch `iris-wasm-native`, or on Zenodo at https://zenodo.org/records/7808708.

# Installation and Compilation

The project can be installed using opam.

Compiling the dependencies and codebase requires having at least 8 GB of RAM on your computer and may take around 30 minutes.
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install .
```

# Usage
For detailed usage, check the Readme file attached on the artifact submission at https://zenodo.org/records/7808708.