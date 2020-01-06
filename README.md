# wasm_coq
Wasm formalisation in Coq, following the AFP formalisation of Conrad Watt.

(C) J. Pichon 2019 - see LICENSE.txt

Usage: `esy` to install the dependencies and compile everything.
Type `esy shell` to open a shell with the right compilation environment.
Type `esy emacs theories/wasm.v` to open Emacs with the right environment (assuming that Emacs is installed with Proof general in your system).

The following programs are assumed to be installed: `git`, `curl`, and `m4`.

Installing `esy` itself should look like something like that:
```bash
sudo apt install npm git curl m4
npm install --global @esy-nightly/esy # Tested with version 0.6.0-8b3dfe of esy.
```

