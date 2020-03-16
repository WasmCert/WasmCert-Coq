# wasm_coq
WebAssembly (aka Wasm) formalisation in Coq, following the AFP formalisation of Conrad Watt.

(C) J. Pichon, M. Bodin, R. Xiaojia, C. Watt 2019-2020 - see LICENSE.txt

Usage: `esy` to download and install the dependencies and compile everything.
Warning: compiling the dependencies requires having about 3 or 4 GB of RAM on your computer.
Type `esy shell` to open a shell with the right compilation environment.

The following programs are assumed to be installed: `git`, `curl`, `m4`, and `autoconf`.
These programs are used to fetch and compile dependencies.

Installing `esy` itself can be done through `npm`.
It should then look like something like that:
```bash
sudo apt install npm git curl m4 autoconf
sudo npm install --global esy@latest # Tested with version 0.6.0-8b3dfe of esy.
```
Note that despite using `npm` to be installed, `esy` is not JavaScript-based.
If you prefer to avoid `npm` altogether, there are other ways to install `esy`: see <https://esy.sh/> for more information.

Once `esy` has been run, you can start editing the files.
Type `esy emacs theories/wasm.v` to open Emacs with the right environment (assuming that Emacs is installed with Proof General in your system).
Note that `emacs theories/wasm.v` (without the `esy` prefix) will open Emacs without setting the local dependencies: doing so will likely prevent `coq` from finding the needed dependencies.

To use CoqIDE in this developpment, you first need to install its system dependencies (these are probably already installed on your system if you are using CoqIDE):
```bash
sudo apt install libcairo2-dev libexpat1-dev libgtk-3-dev libgtksourceview-3.0-dev
```
Then, add the line `"@opam/coqide": "*"` in `devDependencies` in [package.json](./package.json), and run `esy` again.
Typing `esy coqide theories/wasm.v` should now work.

To use VSCoq in this development, you will need to adapt the [.vscode/settings.json](.vscode/settings.json) file.

