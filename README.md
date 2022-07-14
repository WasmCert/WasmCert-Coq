# Usage

## Installation and Compilation

The project comes with an `esy` packaging.

The following programs are assumed to be installed: `git`, `curl`, `m4`, `autoconf`, and `automake`.
These programs are used to fetch and compile dependencies.

Installing `esy` itself can be done through `npm`.
It should then look like something like that:
```bash
sudo apt install npm git curl m4 autoconf
sudo npm install --global esy@latest # Tested with version 0.6.12 of esy.
```
Note that despite using `npm` to be installed, `esy` is not JavaScript-based.
If you prefer to avoid `npm` altogether, there are other ways to install `esy`: see <https://esy.sh/> for more information.

Once `esy` is installed, simply type `esy` to download and install the dependencies and compile everything.
Warning: compiling the dependencies requires having about 3 or 4 GB of RAM on your computer.
```bash
esy
```

Compiling the dependencies may require at least 16GB of RAM.

## Troubleshooting

- On MacOS Monterey, it is required to use at least esy >=0.6.12 as there is a sandboxing bug for versions below that.

- Due to compatibility issues of several dependencies, the codebase currently fails to build on any OS using glibc >= 2.34.

## Editing the Project

Type `esy shell` to open a shell with the right compilation environment.
You can also type `esy emacs theories/wasm.v` to open Emacs with the right environment (assuming that Emacs is installed with Proof General in your system).
Note that `emacs theories/wasm.v` (without the `esy` prefix) will open Emacs without setting the local dependencies: doing so will likely prevent `coq` from finding the needed dependencies.

To use CoqIDE in this developpment, you first need to install its system dependencies (these are probably already installed on your system if you are using CoqIDE):
```bash
sudo apt install libcairo2-dev libexpat1-dev libgtk-3-dev libgtksourceview-3.0-dev
```
Then, replace the line `devDependencies: {},` by `devDependencies: {"@opam/coqide": "*"}` in [package.json](./package.json), and run `esy` again.
Typing `esy coqide theories/wasm.v` should now work.

To use VSCode in this development, a [.vscode/settings.json](.vscode/settings.json) needs to be generated first: this file enables VSCode to know where the dependencies are stored in your system.
It can be generated with `esy vscode`.

The [tests](./tests) folder contains Markdown files checked by `mdx` during the continuous intergration.

## Using the project

A file `wasm_interpreter` will have been generated.
It takes as argument a list of Wasm files, followed by a function name, followed by a depth.
For instance, to interpret the function `hello` defined in [tests/const.wasm](tests/const.wasm), run:
```bash
./wasm_interpreter tests/const.wasm hello 10
```
The interpreter can display intermediate states of the operational semantics:
```bash
./wasm_interpreter tests/const.wasm hello 10 --vi
```
for example
```
step 1:
normal
  local 1
  with values (empty)
    block i32
        i32.const 42
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
      i32.const 42
    end label
  end local
with values (empty)
and store unchanged
```
