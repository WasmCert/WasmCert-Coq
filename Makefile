.PHONY: all clean

all: .vscode/settings.json
	export HOME=`pwd`; dune build @all --verbose
	dune build -p wasm_interpreter
	ln -f -s ./_build/install/default/bin/wasm_interpreter ./wasm_interpreter

clean:
	rm -rf _build || true
	rm theories/*.vo || true
	rm theories/*.glob || true
	rm theories/*.aux || true
	rm theories/extract.{ml,mli} || true

.vscode/settings.json:
	mkdir -p .vscode
	echo $(VSCODESETTINGS) > $@

