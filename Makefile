.PHONY: all clean clean-aux

all: .vscode/settings.json
	export HOME=`pwd`; dune build @all --verbose
	dune build -p wasm_interpreter
	ln -f -s ./_build/install/default/bin/wasm_interpreter ./wasm_interpreter

clean-aux:
	rm theories/*.aux || true
	rm theories/.*.aux || true
	chmod +w _build/default/theories/.*.aux || true
	rm _build/default/theories/*.aux || true
	rm _build/default/theories/.*.aux || true

clean: clean-aux
	rm -rf _build || true
	rm theories/*.vo || true
	rm theories/*.glob || true
	rm theories/extract.{ml,mli} || true

.vscode/settings.json:
	mkdir -p .vscode
	echo $(VSCODESETTINGS) > $@

