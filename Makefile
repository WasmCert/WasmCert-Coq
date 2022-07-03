.PHONY: all clean clean-aux vscode

# Removes a lot of warnings from dune complaining that HOME is not defined.
HOME ?= ${TARGETDIR}
export HOME

INTERPRETER=_build/install/default/bin/wasm_interpreter

all:
	dune build @all --verbose
#	dune build -p wasm_interpreter
#	ln -f -s ${INTERPRETER} ./wasm_interpreter || echo "Compilation done. The wasm interpreter is located in: ${INTERPRETER}"

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
	rm wasm_interpreter || true

vscode: .vscode/settings.json

.vscode/settings.json:
	mkdir -p .vscode
	echo $(VSCODESETTINGS) > $@

