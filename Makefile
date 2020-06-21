.PHONY: all clean travis-hook

all: .vscode/settings.json
	export HOME=`pwd`; dune build @all
	dune build -p wasm_interpreter

clean:
	rm -rf _build || true
	rm theories/*.vo || true
	rm theories/*.glob || true
	rm theories/*.aux || true
	rm theories/extract.{ml,mli} || true

.vscode/settings.json:
	mkdir -p vscode
	echo $(VSCODESETTINGS) > $@

# Some dependencies take quite a while to compile, and Travis consider them as failing because of this.
# This hooks solves this issue by regularly printing on the terminal.
travis-hook:
	( while true; do echo 'Compilation takes a while: keeping Travis alive.'; sleep 60; done ) & esy

