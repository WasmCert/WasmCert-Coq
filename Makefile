.PHONY: all clean subst

all:
	dune build @all
	dune build -p wasm_interpreter

subst:
	dune subst

clean:
	rm -rf _build || true
	rm theories/*.vo || true
	rm theories/*.glob || true
	rm theories/*.aux || true

