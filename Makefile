default:
	opam install .

run_wast_local:
	for wastfile in ./tests/wast/*.wast; do \
		echo "Running: $$wastfile"; \
		dune exec -- wasm_coq_interpreter --wast "$$wastfile"; \
	done