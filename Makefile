default:
	opam pin add -y wasm git+https://github.com/WasmCert/spec#interpreter_only
	opam install .

run_wast:
	@FOLDER=$$(if [ "$(filter-out run_wast,$(MAKECMDGOALS))" ]; then echo "$(word 2, $(MAKECMDGOALS))"; else echo "./wast"; fi);\
	chmod +x run_wast.sh; \
	./run_wast.sh "$$FOLDER"