default:
	opam install .

SHELL := bash

SCRIPT := ./run_wast.sh

FOLDER ?=
FILTER ?=

.PHONY: run_wast
run_wast:
	$(SCRIPT) "$(FOLDER)" "$(FILTER)"
