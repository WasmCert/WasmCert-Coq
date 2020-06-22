(** Extraction to OCaml. **)
(* (C) M. Bodin - see LICENSE.txt *)

From Wasm Require binary_format_parser instantiation type_checker interpreter.

Extraction Language OCaml.

Extraction "extract"
  binary_format_parser.run_parse_module_from_asciis
  instantiation.interp_instantiate_wrapper
  type_checker.cl_type_check
  interpreter.run_v.
