(** Extraction to OCaml. **)
(* (C) M. Bodin - see LICENSE.txt *)

From Wasm Require binary_format_parser instantiation type_checker interpreter pp.

Extraction Language OCaml.

Extraction "extract"
  binary_format_parser.run_parse_module_from_asciis
  instantiation.interp_instantiate_wrapper
  instantiation.lookup_exported_function
  type_checker.cl_type_check
  interpreter.run_step
  Ascii.byte_of_ascii
  pp.pp_config_tuple
  pp.pp_res_tuple
  pp.pp_values
  ansi.ansi_bold
  ansi.ansi_reset
  ansi.ansi_green
  ansi.ansi_red.
