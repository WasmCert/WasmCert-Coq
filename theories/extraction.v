(** Extraction to OCaml. **)
(* (C) M. Bodin, J. Pichon - see LICENSE.txt *)

From Wasm Require Import
  datatypes_properties
  binary_format_parser
  instantiation
  type_checker
  interpreter
  pp.

Extraction Language OCaml.

Extraction "extract"
  run_parse_module_from_asciis
  interp_instantiate_wrapper
  lookup_exported_function
  cl_type_check
  run_step
  value_rec_safe
  Ascii.byte_of_ascii
  pp_config_tuple
  pp_res_tuple
  pp_values
  ansi.ansi_bold
  ansi.ansi_reset
  ansi.ansi_green
  ansi.ansi_red.

