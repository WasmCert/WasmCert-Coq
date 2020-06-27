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
  pp.pp_config_tuple_except_store
  pp.pp_res_tuple_except_store
  pp.pp_values
  pp.pp_store
  operations.const_list.
