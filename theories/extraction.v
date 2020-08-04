(** Extraction to OCaml. **)
(* (C) M. Bodin, J. Pichon - see LICENSE.txt *)

From Wasm Require Import
  datatypes_properties
  binary_format_parser
  instantiation
  type_checker
  interpreter
  pp.

Require Import
  Coq.extraction.ExtrOcamlBasic
  Coq.extraction.ExtrOcamlString.

Extraction Language OCaml.

Extraction "extract"
  run_parse_module
  interp_instantiate_wrapper
  lookup_exported_function
  cl_type_check_single
  run_step_extraction
  run_v_extraction
  value_rec_safe
  pp.pp_config_tuple_except_store
  pp.pp_res_tuple_except_store
  pp.pp_values
  pp.pp_store
  operations.those_const_list.

