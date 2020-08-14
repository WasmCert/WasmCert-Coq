(** Extraction to OCaml. **)
(* (C) M. Bodin, J. Pichon - see LICENSE.txt *)

From Coq Require Extraction.

From Wasm Require Import
  datatypes_properties
  binary_format_parser
  instantiation
  type_checker
  interpreter
  pp.

From Coq Require Import
  extraction.ExtrOcamlBasic
  extraction.ExtrOcamlString.

Extraction Language OCaml.
(*Set Extraction Conservative Types.*)

Extraction "extract"
  run_parse_module
  Instantiation
  cl_type_check_single
  Interpreter
  value_rec_safe
  pp.pp_config_tuple_except_store
  pp.pp_res_tuple_except_store
  pp.pp_values
  pp.pp_store
  operations.those_const_list
  DummyHost.

