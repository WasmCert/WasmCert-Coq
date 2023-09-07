(** Extraction to OCaml. **)
(* (C) M. Bodin, J. Pichon - see LICENSE.txt *)

From Coq Require Extraction.

From Wasm Require Import
  datatypes_properties
  binary_format_parser
  instantiation_func
  interpreter_func
  type_checker
(*  instantiation_itree
  interpreter_itree *)
  pp.

From Coq Require Import
  extraction.ExtrOcamlBasic
  extraction.ExtrOcamlString.

Extraction Language OCaml.
(*Set Extraction Conservative Types.*)

Extraction "extract"
  run_parse_module
  Instantiation_func_extract
  Interpreter_func_extract
(*  Instantiation_itree_extract
  Interpreter_itree_extract*)
  value_rec_safe
  PP
  DummyHost.

