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

(* TODO: Instantiation and interpreter need an update after the rework on host. Maybe rollback to the non-monadic version for a relatively easier fix for now, or simply disable extraction temporarily. *)
Extraction "extract"
  run_parse_module
  (*Instantiation*)
  (*Interpreter *)
  value_rec_safe
  (*PP*).


