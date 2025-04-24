(** Extraction to OCaml. **)

From Coq Require Extraction.

From Wasm Require Import
  efficient
  datatypes_properties
  binary_format_parser
  text_format_parser
  instantiation_func
  interpreter_ctx
  type_checker
  pp
  host
  wast
.

From Coq Require Import
  extraction.ExtrOcamlBasic
  extraction.ExtrOcamlString.

Extraction Language OCaml.

Extract Constant lookup_N => "EfficientExtraction.lookup_N_safe".

Extraction "extract"
  EfficientExtraction
  run_parse_module
  run_parse_arg
  Instantiation_func_extract
  Interpreter_ctx_extract
  Wast_interface
  PP
  DummyHost
  empty_frame
  .
