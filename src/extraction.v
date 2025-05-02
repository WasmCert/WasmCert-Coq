(** Extraction to OCaml. **)

From Coq Require Extraction.
From Coq Require PArray.

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
  extraction_instance
.

From Coq Require Import
  extraction.ExtrOcamlBasic
  extraction.ExtrOcamlString
  ExtrOCamlInt63
.

Extraction Language OCaml.

Extract Constant lookup_N => "EfficientExtraction.lookup_N_safe".

Extract Constant PArray.array "'a" => "Parray.t".
Extraction Inline PArray.array.

Extract Constant PArray.make => "Parray.make".
Extract Constant PArray.get => "Parray.get".
Extract Constant PArray.default => "Parray.default".
Extract Constant PArray.set => "Parray.set".
Extract Constant PArray.length => "Parray.length".
Extract Constant PArray.copy => "Parray.copy".


Extraction "extract"
  EfficientExtraction
  run_parse_module
  run_parse_arg
  Extraction_instance
  .
