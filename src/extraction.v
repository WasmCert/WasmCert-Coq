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

Extract Constant memory_vec.array "'a" => "Parray.t".
Extraction Inline memory_vec.array.

Extract Constant memory_vec.arr_make => "Parray.make".
Extract Constant memory_vec.arr_make_copy => "Parray.make_copy".
Extract Constant memory_vec.arr_get => "Parray.get".
Extract Constant memory_vec.arr_default => "Parray.default".
Extract Constant memory_vec.arr_set => "Parray.set".
Extract Constant memory_vec.arr_length => "Parray.length".
Extract Constant memory_vec.arr_copy => "Parray.copy".


Extraction "extract"
  EfficientExtraction
  run_parse_module
  run_parse_arg
  Extraction_instance
  .
