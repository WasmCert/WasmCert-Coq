(** Extraction to OCaml. **)

From Coq Require Extraction.
From Coq Require PArray.
From Coq Require Import
  extraction.ExtrOcamlBasic
  extraction.ExtrOcamlString
  extraction.ExtrOcamlZBigInt
  ExtrOCamlInt63
.

From Wasm Require Import
  efficient_extraction
  datatypes_properties
  binary_format_parser
  text_format_parser
  instantiation_func
  interpreter_ctx
  type_checker
  pp
  host
  simd_execute
  extraction_instance
.

Require Import compcert.lib.Integers.

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

Extract Constant SIMD_ops.app_vunop_str => "SIMD_ops.app_vunop_str".
Extract Constant SIMD_ops.app_vbinop_str => "SIMD_ops.app_vbinop_str".
Extract Constant SIMD_ops.app_vternop_str => "SIMD_ops.app_vternop_str".

Extraction "extract"
  EfficientExtraction
  run_parse_module
  run_parse_arg
  Extraction_instance
  .
