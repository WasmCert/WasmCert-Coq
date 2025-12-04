(** Extraction to OCaml. **)

From Coq Require Extraction.
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
Require Import ZArith NArith.

From Coq Require PArray.
From Coq Require Import
  extraction.ExtrOcamlBasic
  extraction.ExtrOcamlNativeString
  extraction.ExtrOcamlNatInt
  extraction.ExtrOcamlZInt
.

Extraction Language OCaml.

Extract Inductive positive => "Coq_types.ocaml_int"
[ "(fun p->1+2*p)" "(fun p->2*p)" "1" ]
"(fun f2p1 f2p f1 p -> if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))".

Extract Inductive Z => "Coq_types.ocaml_int"
[ "0" "" "(~-)" ]
"(fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))".

Extract Inductive N => "Coq_types.ocaml_int"
[ "0" "" ]
"(fun f0 fp n -> if n=0 then f0 () else fp n)".

Extract Constant lookup_N => "EfficientExtraction.lookup_N_safe".

Extract Constant memory_vec.array "'a" => "Parray.t".
Extraction Inline memory_vec.array.

Extract Constant memory_vec.arr_make => "Parray.make".
Extract Constant memory_vec.arr_make_copy => "Parray.make_copy".
Extract Constant memory_vec.arr_get => "Parray.get".
Extract Constant memory_vec.arr_default => "Parray.default".
Extract Constant memory_vec.arr_set => "Parray.set".
Extract Constant memory_vec.arr_set_gen => "Parray.set_gen".
Extract Constant memory_vec.arr_length => "Parray.length".
Extract Constant memory_vec.arr_copy => "Parray.copy".

Extract Constant SIMD_ops.app_vunop_str => "SIMD_ops.app_vunop_str".
Extract Constant SIMD_ops.app_vbinop_str => "SIMD_ops.app_vbinop_str".
Extract Constant SIMD_ops.app_vternop_str => "SIMD_ops.app_vternop_str".
Extract Constant SIMD_ops.app_vtestop_str => "SIMD_ops.app_vtestop_str".
Extract Constant SIMD_ops.app_vshiftop_str => "SIMD_ops.app_vshiftop_str".

Extraction "extract"
  EfficientExtraction
  run_parse_module_str
  run_parse_arg
  Extraction_instance
  .
