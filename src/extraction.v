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
  extraction.ExtrOcamlZBigInt
.

Extraction Language OCaml.

Extract Inductive positive => "Big_int_Z.big_int"
 [ "(fun x -> Big_int_Z.succ_big_int (Big_int_Z.shift_left_big_int x 1))"
   "(fun x -> Big_int_Z.shift_left_big_int x 1)" "Big_int_Z.unit_big_int" ]
 "(fun f2p1 f2p f1 p -> if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else if Big_int_Z.eq_big_int (Big_int_Z.and_big_int p Big_int_Z.unit_big_int) Big_int_Z.unit_big_int then f2p1 (Big_int_Z.shift_right_big_int p 1) else f2p (Big_int_Z.shift_right_big_int p 1))".

(* A bit ugly, but otherwise requires an entire copy of the lookup lemmas for Coq's list types *)
Extract Constant lookup_N => "EfficientExtraction.lookup_N_safe".

(* This could be done better using module types *)
Extract Constant memory_vec.array "'a" => "Parray_shim.t".
Extraction Inline memory_vec.array.

(* Requires some custom rerouting *)

Extract Constant memory_vec.arr_make => "Parray_shim.make".
Extract Constant memory_vec.arr_make_copy => "Parray_shim.make_copy".
Extract Constant memory_vec.arr_get => "Parray_shim.get".
Extract Constant memory_vec.arr_default => "Parray_shim.default".
Extract Constant memory_vec.arr_set => "Parray_shim.set".
Extract Constant memory_vec.arr_set_gen => "Parray_shim.set_gen".
Extract Constant memory_vec.arr_length => "Parray_shim.length".
Extract Constant memory_vec.arr_copy => "Parray_shim.copy".

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
  Monadic_host
  Utility
  .
