(** Extraction to OCaml. **)

From Coq Require Extraction.
From Wasm Require Import
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

Require Import ZArith PArith.

From Coq Require PArray.
From Coq Require Import
  extraction.ExtrOcamlBasic
  extraction.ExtrOcamlNativeString
  extraction.ExtrOcamlZBigInt
  extraction.ExtrOcamlNatBigInt
.

Extraction Language OCaml.

(* Coq's default extraction of integers to Z.t has some problems, including using inefficient Z.quomod and missing some overrides for some reason. *)
Extract Inductive nat => "Big_int_Z.big_int"
 [ "Big_int_Z.zero_big_int" "Big_int_Z.succ_big_int" ]
 "(fun fO fS n -> if Big_int_Z.le_big_int n Big_int_Z.zero_big_int then fO () else fS (Big_int_Z.pred_big_int n))".

Extract Inductive positive => "Big_int_Z.big_int"
 [ "(fun x -> Big_int_Z.succ_big_int (Big_int_Z.shift_left_big_int x 1))"
   "(fun x -> Big_int_Z.shift_left_big_int x 1)" "Big_int_Z.unit_big_int" ]
 "(fun f2p1 f2p f1 p -> if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else if Big_int_Z.eq_big_int (Big_int_Z.and_big_int p Big_int_Z.unit_big_int) Big_int_Z.unit_big_int then f2p1 (Big_int_Z.shift_right_big_int p 1) else f2p (Big_int_Z.shift_right_big_int p 1))".

Extract Constant PosDef.Pos.add => "Big_int_Z.add_big_int".
Extract Constant PosDef.Pos.succ => "Big_int_Z.succ_big_int".
Extract Constant PosDef.Pos.of_succ_nat => "Big_int_Z.succ_big_int".
Extract Constant PosDef.Pos.sub =>
 "(fun n m -> Big_int_Z.max_big_int Big_int_Z.unit_big_int (Big_int_Z.sub_big_int n m))".
Extract Constant PosDef.Pos.mul => "Big_int_Z.mult_big_int".
Extract Constant PosDef.Pos.compare =>
 "(fun x y -> let s = Big_int_Z.compare_big_int x y in if s = 0 then Eq else if s < 0 then Lt else Gt)".
Extract Constant PosDef.Pos.compare_cont =>
          "(fun c x y -> let s = Big_int_Z.compare_big_int x y in if s = 0 then c else if s < 0 then Lt else Gt)".
Extract Constant PosDef.Pos.land => "Big_int_Z.and_big_int".
Extract Constant PosDef.Pos.lor => "Big_int_Z.or_big_int".
Extract Constant PosDef.Pos.eqb => "Big_int_Z.eq_big_int".

(* Zbits.P_mod_two_p is a renormalisation function used a lot by CompCert. Unfortunately, its extraction behaviour is pretty slow due to WordSize being represented in nat. This provides a slightly better version of getting the lowest p bits without going too far -- further optimisations are possible by creating a hashtable lookup of 2^p. *)
Extract Constant Zbits.P_mod_two_p => "(fun x n -> Big_int_Z.and_big_int x (Big_int_Z.sub_big_int (Big_int_Z.shift_left_big_int Big_int_Z.unit_big_int (Big_int_Z.int_of_big_int n)) Big_int_Z.unit_big_int))".

(* The list lookup function is extracted to using OCaml's native list lookup function instead of converting the index to natural (as that explodes when the lookup index is too big). *)
Extract Constant lookup_N => "(fun l n -> List.nth_opt l (Big_int_Z.int_of_big_int n))".

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
  Utility
  Extraction_instance
  .
