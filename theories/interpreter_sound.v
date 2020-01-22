(* soundness of the Wasm interpreter *)
(* (C) J. Pichon - see LICENSE.txt *)

From mathcomp
Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import wasm opsem interpreter.

Section Host.

(* TODO: The host should be defined as a mixin. *)
Variable mem_grow_impl : mem -> nat -> option mem.
Hypothesis mem_grow_impl_correct :
  forall m n m',
    mem_grow_impl m n = Some m' ->
    mem_grow m n = m'.

Variable host_apply_impl : store_record -> function_type -> wasm.host -> list value -> option (store_record * list value).
Hypothesis host_apply_impl_correct :
  forall s tf h vs m',
    host_apply_impl s tf h vs = Some m' ->
    exists hs, wasm.host_apply s tf h vs hs = Some m'.

Let run_step := run_step mem_grow_impl host_apply_impl.

Lemma run_step_soundness : forall d i s vs es s' vs' es',
    run_step d i (s, vs, es) = (s', vs', RS_normal es') ->
    exists j,
      reduce s vs es j s' vs' es'.
Proof.
Admitted. (* TODO *)

End Host.

(* TODO: Here are all what we need to implement.
Print Assumptions run_step.
[[
wasm.wasm_wrap : wasm.i64 -> wasm.i32
wasm.wasm_promote : wasm.f32 -> wasm.f64
wasm.wasm_extend_u : wasm.i32 -> wasm.i64
wasm.wasm_extend_s : wasm.i32 -> wasm.i64
wasm.wasm_deserialise : bytes -> value_type -> value
wasm.wasm_demote : wasm.f64 -> wasm.f32
wasm.wasm_bool : bool -> wasm.i32
wasm.ui64_trunc_f64 : wasm.f64 -> option wasm.i64
wasm.ui64_trunc_f32 : wasm.f32 -> option wasm.i64
wasm.ui32_trunc_f64 : wasm.f64 -> option wasm.i32
wasm.ui32_trunc_f32 : wasm.f32 -> option wasm.i32
wasm.si64_trunc_f64 : wasm.f64 -> option wasm.i64
wasm.si64_trunc_f32 : wasm.f32 -> option wasm.i64
wasm.si32_trunc_f64 : wasm.f64 -> option wasm.i32
wasm.si32_trunc_f32 : wasm.f32 -> option wasm.i32
wasm.serialise_i64 : wasm.i64 -> bytes
wasm.serialise_i32 : wasm.i32 -> bytes
wasm.serialise_f64 : wasm.f64 -> bytes
wasm.serialise_f32 : wasm.f32 -> bytes
wasm.i64_r : Wasm_int.class_of wasm.i64
wasm.i64 : eqType
wasm.i32_r : Wasm_int.class_of wasm.i32
wasm.i32 : eqType
wasm.host : eqType
wasm.f64_r : Wasm_float.class_of wasm.f64
wasm.f64_convert_ui64 : wasm.i64 -> wasm.f64
wasm.f64_convert_ui32 : wasm.i32 -> wasm.f64
wasm.f64_convert_si64 : wasm.i64 -> wasm.f64
wasm.f64_convert_si32 : wasm.i32 -> wasm.f64
wasm.f64 : eqType
wasm.f32_r : Wasm_float.class_of wasm.f32
wasm.f32_convert_ui64 : wasm.i64 -> wasm.f32
wasm.f32_convert_ui32 : wasm.i32 -> wasm.f32
wasm.f32_convert_si64 : wasm.i64 -> wasm.f32
wasm.f32_convert_si32 : wasm.i32 -> wasm.f32
wasm.f32 : eqType
eqfunction_closureP : Equality.axiom function_closure_eqb
eqbasic_instructionP : Equality.axiom wasm.basic_instruction_eqb
eqadministrative_instructionP : Equality.axiom administrative_instruction_eqb
wasm.basic_instruction_eqb : basic_instruction -> basic_instruction -> bool
]]
*)
