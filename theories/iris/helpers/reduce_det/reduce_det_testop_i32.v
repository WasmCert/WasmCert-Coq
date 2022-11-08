From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export iris_reduce_det_prelude.

Lemma testop_i32_det c s f s' f' es testop:
  reduce s f [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_testop T_i32 testop)] s' f' es ->
  reduce_det_goal s f [AI_basic (BI_const (VAL_int32 (wasm_bool (app_testop_i (e:=i32t) testop c))))]
    s' f' es [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_testop T_i32 testop)].
Proof.
  move => Hred.
  by only_one [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_testop T_i32 testop)] Hred.
Qed.
