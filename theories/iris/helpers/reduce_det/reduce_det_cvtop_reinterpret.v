From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export iris_reduce_det_prelude.

Lemma cvtop_reinterpret_det v t1 t2 s f s' f' es:
  types_agree t1 v ->
  reduce s f [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] s' f' es ->
  reduce_det_goal s f [AI_basic (BI_const (wasm_deserialise (bits v) t2))] s' f' es
    [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)].
Proof.
  move => H Hred.
  by only_one [AI_basic (BI_const v) ; AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] Hred.
Qed.
