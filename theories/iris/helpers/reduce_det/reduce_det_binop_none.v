From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export iris_reduce_det_prelude.

Lemma binop_none_det v1 v2 op t s f s' f' es:
  app_binop op v1 v2 = None ->
  reduce s f [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] s' f' es ->
  reduce_det_goal s f [AI_trap] s' f' es [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)].
Proof.
  move => H Hred.
  by only_one [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ; AI_basic (BI_binop t op)] Hred ;
     inversion Heqes ; subst ; rewrite H in H0 ; inversion H0 ; subst.
Qed.
