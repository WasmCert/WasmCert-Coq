From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export iris_reduce_det_prelude.

Lemma binop_det v1 v2 v op t s f s' f' es:
  app_binop op v1 v2 = Some v ->
  reduce s f [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] s' f' es ->
  reduce_det_goal s f [AI_basic (BI_const v)] s' f' es [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)].
Proof.
  move => H Hred.
    (* an example where we the user need to provide some extra work because [ only_one ]
         couldn't exfalso away every possibility : here, knowing that Hred2 is
         hypothesis [ [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ; 
         AI_basic (BI_binop t op)] -> es2 ], the tactic leaves us with two (not one)
         possibilities : Hred2 holds either using rs_binop_success or rs_binop_failure.
         It is up to us to exfalso away the second case using the rest of the
         hypotheses *)
  by only_one [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ; AI_basic (BI_binop t op)] Hred ;
     inversion Heqes ; subst ; rewrite H in H0 ; inversion H0 ; subst.
Qed.
