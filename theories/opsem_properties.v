From Wasm Require Export opsem properties contexts.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program NArith ZArith Wf_nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Variable host_function: eqType.
Variable host_instance: host host_function.

Local Definition reduce := @reduce host_function host_instance.

Lemma reduce_not_nil : forall hs hs' σ1 f es σ2 f' es',
  reduce hs σ1 f es hs' σ2 f' es' -> es <> [::].
Proof.
  move => hs hs' σ1 f es σ2 f' es' Hred.
  elim: {σ1 f es f' σ2} Hred => //;
    try solve [ repeat intro;
                match goal with
                | H : (_ ++ _)%SEQ = [::] |- _ =>
                  by move: (app_eq_nil _ _ H) => [? ?]
                end ].
  { move => e e' _ _ _ Hreds He.
    rewrite He in Hreds.
    apply: not_reduce_simple_nil.
    apply: Hreds. }
  { intros. destruct ves => //. }
  { intros. destruct ves => //. }
  { intros. by destruct ves => //. }
  { intros. apply: lfilled_not_nil. exact H1. exact H0. }
Qed.

End Host.
