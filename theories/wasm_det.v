From Wasm Require Export properties operations opsem common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Bool Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Variable host_function: eqType.

Let store_record := store_record host_function.
Let function_closure := function_closure host_function.

Let host := host host_function.

Variable host_instance: host.

Let host_state := host_state host_instance.

Let reduce : host_state -> store_record -> frame -> list administrative_instruction ->
             host_state -> store_record -> frame -> list administrative_instruction -> Prop :=
  @reduce _ _.

(*

Search AI_label.

Fixpoint det_no_exception_single (e: administrative_instruction) : bool :=
  match e with
  | AI_invoke _ => false
  | AI_basic (BI_grow_memory) => false
  | AI_basic (BI_call _) => false
(*  | AI_label _ es1 es2 => ( det_exception_singl*)
  | _ => true          
  end.

Definition det_no_exception (es: list administrative_instruction) : bool :=
  all det_no_exception_single es.
  
Lemma wasm_det: forall hs s f es hs1 s1 f1 es1 hs2 s2 f2 es2,
    reduce hs s f es hs1 s1 f1 es1 ->
    reduce hs s f es hs2 s2 f2 es2 ->
    det_no_exception es ->
    (hs1, s1, f1, es1) = (hs2, s2, f2, es2).
Proof.
  move => hs s f es hs1 s1 f1 es1 hs2 s2 f2 es2 HR1 HR2 Hdet.
  move: hs2 s2 f2 es2 HR2 Hdet.
  elim: HR1 => //=.
Admitted.
 *)

Lemma lfilled0_in1: forall lh e les,
  lfilled 0 lh [::e] les ->
  ~ e \in les ->
  False.
Proof.
  move => lh e les Hlf Hin.
  apply Hin; clear Hin.
  move/lfilledP in Hlf.
  inversion Hlf; subst; clear Hlf.
  rewrite mem_cat in_cons.
  apply/orP. right.
  apply/orP. left.
  by apply/eqP.
Qed.

Lemma cat1_eq: forall T (es1 es2: list T) e1 e2,
    es1 ++ [::e1] = es2 ++ [::e2] ->
    es1 = es2 /\ e1 = e2.
Proof.
Admitted.
  
Ltac simpl_eq :=
  repeat match goal with
  | H: ?x = _, H1: ?x = _ |- _ => rewrite H in H1; try by inversion H1
  end.
  
Lemma wasm_rs_det: forall es es1 es2,
    reduce_simple es es1 ->
    reduce_simple es es2 ->
    es1 = es2.
Proof.
  move => es es1 es2 HR1.
  move: es2.
  inversion HR1; move => es2 HR2; inversion HR2 => //=; try (by do 5 destruct vs => //=); subst; try (exfalso; by eapply lfilled0_in1; eauto); simpl_eq.
  - admit.
Admitted.

End Host.
