(** Iris bindings **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrbool eqtype seq.

From iris.program_logic Require Import language.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import operations opsem interpreter.


Section Host.

Variable host_function : eqType.

Let host := host host_function.
Let administrative_instruction := administrative_instruction host_function.
Let store_record := store_record host_function.
Let lholed := lholed host_function.

Let lfilled : nat -> lholed -> list administrative_instruction -> list administrative_instruction -> bool :=
  @lfilled _.
Let split_vals_e : list administrative_instruction -> list value * list administrative_instruction :=
  @split_vals_e _.

Variable host_instance : host.

Let host_state := host_state host_instance.
Let reduce_simple : list administrative_instruction -> list administrative_instruction -> Prop :=
  @reduce_simple _.
Let reduce : host_state -> store_record -> list value -> list administrative_instruction -> instance ->
             host_state -> store_record -> list value -> list administrative_instruction -> Prop :=
  @reduce _ _.
Let lfill : nat -> lholed -> list administrative_instruction -> option (list administrative_instruction) :=
  @lfill _.

Definition expr := list administrative_instruction.
Definition val := list value.
Definition state : Type := host_state * store_record.
Definition observation := unit. (* TODO: maybe change? *)

Definition of_val (v : val) : expr := map (fun v => Basic (EConst v)) v.

Fixpoint to_val (e : expr) : option val :=
  match e with
  | [::] => Some [::]
  | Basic (EConst v) :: e' =>
    match to_val e' with
    | Some v' => Some (v :: v')
    | None => None
    end
  | _ => None
  end.

Definition prim_step (e : expr) (s : state) (os : list observation) (e' : expr) (s' : state) (fork_es' : list expr) : Prop :=
  let '(hs, σ) := s in
  let '(hs', σ') := s' in
  let '(vs, es) := split_vals_e e in
  let '(vs', es') := split_vals_e e' in
  exists i,
    reduce hs σ vs es i hs' σ' vs' es' /\ os = [] /\ fork_es' = [].

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  move: v.
  elim => //=.
  move => v0 v IH.
  by rewrite IH.
Qed.

Definition is_none_or {A : Type} (p : A -> bool) (x : option A) : bool :=
  match x with
  | None => true
  | Some y => p y
  end.

Lemma to_val_cons_is_none_or_cons : forall e0 e r,
  to_val (e0 :: e)%SEQ = r -> is_none_or (fun l => l != []) r.
Proof.
  move => e0 e.
  rewrite /=.
  case.
  { rewrite /=.
    case: e0 => //=.
    case => //=.
    move => v0 v.
    case: (to_val e) => //=.
    move => a H.
    by case: v H. }
  { by case: e0. }
Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  move: e v.
  elim.
  { move => v /= H.
    injection H => {H} H2.
    by rewrite -H2. }
  { move => e0 e IH.
    case.
    { move => {IH} H.
      exfalso.
      move: (to_val_cons_is_none_or_cons H) => {} H.
      discriminate H. }
    { move => v0 v.
      case: e0 => //=.
      case => //=.
      move => v1.
      case_eq (to_val e) => //=.
      move => v' Hve H.
      injection H => {H} Hv' Hv1.
      rewrite Hv' in Hve => {v' Hv'}.
      rewrite Hv1 => {v1 Hv1}.
      rewrite (IH _ Hve) => {IH Hve}.
      done. }
  }
Qed.

Lemma split_vals_not_empty_res : forall es v vs es',
  split_vals_e es = (v :: vs, es') -> es <> [].
Proof. by case. Qed.

Lemma splits_vals_e_to_val_hd : forall e1 e es vs,
  split_vals_e e1 = (vs, e :: es) -> to_val e1 = None.
Proof.
  elim; first done.
  case; try done.
  case; try done.
  move => v es1 IH e es vs H.
  rewrite /= in H.
  move: vs H.
  case_eq (split_vals_e es1) => x xs H1 H2 [H3 H4].
  rewrite /=.
  rewrite H4 in H1.
  rewrite (IH _ _ _ H1).
  done.
Qed.

Lemma cat_cons_not_nil : forall T (xs : list T) y ys,
  xs ++ (y :: ys) <> [].
Proof. move => T xs y ys E. by move: (app_eq_nil _ _ E) => [? ?]. Qed.

Lemma not_reduce_simple_nil : forall es', ~ reduce_simple [] es'.
Proof.
  assert (forall es es', reduce_simple es es' -> es = [] -> False) as H.
  { move => es es' H.
    elim: {es es'} H => //=.
    { move => vs es _ _ t1s t2s _ _ _ _ H.
      by apply: cat_cons_not_nil. }
    { move => vs es _ _ t1s t2s _ _ _ _ H.
      by apply: cat_cons_not_nil. }
    { move => es lh _ H Hes.
      rewrite Hes {es Hes} /lfilled /operations.lfilled /= in H.
      case: lh H => //=.
      { move => es es2.
        case_eq (const_list es) => //=.
        move=> _ /eqP H.
        symmetry in H.
        by move: (app_eq_nil _ _ H) => [? ?]. } } }
  { move => es' H2.
    by apply: H. }
Qed.

Lemma lfill_cons_not_Some_nil : forall i lh es es' e es0,
  lfill i lh es = es' -> es = e :: es0 -> es' <> Some [].
Proof.
  elim.
  { elim; last by intros; subst.
    move=> l l0 es es' /=.
    case: (const_list l).
    { move => Hfill H1 H2 H3 H4.
      rewrite H4 in H2.
      injection H2 => H5 {H2}.
      rewrite H3 in H5.
      by apply: cat_cons_not_nil. }
    { intros; subst; discriminate. } }
  { move=> n IH.
    elim; first by intros; subst.
    intros.
    rewrite /= in H0.
    move: H0.
    case: (const_list l).
    { rewrite H1 {H1}.
      case_eq (lfill n l1 (e :: es0)).
      { move=> l3 H1 H2 H3.
        rewrite H3 in H2.
        injection H2.
        move=> {} H2.
        apply: cat_cons_not_nil.
        done. }
      { intros; subst; discriminate. } }
    { intros; subst; discriminate. } }
Qed.

Lemma lfilled_not_nil : forall i lh es es', lfilled i lh es es' -> es <> [] -> es' <> [].
Proof.
  move => i lh es es' H Hes Hes'.
  move: (exists_last Hes) => [e [e0 H']].
  rewrite H' in H.
  move: H.
  rewrite /lfilled /operations.lfilled.
  case_eq (operations.lfill i lh es).
  { intros; subst.
    rewrite H in H0.
    assert ([] = l) as H0'.
    { apply/eqP.
      apply H0. }
    { rewrite H0' in H.
      rewrite /= in H.
      case E: (e ++ (e0 :: l)%SEQ)%list; first by move: (app_eq_nil _ _ E) => [? ?].
      apply: lfill_cons_not_Some_nil.
      apply: H.
      apply: E.
      by rewrite H0'. } }
  { intros; subst.
    rewrite H in H0.
    done. }
Qed.

Lemma reduce_not_nil : forall hs1 σ1 vs es i hs2 σ2 vs' es',
  reduce hs1 σ1 vs es i hs2 σ2 vs' es' -> es <> [].
Proof.
  move => hs1 σ1 vs es i hs2 σ2 vs' es' Hred.
  elim: {hs1 σ1 vs es i hs2 es' σ2 vs'} Hred => //;
    try solve [ repeat intro;
                match goal with
                | H : (_ ++ _)%SEQ = [] |- _ =>
                  by move: (app_eq_nil _ _ H) => [? ?]
                end ].
  { move => e e' _ _ _ _ Hreds He.
    rewrite He in Hreds.
    apply: not_reduce_simple_nil.
    apply: Hreds. }
  { intros. by apply: lfilled_not_nil. }
Qed.

Lemma val_head_stuck : forall e1 s1 κ e2 s2 efs,
  prim_step e1 s1 κ e2 s2 efs →
  to_val e1 = None.
Proof.
  rewrite /prim_step => e1 [hs1 σ1] κ e2 [hs2 σ2] efs.
  case_eq (split_vals_e e1) => vs es H.
  case_eq (split_vals_e e2) => vs' es' _ [i [Hred _]].
  move: vs vs' es' H Hred.
  elim: es.
  { move => vs vs' es' _ Hred.
    exfalso.
    apply: reduce_not_nil.
    apply: Hred.
    done. }
  { move => e es _ vs vs' _ H1 _ {e2 efs}.
    apply: splits_vals_e_to_val_hd.
    apply: H1. }
Qed.

Lemma wasm_mixin : LanguageMixin of_val to_val prim_step.
Proof. split; eauto using to_of_val, of_to_val, val_head_stuck. Qed.

End Host.

