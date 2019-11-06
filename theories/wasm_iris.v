From mathcomp Require Import ssreflect ssrbool eqtype seq.

From iris.program_logic Require Import language.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import wasm wasm_opsem wasm_interpreter.

Definition expr := list administrative_instruction.
Definition val := value.
Definition state := store_record.
Definition observation := unit. (* TODO: maybe change? *)

Definition of_val (v : val) : expr := [Basic (EConst v)].

Definition to_val (e : expr) : option val :=
  match e with
  | [Basic (EConst v)] => Some v
  | _ => None
  end.

Definition prim_step (e : expr) (s : state) (os : list observation) (e' : expr) (s' : state) (fork_es' : list expr) : Prop :=
  let '(vs, es) := split_vals_e e in
  let '(vs', es') := split_vals_e e' in
  exists i,
    reduce s vs es i s' vs' es' /\ os = [] /\ fork_es' = [].

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.


Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  move: e v.
  case => //=.
  case => //=.
  case => //=.
  move => v.
  case => //=.
  move => v' H.
  injection H => {H} H.
  rewrite H {H v}.
  done.
Qed.

Lemma split_vals_not_empty_res : forall es v vs es', split_vals_e es = (v :: vs, es') -> es <> [].
Proof.
  case => //=.
Qed.

Lemma foo : forall e1 es, split_vals_e e1 = ([], es) -> to_val e1 = None.
Proof.
  case => //=.
  case => //=.
  case => //=.
  move => v es1 es2.
  case: (split_vals_e es1).
  move => a b H.
  discriminate H.
Qed.

Lemma foo3 : forall T xs y ys,
    seq.size (@seq.cat T xs (y :: ys)) <> 0.
Proof.
  move => T xs y ys.
  change 0 with (@seq.size T []).
  rewrite seq.size_cat /= ssrnat.addnS.
  done.
Qed.

Lemma foo7 : forall T (xs : list T) y ys,
    xs ++ (y :: ys) <> [].
Proof.
  move => T xs y ys.
  assert (seq.size (seq.cat xs (y :: ys)) <> @seq.size T []).
  { move => /= H; by apply: foo3. }
  {move => H2.
   apply: H.
   by f_equal. }
Qed.

Lemma foo2 : forall es', ~ (reduce_simple [] es').
Proof.
  assert (forall es es', reduce_simple es es' -> es = [] -> False) as H.
  { move => es es' H.
    elim: {es es'} H => //=.
    { move => vs es _ _ t1s t2s _ _ _ _ H.
      by apply: foo7. }
    { move => vs es _ _ t1s t2s _ _ _ _ H.
      by apply: foo7. }
    { move => es lh _ H Hes.
      rewrite Hes {es Hes} /lfilled /= in H.
      case: lh H => //=.
      { move => es es2.
        case_eq (const_list es) => //=.
        move => _ H.
        assert (seq.size (es ++ Trap :: es2) = @seq.size administrative_instruction []) as Hx.
        { f_equal.
          symmetry.
          by move/eqP: H. }
        { move => {H}.
          by apply: foo3. } } } }
  { move => es' H2.
    apply: H.
    apply: H2.
    done. }
Qed.

Lemma foo6 : forall i lh es es' e es0, lfill i lh es = es' -> es = e :: es0 -> es' <> Some [].
Proof.
  elim.
  { elim; last by intros; subst.
    move => l l0 es es' /=.
    case: (const_list l).
    { move => Hfill H1 H2 H3 H4.
      rewrite H4 in H2.
      injection H2 => H5 {H2}.
      rewrite H3 in H5.
        by apply: foo7. }
    { intros; subst; discriminate. } }
  { move => n IH.
    elim; first by intros; subst.
    intros.
    rewrite /= in H0.
    move: H0.
    case: (const_list l).
    { rewrite H1 {H1}.
      case_eq (lfill n l1 (e :: es0)).
      { move => l3 H1 H2 H3.
        rewrite H3 in H2.
        injection H2.
        move => {H2} H2.
        apply: foo7.
        done. }
      { intros; subst; discriminate. } }
    { intros; subst; discriminate. } }
Qed.

Lemma foo10 : forall i lh es es' e es0, lfill i lh es = es' -> es = e :: es0 -> es' <> Some [].
Proof.
  intros.
  apply: foo6.
  apply: H.
  done.
Qed.

Lemma foo11 : forall T (xs : list T) (y : T) (ys : list T), exists x xs', xs ++ (y :: ys) = x :: xs'.
Proof.
  move => T.
  case.
  { intros. eexists. eexists.
    reflexivity. }
  { intros. eexists. eexists. reflexivity. }
Qed.
  
Lemma foo5 : forall i lh es es', lfilled i lh es es' -> es <> [] -> es' = [] -> False.
Proof.
  move => i lh es es' H Hes Hes'.
  move: (exists_last Hes) => [e [e0 H']].
  rewrite H' in H.
  move: H.
  rewrite /lfilled.
  case_eq (lfill i lh es).
  { intros; subst.
    rewrite H in H0.
    assert ([] = l) as H0'.
    { apply/eqP.
      apply H0. }
    { rewrite H0' in H.
      rewrite /= in H.
      move: (foo11 e e0 l) => [x [xs Hxs]].
      apply: foo6.
      apply: H.
      apply: Hxs.
        by rewrite H0'. } }
  { intros; subst.
    rewrite H in H0.
    done. }
Qed.

Lemma foo4 : forall σ1 vs es i σ2 vs' es', reduce σ1 vs es i σ2 vs' es' -> es = [] -> False.
Proof.
  move => σ1 vs es i σ2 vs' es' Hred.
  elim: {σ1 vs es i es' σ2 vs'} Hred => //=.
  { move => e e' _ _ _ Hreds He.
    rewrite He in Hreds.
    apply: foo2.
    apply: Hreds. }
  (* there must be a better way *)
  { move => cl _ _ _ _ es _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H8.
    assert (seq.size (es ++ [Callcl cl]) = @seq.size administrative_instruction []) as Hx; first by f_equal.
      by apply: foo3. }
  { move => cl f t1s t2s es ves vcs _ _ _ _ _ _ _ _ _ _ _ _ _ H.
    assert (seq.size (es ++ [Callcl cl]) = @seq.size administrative_instruction []) as Hx; first by f_equal.
      by apply: foo3. }
  { move => cl _ _ _ es _ _ _ _ _ _ _ _ _ _ _ H.
    assert (seq.size (es ++ [Callcl cl]) = @seq.size administrative_instruction []) as Hx; first by f_equal.
      by apply: foo3. }
  { move => s vs es les i s' vs' le's les' k lh Hred Hes Hfill Hfill' Hles.
    by apply: (foo5 Hfill). }
Qed.

Lemma val_head_stuck e1 σ1 κ e2 σ2 efs : prim_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof.
  rewrite /prim_step.
  case_eq (split_vals_e e1) => vs es H.
  case_eq (split_vals_e e2) => vs' es' _ [i [Hred _]].
  case: es H Hred.
  { move => _ Hred.
    exfalso.
    apply: foo4.
    apply: Hred.
    done. }
  { move => e es H1 _ {i vs' es' e2 efs}.
    case: e1 H1 => //=.
    move => e' es'.
    case e' => //=.
    move => b.
    case b => //=.
    move => v.
    case es' => //=. }
Qed.

Lemma wasm_mixin : LanguageMixin of_val to_val prim_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck.
Qed.

Canonical Structure wasm := Language wasm_mixin.

Export wasm.
