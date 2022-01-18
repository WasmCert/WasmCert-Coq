(** Iris bindings **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrbool eqtype seq.

From iris.program_logic Require Import language.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import common operations opsem interpreter.

Section Host.
  
Import DummyHosts.
(*
Print store_record.

Let store_record := store_record host_function.

Variable host_instance : host.


Print reduce.
*)
Let host_state := host_state host_instance.
Let reduce : host_state -> store_record -> frame -> list administrative_instruction ->
             host_state -> store_record -> frame -> list administrative_instruction -> Prop :=
  @reduce _ _.
Definition expr := list administrative_instruction.

(* Add [::AI_trap] to val? *)
Inductive val : Type :=
| immV : (list value) -> val
| trapV : val.

Definition val_eq_dec : forall v1 v2: val, {v1 = v2} + {v1 <> v2}.
Proof.
  decidable_equality.
Defined.
Definition val_eqb (v1 v2: val) : bool := val_eq_dec v1 v2.
Definition eqvalP : Equality.axiom val_eqb :=
  eq_dec_Equality_axiom val_eq_dec.

Canonical Structure val_eqMixin := EqMixin eqvalP.
Canonical Structure val_eqType := Eval hnf in EqType val val_eqMixin.

(* The following operation mirrors the opsem of AI_trap *)
(* in which a trap value swallows all other stack values *)
Definition val_combine (v1 v2 : val) :=
  match v1 with
  | immV l => match v2 with
             | immV l' => immV (l ++ l')
             | trapV => trapV
             end
  | trapV => trapV
  end.

Definition state : Type := host_state * store_record * (list value) * instance.

Definition observation := unit. (* TODO: maybe change? *)

Definition of_val (v : val) : expr :=
  match v with
  | immV l => fmap (fun v => AI_basic (BI_const v)) l
  | trapV => [::AI_trap]
  end.
Lemma of_val_imm (vs : list value) :
  ((λ v : value, AI_basic (BI_const v)) <$> vs) = of_val (immV vs).
Proof. done. Qed.

Fixpoint to_val (e : expr) : option val :=
  match e with
  | [::AI_trap] => Some trapV
  | [::] => Some (immV [::])
  | AI_basic (BI_const v) :: e' =>
    match to_val e' with
    | Some (immV v') => Some (immV (v :: v')) (* No interweaving of trap and values *)
    | _ => None
    end
  | _ => None
  end.

Definition prim_step (e : expr) (s : state) (os : list observation) (e' : expr) (s' : state) (fork_es' : list expr) : Prop :=
  let '(hs, σ, locs, inst) := s in
  let '(hs', σ', locs', inst') := s' in
    reduce hs σ (Build_frame locs inst) e hs' σ' (Build_frame locs' inst') e' /\ os = [] /\ fork_es' = [].

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  destruct 0 => //.
  move: l.
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
  to_val (e0 :: e)%SEQ = r -> is_none_or (fun l => match l with | immV v => v != [] | _ => true end) r.
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
    case: v H. case: a => //.
    move => l l0 //=.
    by case: l0 => //. done.
    move => a H.
    case: a H => //.
    move => l H.
    by case: e H. }
  { by case: e0. }
Qed.
Lemma to_val_trap_is_singleton : ∀ e,
    to_val e = Some trapV -> e = [::AI_trap].
Proof.
  move => e.
  case: e => //=.
  move => a l.
  case: a => //=.
  move => b.
  case: b => //=.
  move => v.
  case (to_val l) => v0.
  by case v0 => //=. done.
  case: l => //=.
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
    { case. 
      { move => {IH} H.
        exfalso.
        move: (to_val_cons_is_none_or_cons H) => {} H.
        discriminate H. }
      { move => v0 l v.
        case: e0 v => //=.
        case => //=.
        move => v1.
        case_eq (to_val e) => //=.
        move => v' Hve H.
        case: v' Hve H => //=.
        move => l0 H H'.
        injection H' => {H'} <- ->.
        f_equiv.
        by rewrite -(IH _ H).
        move => H//=.
        case: e {IH} H => H//=. }
    }
    { move => H //=.
      case: e {IH} H => H.
      injection (to_val_trap_is_singleton H).
      by move ->.
      move => l H'.
      injection (to_val_trap_is_singleton H').
      by move => H0.
    }
  }
Qed.

Lemma split_vals_not_empty_res : forall es v vs es',
  split_vals_e es = (v :: vs, es') -> es <> [].
Proof. by case. Qed.

Lemma splits_vals_e_to_val_hd : forall e1 e es vs,
  split_vals_e e1 = (vs, e :: es) -> to_val e1 = None ∨ (vs = [] ∧ to_val e1 = Some trapV).
Proof.
  elim; first done.
  case;try (move => e l H e' es' vs H'; by left).
  { move => b l H e es vs H'. left.
    rewrite /= in H.
    move: vs H'.
    case.
    move => H' //=.
    case: b H' => //=.
    case_eq (split_vals_e l) => x xs H1 H2 [H3 H4].
    rewrite /=.
    rewrite H4 in H1.
    destruct (H _ _ _ H1) => //=.
    move => a l0.
    case: b => v' //=.
    case_eq (split_vals_e l) => x xs H1 [-> H2] H3.
    subst xs x.
    destruct (H _ _ _ H1) => //=. by rewrite H0.
    by destruct H0 as [-> ->]. }
  { move => l IH e es vs H'.
    case: l IH H'.
    move => IH [H1 H2]. subst;auto.
    move => a l IH //=;auto. }
Qed.

Lemma to_val_None_prepend: forall es1 es2,
  to_val es2 = None ->
  to_val (es1 ++ es2) = None.
Proof.
  move => es1 es2 H.
  induction es1 => //=.
  destruct a => //=.
  destruct b => //=.
  by rewrite IHes1.
  destruct (es1 ++ es2);auto.
  done.
Qed.
  
Lemma to_val_None_append: forall es1 es2,
  to_val es1 = None ->
  to_val (es1 ++ es2) = None.
Proof.
  move => es1 es2.
  induction es1 => //=.
  destruct a => //=.
  destruct b => //=.
  destruct (to_val es1) eqn:H => //=.
  { case: v0 H IHes1 => //=.
    move => Ht _ _.
    apply to_val_trap_is_singleton in Ht as ->.
    case es2;auto. }
  { rewrite IHes1//. }
  move => Hn.
  destruct es2 => //=.
  rewrite app_nil_r //.
  case es1 => //=.
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

Lemma reduce_not_nil : forall hs1 σ1 f es hs2 σ2 f' es',
  reduce hs1 σ1 f es hs2 σ2 f' es' -> es <> [].
Proof.
  move => hs1 σ1 f es hs2 σ2 f' es' Hred.
  elim: {hs1 σ1 f es hs2 f' σ2} Hred => //;
    try solve [ repeat intro;
                match goal with
                | H : (_ ++ _)%SEQ = [] |- _ =>
                  by move: (app_eq_nil _ _ H) => [? ?]
                end ].
  { move => e e' _ _ _ Hreds He.
    rewrite He in Hreds.
    apply: not_reduce_simple_nil.
    apply: Hreds. }
  { intros. by apply: lfilled_not_nil. }
Qed.

Lemma to_val_not_trap_interweave : ∀ es es',
    es != [] ∨ es' != [] -> to_val (es ++ [AI_trap] ++ es')%SEQ = None.
Proof.
  elim.
  { move => es'.
    case: es'=> H //=.
    destruct H => //. }
  move => a l IH es' H //=.
  case: a H => b //=.
  2: case l => //.
  move => _.
  case b => //=.
  move => v /=.
  case: l IH.
  { case: es' => //=. }
  move => a l IH. rewrite IH//. by left.
Qed.

Lemma val_head_stuck_reduce : ∀ hs1 locs1 s1 e1 hs2 locs2 s2 e2,
    reduce hs1 locs1 s1 e1 hs2 locs2 s2 e2 ->
    to_val e1 = None.
Proof.
  move => hs1 locs1 s1 e1 hs2 locs2 s2 e2 HRed.
  induction HRed => //=; subst; try by apply to_val_None_prepend.
  - inversion H; subst => //=; try by apply to_val_None_prepend.
    + destruct v => //=.
      by destruct b => //=.
    + move/lfilledP in H1.
      inversion H1. subst es e.
      apply to_val_not_trap_interweave.
      case: vs {H H1 H2 H4} H0 => //=.
      case: es' => //=.
      move => a l H. by right.
      move => a l H. by left.
  - move/lfilledP in H.
    inversion H; subst; clear H.
    by apply to_val_None_prepend, to_val_None_append.
  - by apply to_val_None_prepend, to_val_None_append.
Qed.

Lemma val_head_stuck : forall e1 s1 κ e2 s2 efs,
  prim_step e1 s1 κ e2 s2 efs →
  to_val e1 = None.
Proof.
  rewrite /prim_step => e1 [[[hs1 locs1] σ1] inst] κ e2 [[[hs2 locs2] σ2] inst'] efs.
  move => [HRed _].
  eapply val_head_stuck_reduce;eauto.
Qed.

Lemma wasm_mixin : LanguageMixin of_val to_val prim_step.
Proof. split; eauto using to_of_val, of_to_val, val_head_stuck. Qed.

End Host.


