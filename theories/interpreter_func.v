(** Proof-carrying interpreter for Wasm **)

From Wasm Require Import common opsem properties tactic typing_inversion.
From Coq Require Import ZArith.BinInt Program.Equality.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Export operations host.
Require Import BinNat.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.

Inductive res_crash : Type :=
| C_error : res_crash
| C_exhaustion : res_crash.

Scheme Equality for res_crash.
Definition res_crash_eqb c1 c2 := is_left (res_crash_eq_dec c1 c2).
Definition eqres_crashP : Equality.axiom res_crash_eqb :=
  eq_dec_Equality_axiom res_crash_eq_dec.

Canonical Structure res_crash_eqMixin := EqMixin eqres_crashP.
Canonical Structure res_crash_eqType := Eval hnf in EqType res_crash res_crash_eqMixin.

Inductive res : Type :=
| R_crash : res_crash -> res
| R_trap : res
| R_value : list value -> res.

Definition res_eq_dec : forall r1 r2 : res, {r1 = r2} + {r1 <> r2}.
Proof. decidable_equality. Defined.

Definition res_eqb (r1 r2 : res) : bool := res_eq_dec r1 r2.
Definition eqresP : Equality.axiom res_eqb :=
  eq_dec_Equality_axiom res_eq_dec.

Canonical Structure res_eqMixin := EqMixin eqresP.
Canonical Structure res_eqType := Eval hnf in EqType res res_eqMixin.

Section Host_func.

Variable host_function : eqType.
Let host := host host_function.

Variable host_instance : host.

Let store_record := store_record host_function.
Let host_state := host_state host_instance.


Let e_typing := @e_typing host_function.
Let inst_typing := @inst_typing host_function.

Variable host_application_impl : host_state -> store_record -> function_type -> host_function -> seq value ->
                       (host_state * option (store_record * result)).

Hypothesis host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).

Definition fragment_typeable s f ves es :=
  exists C C' ret lab t1s t2s t1s',
    C = upd_label (upd_local_return C' (map typeof f.(f_locs)) ret) lab /\
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C' /\
    store_typing s /\
    e_typing s C es (Tf t1s t2s).

Inductive res_step : Type :=
| RS_crash : res_crash -> res_step
| RS_break : nat -> list value -> res_step
| RS_return : list value -> res_step
| RS_normal : list administrative_instruction -> res_step.

Inductive res_step'
  (hs : host_state) (s : store_record) (f : frame)
  (es : list administrative_instruction) : Type :=
| RS'_value :
    const_list es \/ es_is_trap es ->
    res_step' hs s f es
| RS'_error :
    (~ exists C C' ret lab ts,
      C = upd_label (upd_local_return C' (map typeof f.(f_locs)) ret) lab /\
      inst_typing s f.(f_inst) C' /\
      store_typing s /\
      e_typing s C es (Tf [::] ts)) ->
    res_step' hs s f es
| RS'_break k bvs :
    (exists i j lh,
      i + k = j /\
      lfilledInd i lh (vs_to_es bvs ++ [::AI_basic (BI_br j)]) es /\
      empty_vs_base lh) ->
    res_step' hs s f es
| RS'_return rvs :
    (exists i lh,
      lfilledInd i lh (vs_to_es rvs ++ [:: AI_basic BI_return]) es /\
      empty_vs_base lh) ->
    res_step' hs s f es
| RS'_normal hs' s' f' es' :
    reduce hs s f es hs' s' f' es' ->
    res_step' hs s f es.

Inductive res_step'_separate_e
  (hs : host_state) (s : store_record) (f : frame)
  (ves : list value) (e : administrative_instruction) : Type :=
| RS''_error :
    (~ fragment_typeable s f ves [:: e]) ->
    res_step'_separate_e hs s f ves e

| RS''_break k bvs :
    (exists i j lh,
      i + k = j /\
      lfilledInd i lh
        (vs_to_es bvs ++ [:: AI_basic (BI_br j)]) (vs_to_es ves ++ [:: e]) /\
      empty_vs_base lh) ->
    res_step'_separate_e hs s f ves e

| RS''_return rvs :
    (e = AI_basic BI_return /\ rvs = ves) \/
    (exists ln les es i lh,
      e = AI_label ln les es /\
      lfilledInd i lh (vs_to_es rvs ++ [:: AI_basic BI_return]) es /\
      empty_vs_base lh) ->
    res_step'_separate_e hs s f ves e
| RS''_normal hs' s' f' es' :
    reduce hs s f ((vs_to_es ves) ++ [:: e]) hs' s' f' es' ->
    res_step'_separate_e hs s f ves e.

(* Notation for RS'_normal. This forces hs', s', f' es' to be explicitly
 * stated. Their values could be inferred from the type of H instead but we
 * want to make those values clear. *)
Notation "<< hs' , s' , f' , es' >>" := (@RS'_normal _ _ _ _ hs' s' f' es').
Notation "<< hs' , s' , f' , es' >>'" := (@RS''_normal _ _ _ _ _ hs' s' f' es').
Notation "break( k , bvs )" := (@RS''_break _ _ _ _ _ k bvs).
(* TODO return notation? *)

Definition res_step_eq_dec : forall r1 r2 : res_step, {r1 = r2} + {r1 <> r2}.
Proof. decidable_equality. Defined.

Definition res_step_eqb (r1 r2 : res_step) : bool := res_step_eq_dec r1 r2.
Definition eqres_stepP : Equality.axiom res_step_eqb :=
  eq_dec_Equality_axiom res_step_eq_dec.

Canonical Structure res_step_eqMixin := EqMixin eqres_stepP.
Canonical Structure res_step_eqType := Eval hnf in EqType res_step res_step_eqMixin.

Definition crash_error := RS_crash C_error.

Definition depth := nat.

Definition fuel := nat.

Definition config_tuple := ((host_state * store_record * frame * list administrative_instruction)%type).

Definition config_one_tuple_without_e := (host_state * store_record * frame * list value)%type.

Definition res_tuple := (host_state * store_record * frame * res_step)%type.

(* TODO use some ltacs from progress/preservation? invert_typeof_vcs etc *)

(* TODO auto instantiate lh, k? *)
Ltac solve_lfilled :=
  unfold lfilled, lfill, vs_to_es;
  try rewrite v_to_e_is_const_list; apply/eqP; simplify_lists => //;
  repeat rewrite List.app_nil_r.

(* get f z = x from (H : rev (map f (z :: zs)) = xs ++ ys ++ [:: x]) *)
Ltac cats1_last_eq H :=
  rewrite rev_cons in H; rewrite <- cats1 in H; repeat rewrite catA in H;
  apply concat_cancel_last in H as [H ?].

(* using (H : rev (map f [::]) = xs ++ ys), substitute xs = ys = [::] *)
Ltac apply_cat0_inv H :=
  try match type of H with
  | _ = ?xs ++ ?ys => symmetry in H
  end;
  match type of H with
  | ?xs ++ ?ys = _ =>
      repeat rewrite catA in H; apply cat0_inv in H as [H ?];
      try subst xs; try subst ys; try apply_cat0_inv H
  end.

Ltac simpl_vs_to_es_size :=
    unfold vs_to_es, v_to_e_list; rewrite size_map; rewrite size_rev.

Ltac if_lias :=
  match goal with
  | |- (if ?cond then _ else _) = _ =>
    destruct cond eqn:?; lias
  end.

Ltac size_unequal H :=
  apply (f_equal size) in H;
  revert H;
  repeat rewrite size_cat; try rewrite size_rev; try rewrite size_map; simpl; lias.

Lemma vs_to_es_cons : forall v ves,
  vs_to_es ves ++ [:: AI_basic (BI_const v)] = vs_to_es (v :: ves).
Proof.
  intros.
  unfold vs_to_es. rewrite rev_cons. rewrite cats1. unfold v_to_e_list. rewrite map_rcons.
  by apply f_equal.
Qed.

(* TODO use this in more places? might have to generalise a bit
 * maybe leave out 'apply r_simple' *)
Ltac simpl_reduce_simple :=
  (* TODO use some existing list ltacs instead of these initial matches? *)
  try match goal with
  | |- reduce _ _ _ (vs_to_es (?v :: ?ves') ++ [:: ?e]) _ _ _ _ =>
      replace (v :: ves') with ([:: v] ++ ves');
      last by apply cat1s
  | |- reduce
      _ _ _ (vs_to_es ?ves ++ [:: ?e])
      _ _ _ (vs_to_es ?ves ++ [:: ?e']) =>
      replace ves with ([::] ++ ves) at 1;
      last by apply cat0s
  end;
  try match goal with
  | |- reduce _ _ _ _ _ _ _ (vs_to_es (?v' :: ?ves')) =>
      replace (vs_to_es (v' :: ves'))
         with (vs_to_es ves' ++ [:: AI_basic (BI_const v')]);
      last by apply vs_to_es_cons
  end;
  match goal with
  | |- reduce
      _ _ _ (vs_to_es (?vs ++ ?ves') ++ [:: ?e])
      _ _ _ (vs_to_es ?ves' ++ [:: ?e']) =>
        eapply r_label with
          (k := 0) (lh := (LH_base (vs_to_es ves') [::]))
          (es := vs_to_es vs ++ [:: e])
          (es' := [:: e']);
        try solve_lfilled; apply r_simple
  end.

Lemma error_rec : forall s f e es es' es'' ves,
  es' = e :: es'' ->
  split_vals_e es = (ves, es') ->
  ~ (exists C C' ret lab t1s t2s t1s',
      C = upd_label (upd_local_return C' (map typeof f.(f_locs)) ret) lab /\
      rev [seq typeof i | i <- rev ves] = t1s' ++ t1s /\
      inst_typing s f.(f_inst) C' /\
      store_typing s /\ e_typing s C [:: e] (Tf t1s t2s)) ->
  ~ (exists C C' ret lab ts,
      C = upd_label (upd_local_return C' (map typeof f.(f_locs)) ret) lab /\
      inst_typing s f.(f_inst) C' /\ store_typing s /\ e_typing s C es (Tf [::] ts)).
Proof.
  intros s f e es es' es'' ves ? Hsplit Hrec [C [C' [ret [lab [? [? [? [? Hetype]]]]]]]].
  apply split_vals_e_v_to_e_duality in Hsplit. subst es es'.
  apply e_composition_typing in Hetype as [? [t1s [? [? [Ht1s [? [Hetypeves Hetype]]]]]]].
  apply_cat0_inv Ht1s.
  rewrite <- cat1s in Hetype.
  apply e_composition_typing in Hetype as [ts [t2s [? [t3s [Ht2s [? [??]]]]]]].
  apply et_to_bet in Hetypeves as Hbtypeves;
    last by apply const_list_is_basic; apply v_to_e_is_const_list.
  apply Const_list_typing in Hbtypeves.
  apply Hrec. exists C, C', ret, lab, (ts ++ t2s), (ts ++ t3s), [::].
  repeat split => //; try by apply ety_weakening.
  rewrite map_rev. rewrite revK.
  rewrite <- Ht2s. by rewrite Hbtypeves.
Qed.

Lemma break_rec : forall e es es'' ves k bvs,
  split_vals_e es = (ves, e :: es'') ->
  (exists i j lh,
    i + k = j /\
    lfilledInd i lh
      (vs_to_es bvs ++ [:: AI_basic (BI_br j)]) (vs_to_es (rev ves) ++ [:: e]) /\
    empty_vs_base lh) ->
  exists i j lh,
   i + k = j /\
   lfilledInd i lh (vs_to_es bvs ++ [:: AI_basic (BI_br j)]) es /\
   empty_vs_base lh.
Proof.
  intros e es es'' ves k bvs Hsplit
    [i [j [[lh_vs lh_es | lh_vs n lh_es' lh' lh_es] [Heqj [Hlf Hbase]]]]];
    apply split_vals_e_v_to_e_duality in Hsplit; subst es; unfold vs_to_es.
  - destruct lh_vs => //.
    inversion Hlf as [???? H1 H2 H3 Heqes|]; subst; clear Hlf.
    exists 0, k, (LH_base [::] es''). repeat split => //.
    rewrite add0n -catA in Heqes. unfold vs_to_es in Heqes.
    apply ves_cat_e_split in Heqes as [-> [<- ->]] => //;
      try by apply v_to_e_is_const_list.
    rewrite revK.
    replace (AI_basic (BI_br k) :: es'')
      with ([:: AI_basic (BI_br k)] ++ es'') => //.
    by rewrite catA; apply LfilledBase.
  - inversion Hlf as [ | i' vs0 m es'0 lh'0 es''0 es0 LI Hconst Hlf0 H1 H2 H5 Heqes].
    subst i vs0 m es'0 lh'0 es''0 es0.
    unfold vs_to_es in Heqes.
    apply ves_cat_e_split in Heqes as [-> [<- ->]] => //;
      try by apply v_to_e_is_const_list.
    exists i'.+1, j, (LH_rec (v_to_e_list ves) n lh_es' lh' es'').
    by repeat split => //; apply LfilledRec => //; apply v_to_e_is_const_list.
Qed.

Lemma return_rec : forall e es es'' ves rvs,
  split_vals_e es = (ves, e :: es'') ->
  (e = AI_basic BI_return /\ rvs = rev ves) \/
  (exists ln les es i lh,
    e = AI_label ln les es /\
    lfilledInd i lh (vs_to_es rvs ++ [:: AI_basic BI_return]) es /\
    empty_vs_base lh) ->
  exists i lh,
  lfilledInd i lh (vs_to_es rvs ++ [:: AI_basic BI_return]) es /\
  empty_vs_base lh.
Proof.
  intros e es es'' ves rvs Hsplit H.
  apply split_vals_e_v_to_e_duality in Hsplit. subst es.
  destruct H as [[??] | [ln [les [es [i [lh [? [HLF Hbase]]]]]]]]; subst e.
  - subst rvs. unfold vs_to_es. rewrite revK.
    exists 0, (LH_base [::] es'').
    split => //.
    apply/lfilledP. solve_lfilled. by rewrite <- catA.
  - exists (i.+1), (LH_rec (v_to_e_list ves) ln les lh es'').
    replace (AI_label ln les es :: es'') with ([:: AI_label ln les es] ++ es'') => //.
    split => //.
    by apply LfilledRec => //; apply v_to_e_is_const_list.
Qed.

Lemma reduce_rec : forall (hs hs' : host_state) s s' f f' e es es' es'' ves res,
  es' = e :: es'' ->
  split_vals_e es = (ves, es') ->
  reduce hs s f (vs_to_es (rev ves) ++ [:: e]) hs' s' f' res ->
  reduce hs s f es hs' s' f' (res ++ es'').
Proof.
  intros hs hs' s s' f f' e es es' es'' ves res ?? Hreduce.
  assert (es = v_to_e_list ves ++ es'). { by apply split_vals_e_v_to_e_duality. }
  subst es es'.
  eapply r_label with (k := 0) (lh := (LH_base [::] es'')).
  - by apply Hreduce.
  - solve_lfilled. by rewrite <- catA.
  - by solve_lfilled.
Qed.

Lemma value_split_0 : forall es ves,
  split_vals_e es = (ves, [::]) ->
  const_list es \/ es_is_trap es.
Proof.
  intros es ves Hsplit. left.
  apply split_vals_e_v_to_e_duality in Hsplit. subst es.
  rewrite cats0. by apply v_to_e_is_const_list.
Qed.

Lemma reduce_trap : forall (hs : host_state) s f e es es'' ves,
  split_vals_e es = (ves, e :: es'') ->
  e_is_trap e ->
  (es'' != [::]) || (ves != [::]) ->
  reduce hs s f es hs s f [:: AI_trap].
Proof.
  intros hs s f e es es'' ves Hsplit Htrap Hesves.
  destruct e => //.
  apply split_vals_e_v_to_e_duality in Hsplit. subst es.
  move/orP in Hesves.
  apply r_simple. eapply rs_trap with (lh := LH_base (vs_to_es (rev ves)) es'');
    try by solve_lfilled.
  destruct Hesves as [Hes | Hves].
  - assert (size es'' > 0); first by destruct es'' => //.
    intros Hcontr. by size_unequal Hcontr.
  - assert (size ves > 0); first by destruct ves => //.
    intros Hcontr. by size_unequal Hcontr.
Qed.

Lemma value_trap : forall e es es'' ves,
  split_vals_e es = (ves, e :: es'') ->
  e_is_trap e ->
  ((es'' != [::]) || (ves != [::])) = false ->
  const_list es \/ es_is_trap es.
Proof.
  intros e es es'' ves Hsplit Htrap Hesves. right.
  apply split_vals_e_v_to_e_duality in Hsplit. subst es.
  rewrite <- negb_and in Hesves. move/andP in Hesves. destruct Hesves as [Hes Hves].
  move/eqP in Hes. move/eqP in Hves. subst es'' ves.
  by destruct e.
Qed.

Lemma split_vals_e_not_const : forall e es es'' ves,
  split_vals_e es = (ves, e :: es'') ->
  (is_const e) = false.
Proof.
  intros e es es'' ves. apply contraPF. intros Hconst Hsplit.
  assert (Hsplit' : split_vals_e es = (ves, e :: es'')). { by assumption. }
  apply split_vals_e_v_to_e_duality in Hsplit'. subst es.
  unfold is_const in Hconst.
  destruct e as [b| | | |] => //. destruct b => //.
  dependent induction ves.
  - replace (v_to_e_list [::] ++ AI_basic (BI_const v) :: es'')
      with (AI_basic (BI_const v) :: es'') in Hsplit;
      last by auto.
    simpl in Hsplit.
    destruct (split_vals_e es'') => //.
  - apply IHves => //.
    simpl in Hsplit.
    destruct (split_vals_e (v_to_e_list ves ++ AI_basic (BI_const v) :: es'')) => //.
    injection Hsplit as ??.
    by apply pair_equal_spec.
Qed.

Lemma reduce_unreachable : forall (hs : host_state) s f ves,
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic BI_unreachable])
    hs s f (vs_to_es ves ++ [:: AI_trap]).
Proof. intros. simpl_reduce_simple. by apply rs_unreachable. Qed.

(* TODO extend simpl_reduce_simple to handle this? *)
Lemma reduce_nop : forall (hs : host_state) s f ves,
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic BI_nop])
    hs s f (vs_to_es ves).
Proof.
  intros ??? ves.
  eapply r_label with
    (k := 0) (lh := (LH_base (vs_to_es ves) [::]))
    (es := [:: AI_basic BI_nop])
    (es' := [::]); try by solve_lfilled.
  apply r_simple. by apply rs_nop.
Qed.

Lemma reduce_drop : forall (hs : host_state) s f v ves',
  reduce
    hs s f (vs_to_es (v :: ves') ++ [:: AI_basic BI_drop])
    hs s f (vs_to_es ves').
Proof.
  intros ??? v ves'.
  eapply r_label with
    (k := 0) (lh := (LH_base (vs_to_es ves') [::]))
    (es := vs_to_es [:: v] ++ [:: AI_basic BI_drop])
    (es' := [::]); try by solve_lfilled.
  apply r_simple. by apply rs_drop.
Qed.

Lemma drop_error : forall s f ves,
  ves = [::] ->
  ~ fragment_typeable s f ves [:: AI_basic BI_drop].
Proof.
  intros s f ves Heqves [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply_cat0_inv Ht1s.
  apply Drop_typing in Hbtype as [??]. by destruct t2s.
Qed.

Lemma reduce_select_false : forall (hs : host_state) s f c v2 v1 ves',
  c == Wasm_int.int_zero i32m ->
  reduce
    hs s f (vs_to_es (VAL_int32 c :: v2 :: v1 :: ves') ++ [:: AI_basic BI_select])
    hs s f (vs_to_es (v2 :: ves')).
Proof.
  intros ??? c v2 v1 ves' Hc.
  replace (VAL_int32 c :: v2 :: v1 :: ves')
    with ([:: VAL_int32 c; v2; v1] ++ ves') => //.
  simpl_reduce_simple.
  apply rs_select_false.
  by apply/eqP.
Qed.

Lemma reduce_select_true : forall (hs : host_state) s f c v2 v1 ves',
  c != Wasm_int.int_zero i32m ->
  reduce
    hs s f (vs_to_es (VAL_int32 c :: v2 :: v1 :: ves') ++ [:: AI_basic BI_select])
    hs s f (vs_to_es (v1 :: ves')).
Proof.
  intros ??? c v2 v1 ves' Hc.
  replace (VAL_int32 c :: v2 :: v1 :: ves')
    with ([:: VAL_int32 c; v2; v1] ++ ves') => //.
  simpl_reduce_simple.
  apply rs_select_true.
  by apply/eqP.
Qed.

Lemma select_error_i32 : forall s f v3 v2 v1 ves ves',
  typeof v3 <> T_i32 ->
  ves = v3 :: v2 :: v1 :: ves' ->
  ~ fragment_typeable s f ves [:: AI_basic BI_select].
Proof.
  intros s f v3 v2 v1 ves ves' Hv Heqves [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Select_typing in Hbtype as [? [? [??]]]. subst t1s t2s.

  (* TODO move this into the ltac? *)
  replace ([:: x0; x0; T_i32]) with ([:: x0; x0] ++ [:: T_i32]) in Ht1s => //.
  by cats1_last_eq Ht1s.
Qed.

Lemma select_error_size : forall s f ves,
  size ves < 3 ->
  ~ fragment_typeable s f ves [:: AI_basic BI_select].
Proof.
  intros s f ves ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Select_typing in Hbtype as [ts [? [??]]].
  subst t1s t2s.
  by size_unequal Ht1s.
Qed.

Lemma reduce_block : forall (hs : host_state) s f ves ves' ves'' es t1s t2s m n,
  size ves >= size t1s ->
  n = size t1s ->
  m = size t2s ->
  (ves', ves'') = split_n ves n ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_block (Tf t1s t2s) es)])
    hs s f (vs_to_es ves'' ++ [::AI_label m [::] (vs_to_es ves' ++ to_e_list es)]).
Proof.
  intros ??? ves ves' ves'' es t1s t2s m n Hlen Heqn Heqm Hsplit.
  rewrite split_n_is_take_drop in Hsplit.
  injection Hsplit as Heqves' Heqves''.
  replace ves with (ves' ++ ves''); last by subst ves' ves''; rewrite cat_take_drop.
  eapply r_label with
    (k := 0) (lh := (LH_base (vs_to_es ves'') [::])).
  apply r_simple.
  eapply rs_block
    with (vs := vs_to_es ves') (t1s := t1s) => //.
  - by apply v_to_e_is_const_list.
  - repeat rewrite length_is_size.
    simpl_vs_to_es_size.
    (* TODO ltac for this? *)
    rewrite Heqves'. rewrite <- Heqn.
    rewrite size_take.
    (* TODO put symmetry into the ltac? *)
    by symmetry; if_lias.
  - by solve_lfilled.
  - solve_lfilled. apply List.app_inj_tail_iff. by split; subst m.
Qed.

Lemma block_error : forall s f ves bt1s bt2s es,
  size ves < size bt1s ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_block (Tf bt1s bt2s) es)].
Proof.
  intros s f ves bt1s bt2s es ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Block_typing host_instance) in Hbtype as [ts [? [??]]] => //.
  subst t1s. by size_unequal Ht1s.
Qed.

Lemma reduce_loop : forall (hs : host_state) s f ves ves' ves'' t1s t2s es,
  size t1s <= size ves ->
  split_n ves (length t1s) = (ves', ves'') ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_loop (Tf t1s t2s) es)])
    hs s f (vs_to_es ves'' ++ [:: AI_label
      (length t1s)
      [:: AI_basic (BI_loop (Tf t1s t2s) es)]
      (vs_to_es ves' ++ to_e_list es)
    ]).
Proof.
  intros hs s f ves ves' ves'' t1s t2s es Hlen Hsplit.
  rewrite split_n_is_take_drop in Hsplit.
  injection Hsplit as Hsplit' Hsplit''.
  assert (Hlen' : size t1s = size ves').
  {
    subst ves'. rewrite size_take. rewrite length_is_size.
    by symmetry; if_lias.
  }
  eapply r_label with
    (k := 0) (lh := (LH_base (vs_to_es ves'') [::])).
  - apply r_simple.
    eapply rs_loop with (vs := vs_to_es ves') (t1s := t1s) (t2s := t2s) (es := es) => //.
    * by apply v_to_e_is_const_list.
    * unfold vs_to_es.
      repeat rewrite length_is_size.
      rewrite v_to_e_size.
      by rewrite size_rev.
  - solve_lfilled.
    replace (v_to_e_list (rev ves))
      with (v_to_e_list (rev ves'') ++ v_to_e_list (rev ves')).
    * by rewrite <- catA.
    * rewrite <- (cat_take_drop (length t1s) ves).
      repeat rewrite v_to_e_rev.
      rewrite <- v_to_e_cat.
      rewrite <- rev_cat.
      by subst ves' ves''.
  - solve_lfilled. by rewrite Hlen'.
Qed.

Lemma loop_error : forall s f ves lt1s lt2s es,
  size lt1s > size ves ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_loop (Tf lt1s lt2s) es)].
Proof.
  intros s f ves lt1s lt2s es Hlen [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Loop_typing host_instance) in Hbtype as [ts [? [??]]] => //.
  subst t1s t2s. by size_unequal Ht1s.
Qed.

Lemma reduce_if_false : forall (hs : host_state) s f c ves ves' tf es1 es2,
  ves = VAL_int32 c :: ves' ->
  c == Wasm_int.int_zero i32m ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_if tf es1 es2)])
    hs s f (vs_to_es ves' ++ [:: AI_basic (BI_block tf es2)]).
Proof.
  intros hs s f c ves ves' tf es1 es2 ? Heqc. subst ves.
  eapply r_label with
    (k := 0) (lh := (LH_base (vs_to_es ves') [::])).
  - apply r_simple. by apply rs_if_false.
  - solve_lfilled.
    replace c with (Wasm_int.int_zero i32m) => //.
    symmetry. by apply/eqP.
  - by solve_lfilled.
Qed.

Lemma reduce_if_true : forall (hs : host_state) s f c ves ves' tf es1 es2,
  ves = VAL_int32 c :: ves' ->
  (c == Wasm_int.int_zero i32m) = false ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_if tf es1 es2)])
    hs s f (vs_to_es ves' ++ [:: AI_basic (BI_block tf es1)]).
Proof.
  intros hs s f c ves ves' tf es1 es2 ? Heqc. subst ves.
  eapply r_label with
    (k := 0) (lh := (LH_base (vs_to_es ves') [::]));
    try by solve_lfilled.
  apply r_simple. apply rs_if_true with (n := c).
  apply/eqP. by lias.
Qed.

Lemma if_error_0 : forall s f ves tf es1 es2,
  ves = [::] ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_if tf es1 es2)].
Proof.
  intros s f ves tf es1 es2 ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves. destruct tf.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply If_typing in Hbtype as [? [? [? [??]]]]. subst t1s.
  by size_unequal Ht1s.
Qed.

Lemma if_error_typeof : forall s f v ves ves' tf es1 es2,
  typeof v <> T_i32 ->
  ves = v :: ves' ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_if tf es1 es2)].
Proof.
  intros s f v ves ves' tf es1 es2 ?? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves. destruct tf.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply If_typing in Hbtype as [? [? [? [??]]]]. subst t1s.
  by cats1_last_eq Ht1s.
Qed.

Lemma break_br : forall j ves,
  exists (i j' : nat) (lh : lholed),
    i + j = j' /\
    lfilledInd i lh
      (vs_to_es ves ++ [:: AI_basic (BI_br j')])
      (vs_to_es ves ++ [:: AI_basic (BI_br j)]) /\
    empty_vs_base lh.
Proof.
  intros j ves.
  exists 0, j, (LH_base [::] [::]).
  repeat split => //.
  replace (vs_to_es ves ++ [:: AI_basic (BI_br j)])
    with ([::] ++ (vs_to_es ves ++ [:: AI_basic (BI_br j)]) ++ [::]) at 2;
    last by rewrite <- catA.
  by apply LfilledBase => //.
Qed.

Lemma reduce_br_if_true : forall (hs : host_state) s f c ves' j,
  c != Wasm_int.int_zero i32m ->
  reduce
    hs s f (vs_to_es (VAL_int32 c :: ves') ++ [:: AI_basic (BI_br_if j)])
    hs s f (vs_to_es ves' ++ [:: AI_basic (BI_br j)]).
Proof.
  intros ??? c ves' j ?.
  apply r_label with
    (k := 0) (lh := (LH_base (vs_to_es ves') [::]))
    (es := vs_to_es [::VAL_int32 c] ++ [:: AI_basic (BI_br_if j)])
    (es' := [:: AI_basic (BI_br j)]);
    try by solve_lfilled.
  apply r_simple. apply rs_br_if_true. by apply/eqP.
Qed.

Lemma reduce_br_if_false : forall (hs : host_state) s f c ves' j,
  c == Wasm_int.int_zero i32m ->
  reduce
    hs s f (vs_to_es (VAL_int32 c :: ves') ++ [:: AI_basic (BI_br_if j)])
    hs s f (vs_to_es ves').
Proof.
  intros ??? c ves' j ?.
  (* TODO make simpl_reduce_simple applicable? *)
  eapply r_label with
    (k := 0) (lh := (LH_base (vs_to_es ves') [::]))
    (es := vs_to_es [::VAL_int32 c] ++ [:: AI_basic (BI_br_if j)])
    (es' := [::]);
    try by solve_lfilled.
  apply r_simple. apply rs_br_if_false. by apply/eqP.
Qed.

Lemma br_if_error_0 : forall s f ves j,
  ves = [::] ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_br_if j)].
Proof.
  intros s f ves j ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Br_if_typing in Hbtype as [ts [ts' [? [? [??]]]]]. subst t1s t2s.
  by apply_cat0_inv Ht1s.
Qed.

Lemma br_if_error_i32 : forall s f v ves ves' j,
  typeof v <> T_i32 ->
  ves = v :: ves' ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_br_if j)].
Proof.
  intros s f v ves ves' j ?? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Br_if_typing in Hbtype as [? [? [? [? [??]]]]]. subst t1s t2s.
  by cats1_last_eq Ht1s.
Qed.

Lemma reduce_br_table : forall (hs : host_state) s f c ves' k j js js_at_k,
  k = Wasm_int.nat_of_uint i32m c ->
  k < length js ->
  List.nth_error js k = Some js_at_k ->
  reduce
    hs s f (vs_to_es (VAL_int32 c :: ves') ++ [:: AI_basic (BI_br_table js j)])
    hs s f (vs_to_es ves' ++ [:: AI_basic (BI_br js_at_k)]).
Proof.
  intros ??? c ves' k j js js_at_k ???. subst k.
  eapply r_label with
    (k := 0) (lh := (LH_base (vs_to_es ves') [::]));
    try by by solve_lfilled.
  apply r_simple. by apply rs_br_table.
Qed.

Lemma reduce_br_table_length : forall (hs : host_state) s f c ves' k j js,
  k = Wasm_int.nat_of_uint i32m c ->
  k >= length js ->
  reduce
    hs s f (vs_to_es (VAL_int32 c :: ves') ++ [:: AI_basic (BI_br_table js j)])
    hs s f (vs_to_es ves' ++ [:: AI_basic (BI_br j)]).
Proof.
  intros ??? c ves' k j js ??. subst k.
  eapply r_label with
    (k := 0) (lh := (LH_base (vs_to_es ves') [::]));
    try by solve_lfilled.
  apply r_simple. by apply rs_br_table_length.
Qed.

Lemma br_table_error_0 : forall s f ves js j,
  ves = [::] ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_br_table js j)].
Proof.
  intros s f ves js j ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Br_table_typing in Hbtype as [ts [ts' [??]]]. subst t1s.
  by apply_cat0_inv Ht1s.
Qed.

Lemma br_table_error_kth : forall s f c ves ves' k js j,
  ves = VAL_int32 c :: ves' ->
  k = Wasm_int.nat_of_uint i32m c ->
  k < length js ->
  List.nth_error js k = None ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_br_table js j)].
Proof.
  intros s f c ves ves' k js j ??? Hkth [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves k.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Br_table_typing in Hbtype as [? [? [??]]]. subst t1s.
  apply List.nth_error_None in Hkth.
  by lias.
Qed.

Lemma br_table_error_i32 : forall s f v ves ves' js j,
  typeof v <> T_i32 ->
  ves = v :: ves' ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_br_table js j)].
Proof.
  intros s f v ves ves' js j ?? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Br_table_typing in Hbtype as [ts [ts' [??]]]. subst t1s.
  by cats1_last_eq Ht1s.
Qed.

Lemma reduce_call : forall (hs : host_state) s f ves j a,
  List.nth_error (inst_funcs f.(f_inst)) j = Some a ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_call j)])
    hs s f (vs_to_es ves ++ [:: AI_invoke a]).
Proof.
  intros hs s f ves j a ?.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves) [::]));
    try by solve_lfilled.
  apply r_call with (a := a) (i := j) => //.
Qed.

Lemma call_error : forall (hs : host_state) s f ves j,
  List.nth_error (inst_funcs f.(f_inst)) j = None ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_call j)].
Proof.
  intros s f v ves j Hjth [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [Hitype [? Hetype]]]]]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Call_typing host_instance) in Hbtype as [? [t1s'' [t2s'' [? [? [??]]]]]].
  apply func_context_store with (j := j) (x := Tf t1s'' t2s'') in Hitype
    as [? Hjth'] => //; try by subst C.
  by rewrite Hjth' in Hjth.
Qed.

Lemma reduce_call_indirect_success : forall (hs : host_state) s f c ves ves' j a cl,
  ves = VAL_int32 c :: ves' ->
  stab_addr s f (Wasm_int.nat_of_uint i32m c) = Some a ->
  List.nth_error s.(s_funcs) a = Some cl ->
  stypes s f.(f_inst) j == Some (cl_type cl) ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_call_indirect j)])
    hs s f (vs_to_es ves' ++ [:: AI_invoke a]).
Proof.
  intros hs s f c ves ves' j a cl ????. subst ves.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::]));
    try by solve_lfilled.
  apply r_call_indirect_success with (cl := cl) => //.
  by apply/eqP.
Qed.

Lemma reduce_call_indirect_failure_1 : forall (hs : host_state) s f c ves ves' j a cl,
  ves = VAL_int32 c :: ves' ->
  stab_addr s f (Wasm_int.nat_of_uint i32m c) = Some a ->
  List.nth_error s.(s_funcs) a = Some cl ->
  (stypes s f.(f_inst) j == Some (cl_type cl)) = false ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_call_indirect j)])
    hs s f (vs_to_es ves' ++ [:: AI_trap]).
Proof.
  intros hs s f c ves ves' j a cl ????. subst ves.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::]));
    try by solve_lfilled.
  eapply r_call_indirect_failure1 with (cl := cl) (a := a) => //.
  by apply/eqP; lias.
Qed.

Lemma reduce_call_indirect_failure_2 : forall (hs : host_state) s f c ves ves' j,
  ves = VAL_int32 c :: ves' ->
  stab_addr s f (Wasm_int.nat_of_uint i32m c) = None ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_call_indirect j)])
    hs s f (vs_to_es ves' ++ [:: AI_trap]).
Proof.
  intros hs s f c ves ves' j ??. subst ves.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::]));
    try by solve_lfilled.
  by apply r_call_indirect_failure2.
Qed.

Lemma call_indirect_error_0 : forall s f ves j,
  ves = [::] ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_call_indirect j)].
Proof.
  intros s f ves j ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]]. subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Call_indirect_typing host_instance) in Hbtype as [? [? [? [? [? [? [??]]]]]]].
  subst t1s. by size_unequal Ht1s.
Qed.

Lemma call_indirect_error_typeof : forall s f v ves ves' j,
  typeof v <> T_i32 ->
  ves = v :: ves' ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_call_indirect j)].
Proof.
  intros s f v ves ves' j Hv ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]]. subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Call_indirect_typing host_instance) in Hbtype as [? [? [? [? [? [? [??]]]]]]].
  subst t1s. by cats1_last_eq Ht1s.
Qed.

Lemma call_indirect_error_ath : forall s f c ves ves' j a,
  ves = VAL_int32 c :: ves' ->
  stab_addr s f (Wasm_int.nat_of_uint i32m c) = Some a ->
  List.nth_error s.(s_funcs) a = None ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_call_indirect j)].
Proof.
  intros s f c ves ves' j a ?? Hath [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [Hitype [? Hetype]]]]]]]]]]]. subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Call_indirect_typing host_instance) in Hbtype as [? [? [? [? [? [? [??]]]]]]].
  eapply store_typing_stabaddr with (a := a) (c := Wasm_int.nat_of_uint i32m c) in Hitype as [? Hath'] => //.
  by rewrite Hath in Hath'.
Qed.

Lemma reduce_get_local : forall (hs : host_state) s f ves j vs_at_j,
  j < length f.(f_locs) ->
  List.nth_error f.(f_locs) j = Some vs_at_j ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_get_local j)])
    hs s f (vs_to_es (vs_at_j :: ves)).
Proof.
  intros hs s f ves j vs_at_j ??.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves) [::])).
  - apply r_get_local with (j := j) (v := vs_at_j) => //.
  - by solve_lfilled.
  - by solve_lfilled.
Qed.

Lemma get_local_error_jth_none : forall s f ves j,
  List.nth_error f.(f_locs) j = None ->
  j < length f.(f_locs) ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_get_local j)].
Proof.
  (* TODO rename Hitype to Hitype everywhere *)
  intros s f ves j Hjth ? [C [C' [ret [lab [t1s [t2s [t1s' [? [? [? [? Hetype]]]]]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Get_local_typing host_instance) in Hbtype as [? [Hjth' [??]]].
  by apply List.nth_error_None in Hjth; lias.
Qed.

Lemma get_local_error_length : forall s f ves j,
  j >= length f.(f_locs) ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_get_local j)].
Proof.
  intros s f ves j Hlen [C [C' [ret [lab [t1s [t2s [t1s' [? [? [? [? Hetype]]]]]]]]]]].
  subst C.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Get_local_typing host_instance) in Hbtype as [? [? [? Hlen']]].
  by rewrite List.map_length in Hlen'; lias.
Qed.

Lemma reduce_set_local : forall (hs : host_state) s f f' v ves ves' j,
  ves = v :: ves' ->
  j < length f.(f_locs) ->
  f' = Build_frame (update_list_at f.(f_locs) j v) f.(f_inst) ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_set_local j)])
    hs s f' (vs_to_es ves').
Proof.
  intros hs s f f' v ves ves' j ???. subst ves f'.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::])).
  - apply r_set_local with (i := j) (v := v) (vd := v) => //.
    by rewrite update_list_at_is_set_nth => //.
  - by solve_lfilled.
  - by solve_lfilled.
Qed.

Lemma set_local_error_0 : forall (hs : host_state) s f ves j,
  ves = [::] ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_set_local j)].
Proof.
  intros hs s f ves j ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]]. subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply_cat0_inv Ht1s.
  apply (Set_local_typing host_instance) in Hbtype as [? [? [??]]].
  by destruct t2s => //.
Qed.

Lemma set_local_error_length : forall (hs : host_state) s f v ves ves' j,
  ves = v :: ves' ->
  (j < length f.(f_locs)) = false ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_set_local j)].
Proof.
  intros hs s f v ves ves' j ? Hlen [C [C' [ret [lab [t1s [t2s [t1s' [? [? [? [? Hetype]]]]]]]]]]].
  subst ves C.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Set_local_typing host_instance) in Hbtype as [? [? [? Hlen']]].
  by rewrite List.map_length in Hlen'; lias.
Qed.

Lemma reduce_tee_local : forall (hs : host_state) s f v ves ves' j,
  ves = v :: ves' ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_tee_local j)])
    hs s f (vs_to_es (v :: ves) ++ [:: AI_basic (BI_set_local j)]).
Proof.
  intros hs s f v ves ves' j ?.
  subst ves.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::])).
  - apply r_simple.
    by apply rs_tee_local with (i := j) (v := AI_basic (BI_const v)).
  - by solve_lfilled.
  - by solve_lfilled.
Qed.

Lemma tee_local_error_0 : forall (hs : host_state) s f ves j,
  ves = [::] ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_tee_local j)].
Proof.
  intros hs s f ves j ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]]. subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply_cat0_inv Ht1s.
  by apply Tee_local_typing in Hbtype as [[|] [? [? [? [??]]]]] => //.
Qed.

Lemma reduce_get_global : forall (hs : host_state) s f ves j xx,
  sglob_val s f.(f_inst) j = Some xx ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_get_global j)])
    hs s f (vs_to_es (xx :: ves)).
Proof.
  intros hs s f ves j xx Heqxx.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves) [::])).
  - by apply r_get_global with (i := j) (v := xx).
  - by solve_lfilled.
  - by solve_lfilled.
Qed.

Lemma get_global_error : forall (hs : host_state) s f ves j,
  sglob_val s f.(f_inst) j = None ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_get_global j)].
Proof.
  intros hs s f ves j Hjth [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [Hitype [? Hetype]]]]]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Get_global_typing host_instance) in Hbtype as [t [Hjth' [??]]].
  destruct (List.nth_error (tc_global C) j) eqn:Heqg; subst C => //.
  eapply glob_context_store with (j := j) in Hitype => //;
    last by (rewrite Heqg; f_equal).
  unfold sglob_val, option_map in Hjth.
  unfold sglob, option_bind in Hitype.
  by destruct (sglob s f.(f_inst) j) eqn:? => //.
Qed.

Lemma reduce_set_global : forall (hs : host_state) s s' f v ves ves' j,
  supdate_glob s f.(f_inst) j v = Some s' ->
  ves = v :: ves' ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_set_global j)])
    hs s' f (vs_to_es ves').
Proof.
  intros hs s s' f v ves ves' j Heqs' ?. subst ves.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::])).
  - by apply r_set_global with (i := j) (v := v).
  - by solve_lfilled.
  - by solve_lfilled.
Qed.

Lemma set_global_error_0 : forall (hs : host_state) s f ves j,
  ves = [::] ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_set_global j)].
Proof.
  intros hs s f ves j ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]]. subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply_cat0_inv Ht1s.
  apply (Set_global_typing host_instance) in Hbtype as [? [? [? [? [? [??]]]]]].
  by destruct t2s => //.
Qed.

Lemma set_global_error_jth : forall (hs : host_state) s f v ves ves' j,
  ves = v :: ves' ->
  supdate_glob s f.(f_inst) j v = None ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_set_global j)].
Proof.
  intros hs s f v ves ves' j ? Hjth [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [Hitype [? Hetype]]]]]]]]]]].
  subst ves C.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Set_global_typing host_instance) in Hbtype as [g [? [Hjth' [? [? [??]]]]]].
  apply glob_context_store with (j := j) (g := g) in Hitype => //.
  unfold sglob in Hitype. unfold option_bind in Hitype.
  unfold supdate_glob in Hjth. unfold option_bind in Hjth.
  destruct (sglob_ind s f.(f_inst) j) eqn:? => //.
  unfold supdate_glob_s in Hjth.
  by destruct (List.nth_error (s_globals s) n).
Qed.

Lemma reduce_load_packed_success : forall (hs : host_state) s f c ves ves' t tp sx a off j mem_s_j bs,
  ves = VAL_int32 c :: ves' ->
  smem_ind s f.(f_inst) = Some j ->
  List.nth_error s.(s_mems) j = Some mem_s_j ->
  load_packed sx (mem_s_j) (Wasm_int.N_of_uint i32m c) off (tp_length tp) (t_length t) = Some bs ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_load t (Some (tp, sx)) a off)])
    hs s f (vs_to_es (wasm_deserialise bs t :: ves')).
Proof.
  intros hs s f c ves ves' t tp sx a off j mem_s_j bs ????. subst ves.
  (* XXX make this into an ltac? (selecting the LH_base) *)
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::]));
    try by solve_lfilled.
  by apply r_load_packed_success with (i := j) (m := mem_s_j).
Qed.

Lemma reduce_load_packed_failure : forall (hs : host_state) s f c ves ves' t tp sx a off j mem_s_j,
  ves = VAL_int32 c :: ves' ->
  smem_ind s f.(f_inst) = Some j ->
  List.nth_error s.(s_mems) j = Some mem_s_j ->
  load_packed sx (mem_s_j) (Wasm_int.N_of_uint i32m c) off (tp_length tp) (t_length t) = None ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_load t (Some (tp, sx)) a off)])
    hs s f (vs_to_es ves' ++ [:: AI_trap]).
Proof.
  intros hs s f c ves ves' t tp sx a off j mem_s_j ????. subst ves.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::]));
    try by solve_lfilled.
  by apply r_load_packed_failure with (i := j) (m := mem_s_j).
Qed.

Lemma reduce_load_success : forall (hs : host_state) s f c ves ves' t a off j mem_s_j bs,
  ves = VAL_int32 c :: ves' ->
  smem_ind s f.(f_inst) = Some j ->
  List.nth_error s.(s_mems) j = Some mem_s_j ->
  load (mem_s_j) (Wasm_int.N_of_uint i32m c) off (t_length t) = Some bs ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_load t None a off)])
    hs s f (vs_to_es (wasm_deserialise bs t :: ves')).
Proof.
  intros hs s f c ves ves' t a off j mem_s_j bs ????. subst ves.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::]));
    try by solve_lfilled.
  by apply r_load_success
    with (i := j) (m := mem_s_j) (bs := bs) (k := c) (off := off) (t := t).
Qed.

Lemma reduce_load_failure : forall (hs : host_state) s f c ves ves' t a off j mem_s_j,
  ves = VAL_int32 c :: ves' ->
  smem_ind s f.(f_inst) = Some j ->
  List.nth_error s.(s_mems) j = Some mem_s_j ->
  load (mem_s_j) (Wasm_int.N_of_uint i32m c) off (t_length t) = None ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_load t None a off)])
    hs s f (vs_to_es ves' ++ [:: AI_trap]).
Proof.
  intros hs s f c ves ves' t a off j mem_s_j ????. subst ves.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::]));
    try by solve_lfilled.
  by apply r_load_failure with (i := j) (m := mem_s_j).
Qed.

Lemma load_error_0 : forall s f ves t tp_sx a off,
  ves = [::] ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_load t tp_sx a off)].
Proof.
  intros s f ves t tp_sx a off ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves. apply_cat0_inv Ht1s.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  by apply (Load_typing host_instance) in Hbtype as [[|] [? [? [??]]]].
Qed.

Lemma load_error_typeof : forall s f v ves ves' t tp_sx a off,
  typeof v <> T_i32 ->
  ves = v :: ves' ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_load t tp_sx a off)].
Proof.
  intros s f v ves ves' t tp_sx a off Hv ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Load_typing host_instance) in Hbtype as [? [? [? [??]]]]. subst t1s t2s.
  by cats1_last_eq Ht1s.
Qed.

Lemma load_error_jth : forall s f ves ves' c t tp_sx a off j,
  ves = VAL_int32 c :: ves' ->
  smem_ind s f.(f_inst) = Some j ->
  List.nth_error s.(s_mems) j = None ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_load t tp_sx a off)].
Proof.
  intros s f ves ves' c t tp_sx a off j ? Hsmem Hjth [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [Hitype [? Hetype]]]]]]]]]]].
  subst ves C.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Load_typing host_instance) in Hbtype as [? [? [? [??]]]].
  apply mem_context_store in Hitype as [j' [Hsmem' Hjth']] => //.
  rewrite Hsmem in Hsmem'. injection Hsmem' as Hsmem'. subst j'.
  by apply Hjth'.
Qed.

Lemma load_error_smem_ind : forall s f ves ves' c t tp_sx a off,
  ves = VAL_int32 c :: ves' ->
  smem_ind s f.(f_inst) = None ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_load t tp_sx a off)].
Proof.
  intros s f ves ves' c t tp_sx a off ? Hsmem [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [Hitype [? Hetype]]]]]]]]]]].
  subst ves C.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Load_typing host_instance) in Hbtype as [? [? [? [??]]]].
  apply mem_context_store in Hitype as [? [Hsmem' ?]] => //.
  by rewrite Hsmem' in Hsmem.
Qed.

Lemma reduce_store_packed_success : forall (hs : host_state) s f c v ves ves' t tp a off j mem_s_j mem',
  ves = v :: VAL_int32 c :: ves' ->
  types_agree t v ->
  smem_ind s f.(f_inst) = Some j ->
  List.nth_error s.(s_mems) j = Some mem_s_j ->
  store_packed mem_s_j (Wasm_int.N_of_uint i32m c) off (bits v) (tp_length tp) = Some mem' ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_store t (Some tp) a off)])
    hs (upd_s_mem s (update_list_at s.(s_mems) j mem')) f (vs_to_es ves').
Proof.
  intros hs s f c v ves ves' t tp a off j mem_s_j mem' ?????. subst ves.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::])).
  - by apply r_store_packed_success
      with (m := mem_s_j) (k := c) (off := off) (t := t) (v := v) (tp := tp).
  - by solve_lfilled.
  - by solve_lfilled.
Qed.

Lemma reduce_store_packed_failure : forall (hs : host_state) s f c v ves ves' t tp a off j mem_s_j,
  ves = v :: VAL_int32 c :: ves' ->
  types_agree t v ->
  smem_ind s f.(f_inst) = Some j ->
  List.nth_error s.(s_mems) j = Some mem_s_j ->
  store_packed mem_s_j (Wasm_int.N_of_uint i32m c) off (bits v) (tp_length tp) = None ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_store t (Some tp) a off)])
    hs s f (vs_to_es ves' ++ [:: AI_trap]).
Proof.
  intros hs s f c v ves ves' t tp a off j mem_s_j ?????. subst ves.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::]));
    try by solve_lfilled.
  by apply r_store_packed_failure with (i := j) (m := mem_s_j).
Qed.

Lemma reduce_store_success : forall (hs : host_state) s f c v ves ves' t a off j mem_s_j mem',
  ves = v :: VAL_int32 c :: ves' ->
  types_agree t v ->
  smem_ind s f.(f_inst) = Some j ->
  List.nth_error s.(s_mems) j = Some mem_s_j ->
  store mem_s_j (Wasm_int.N_of_uint i32m c) off (bits v) (t_length t) = Some mem' ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_store t None a off)])
    hs (upd_s_mem s (update_list_at s.(s_mems) j mem')) f (vs_to_es ves').
Proof.
  intros hs s f c v ves ves' t a off j mem_s_j mem' ?????. subst ves.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::])).
  - by apply r_store_success
      with (m := mem_s_j) (k := c) (off := off) (t := t) (v := v).
  - by solve_lfilled.
  - by solve_lfilled.
Qed.

Lemma reduce_store_failure : forall (hs : host_state) s f c v ves ves' t a off j mem_s_j,
  ves = v :: VAL_int32 c :: ves' ->
  types_agree t v ->
  smem_ind s f.(f_inst) = Some j ->
  List.nth_error s.(s_mems) j = Some mem_s_j ->
  store mem_s_j (Wasm_int.N_of_uint i32m c) off (bits v) (t_length t) = None ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic (BI_store t None a off)])
    hs s f (vs_to_es ves' ++ [:: AI_trap]).
Proof.
  intros hs s f c v ves ves' t a off j mem_s_j ?????. subst ves.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::]));
    try by solve_lfilled.
  by apply r_store_failure
    with (i := j) (m := mem_s_j) (k := c) (off := off) (t := t) (v := v).
Qed.

Lemma store_error_size : forall s f ves t tp a off,
  size ves < 2 ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_store t tp a off)].
Proof.
  intros s f ves t tp a off ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Store_typing host_instance) in Hbtype as [? [??]].
  subst t1s. by size_unequal Ht1s.
Qed.

Lemma store_error_typeof : forall s f v v' ves ves' t tp a off,
  ves = v :: v' :: ves' ->
  typeof v' <> T_i32 ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_store t tp a off)].
Proof.
  intros s f v v' ves ves' t tp a off ?? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Store_typing host_instance) in Hbtype as [? [??]].
  subst t1s.
  (* TODO move this into the ltac? *)
  replace [:: T_i32; t] with ([:: T_i32] ++ [:: t]) in Ht1s => //.
  by repeat cats1_last_eq Ht1s.
Qed.

Lemma store_error_types_disagree : forall s f v c ves ves' t tp a off,
  ves = v :: VAL_int32 c :: ves' ->
  types_agree t v = false ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_store t tp a off)].
Proof.
  intros s f v c ves ves' t tp a off ?? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Store_typing host_instance) in Hbtype as [? [??]].
  subst t1s.
  replace [:: T_i32; t] with ([:: T_i32] ++ [:: t]) in Ht1s => //.
  cats1_last_eq Ht1s. by destruct v, t => //.
Qed.

Lemma store_error_jth : forall s f v c ves ves' t tp a off j,
  ves = v :: VAL_int32 c :: ves' ->
  types_agree t v ->
  smem_ind s f.(f_inst) = Some j ->
  List.nth_error s.(s_mems) j = None ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_store t tp a off)].
Proof.
  intros s f v c ves ves' t tp a off j ?? Hsmem ?
    [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [Hitype [? Hetype]]]]]]]]]]].
  subst ves C.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Store_typing host_instance) in Hbtype as [? [??]].
  apply mem_context_store in Hitype as [j' [Hsmem' Hjth']] => //.
  (* TODO this repeats elsewhere -- make a lemma / ltac? *)
  rewrite Hsmem in Hsmem'. injection Hsmem' as Hsmem'. subst j'.
  by apply Hjth'.
Qed.

Lemma store_error_smem : forall s f v c ves ves' t tp a off,
  ves = v :: VAL_int32 c :: ves' ->
  types_agree t v ->
  smem_ind s f.(f_inst) = None ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_store t tp a off)].
Proof.
  intros s f v c ves ves' t tp a off ?? Hsmem [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [Hitype [? Hetype]]]]]]]]]]].
  subst ves C.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Store_typing host_instance) in Hbtype as [? [??]].
  apply mem_context_store in Hitype as [? [Hsmem' ?]] => //.
  by rewrite Hsmem in Hsmem'.
Qed.

Lemma reduce_current_memory : forall (hs : host_state) s f v ves s_mem_s_j j,
  smem_ind s f.(f_inst) = Some j ->
  List.nth_error (s_mems s) j = Some s_mem_s_j ->
  v = VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j))) ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic BI_current_memory])
    hs s f (vs_to_es (v :: ves)).
Proof.
  intros hs s f v ves s_mem_s_j j ???. subst v.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves) [::]));
    try by solve_lfilled.
  (* TODO rename s_mem_s_j to m? *)
  by apply r_current_memory with (i := j) (m := s_mem_s_j).
Qed.

Lemma current_memory_error_jth : forall s f ves j,
  smem_ind s f.(f_inst) = Some j ->
  List.nth_error (s_mems s) j = None ->
  ~ fragment_typeable s f ves [:: AI_basic BI_current_memory].
Proof.
  intros s f ves j Hsmem ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [Hitype [? Hetype]]]]]]]]]]].
  subst C.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Current_memory_typing host_instance) in Hbtype as [??] => //.
  apply mem_context_store in Hitype as [j' [Hsmem' Hjth]] => //.
  rewrite Hsmem' in Hsmem. injection Hsmem as Hsmem. subst j'.
  by apply Hjth.
Qed.

Lemma current_memory_error_smem : forall s f ves,
  smem_ind s f.(f_inst) = None ->
  ~ fragment_typeable s f ves [:: AI_basic BI_current_memory].
Proof.
  intros s f ves Hsmem [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [Hitype [? Hetype]]]]]]]]]]].
  subst C.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Current_memory_typing host_instance) in Hbtype as [??] => //.
  apply mem_context_store in Hitype as [? [Hsmem' ?]] => //.
  by rewrite Hsmem' in Hsmem.
Qed.

(* TODO extend simpl_reduce_simple to handle this? *)
Lemma reduce_grow_memory : forall (hs : host_state) s s' f c v ves' mem'' s_mem_s_j j l,
  smem_ind s f.(f_inst) = Some j ->
  List.nth_error (s_mems s) j = Some s_mem_s_j ->
  l = mem_size s_mem_s_j ->
  Some mem'' = mem_grow s_mem_s_j (Wasm_int.N_of_uint i32m c) ->
  s' = upd_s_mem s (update_list_at (s_mems s) j mem'') ->
  v = VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat l)) ->
  reduce
    hs s f (vs_to_es (VAL_int32 c :: ves') ++ [:: AI_basic BI_grow_memory])
    hs s' f (vs_to_es (v :: ves')).
Proof.
  intros hs s s' f c v ves' mem'' s_mem_s_j j l ??????. subst s' v l.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::]));
    try by solve_lfilled.
  by apply r_grow_memory_success with (m := s_mem_s_j) (c := c).
Qed.

Lemma reduce_grow_memory_failure : forall (hs : host_state) s f c ves' s_mem_s_j j l,
  smem_ind s f.(f_inst) = Some j ->
  List.nth_error (s_mems s) j = Some s_mem_s_j ->
  l = mem_size s_mem_s_j ->
  mem_grow s_mem_s_j (Wasm_int.N_of_uint i32m c) = None ->
  reduce
    hs s f (vs_to_es (VAL_int32 c :: ves') ++ [:: AI_basic BI_grow_memory])
    hs s f (vs_to_es (VAL_int32 int32_minus_one :: ves')).
Proof.
  intros hs s f c ves' s_mem_s_j j l ????. subst l.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::]));
    try by solve_lfilled.
  by eapply r_grow_memory_failure with (m := s_mem_s_j) (i := j).
Qed.

Lemma grow_memory_error_0 : forall s f ves,
  ves = [::] ->
  ~ fragment_typeable s f ves [:: AI_basic BI_grow_memory].
Proof.
  intros s f ves ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply_cat0_inv Ht1s.
  (* XXX why is host_instance needed for Grow_memory_typing
   * and not for Binop_typing etc? *)
  by apply (Grow_memory_typing host_instance) in Hbtype as [[|] [? [??]]].
Qed.

Lemma grow_memory_error_jth : forall s f ves ves' j c,
  ves = VAL_int32 c :: ves' ->
  smem_ind s f.(f_inst) = Some j ->
  List.nth_error (s_mems s) j = None ->
  ~ fragment_typeable s f ves [:: AI_basic BI_grow_memory].
Proof.
  intros s f ves ves' j c ? Hsmem ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [Hitype [? Hetype]]]]]]]]]]].
  subst ves C.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Grow_memory_typing host_instance) in Hbtype as [? [? [??]]] => //.
  apply mem_context_store in Hitype as [j' [Hsmem' Hjth]] => //.
  rewrite Hsmem' in Hsmem. injection Hsmem as Hsmem. subst j'.
  by apply Hjth.
Qed.

Lemma grow_memory_error_smem : forall s f ves ves' c,
  ves = VAL_int32 c :: ves' ->
  smem_ind s f.(f_inst) = None ->
  ~ fragment_typeable s f ves [:: AI_basic BI_grow_memory].
Proof.
  intros s f ves ves' c ? Hsmem [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [Hitype [? Hetype]]]]]]]]]]].
  subst ves C.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Grow_memory_typing host_instance) in Hbtype as [? [? [??]]] => //.
  apply mem_context_store in Hitype as [? [Hsmem' ?]] => //.
  by rewrite Hsmem' in Hsmem.
Qed.

Lemma grow_memory_error_typeof : forall s f v ves ves',
  typeof v <> T_i32 ->
  ves = v :: ves' ->
  ~ fragment_typeable s f ves [:: AI_basic BI_grow_memory].
Proof.
  intros s f v ves ves' Hv Heqves [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves C.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Grow_memory_typing host_instance) in Hbtype as [? [? [??]]] => //. subst t1s t2s.
  by cats1_last_eq Ht1s.
Qed.

Lemma reduce_unop : forall (hs : host_state) s f t op v ves',
  reduce
    hs s f (vs_to_es (v :: ves') ++ [:: AI_basic (BI_unop t op)])
    hs s f (vs_to_es (app_unop op v :: ves')).
Proof. intros. simpl_reduce_simple. by apply rs_unop. Qed.

Lemma unop_error : forall s f ves t op,
  ves = [::] ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_unop t op)].
Proof.
  intros s f ves t op Heqves [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply_cat0_inv Ht1s.
  by apply Unop_typing in Hbtype as [? [[|] ?]].
Qed.

Lemma reduce_binop : forall (hs : host_state) s f t op v1 v2 v ves',
  app_binop op v1 v2 = Some v ->
  reduce
    hs s f (vs_to_es ([:: v2; v1] ++ ves') ++ [:: AI_basic (BI_binop t op)])
    hs s f (vs_to_es (v :: ves')).
Proof. intros. simpl_reduce_simple. by apply rs_binop_success. Qed.

(* XXX why is there a rule for this? shouldn't happen in a well typed
 * configuration *)
Lemma reduce_binop_trap : forall (hs : host_state) s f t op v1 v2 ves',
  app_binop op v1 v2 = None ->
  reduce
    hs s f (vs_to_es ([:: v2; v1] ++ ves') ++ [:: AI_basic (BI_binop t op)])
    hs s f (vs_to_es ves' ++ [:: AI_trap]).
Proof. intros. simpl_reduce_simple. by apply rs_binop_failure. Qed.

Lemma binop_error_size : forall s f ves t op,
  size ves < 2 ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_binop t op)].
Proof.
  intros s f ves t op ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Binop_typing in Hbtype as [? [ts' ?]].
  subst t1s t2s.
  by size_unequal Ht1s.
Qed.

(* 0 arguments given to testop *)
Lemma testop_error_0 : forall s f ves t testop,
  ves = [::] ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_testop t testop)].
Proof.
  intros s f ves t testop ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply_cat0_inv Ht1s.
  by apply Testop_typing in Hbtype as [[|] [??]].
Qed.

Lemma reduce_testop_i32 : forall (hs : host_state) s f ves' c testop,
  reduce
    hs s f (vs_to_es (VAL_int32 c :: ves') ++ [:: AI_basic (BI_testop T_i32 testop)])
    hs s f (vs_to_es (VAL_int32 (wasm_bool (app_testop_i testop c)) :: ves')).
Proof. intros. simpl_reduce_simple. by apply rs_testop_i32. Qed.

Lemma testop_i32_error : forall s f v ves ves' testop,
  typeof v <> T_i32 ->
  ves = v :: ves' ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_testop T_i32 testop)].
Proof.
  intros s f v ves ves' testop ?? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Testop_typing in Hbtype as [? [ts' ?]].
  subst ves t1s t2s.
  by cats1_last_eq Ht1s.
Qed.

Lemma reduce_testop_i64 : forall (hs : host_state) s f ves' c testop,
  reduce
    hs s f (vs_to_es (VAL_int64 c :: ves') ++ [:: AI_basic (BI_testop T_i64 testop)])
    hs s f (vs_to_es (VAL_int32 (wasm_bool (app_testop_i testop c)) :: ves')).
Proof. intros. simpl_reduce_simple. by apply rs_testop_i64. Qed.

Lemma testop_i64_error : forall s f v ves ves' testop,
  typeof v <> T_i64 ->
  ves = v :: ves' ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_testop T_i64 testop)].
Proof.
  intros s f v ves ves' testop ?? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Testop_typing in Hbtype as [? [ts' ?]].
  subst ves t1s t2s.
  by cats1_last_eq Ht1s.
Qed.

(* TODO dedupe testop_*_error *)
Lemma testop_f32_error : forall s f ves testop,
  ~ fragment_typeable s f ves [:: AI_basic (BI_testop T_f32 testop)].
Proof.
  intros s f ves testop [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Testop_typing_is_int_t in Hbtype => //.
Qed.

Lemma testop_f64_error : forall s f ves testop,
  ~ fragment_typeable s f ves [:: AI_basic (BI_testop T_f64 testop)].
Proof.
  intros s f ves testop [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Testop_typing_is_int_t in Hbtype => //.
Qed.

Lemma reduce_relop : forall (hs : host_state) s f t op v1 v2 ves',
  reduce
    hs s f (vs_to_es ([:: v2; v1] ++ ves') ++ [:: AI_basic (BI_relop t op)])
    hs s f (vs_to_es (VAL_int32 (wasm_bool (app_relop op v1 v2)) :: ves')).
Proof. intros. simpl_reduce_simple. by apply rs_relop. Qed.

Lemma relop_error_size : forall s f ves t op,
  size ves < 2 ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_relop t op)].
Proof.
  intros s f ves t op ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Relop_typing in Hbtype as [? [??]]. subst t1s t2s.
  by size_unequal Ht1s.
Qed.

(* TODO rename this and following lemmas from cvtop to convert *)
Lemma reduce_cvtop_success : forall (hs : host_state) s f t1 t2 sx v v' ves',
  types_agree t1 v ->
  cvt t2 sx v = Some v' ->
  reduce
    hs s f (vs_to_es (v :: ves') ++ [:: AI_basic (BI_cvtop t2 CVO_convert t1 sx)])
    hs s f (vs_to_es (v' :: ves')).
Proof.
  intros hs s f t1 t2 sx v v' ves' ??.
  simpl_reduce_simple.
  by apply rs_convert_success with (t1 := t1) (t2 := t2) (v := v) (v' := v') (sx := sx).
Qed.

Lemma reduce_cvtop_trap : forall (hs : host_state) s f t1 t2 sx v ves',
  types_agree t1 v ->
  cvt t2 sx v = None ->
  reduce
    hs s f (vs_to_es (v :: ves') ++ [:: AI_basic (BI_cvtop t2 CVO_convert t1 sx)])
    hs s f (vs_to_es ves' ++ [::AI_trap]).
Proof.
  intros hs s f t1 t2 sx v ves' ??.
  simpl_reduce_simple.
  by apply rs_convert_failure with (t1 := t1) (t2 := t2) (v := v) (sx := sx).
Qed.

Lemma cvtop_error_0 : forall s f ves t1 t2 cvtop sx,
  ves = [::] ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_cvtop t2 cvtop t1 sx)].
Proof.
  intros s f ves t1 t2 cvtop sx ? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply_cat0_inv Ht1s.
  by apply Cvtop_typing in Hbtype as [[|] [??]].
Qed.

Lemma cvtop_error_types_disagree : forall s f v ves ves' t1 t2 cvtop sx,
  ves = v :: ves' ->
  types_agree t1 v = false ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_cvtop t2 cvtop t1 sx)].
Proof.
  intros s f v ves ves' t1 t2 cvtop sx ? Hdisagree [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Cvtop_typing in Hbtype as [? [??]].
  subst t1s. cats1_last_eq Ht1s.
  unfold types_agree in Hdisagree.
  destruct (typeof v == t1) eqn:Hv => //.
  assert (Hv' : typeof v <> t1). { apply/eqP. by rewrite Hv. } by apply Hv'.
Qed.

Lemma cvtop_error_reinterpret_sx : forall s f v ves ves' t1 t2 sx,
  ves = v :: ves' ->
  types_agree t1 v = true ->
  ~ fragment_typeable s f ves [:: AI_basic (BI_cvtop t2 CVO_reinterpret t1 (Some sx))].
Proof.
  intros s f v ves ves' t1 t2 sx ?? [C [C' [ret [lab [t1s [t2s [t1s' [? [Ht1s [? [? Hetype]]]]]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  by apply Cvtop_reinterpret_typing in Hbtype.
Qed.

Lemma reduce_reinterpret : forall (hs : host_state) s f t1 t2 v ves',
  types_agree t1 v ->
  reduce
    hs s f (vs_to_es (v :: ves') ++ [:: AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)])
    hs s f (vs_to_es (wasm_deserialise (bits v) t2 :: ves')).
Proof.
  intros hs s f t1 t2 v ves' ?.
  simpl_reduce_simple.
  by apply rs_reinterpret with (t1 := t1) (v := v).
Qed.

Lemma reduce_invoke_native : forall (hs : host_state) s f a ves ves' ves'' n m t1s t2s cl ts i zs es,
  n = length t1s ->
  m = length t2s ->
  n <= length ves ->
  cl = FC_func_native i (Tf t1s t2s) ts es ->
  List.nth_error s.(s_funcs) a = Some cl ->
  split_n ves n = (ves', ves'') ->
  zs = n_zeros ts ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_invoke a])
    hs s f (vs_to_es ves'' ++ [:: AI_local m (Build_frame (rev ves' ++ zs) i) [:: AI_basic (BI_block (Tf [::] t2s) es)]]).
Proof.
  intros hs s f a ves ves' ves'' n m t1s t2s cl ts i zs es ?? Hn ?? Hsplit ?.
  subst n m cl zs.
  rewrite split_n_is_take_drop in Hsplit.
  injection Hsplit as Heqves' Heqves''.
  replace ves with (ves' ++ ves''); last by subst ves' ves''; rewrite cat_take_drop.
  replace (vs_to_es (ves' ++ ves'')) with (vs_to_es ves'' ++ vs_to_es ves');
    last by unfold vs_to_es; rewrite rev_cat; rewrite v_to_e_cat.
  eapply r_label with (k := 0) (lh := LH_base (vs_to_es ves'') [::]);
    try by solve_lfilled.
  eapply r_invoke_native with (t1s := t1s) => //; try by assumption.
  (* TODO lias to apply length_is_size aggresively? *)
  repeat rewrite length_is_size; rewrite size_rev; subst ves'.
  rewrite size_take; rewrite length_is_size.
  repeat rewrite length_is_size in Hn.
  by symmetry; if_lias.
Qed.

(* TODO dedupe with above *)
Lemma reduce_invoke_host_success : forall (hs hs' : host_state) s s' f a ves ves' ves'' rves n m t1s t2s cl cl',
  n = length t1s ->
  m = length t2s ->
  n <= length ves ->
  cl = FC_func_host (Tf t1s t2s) cl' ->
  List.nth_error s.(s_funcs) a = Some cl ->
  split_n ves n = (ves', ves'') ->
  host_application_impl hs s (Tf t1s t2s) cl' (rev ves') = (hs', Some (s', rves)) ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_invoke a])
    hs' s' f (vs_to_es ves'' ++ result_to_stack rves).
Proof.
  intros hs hs' s s' f a ves ves' ves'' rves n m t1s t2s cl cl' ?? Hn ?? Hsplit ?.
  subst n m cl.
  rewrite split_n_is_take_drop in Hsplit; injection Hsplit as Heqves' Heqves''.
  replace ves with (ves' ++ ves''); last by subst ves' ves''; rewrite cat_take_drop.
  replace (vs_to_es (ves' ++ ves'')) with (vs_to_es ves'' ++ vs_to_es ves');
    last by unfold vs_to_es; rewrite rev_cat; rewrite v_to_e_cat.
  eapply r_label with (k := 0) (lh := LH_base (vs_to_es ves'') [::]);
    try by solve_lfilled.
  eapply r_invoke_host_success with (t1s := t1s) (t2s := t2s) (h := cl') => //;
    try by assumption.
  - repeat rewrite length_is_size; rewrite size_rev; subst ves'.
    rewrite size_take; rewrite length_is_size.
    repeat rewrite length_is_size in Hn.
    by destruct (size t1s < size ves) eqn:?; lias.
  - by apply host_application_impl_correct.
Qed.

(* TODO dedupe with above *)
Lemma reduce_invoke_host_diverge : forall (hs hs' : host_state) s f a ves ves' ves'' n m t1s t2s cl cl',
  n = length t1s ->
  m = length t2s ->
  n <= length ves ->
  cl = FC_func_host (Tf t1s t2s) cl' ->
  List.nth_error s.(s_funcs) a = Some cl ->
  split_n ves n = (ves', ves'') ->
  host_application_impl hs s (Tf t1s t2s) cl' (rev ves') = (hs', None) ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_invoke a])
    hs' s f (vs_to_es ves ++ [:: AI_invoke a]).
Proof.
  intros hs hs' s f a ves ves' ves'' n m t1s t2s cl cl' ?? Hn ?? Hsplit ?.
  subst n m cl.
  rewrite split_n_is_take_drop in Hsplit; injection Hsplit as Heqves' Heqves''.
  replace ves with (ves' ++ ves''); last by subst ves' ves''; rewrite cat_take_drop.
  replace (vs_to_es (ves' ++ ves'')) with (vs_to_es ves'' ++ vs_to_es ves');
    last by unfold vs_to_es; rewrite rev_cat; rewrite v_to_e_cat.
  eapply r_label with (k := 0) (lh := LH_base (vs_to_es ves'') [::]);
    try by solve_lfilled.
  eapply r_invoke_host_diverge with (t1s := t1s) (t2s := t2s) (h := cl') => //;
    try by assumption.
  - repeat rewrite length_is_size; rewrite size_rev; subst ves'.
    rewrite size_take; rewrite length_is_size.
    repeat rewrite length_is_size in Hn.
    by destruct (size t1s < size ves) eqn:?; lias.
  - by apply host_application_impl_correct.
Qed.

Lemma invoke_func_native_error_n : forall s f ves cl i t1s t2s ts es a n m,
  cl = FC_func_native i (Tf t1s t2s) ts es ->
  List.nth_error (s_funcs s) a = Some cl ->
  n = length t1s ->
  m = length t2s ->
  (n <= length ves) = false ->
  ~ fragment_typeable s f ves [:: AI_invoke a].
Proof.
  intros s f ves cl i t1s t2s ts es a n m ? Hcl ?? Hlen
    [C [C' [ret [lab [t1s' [t2s' [ts' [? [Ht1s' [? [? Hetype]]]]]]]]]]].
  subst cl n m.
  eapply Invoke_func_native_typing in Hetype as [? [? [? [? [??]]]]] => //;
    last by apply Hcl.
  subst t1s'. repeat rewrite length_is_size in Hlen.
  by size_unequal Ht1s'.
Qed.

Lemma invoke_func_host_error_n : forall s f ves cl t1s t2s cl' a n m,
  cl = FC_func_host (Tf t1s t2s) cl' ->
  List.nth_error (s_funcs s) a = Some cl ->
  n = length t1s ->
  m = length t2s ->
  (n <= length ves) = false ->
  ~ fragment_typeable s f ves [:: AI_invoke a].
Proof.
  intros s f ves cl t1s t2s c' a n m ? Hcl ?? Hlen
    [C [C' [ret [lab [t1s' [t2s' [ts' [? [Ht1s' [? [? Hetype]]]]]]]]]]].
  subst cl n m.
  eapply Invoke_func_host_typing in Hetype as [? [??]] => //;
    last by apply Hcl.
  subst t1s'. repeat rewrite length_is_size in Hlen.
  by size_unequal Ht1s'.
Qed.

Lemma invoke_host_error_ath : forall s f ves a,
  List.nth_error (s_funcs s) a = None ->
  ~ fragment_typeable s f ves [:: AI_invoke a].
Proof.
  intros s f ves a Hath
    [C [C' [ret [lab [t1s' [t2s' [ts' [? [? [? [? Hetype]]]]]]]]]]].
  apply Invoke_func_typing in Hetype as [? Hath'].
  by rewrite Hath in Hath'.
Qed.

Lemma reduce_label_trap : forall (hs : host_state) s f ves ln les es,
  es_is_trap es ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_label ln les es])
    hs s f (vs_to_es ves ++ [:: AI_trap]).
Proof.
  intros hs s f ves ln les es Htrap.
  move/es_is_trapP in Htrap; subst es.
  by simpl_reduce_simple; apply rs_label_trap.
Qed.

Lemma reduce_label_const : forall (hs : host_state) s f ves ln les es,
  const_list es ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_label ln les es])
    hs s f (vs_to_es ves ++ es).
Proof.
  intros hs s f ves ln les es Htrap.
  eapply r_label with (k := 0) (lh := LH_base (vs_to_es ves) [::]);
    try by solve_lfilled.
  by apply r_simple; apply rs_label_const.
Qed.

Lemma const_trap_contradiction : forall es,
  es_is_trap es = false ->
  const_list es = false ->
  ~ (const_list es \/ es_is_trap es).
Proof.
  intros es Htrap Hconst [Hconst' | Htrap'].
  - by rewrite Hconst in Hconst'.
  - by rewrite Htrap in Htrap'.
Qed.

Lemma label_error_rec : forall s f es ves ln les,
  ~ (exists C C' ret lab ts,
      C = upd_label (upd_local_return C' (map typeof f.(f_locs)) ret) lab /\
      inst_typing s f.(f_inst) C' /\
      store_typing s /\
      e_typing s C es (Tf [::] ts)) ->
  ~ (exists C C' ret lab t1s t2s t1s',
      C = upd_label (upd_local_return C' (map typeof f.(f_locs)) ret) lab /\
      rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
      inst_typing s f.(f_inst) C' /\
      store_typing s /\
      e_typing s C [:: AI_label ln les es] (Tf t1s t2s)).
Proof.
  intros s f es ves ln les H [C [C' [ret [lab [t1s [t2s [ts [? [? [Hinst [? Hetype]]]]]]]]]]].
  apply Label_typing in Hetype as [t1s' [t2s' [? [? [??]]]]].
  remember ([:: t1s'] ++ tc_label C) as lab' eqn:?.
  apply H.
  exists (upd_label C lab'), C', ret, lab', t2s'.
  repeat split => //.
  by subst C.
Qed.

Lemma reduce_label_rec : forall (hs hs' : host_state) s s' f f' es es' ves ln les,
  reduce hs s f es hs' s' f' es' ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_label ln les es])
    hs' s' f' (vs_to_es ves ++ [:: AI_label ln les es']).
Proof.
  intros hs hs' s s' f f' es es' ves ln les IH.
  eapply r_label with
    (k := 1) (lh := (LH_rec (vs_to_es ves) ln les (LH_base [::] [::]) [::]));
    try by solve_lfilled.
  by apply IH.
Qed.

Lemma lfilled_take_v_to_e : forall i lh n ves e es,
  n <= size ves ->
  lfilledInd i lh (vs_to_es ves ++ [:: e]) es ->
  exists lh', lfilledInd i lh' (vs_to_es (take n ves) ++ [:: e]) es.
Proof.
  intros i lh n ves e es Hn H.
  unfold vs_to_es. unfold vs_to_es in H.
  remember (size ves - n) as n'.
  assert (Hn' : n = (size ves - n')). { by lias. }
  rewrite Hn'.
  rewrite <- drop_rev. rewrite v_to_e_drop.
  apply lfilled_collapse1 with (l := n) in H as [lh' H].
  - exists lh'.
    rewrite length_is_size in H. rewrite v_to_e_size in H. rewrite size_rev in H.
    subst n'. by apply H.
  - by apply v_to_e_is_const_list.
  - rewrite length_is_size. rewrite v_to_e_size. rewrite size_rev.
    by lias.
Qed.

Lemma reduce_label_break_rec : forall (hs : host_state) s f ln les es ves bvs,
  ln <= length bvs ->
  (exists i j lh,
    i + 0 = j /\
    lfilledInd i lh (vs_to_es bvs ++ [:: AI_basic (BI_br j)]) es /\
    empty_vs_base lh) ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_label ln les es])
    hs s f (vs_to_es (take ln bvs ++ ves) ++ les).
Proof.
  intros hs s f ln les es ves bvs Hlen [i [j [lh [Heqj [HLF Hbase]]]]].
  rewrite addn0 in Heqj. subst j.
  apply lfilled_take_v_to_e with (n := ln) in HLF as [lh' HLF] => //.
  move/lfilledP in HLF.
  unfold vs_to_es. rewrite rev_cat. rewrite <- v_to_e_cat.
  eapply r_label with (k := 0) (lh := LH_base (vs_to_es ves) [::]);
    try by solve_lfilled.
  apply r_simple. apply rs_br with (i := i) (lh := lh') => //.
  - by apply v_to_e_is_const_list.
  - rewrite length_is_size. rewrite length_is_size in Hlen.
    rewrite v_to_e_size. rewrite size_rev. rewrite size_take.
    by if_lias.
Qed.

Lemma label_break_rec : forall n ln les es bvs ves,
  (exists i j lh,
    i + n.+1 = j /\
    lfilledInd i lh (vs_to_es bvs ++ [:: AI_basic (BI_br j)]) es /\
    empty_vs_base lh) ->
  (exists i j lh,
    i + n = j /\
    lfilledInd i lh
      (vs_to_es bvs ++ [:: AI_basic (BI_br j)])
      (vs_to_es ves ++ [:: AI_label ln les es]) /\
    empty_vs_base lh).
Proof.
  intros n ln les es bvs ves [i [j [lh [Heqj [HLF Hbase]]]]].
  exists (i.+1), j, (LH_rec (vs_to_es ves) ln les lh [::]).
  repeat split; try by lias.
  by apply LfilledRec => //; apply v_to_e_is_const_list.
Qed.

Lemma br_arguments_length: forall s C ts t_br j bvs,
  e_typing s C (vs_to_es bvs ++ [:: AI_basic (BI_br j)]) (Tf [::] ts) ->
  plop2 C j t_br ->
  length bvs >= length t_br.
Proof.
  move => s C ts t_br j bvs Hetype Hplop.
  apply e_composition_typing in Hetype
      as [? [t0s [ts' [t1s' [Ht0s [Hts'' [Hetypebvs Hetypebr]]]]]]].
  apply_cat0_inv Ht0s; simpl in *; subst.
  apply et_to_bet in Hetypebr; last by auto_basic.
  apply (Break_typing host_instance) in Hetypebr
    as [ts'0 [ts'' [Hj [Hplop' Heqt1s']]]].
  assert (ts'0 = t_br).
  {
    unfold plop2 in Hplop, Hplop'. move/eqP in Hplop. move/eqP in Hplop'.
    rewrite Hplop' in Hplop. by injection Hplop.
  }
  subst ts'0 t1s'.
  apply et_to_bet in Hetypebvs;
    last by apply const_list_is_basic; apply v_to_e_is_const_list.
  apply Const_list_typing in Hetypebvs.
  simpl in Hetypebvs.
  apply f_equal with (f := size) in Hetypebvs.
  rewrite size_map size_cat size_rev in Hetypebvs.
  repeat rewrite length_is_size; by lias.
Qed.

Lemma lfilled_hole_typed_br : forall lh s C es ts i m j bvs,
  e_typing s C es (Tf [::] ts) ->
  empty_vs_base lh ->
  lfilledInd i lh (v_to_e_list bvs ++ [:: AI_basic (BI_br j)]) es ->
  i + m = j ->
  exists ts C',
    List.nth_error C'.(tc_label) j = List.nth_error C.(tc_label) m /\
    e_typing s C' (v_to_e_list bvs ++ [:: AI_basic (BI_br j)]) (Tf [::] ts).
Proof.
  induction lh as [vs es' | vs k es' lh' IH]; move => s C es ts i m j bvs Hetype Hbase Hlf Hj.
  - destruct vs => //.
    inversion Hlf; subst; simpl in Hetype; clear Hlf.
    apply e_composition_typing in Hetype
      as [? [t0s [ts' [t1s' [Ht0s [Hts'' [Hetypebvs Hetype]]]]]]].
    apply_cat0_inv Ht0s. simpl in Hts''; subst.
    by exists t1s', C.
  - inversion Hlf as [ | i' vs0 n es'0 lh'0 es''0 es0 LI Hconst Hlf0].
    subst i es vs0 n es'0 lh'0 es''0 es0; clear Hlf.
    apply e_composition_typing in Hetype
      as [? [t0s [ts' [t1s' [Ht0s [Hts'' [Hetypevs Hetype]]]]]]].
    apply_cat0_inv Ht0s; subst ts.
    apply e_composition_typing in Hetype
      as [? [t0s' [ts'' [t1s'' [Ht0s [Hts'' [Hetypebvs Hetype]]]]]]].
    apply Label_typing in Hetypebvs
      as [? [t2s' [-> [Hetypees' [HetypeLI Hlen]]]]].

    apply IH with (bvs := bvs) (i := i') (m := m.+1) (j := j) in HetypeLI
      as [ts''' [C' [Hlab Hetypebase]]] => //; last by lias.
    exists ts''', C' => //.
Qed.

Lemma lfilled_br_empty_vs_base : forall lh s C ln les es t1s t2s i bvs,
  e_typing s C [:: AI_label ln les es] (Tf t1s t2s) ->
  empty_vs_base lh ->
  lfilledInd i lh (vs_to_es bvs ++ [:: AI_basic (BI_br i)]) es ->
  length bvs >= ln.
Proof.
  move => lh s C ln les es t1s t2s i bvs Hetype Hbase Hlf.
  apply Label_typing in Hetype as [ts [t2s' [-> [Hetypeles [Hetypees <-]]]]].
  eapply lfilled_hole_typed_br with (m := 0) in Hetypees
    as [ts0 [C0 [Heqlab Hetype]]]; eauto; last by lias.
  eapply br_arguments_length with (t_br := ts) in Hetype => //.
  destruct C, C0; simpl in *.
  by apply/eqP.
Qed.

Lemma label_error_break_rec : forall s f ves bvs ln les es,
  (exists i j lh,
    i + 0 = j /\
    lfilledInd i lh (vs_to_es bvs ++ [:: AI_basic (BI_br j)]) es /\
    empty_vs_base lh) ->
  (ln <= length bvs) = false ->
  ~ (exists C C' ret lab t1s t2s t1s',
      C = upd_label (upd_local_return C' (map typeof f.(f_locs)) ret) lab /\
      rev (map typeof ves) = t1s' ++ t1s /\
      inst_typing s f.(f_inst) C' /\
      store_typing s /\
      e_typing s C [:: AI_label ln les es] (Tf t1s t2s)).
Proof.
  intros s f ves bvs ln les es [i [j [lh [Heqj [HLF Hbase]]]]] Hlen
    [C [C' [ret [lab [t1s [t2s [ts [? [? [Hinst [? Hetype]]]]]]]]]]].
  rewrite addn0 in Heqj; subst j.
  assert (ln <= length bvs).
  {
    rewrite length_is_size.
    by apply (lfilled_br_empty_vs_base Hetype Hbase HLF).
  }
  by lias.
Qed.

Lemma reduce_local_trap : forall (hs : host_state) s f ves ln lf es,
  es_is_trap es ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_local ln lf es])
    hs s f (vs_to_es ves ++ [:: AI_trap]).
Proof.
  intros hs s f ves ln lf es Htrap.
  move/es_is_trapP in Htrap; subst es.
  by simpl_reduce_simple; apply rs_local_trap.
Qed.

Lemma reduce_local_const : forall (hs : host_state) s f ves ln lf es,
  const_list es ->
  length es == ln ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_local ln lf es])
    hs s f (vs_to_es ves ++ es).
Proof.
  intros hs s f ves ln lf es ??.
  eapply r_label with (k := 0) (lh := LH_base (vs_to_es ves) [::]);
    try by solve_lfilled.
  apply r_simple. by apply rs_local_const => //; apply/eqP.
Qed.

Lemma local_error_const_len : forall s f es ves ln lf,
  const_list es ->
  (length es == ln) = false ->
  ~ (exists C C' ret lab t1s t2s t1s',
      C = upd_label (upd_local_return C' (map typeof f.(f_locs)) ret) lab /\
      rev (map typeof ves) = t1s' ++ t1s /\
      inst_typing s f.(f_inst) C' /\
      store_typing s /\
      e_typing s C [:: AI_local ln lf es] (Tf t1s t2s)).
Proof.
  intros s f es ves ln lf Hconst Hlen [C [C' [ret [lab [t1s [t2s [ts [? [? [Hinst [? Hetype]]]]]]]]]]].
  apply Local_typing in Hetype as [ts' [? [Hstype Hlen']]].
  destruct Hstype as [s lf es ret' ts' C'' C''' Hftype HeqC'' Hetype Heqts'].
  apply et_to_bet in Hetype as Hbtype; last by apply const_list_is_basic.
  apply const_es_exists in Hconst as [vs ?]; subst es.
  apply Const_list_typing in Hbtype; simpl in Hbtype; subst ts'.
  (* XXX could this be shorter? *)
  rewrite List.map_length in Hlen'. repeat rewrite length_is_size in Hlen, Hlen'.
  rewrite v_to_e_size in Hlen. by move/eqP in Hlen.
Qed.

Lemma lfilled_collapse': forall n lh vs es LI,
    lfilledInd n lh (vs ++ es) LI ->
    const_list vs ->
    exists lh', lfilledInd n lh' es LI.
Proof.
  intros n lh vs es LI HLF Hconst.
  apply lfilled_collapse1 with (l := 0) in HLF => //.
  rewrite subn0 in HLF.
  by rewrite drop_size in HLF => //.
Qed.

Lemma local_error_rec : forall s f es ves ln lf,
  ~ (exists C C' ret lab ts,
      C = upd_label (upd_local_return C' (map typeof lf.(f_locs)) ret) lab /\
      inst_typing s lf.(f_inst) C' /\
      store_typing s /\
      e_typing s C es (Tf [::] ts)) ->
  ~ (exists C C' ret lab t1s t2s t1s',
      C = upd_label (upd_local_return C' (map typeof f.(f_locs)) ret) lab /\
      rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
      inst_typing s f.(f_inst) C' /\
      store_typing s /\
      e_typing s C [:: AI_local ln lf es] (Tf t1s t2s)).
Proof.
  intros s f es ves ln lf IH [C [C' [ret [lab [t1s [t2s [ts [? [? [Hitype [? Hetype]]]]]]]]]]].
  apply Local_typing in Hetype as [ts' [? [Hstype ?]]].
  destruct Hstype as [s lf es ret' ts' C'' C''' Hftype HeqC'' Hetype Heqts'].
  destruct Hftype as [s i ts'' C''' lf Hitype' Heqi Heqts''].
  subst i ts''.
  apply IH.
  exists
    (upd_label (upd_local C'' (map typeof lf.(f_locs))) [::]),
    C''',
    ret',
    [::],
    ts'.
  subst C''; repeat split => //.
  unfold upd_local in Hetype. unfold upd_return in Hetype. simpl in Hetype.
  replace (tc_local C''') with ([::] : seq value_type) in Hetype;
    last by apply inst_t_context_local_empty in Hitype'.
  replace (tc_label C''') with ([::] : seq (seq value_type)) in Hetype;
    last by apply inst_t_context_label_empty in Hitype'.
  by apply Hetype.
Qed.

Lemma lfilled_labels : forall lh i j k s C bvs es t1s t2s,
  size C.(tc_label) = k ->
  e_typing s C es (Tf t1s t2s) ->
  lfilledInd i lh (vs_to_es bvs ++ [:: AI_basic (BI_br j)]) es ->
  j < i + k.
Proof.
  induction lh as [vs es' | vs m es' lh' IH];
    intros i j k s C bvs es t1s t2s Hlab Hetype Hlf;
    inversion Hlf as [ | i' vs0 m' es'0 lh'0 es''0 es0 LI Hconst Hlf0].
  - subst. repeat rewrite catA in Hetype.
    apply e_composition_typing in Hetype as [? [? [? [? [-> [-> [Hetype _]]]]]]].
    apply e_composition_typing in Hetype as [? [? [? [? [-> [-> [_ Hetypebr]]]]]]].
    apply et_to_bet in Hetypebr; last by auto_basic.
    by apply (Break_typing host_instance) in Hetypebr as [? [? [Hj [??]]]]; auto.
  - subst i k vs0 m' es'0 lh'0 es''0 es0 es.
    apply e_composition_typing in Hetype as [? [t0s [? [t1s' [-> [-> [_ Hetype]]]]]]].
    apply e_composition_typing in Hetype as [? [t1s [? [t2s' [-> [-> [Hetype _]]]]]]].
    apply Label_typing in Hetype as [ts [t3s' [-> [_ [HetypeLI Hlen]]]]].
    eapply IH with (C := (upd_label C ([:: ts] ++ tc_label C))) in Hlf0 => //;
      last by apply HetypeLI.
    by simpl in Hlf0; lias.
Qed.

Lemma lfilled_labels_emp : forall lh i s C bvs j es t1s t2s,
  C.(tc_label) = [::] ->
  e_typing s C es (Tf t1s t2s) ->
  lfilledInd i lh (vs_to_es bvs ++ [:: AI_basic (BI_br j)]) es ->
  j < i.
Proof.
  intros lh i s C bvs j es t1s t2s Hlab Hetype Hlf.
  apply f_equal with (f := size) in Hlab; simpl in Hlab.
  replace i with (i + 0); last by apply addn0.
  by eapply lfilled_labels; eauto.
Qed.

Lemma local_error_break_rec : forall s f es ves ln lf n bvs,
  (exists i j lh,
    i + n = j /\
    lfilledInd i lh (vs_to_es bvs ++ [:: AI_basic (BI_br j)]) es /\
    empty_vs_base lh) ->
  ~ (exists C C' ret lab t1s t2s t1s',
      C = upd_label (upd_local_return C' (map typeof f.(f_locs)) ret) lab /\
      rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
      inst_typing s f.(f_inst) C' /\
      store_typing s /\
      e_typing s C [:: AI_local ln lf es] (Tf t1s t2s)).
Proof.
  intros s f es ves ln lf n bvs [i [j [lh [Heqj [HLF Hbase]]]]]
    [C [C' [ret [lab [t1s [t2s [ts [? [? [Hitype [? Hetype]]]]]]]]]]].
  apply Local_typing in Hetype as [ts' [-> [Hstype ?]]].
  destruct Hstype as [s lf es ret' ts' C'' C''' Hftype HeqC'' Hetype Heqts'].
  destruct Hftype as [s i' ts'' C''' lf Hitype' Heqi Heqts'']. subst i'.
  apply inst_t_context_label_empty in Hitype'.
  assert (Hlab : C''.(tc_label) = [::]). { by subst C''. }
  eapply lfilled_labels_emp in Hlab; eauto.
  by lias.
Qed.

(* XXX this could maybe be simplified by using lfilled_collapse1 more directly *)
Lemma reduce_local_return_rec : forall (hs : host_state) s f lf rvs ves ln es,
  ln <= length rvs ->
  (exists i lh,
    lfilledInd i lh (vs_to_es rvs ++ [:: AI_basic BI_return]) es /\
    empty_vs_base lh) ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_local ln lf es])
    hs s f (vs_to_es (take ln rvs ++ ves)).
Proof.
  intros hs s f lf rvs ves ln es Hlen [i [lh [HLF _]]].

  eapply r_label with (k := 0) (lh := LH_base (vs_to_es ves) [::]);
    try by solve_lfilled.

  assert (length (v_to_e_list (rev (take ln rvs))) = ln).
  {
    rewrite length_is_size in Hlen. rewrite length_is_size.
    rewrite v_to_e_size. rewrite size_rev. rewrite size_take. by if_lias.
  }

  apply lfilled_take_v_to_e with (n := ln) in HLF as [lh' HLF];
    last by rewrite length_is_size in Hlen.

  apply r_simple.
  apply rs_return with (i := i) (lh := lh') => //;
    first by apply v_to_e_is_const_list.

  by apply/lfilledP.
Qed.

Lemma lfilled_hole_typed_return : forall lh s C es ts i rvs,
  e_typing s C es (Tf [::] ts) ->
  empty_vs_base lh ->
  lfilledInd i lh (v_to_e_list rvs ++ [:: AI_basic BI_return]) es ->
  exists ts C',
    C'.(tc_return) = C.(tc_return) /\
    e_typing s C' (v_to_e_list rvs ++ [::AI_basic BI_return]) (Tf [::] ts).
Proof.
  induction lh as [vs es' | vs j es' lh' IH]; move => s C es ts i rvs Hetype Hbase Hlf.
  - destruct vs => //.
    inversion Hlf; subst; simpl in *.
    apply e_composition_typing in Hetype
        as [? [t0s [ts' [t1s' [Ht0s [Hts'' [Hetypervs Hetype]]]]]]].
    apply_cat0_inv Ht0s; simpl in *; subst.
    by exists t1s', C.
  - inversion Hlf as [ | k vs0 n es'0 lh'0 es''0 es0 LI Hconst Hlf0]; subst; clear Hlf.
    apply e_composition_typing in Hetype
        as [? [t0s [ts' [t1s' [Ht0s [Hts'' [Hetypevs Hetype]]]]]]].
    apply_cat0_inv Ht0s; subst.
    apply e_composition_typing in Hetype
        as [? [t0s' [ts'' [t1s'' [Ht0s [Hts'' [Hetypervs Hetype]]]]]]].
    (* XXX misleading naming *)
    apply Label_typing in Hetypervs
        as [? [ts2' [-> [Hetypees' [HetypeLI Hlen]]]]].
    by eapply IH in HetypeLI; eauto.
Qed.

Lemma return_arguments_length: forall s C ts t_ret rvs,
    e_typing s C (vs_to_es rvs ++ [::AI_basic BI_return]) (Tf [::] ts) ->
    C.(tc_return) = Some t_ret ->
    length rvs >= length t_ret.
Proof.
  move => s C ts t_ret rvs Hetype Heqret.
  apply e_composition_typing in Hetype
      as [? [t0s [ts' [t1s' [Ht0s [Hts'' [Hetypervs Hetyperet]]]]]]].
  apply_cat0_inv Ht0s; simpl in *; subst.
  apply et_to_bet in Hetyperet; last by auto_basic.
  apply (Return_typing host_instance) in Hetyperet
      as [ts'0 [ts'' [Heqt0s Heqts'0]]].
  rewrite Heqts'0 in Heqret.
  injection Heqret; subst; clear Heqret.
  move => <-.
  apply et_to_bet in Hetypervs;
    last by apply const_list_is_basic; apply v_to_e_is_const_list.
  apply Const_list_typing in Hetypervs.
  simpl in Hetypervs.
  apply f_equal with (f := size) in Hetypervs.
  rewrite size_map size_cat size_rev in Hetypervs.
  repeat rewrite length_is_size; by lias.
Qed.

Lemma lfilled_return_empty_vs_base : forall lh s C ln lf es t1s t2s i rvs,
  e_typing s C [:: AI_local ln lf es] (Tf t1s t2s) ->
  empty_vs_base lh ->
  lfilledInd i lh (vs_to_es rvs ++ [:: AI_basic BI_return]) es ->
  length rvs >= ln.
Proof.
  move => lh s C ln lf es t1s t2s i rvs Hetype Hbase Hlf.
  apply Local_typing in Hetype as [ts' [-> [Hstype Hlen']]].
  inversion Hstype as [s0 lf0 es' ret'0 ts'0 C'' C' Hftype HeqC'' Hetype _].
  subst s0 ret'0 lf0 ts'0 es' C''.
  eapply lfilled_hole_typed_return in Hetype as [ts0 [C0 [Heqret Hetype]]]; eauto.
  by eapply return_arguments_length in Hetype; eauto.
Qed.

(* return has not returned enough values *)
Lemma local_return_error : forall s f ln lf es rvs ves,
  (exists i lh,
    lfilledInd i lh (vs_to_es rvs ++ [:: AI_basic BI_return]) es /\
    empty_vs_base lh) ->
  (ln <= length rvs) = false ->
  ~ (exists C C' ret lab t1s t2s t1s',
      C = upd_label (upd_local_return C' (map typeof f.(f_locs)) ret) lab /\
      rev (map typeof ves) = t1s' ++ t1s /\
      inst_typing s f.(f_inst) C' /\
      store_typing s /\
      e_typing s C [:: AI_local ln lf es] (Tf t1s t2s)).
Proof.
  intros s f ln lf es rvs ves [i [lh [Hlf Hbase]]] Hlen
    [C [C' [ret [lab [t1s [t2s [ts [? [? [Hitype [? Hetype]]]]]]]]]]].
  eapply lfilled_return_empty_vs_base
    with (i := i) (lh := lh) (rvs := rvs) in Hetype => //.
  by lias.
Qed.

Lemma reduce_local_rec : forall (hs hs' : host_state) s s' f f' es es' ves ln lf,
  reduce hs s lf es hs' s' f' es' ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_local ln lf es])
    hs' s' f (vs_to_es ves ++ [:: AI_local ln f' es']).
Proof.
  intros hs hs' s s' f f' es es' ves ln lf IH.
  eapply r_label with (k := 0) (lh := LH_base (vs_to_es ves) [::]);
    try by solve_lfilled.
  by apply r_local.
Qed.

(** A new method of dealing with termination, calculating the exact number of recursive calls required instead of just an upper bound **)
Fixpoint first_non_zero (l: list nat) : nat :=
  match l with
  | [::] => 0
  | n :: l' =>
      if n > 0 then n
      else first_non_zero l'
  end.

(* Program Fixpoint does not support mutual recursion *)
Program Fixpoint run_one_step_measure (e: administrative_instruction): nat :=
  match e with
  | AI_label _ _ es => (first_non_zero (map run_one_step_measure es)).+2
  | AI_local _ _ es => (first_non_zero (map run_one_step_measure es)).+2
  | _ => if is_const e then 0 else 1
  end.
Next Obligation.
  by split => //.
Qed.
Next Obligation.
  by split => //.
Qed.
Next Obligation.
  by split => //.
Qed.

Definition run_step_measure (es: list administrative_instruction): nat :=
  match split_vals_e es with
  | (vs, es') =>
     match es' with
     | [::] => 0
     | e :: es'' => S (run_one_step_measure e)
     end
  end.

Lemma run_step_measure_eq (es: list administrative_instruction):
  const_list es = false ->
  run_step_measure es = S (first_non_zero (map run_one_step_measure es)).
Proof.
  unfold run_step_measure.
  destruct (split_vals_e es) as [vs es'] eqn:Hsplitvals.
  move: Hsplitvals.
  move: es es'.
  induction vs; move => es es' Hsplitvals Hnconst => //=.
  - destruct es' => /=.
    + apply split_vals_e_v_to_e_duality in Hsplitvals; by subst es.
    + specialize (split_vals_e_not_const Hsplitvals) as Hnconsta.
      apply split_vals_e_v_to_e_duality in Hsplitvals; subst es => /=.
      destruct a => //=.
      by destruct b.
  - destruct es as [ | e es''] => //.
    simpl in Hsplitvals.
    destruct e => //.
    destruct b => //=.
    apply IHvs => //.
    destruct (split_vals_e es'') eqn:Hes.
    by inversion Hsplitvals.
Qed.
    
Theorem run_step (measure: nat) hs s f (es: list administrative_instruction) (Hmeasure: run_step_measure es = measure): res_step' hs s f es
  with
  run_one_step'' (measure: nat) hs s f ves e (Htrap : (e_is_trap e) = false) (Hconst : (is_const e) = false) (Hmeasure: run_one_step_measure e = measure) : res_step'_separate_e hs s f ves e.
Proof.
  (* run_step *)
  (** Framing out constants. **)
  {
    clear run_step.
    unfold run_step_measure in Hmeasure.
    destruct (split_vals_e es) as [ves es'] eqn:Heqes.
    destruct es' as [|e es''] eqn:Heqes'.
    * (* es' = [::] *)
      apply RS'_value. by apply value_split_0 with (ves := ves).
    * (* es' = e :: es'' *)
      destruct (e_is_trap e) eqn:Htrap.
      + destruct ((es'' != [::]) || (ves != [::])) eqn:?.
        -- apply <<hs, s, f, [:: AI_trap]>>.
           by apply reduce_trap with (e := e) (es'' := es'') (ves := ves).
        -- apply RS'_value.
           by apply value_trap with (e := e) (es'' := es'') (ves := ves).
      + remember (split_vals_e_not_const Heqes) as Hconst.
        destruct measure as [|measure']=> //.
        injection Hmeasure; clear Hmeasure; move => Hmeasure.
        remember (run_one_step'' measure' hs s f (rev ves) e Htrap Hconst Hmeasure) as r.
        destruct r as [| k bvs Hbr | rvs | hs' s' f' res].
        -- (* RS''_error *)
           apply RS'_error.
           by eapply error_rec with (es' := es') (ves := ves) => //; subst es'.
        -- (* RS''_break *)
           apply RS'_break with (k := k) (bvs := bvs).
           (* XXX why is there rev ves (unfoldfed v_to_e_list) in Hbr? *)
           by apply break_rec with (e := e) (es'' := es'') (ves := ves) => //.
        -- (* RS''_return rvs *)
           apply RS'_return with (rvs := rvs).
           by eapply return_rec with (ves := ves) (e := e) (es'' := es'') => //.
        -- (* RS''_normal hs' s' f' res *)
           apply <<hs', s', f', (res ++ es'')>>.
           by eapply reduce_rec with (es' := es') (ves := ves); subst es'.
  }
  
  (* run_one_step'' *)
  {
    clear run_one_step''.
  (* initial es, useful as an arg for reduce *)
  remember ((vs_to_es ves) ++ [::e]) as es0 eqn:Heqes0.
    destruct e as [
      (* AI_basic *) [
      (* BI_unreachable *) |
      (* BI_nop *) |
      (* BI_drop *) |
      (* BI_select *) |
      (* BI_block (Tf t1s t2s) es *) [t1s t2s] es |
      (* BI_loop (Tf t1s t2s) es *) [t1s t2s] es |
      (* BI_if tf es1 es2 *) tf es1 es2 |
      (* BI_br j *) j |
      (* BI_br_if j *) j |
      (* BI_br_table js j *) js j |
      (* BI_return *) |
      (* BI_call j *) j |
      (* BI_call_indirect j *) j |
      (* BI_get_local j *) j |
      (* BI_set_local j *) j |
      (* BI_tee_local j *) j |
      (* BI_get_global j *) j |
      (* BI_set_global j *) j |
      (* BI_load t [Some (tp, sx)|None] a off *) t [[tp sx]|] a off |
      (* BI_store t [Some tp|None] a off *) t [tp|] a off |
      (* BI_current_memory *) |
      (* BI_grow_memory *) |
      (* BI_const _ *) |
      (* BI_unop t op *) t op |
      (* BI_binop t op *) t op |
      (* BI_testop [T_i32|T_i64|T_f32|T_f64] testop *) [| | |] testop |
      (* BI_relop t op *) t op |
      (* BI_cvtop t2 [CVO_convert|CVO_reinterpret] t1 sx *) t2 [|] t1 sx ] |
      (* AI_trap *) |
      (* AI_invoke a *) a |
      (* AI_label ln les es *) ln les es |
      (* AI_local ln lf es *) ln lf es ].

    * (* AI_basic BI_unreachable *)
      apply <<hs, s, f, vs_to_es ves ++ [:: AI_trap]>>'.
      by apply reduce_unreachable.

    * (* AI_basic BI_nop *)
      apply <<hs, s, f, vs_to_es ves>>'.
      by apply reduce_nop.

    * (* AI_basic BI_drop *)
      destruct ves as [|v ves'] eqn:Heqves.
      + (* [::] *)
        apply RS''_error. by apply drop_error.
      + (* v :: ves' *)
        apply <<hs, s, f, vs_to_es ves'>>'. by apply reduce_drop.

    * (* AI_basic BI_select *)
      destruct ves as [|v3 [|v2 [|v1 ves']]];
        try by (apply RS''_error; apply select_error_size).
      (* [:: v3, v2, v1 & ves'] *)
      destruct v3 as [c| | |] eqn:?;
        try by
          (apply RS''_error; eapply select_error_i32 with (v3 := v3); subst v3).
      (* VAL_int32 c *)
      destruct (c == Wasm_int.int_zero i32m) eqn:?.
      + (* true *)
        apply <<hs, s, f, vs_to_es (v2 :: ves')>>'.
        by apply reduce_select_false.
      + (* false *)
        apply <<hs, s, f, vs_to_es (v1 :: ves')>>'.
        by apply reduce_select_true; lias.

    * (* AI_basic (BI_block (Tf t1s t2s) es) *)
      destruct (length ves >= length t1s) eqn:?.
      + (* true *)
        destruct (split_n ves (length t1s)) as [ves' ves''] eqn:?.
        remember (AI_label (length t2s) [::] (vs_to_es ves' ++ to_e_list es)) as e'.
        apply <<hs, s, f, vs_to_es ves'' ++ [:: e']>>'.
        by subst e'; eapply reduce_block.
      + (* false *)
        apply RS''_error.
        (* TODO should use length in lemmas instead? *)
        repeat rewrite length_is_size in Heqb.
        by apply block_error; lias.

    * (* AI_basic (BI_loop (Tf t1s t2s) es) *)
      destruct (length ves >= length t1s) eqn:?.
      + (* true *)
        destruct (split_n ves (length t1s)) as [ves' ves''] eqn:?.
        apply <<hs, s, f, vs_to_es ves''
          ++ [:: AI_label (length t1s) [:: AI_basic (BI_loop (Tf t1s t2s) es)] (vs_to_es ves' ++ to_e_list es)]
        >>'.
        by apply reduce_loop.
      + (* false *)
        apply RS''_error.
        apply loop_error; repeat rewrite -length_is_size; lias.

    * (* AI_basic (BI_if tf es1 es2) *)
      destruct ves as [|v ves'] eqn:?;
        try by (apply RS''_error; apply if_error_0).
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?;
        try by (apply RS''_error; eapply if_error_typeof => //).
      (* VAL_int32 c *)
      destruct (c == Wasm_int.int_zero i32m) eqn:?.
      + (* true *)
        apply <<hs, s, f, vs_to_es ves' ++ [:: AI_basic (BI_block tf es2)]>>'.
        by eapply reduce_if_false.
      + (* false *)
        apply <<hs, s, f, vs_to_es ves' ++ [:: AI_basic (BI_block tf es1)]>>'.
        by eapply reduce_if_true.

    * (* AI_basic (BI_br j) *)
      apply break(j, ves).
      by apply break_br.

    * (* AI_basic (BI_br_if j) *)
      destruct ves as [|v ves'];
        try by (apply RS''_error; apply br_if_error_0).
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?;
        try by (apply RS''_error; eapply br_if_error_i32 with (v := v); subst v).
      (* VAL_int32 c *)
      destruct (c == Wasm_int.int_zero i32m) eqn:?.
      ** (* true *)
         apply <<hs, s, f, vs_to_es ves'>>'.
         by eapply reduce_br_if_false.
      ** (* false *)
         apply <<hs, s, f, vs_to_es ves' ++ [:: AI_basic (BI_br j)]>>'.
         by eapply reduce_br_if_true; lias.

    * (* AI_basic (BI_br_table js j) *)
      destruct ves as [|v ves'];
        try by (apply RS''_error; apply br_table_error_0).
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?;
        try by (apply RS''_error; eapply br_table_error_i32 with (v := v); subst v).
      remember (Wasm_int.nat_of_uint i32m c) as k.
      destruct (k < length js) eqn:?.
      + (* true *)
        destruct (List.nth_error js k) as [js_at_k|] eqn:?.
        -- (* Some js_at_k *)
           apply <<hs, s, f, vs_to_es ves' ++ [::AI_basic (BI_br js_at_k)]>>'.
           by apply reduce_br_table with (k := k).
        -- (* None *)
           apply RS''_error.
           by apply br_table_error_kth with (k := k) (c := c) (ves' := ves').
      + (* false *)
        apply <<hs, s, f, vs_to_es ves' ++ [::AI_basic (BI_br j)]>>'.
        by apply reduce_br_table_length with (k := k); lias.

    * (* AI_basic BI_return *)
      apply RS''_return with (rvs := ves).
      by left => //.

    * (* AI_basic (BI_call j) *)
      destruct (List.nth_error f.(f_inst).(inst_funcs) j) as [a|] eqn:?.
      + (* Some a *)
        apply <<hs, s, f, vs_to_es ves ++ [:: AI_invoke a]>>'.
        by apply reduce_call.
      + (* None *)
        apply RS''_error.
        by apply call_error.

    * (* AI_basic (BI_call_indirect j) *)
      destruct ves as [|v ves'] eqn:?;
        try by (apply RS''_error; apply call_indirect_error_0).
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?;
        try by (apply RS''_error; eapply call_indirect_error_typeof => //).
      (* VAL_int32 c *)
      destruct (stab_addr s f (Wasm_int.nat_of_uint i32m c)) as [a|] eqn:?.
      + (* Some a *)
        destruct (List.nth_error s.(s_funcs) a) as [cl|] eqn:?.
        -- (* Some cl *)
           destruct (stypes s f.(f_inst) j == Some (cl_type cl)) eqn:?.
           ** (* true *)
              apply <<hs, s, f, vs_to_es ves' ++ [:: AI_invoke a]>>'.
              by eapply reduce_call_indirect_success with (cl := cl).
           ** (* false *)
              apply <<hs, s, f, vs_to_es ves' ++ [:: AI_trap]>>'.
              by eapply reduce_call_indirect_failure_1 with (cl := cl) (a := a).
        -- (* None *)
           apply RS''_error.
           by eapply call_indirect_error_ath with (a := a).
      + (* None *)
        apply <<hs, s, f, vs_to_es ves' ++ [:: AI_trap]>>'.
        by eapply reduce_call_indirect_failure_2.

    * (* AI_basic (BI_get_local j) *)
      destruct (j < length f.(f_locs)) eqn:?.
      + (* true *)
        destruct (List.nth_error f.(f_locs) j) as [vs_at_j|] eqn:?.
        -- (* Some vs_at_j *)
           apply <<hs, s, f, vs_to_es (vs_at_j :: ves)>>'.
           by apply reduce_get_local.
        -- (* None *)
           apply RS''_error. by apply get_local_error_jth_none.
      + (* false *)
        apply RS''_error. by apply get_local_error_length; lias.

    * (* AI_basic (BI_set_local j) *)
      destruct ves as [|v ves'] eqn:?.
      + (* [::] *)
        apply RS''_error. by apply set_local_error_0.
      + (* v :: ves' *)
        destruct (j < length f.(f_locs)) eqn:?.
        -- (* true *)
           apply <<hs, s, Build_frame (update_list_at f.(f_locs) j v) f.(f_inst), vs_to_es ves'>>'.
           by eapply reduce_set_local.
        -- (* false *)
           apply RS''_error. by eapply set_local_error_length.

    * (* AI_basic (BI_tee_local j) *)
      destruct ves as [|v ves'] eqn:?.
      + (* [::] *)
        apply RS''_error. by apply tee_local_error_0.
      + (* v :: ves' *)
        apply <<hs, s, f, vs_to_es (v :: v :: ves') ++ [:: AI_basic (BI_set_local j)]>>'.
        by eapply reduce_tee_local.

    * (* AI_basic (BI_get_global j) *)
      destruct (sglob_val s f.(f_inst) j) as [xx|] eqn:?.
      + (* Some xx *)
        apply <<hs, s, f, vs_to_es (xx :: ves)>>'.
        by apply reduce_get_global.
      + (* None *)
        apply RS''_error. by apply get_global_error.

    * (* AI_basic (BI_set_global j) *)
      destruct ves as [|v ves'] eqn:?.
      + (* [::] *)
        apply RS''_error. by apply set_global_error_0.
      + (* v :: ves' *)
        destruct (supdate_glob s f.(f_inst) j v) as [s'|] eqn:?.
        -- (* Some s' *)
           apply <<hs, s', f, vs_to_es ves'>>'.
           by eapply reduce_set_global => //.
        -- (* None *)
           apply RS''_error. by eapply set_global_error_jth.

    * (* AI_basic (BI_load t (Some (tp, sx)) a off) *)
      (* TODO can this and the next branch be deduped? *)
      destruct ves as [|v ves'] eqn:?.
      + (* [::] *)
        apply RS''_error. by apply load_error_0.
      + (* v :: ves' *)
        destruct v as [c| | |] eqn:?;
          try by (apply RS''_error; eapply load_error_typeof => //).
        (* VAL_int32 c *)
        destruct (smem_ind s f.(f_inst)) as [j|] eqn:?.
        -- (* Some j *)
           destruct (List.nth_error s.(s_mems) j) as [mem_s_j|] eqn:?.
           ** (* Some mem_s_j*)
              destruct (load_packed sx (mem_s_j) (Wasm_int.N_of_uint i32m c) off (tp_length tp) (t_length t)) as [bs|] eqn:?.
              ++ (* Some bs *)
                 apply <<hs, s, f, vs_to_es (wasm_deserialise bs t :: ves')>>'.
                 by apply reduce_load_packed_success with (mem_s_j := mem_s_j) (j := j) (c := c).
              ++ (* None *)
                 apply <<hs, s, f, vs_to_es ves' ++ [:: AI_trap]>>'.
                 by apply reduce_load_packed_failure with (mem_s_j := mem_s_j) (j := j) (c := c).
           ** (* None*)
              apply RS''_error. by eapply load_error_jth with (j := j).
        -- (* None *)
           apply RS''_error. by eapply load_error_smem_ind.

    * (* AI_basic (BI_load t None a off) *)
      destruct ves as [|v ves'] eqn:?.
      + (* [::] *)
        apply RS''_error. by apply load_error_0.
      + (* v :: ves' *)
        destruct v as [c| | |] eqn:?;
          try by (apply RS''_error; eapply load_error_typeof => //).
        (* VAL_int32 c *)
        destruct (smem_ind s f.(f_inst)) as [j|] eqn:?.
        -- (* Some j *)
           destruct (List.nth_error s.(s_mems) j) as [mem_s_j|] eqn:?.
           ** (* Some mem_s_j*)
              destruct (load (mem_s_j) (Wasm_int.N_of_uint i32m c) off (t_length t)) as [bs|] eqn:?.
              ++ (* Some bs *)
                 apply <<hs, s, f, vs_to_es (wasm_deserialise bs t :: ves')>>'.
                 by apply reduce_load_success
                   with (c := c) (j := j) (mem_s_j := mem_s_j).
              ++ (* None *)
                 apply <<hs, s, f, vs_to_es ves' ++ [:: AI_trap]>>'.
                 by apply reduce_load_failure
                   with (c := c) (j := j) (mem_s_j := mem_s_j).
           ** (* None*)
              apply RS''_error. by eapply load_error_jth with (j := j).
        -- (* None*)
           apply RS''_error. by eapply load_error_smem_ind.

    * (* AI_basic (BI_store t (Some tp) a off) *)
      (* TODO dedupe with the branch below by matching tp later? *)
      destruct ves as [|v [|v' ves']] eqn:?;
        try by (apply RS''_error; apply store_error_size).
      (* v :: v' :: ves' *)
      destruct v' as [c| | |] eqn:?;
        try by (apply RS''_error; eapply store_error_typeof => //).
      (* VAL_int32 c *)
      destruct (types_agree t v) eqn:?.
      + (* true *)
        destruct (smem_ind s f.(f_inst)) as [j|] eqn:?.
        -- (* Some j *)
           destruct (List.nth_error s.(s_mems) j) as [mem_s_j|] eqn:?.
           ** (* Some mem_s_j *)
              destruct (store_packed mem_s_j (Wasm_int.N_of_uint i32m c) off (bits v) (tp_length tp)) as [mem'|] eqn:?.
              ++ (* Some mem' *)
                 apply <<hs, upd_s_mem s (update_list_at s.(s_mems) j mem'), f, vs_to_es ves'>>'.
                 by eapply reduce_store_packed_success with (mem_s_j := mem_s_j).
              ++ (* None *)
                 apply <<hs, s, f, vs_to_es ves' ++ [:: AI_trap]>>'.
                 by eapply reduce_store_packed_failure with (j := j) (mem_s_j := mem_s_j).
           ** (* None *)
              apply RS''_error. by eapply store_error_jth with (j := j).
        -- (* None *)
           apply RS''_error. by eapply store_error_smem.
      + (* false *)
        apply RS''_error. by apply store_error_types_disagree with (v := v) (c := c) (ves' := ves').

    * (* AI_basic (BI_store t None a off) *)
      destruct ves as [|v [|v' ves']] eqn:?;
        try by (apply RS''_error; apply store_error_size).
      (* v :: v' :: ves' *)
      destruct v' as [c| | |] eqn:?;
        try by (apply RS''_error; eapply store_error_typeof => //).
      (* VAL_int32 c *)
      destruct (types_agree t v) eqn:?.
      + (* true *)
        destruct (smem_ind s f.(f_inst)) as [j|] eqn:?.
        -- (* Some j *)
           destruct (List.nth_error s.(s_mems) j) as [mem_s_j|] eqn:?.
           ** (* Some mem_s_j *)
              destruct (store mem_s_j (Wasm_int.N_of_uint i32m c) off (bits v) (t_length t)) as [mem'|] eqn:?.
              ++ (* Some mem' *)
                 apply <<hs, upd_s_mem s (update_list_at s.(s_mems) j mem'), f, vs_to_es ves'>>'.
                 by eapply reduce_store_success with (mem_s_j := mem_s_j).
              ++ (* None *)
                 apply <<hs, s, f, vs_to_es ves' ++ [:: AI_trap]>>'.
                 by eapply reduce_store_failure with (j := j) (mem_s_j := mem_s_j).
           ** (* None *)
              apply RS''_error. by eapply store_error_jth with (j := j).
        -- (* None *)
           apply RS''_error. by eapply store_error_smem.
      + (* false *)
        apply RS''_error. by apply store_error_types_disagree with (v := v) (c := c) (ves' := ves').

    * (* AI_basic BI_current_memory *)
      destruct (smem_ind s f.(f_inst)) as [j|] eqn:?.
      + (* Some j *)
        destruct (List.nth_error s.(s_mems) j) as [s_mem_s_j|] eqn:?.
        -- (* Some j *)
           remember (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j)))) as v' eqn:?.
           apply <<hs, s, f, vs_to_es (v' :: ves)>>'.
           by apply reduce_current_memory with (j := j) (s_mem_s_j := s_mem_s_j).
        -- (* None *)
           apply RS''_error. by apply current_memory_error_jth with (j := j).
      + (* None *)
        apply RS''_error. by apply current_memory_error_smem => //.

    * (* AI_basic BI_grow_memory *)
      destruct ves as [|v ves'] eqn:?;
        try by (apply RS''_error; apply grow_memory_error_0).
      (* v :: ves' *)
      destruct v as [c| | |] eqn:?;
        try by (apply RS''_error; by eapply grow_memory_error_typeof => //).
      (* VAL_int32 c *)
      destruct (smem_ind s f.(f_inst)) as [j|] eqn:?.
      + (* Some j *)
        destruct (List.nth_error s.(s_mems) j) as [s_mem_s_j|] eqn:Heqsmem.
        -- (* Some s_mem_s_j *)
           remember (mem_grow s_mem_s_j (Wasm_int.N_of_uint i32m c)) as mem'.
           destruct mem' as [mem''|].
           ** (* Some mem'' *)
              remember (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j)))) as v'.
              remember (upd_s_mem s (update_list_at s.(s_mems) j mem'')) as s'.
              apply <<hs, s', f, (vs_to_es (v' :: ves'))>>'.
              by eapply reduce_grow_memory with (j := j) (s_mem_s_j := s_mem_s_j) (mem'' := mem'') => //.
           ** (* None *)
              apply <<hs, s, f, vs_to_es (VAL_int32 int32_minus_one :: ves')>>'.
              by eapply reduce_grow_memory_failure with (j := j) (s_mem_s_j := s_mem_s_j).
        -- (* None *)
           apply RS''_error. by eapply grow_memory_error_jth with (j := j).
      + (* None *)
        apply RS''_error. by eapply grow_memory_error_smem => //.

    * (* AI_basic (BI_const _) *)
      by exfalso.

    * (* AI_basic (BI_unop t op) *)
      destruct ves as [|v ves'].
      + (* [::] *)
        apply RS''_error. by apply unop_error.
      + (* v :: ves' *)
        apply <<hs, s, f, vs_to_es (app_unop op v :: ves')>>'.
        by apply reduce_unop.

    * (* AI_basic (BI_binop t op) *)
      destruct ves as [|v2 [|v1 ves']];
        try by (apply RS''_error; apply binop_error_size).
      (* [:: v2, v1 & ves'] *)
      destruct (app_binop op v1 v2) as [v|] eqn:?.
      + (* Some v *)
        apply <<hs, s, f, vs_to_es (v :: ves')>>'.
        by apply reduce_binop.
      + (* None *)
        apply <<hs, s, f, (vs_to_es ves') ++ [:: AI_trap]>>'.
        by apply reduce_binop_trap.

    * (* AI_basic (BI_testop T_i32 testop) *)
      destruct ves as [|[c| | |] ves'] eqn:?;
        try by (apply RS''_error; by eapply testop_i32_error => //).
      + (* [::] *)
        apply RS''_error. by apply testop_error_0.
      + (* VAL_int32 c :: ves' *)
        apply <<hs, s, f, vs_to_es (VAL_int32 (wasm_bool (@app_testop_i i32t testop c)) :: ves')>>'.
        by apply reduce_testop_i32.

    * (* AI_basic (BI_testop T_i64 testop) *)
      (* TODO un-nest this destruct? could make the 'try by' clearer *)
      destruct ves as [|v ves'].
      + (* [::] *)
        apply RS''_error. by apply testop_error_0.
      + (* v :: ves' *)
        destruct v as [|c| |];
          try by (apply RS''_error; by eapply testop_i64_error => //).
        (* VAL_int64 c *)
        apply <<hs, s, f, vs_to_es (VAL_int32 (wasm_bool (@app_testop_i i64t testop c)) :: ves')>>'.
        by eapply reduce_testop_i64.

    * (* AI_basic (BI_testop T_f32 testop) *)
      apply RS''_error. by apply testop_f32_error.

    * (* AI_basic (BI_testop T_f64 testop) *)
      apply RS''_error. by apply testop_f64_error.

    * (* AI_basic (BI_relop t op) *)
      destruct ves as [|v2 [|v1 ves']];
          try by (apply RS''_error; apply relop_error_size).
      (* [:: v2, v1 & ves'] *)
      apply <<hs, s, f, vs_to_es (VAL_int32 (wasm_bool (app_relop op v1 v2)) :: ves')>>'.
      by apply reduce_relop.

    * (* AI_basic (BI_cvtop t2 CVO_convert t1 sx) *)
      destruct ves as [|v ves'];
        try by (apply RS''_error; apply cvtop_error_0).
      (* v :: ves' *)
      destruct (types_agree t1 v) eqn:Ht1.
      + (* true *)
        destruct (cvt t2 sx v) as [v'|] eqn:Heqv'.
        -- (* Some v' *)
           apply <<hs, s, f, vs_to_es (v' :: ves')>>'.
           by apply reduce_cvtop_success.
        -- (* None *)
           apply <<hs, s, f, vs_to_es ves' ++ [::AI_trap]>>'.
           by apply reduce_cvtop_trap.
      + (* false *)
        apply RS''_error. by eapply cvtop_error_types_disagree.

    * (* AI_basic (BI_cvtop t2 CVO_reinterpret t1 sx) *)
      destruct ves as [|v ves'];
        try by (apply RS''_error; apply cvtop_error_0).
      destruct (types_agree t1 v) eqn:?.
      + (* true *)
        destruct sx eqn:Heqsx.
        -- (* Some _ *)
           apply RS''_error. by eapply cvtop_error_reinterpret_sx.
        -- (* None *)
           apply <<hs, s, f, (vs_to_es (wasm_deserialise (bits v) t2 :: ves'))>>'.
           by apply reduce_reinterpret.
      + (* false *)
        apply RS''_error. by eapply cvtop_error_types_disagree.

    * (* AI_trap *)
      by exfalso.

    * (* AI_invoke a *)
      destruct (List.nth_error s.(s_funcs) a) as [cl|] eqn:?.
      + (* Some cl *)
        destruct cl as [i [t1s t2s] ts es | [t1s t2s] cl'] eqn:?.
        -- (* FC_func_native i (Tf t1s t2s) ts es *)
           remember (length t1s) as n eqn:?.
           remember (length t2s) as m eqn:?.
           destruct (length ves >= n) eqn:?.
           ** (* true *)
              destruct (split_n ves n) as [ves' ves''] eqn:?.
              remember (n_zeros ts) as zs eqn:?.
              apply <<hs, s, f, vs_to_es ves'' ++ [::
                AI_local
                m
                (Build_frame (rev ves' ++ zs) i)
                [::AI_basic (BI_block (Tf [::] t2s) es)]
              ]>>'.
              by eapply reduce_invoke_native with (n := n) (ts := ts) (t1s := t1s).
           ** (* false *)
              apply RS''_error.
              by eapply invoke_func_native_error_n with
                (n := n) (t1s := t1s) (t2s := t2s) (i := i) (ts := ts) (es := es).
        -- (* FC_func_host (Tf t1s t2s) cl' *)
           remember (length t1s) as n eqn:?.
           remember (length t2s) as m eqn:?.
           destruct (length ves >= n) eqn:?.
           ** (* true *)
              destruct (split_n ves n) as [ves' ves''] eqn:?.
              destruct (host_application_impl hs s (Tf t1s t2s) cl' (rev ves')) as [hs' [[s' rves]|]] eqn:?.
              ++ (* (hs', Some (s', rves)) *)
                 apply <<hs', s', f, vs_to_es ves'' ++ (result_to_stack rves)>>'.
                 by eapply reduce_invoke_host_success with
                   (n := n) (t1s := t1s) (t2s := t2s) (cl' := cl') (ves' := ves').
              ++ (* (hs', None) *)
                 apply <<hs', s, f, vs_to_es ves ++ [::AI_invoke a]>>'.
                 by eapply reduce_invoke_host_diverge with
                   (n := n) (t1s := t1s) (t2s := t2s) (cl' := cl') (ves' := ves') (ves'' := ves'') => //.
           ** (* false *)
              apply RS''_error.
              by eapply invoke_func_host_error_n with
                (n := n) (t1s := t1s) (t2s := t2s) (cl' := cl').
      + (* None *)
        apply RS''_error. by apply invoke_host_error_ath.

    * (* AI_label ln les es *)
      destruct (es_is_trap es) eqn:?.
      + (* true *)
        apply <<hs, s, f, vs_to_es ves ++ [::AI_trap]>>'.
        by apply reduce_label_trap.
      + (* false *)
        destruct (const_list es) eqn:?.
        -- (* true *)
           apply <<hs, s, f, vs_to_es ves ++ es>>'.
           by apply reduce_label_const.
        -- (* false *)
          simpl in Hmeasure.
          destruct measure as [|measure'] => //.
          injection Hmeasure; clear Hmeasure; move => Hmeasure.
          rewrite - run_step_measure_eq in Hmeasure; last done.
          destruct (run_step measure' hs s f es Hmeasure) as
             [ Hv | Herr | n bvs H | rvs H | hs' s' f' es'] eqn:?.
           ** (* RS'_value hs s f Hv *)
              exfalso. by apply const_trap_contradiction with (es := es).
           ** (* RS'_error hs Herr *)
              apply RS''_error.
              by apply label_error_rec.
           ** (* RS'_break hs s f es n bvs *)
              destruct n as [|n].
              ++ (* 0 *)
                 destruct (length bvs >= ln) eqn:?.
                 --- (* true *)
                     apply <<hs, s, f, vs_to_es ((take ln bvs) ++ ves) ++ les>>'.
                     by apply reduce_label_break_rec.
                 --- (* false *)
                     apply RS''_error.
                     by apply label_error_break_rec with (bvs := bvs).
              ++ (* n.+1 *)
                 apply break(n, bvs).
                 by apply label_break_rec.
           ** (* RS'_return hs s f es rvs H *)
              apply RS''_return with (rvs := rvs).
              (* TODO move into a lemma? *)
              right. destruct H as [i [lh H]].
              by exists ln, les, es, i, lh => //.
           ** (* RS'_normal hs s f es hs' s' f' es' *)
              apply <<hs', s', f', vs_to_es ves ++ [:: AI_label ln les es']>>'.
              by apply reduce_label_rec.

    * (* AI_local ln lf es *)
      destruct (es_is_trap es) eqn:?.
      + (* true *)
        apply <<hs, s, f, vs_to_es ves ++ [::AI_trap]>>'.
        by apply reduce_local_trap.
      + (* false *)
        destruct (const_list es) eqn:?.
        -- (* true *)
           destruct (length es == ln) eqn:?.
           ** (* true *)
              apply <<hs, s, f, vs_to_es ves ++ es>>'.
              by apply reduce_local_const.
           ** (* false *)
              apply RS''_error.
              by apply local_error_const_len.
        -- (* false *)
          simpl in Hmeasure.
          destruct measure as [|measure'] => //.
          injection Hmeasure; clear Hmeasure; move => Hmeasure.
          rewrite - run_step_measure_eq in Hmeasure; last done.
           destruct (run_step measure' hs s lf es Hmeasure) as
             [ Hv | Herr | n bvs | rvs H | hs' s' f' es'] eqn:?.
           ** (* RS'_value hs s f Hv *)
              exfalso. by apply const_trap_contradiction with (es := es).
           ** (* RS'_error hs Herr *)
              apply RS''_error.
              by apply local_error_rec.
           ** (* RS'_break hs s f es n bvs *)
              apply RS''_error.
              by apply local_error_break_rec with (n := n) (bvs := bvs).
           ** (* RS'_return hs s f es rvs H *)
              destruct (length rvs >= ln) eqn:?.
              ++ (* true *)
                 apply <<hs, s, f, vs_to_es (take ln rvs ++ ves)>>'.
                 by apply reduce_local_return_rec.
              ++ (* false *)
                 apply RS''_error.
                 apply local_return_error with (rvs := rvs) => //.
           ** (* RS'_normal hs s f es hs' s' f' es' *)
              apply <<hs', s', f, vs_to_es ves ++ [:: AI_local ln f' es']>>'.
              by apply reduce_local_rec.
  }
Defined.

(***************************************)

Definition run_step_with_measure hs s f es :=
  @run_step (run_step_measure es) hs s f es (Logic.eq_refl (run_step_measure es)).

Definition run_step_compat (d : depth) (cfg : config_tuple) : res_tuple :=
  let: (hs, s, f, es) := cfg in
  match run_step_with_measure hs s f es with
  | RS'_normal hs' s' f' es' _ => (hs', s', f', RS_normal es')
  | _ => (hs, s, f, RS_crash C_error)
  end.

Fixpoint run_v hs s f es (fuel : fuel) : ((host_state * store_record * res)%type) :=
  match fuel with
  | 0 => (hs, s, R_crash C_exhaustion)
  | fuel.+1 =>
    if es_is_trap es
    then (hs, s, R_trap)
    else
      if const_list es
      then (hs, s, R_value (fst (split_vals_e es)))
      else
        match run_step_with_measure hs s f es with
        | RS'_normal hs' s' f' es' _ => run_v hs' s' f' es' fuel
        | RS'_error _ => (hs, s, R_crash C_error)
        | _ => (hs, s, R_crash C_error)
        end
  end.

Definition terminal_form (es: seq administrative_instruction) :=
  const_list es \/ es = [::AI_trap].

Definition not_lf_return (es: seq administrative_instruction) (n: nat) :=
  forall lh, ~ lfilled n lh [::AI_basic BI_return] es.

(* XXX do not separate vcs and es? *)
Lemma t_progress_e' : forall (d : depth) s C C' f vcs es t1s t2s lab ret (hs : host_state),
    e_typing s C es (Tf t1s t2s) ->
    C = (upd_label (upd_local_return C' (map typeof f.(f_locs)) ret) lab) ->
    inst_typing s f.(f_inst) C' ->
    map typeof vcs = t1s ->
    store_typing s ->
    (forall n lh k, lfilled n lh [::AI_basic (BI_br k)] es -> k < n) ->
    (forall n, not_lf_return es n) ->
    terminal_form (v_to_e_list vcs ++ es) \/
    exists s' f' es' hs', reduce hs s f (v_to_e_list vcs ++ es) hs' s' f' es'.
Proof.
  intros d s C C' f vcs es t1s t2s lab ret hs Hetype ? Hitype ? Hstype HLFbr HLFret.
  destruct (run_step_with_measure hs s f (v_to_e_list vcs ++ es))
    as [Hval | Herr | n bvs Hbr | rvs Hret | hs' s' f' es' Hr].
  - (* RS'_value *)
    left. unfold terminal_form.
    destruct Hval as [Hconst | Htrap]; [left | right] => //.
    by move/es_is_trapP in Htrap.
  - (* RS'_error *)
    exfalso.
    apply Herr.
    exists C, C', ret, lab, t2s.
    repeat split => //.
    apply et_composition' with (t2s := t1s) => //.
    apply ety_a'; first by apply const_list_is_basic; apply v_to_e_is_const_list.
    rewrite to_b_v_to_e_is_bi_const. subst t1s.
    by apply bet_const'.
  - (* RS'_break *)
    exfalso.
    destruct Hbr as [i [j [lh [Heqj [HLF Hbase]]]]].
    apply lfilled_collapse_empty_vs_base in HLF as [lh' HLF'] => //.
    move/lfilledP in HLF'.
    apply HLFbr in HLF'.
    by lias.
  - (* RS'_return *)
    exfalso.
    destruct Hret as [i [lh [HLF Hbase]]].
    apply lfilled_collapse_empty_vs_base in HLF as [lh' HLF'] => //.
    move/lfilledP in HLF'.
    by apply (HLFret i lh').
  - right. exists s', f', es', hs' => //.
Qed.

End Host_func.

Module EmptyHost.

Definition host_function := void.

Definition host_function_eq_dec : forall f1 f2 : host_function, {f1 = f2} + {f1 <> f2}.
Proof. decidable_equality. Defined.

Definition host_function_eqb f1 f2 : bool := host_function_eq_dec f1 f2.
Definition host_functionP : Equality.axiom host_function_eqb :=
  eq_dec_Equality_axiom host_function_eq_dec.

Canonical Structure host_function_eqMixin := EqMixin host_functionP.
Canonical Structure host_function_eqType :=
  Eval hnf in EqType host_function host_function_eqMixin.

Definition host : Type := host host_function_eqType.

Definition store_record := store_record host_function_eqType.
Definition function_closure := function_closure host_function_eqType.

Definition host_instance : host.
Proof.
  by refine {|
      host_state := unit_eqType ;
      host_application _ _ _ _ _ _ _ := False
    |}; intros; exfalso; auto.
Defined.

Definition config_tuple := config_tuple host_instance.
Definition res_tuple := res_tuple host_instance.

Definition host_state := host_state host_instance.

End EmptyHost.

Module Interpreter_func.

Export EmptyHost.

Definition host_application_impl : host_state -> store_record -> function_type -> host_function_eqType -> seq value ->
                                   (host_state * option (store_record * result)).
Proof.
  move => ??? hf; by inversion hf.
Defined.

Definition host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).
Proof.
  move => ??? hf; by inversion hf.
Defined.

Definition run_v := run_v host_application_impl_correct.

Definition run_step := run_step host_application_impl_correct.

Definition run_step_compat := run_step_compat host_application_impl_correct.

(** State whether a list of administrative instruction is a final value. **)
Definition is_const_list : list administrative_instruction -> option (list value) :=
  @those_const_list.

End Interpreter_func.

