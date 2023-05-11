(** Wasm interpreter **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From Wasm Require Import common opsem properties tactic type_preservation type_progress.
From Coq Require Import ZArith.BinInt.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Export operations host type_checker.
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
(*Let administrative_instruction := administrative_instruction host_function.*)
Let host_state := host_state host_instance.

(*Let vs_to_es : seq value -> seq administrative_instruction := @vs_to_es _.*)

Let e_typing := @e_typing host_function.
Let inst_typing := @inst_typing host_function.

Variable host_application_impl : host_state -> store_record -> function_type -> host_function -> seq value ->
                       (host_state * option (store_record * result)).

Hypothesis host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).

Inductive res_step : Type :=
| RS_crash : res_crash -> res_step
| RS_break : nat -> list value -> res_step
| RS_return : list value -> res_step
| RS_normal : list administrative_instruction -> res_step.

(* TODO: the break/return cases also need some proofs to go with them,
 * see interpreter_func_sound. *)
Inductive res_step'
  (hs : host_state) (s : store_record) (f : frame)
  (es : list administrative_instruction) : Type :=
| RS'_exhaustion : res_step' hs s f es
| RS'_value :
    const_list es \/ es_is_trap es ->
    res_step' hs s f es
| RS'_error :
    (~ exists C t,
      inst_typing s f.(f_inst) C /\
      store_typing s /\
      e_typing s C es t) ->
    res_step' hs s f es
| RS'_break : host_state -> store_record -> frame -> nat -> list value -> res_step' hs s f es (* TODO needs some reduce proof *)
| RS'_return : host_state -> store_record -> frame -> list value -> res_step' hs s f es (* TODO needs some reduce proof *)
| RS'_normal hs' s' f' es' :
    reduce hs s f es hs' s' f' es' ->
    res_step' hs s f es.

(** Main proof for the [RS_break] case. **)
(* Lemma reduce_label_break: forall fuel d hs s f es es' hs' s' f' es'' n, *)
(* run_step_with_fuel fuel d (hs, s, f, es') = (hs', s', f', RS_break 0 es'') -> *)
(*   n <= size es'' -> *)
(*   reduce hs s f ([:: AI_label n es es']) hs' s' f' *)
(*    (v_to_e_list (rev (take n es'')) ++ es). *)
Inductive res_step'_separate_e
  (hs : host_state) (s : store_record) (f : frame)
  (ves : list value) (e : administrative_instruction) : Type :=
| RS''_exhaustion : res_step'_separate_e hs s f ves e
| RS''_error :
    (~ exists C t1s t2s t1s',
      (* XXX easier to rev LHS or RHS? *)
      rev (map typeof ves) = t1s' ++ t1s /\
      inst_typing s f.(f_inst) C /\
      store_typing s /\
      e_typing s C [::e] (Tf t1s t2s)) ->
    res_step'_separate_e hs s f ves e

| RS''_break k ves' :
    forall n lh es vs0 ces,
      lfilled k lh (vs0 ++ [::AI_basic (BI_br k)]) es ->
      v_to_e_list ves' = rev vs0 ->
      reduce
        hs s f [::AI_label n ces es]
        hs s f (drop (size vs0 - n) vs0 ++ ces) ->
      res_step'_separate_e hs s f ves e

| RS''_return (ves' : list value) : False -> res_step'_separate_e hs s f ves e
(* TODO RS''_return needs a proof *)
| RS''_normal hs' s' f' es' :
    reduce hs s f ((vs_to_es ves) ++ [::e]) hs' s' f' es' ->
    res_step'_separate_e hs s f ves e.

(* Notation for RS'_normal. This forces hs', s', f' es' to be explicitly
 * stated. Their values could be inferred from the type of H instead but we
 * want to make those values clear. *)
Notation "<< hs' , s' , f' , es' >>" := (@RS'_normal _ _ _ _ hs' s' f' es').
Notation "<< hs' , s' , f' , es' >>'" := (@RS''_normal _ _ _ _ _ hs' s' f' es').
(* TODO better (or none?) break notation? *)
Notation "break( n , ves' )" := (@RS''_break _ _ _ _ _ n ves').

(* Using this as a TODO placeholder *)
Axiom admitted_TODO : forall A : Type, A.

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

Check config_typing.

Definition config_tuple_typing (cfg : config_tuple) (t : seq value_type) : Prop :=
  match cfg with
  | (_, s, f, es) => config_typing s f es t
  end.

Definition config_tuple_separate_e_typing (cfg : config_one_tuple_without_e) (e : administrative_instruction) (t : seq value_type) : Prop :=
  match cfg with
  | (_, s, f, vs) => config_typing s f ((vs_to_es vs) ++ [::e]) t
  end.

Definition res_tuple := (host_state * store_record * frame * res_step)%type.

(* TODO *)
Axiom coerce_res : forall hs s f es ves e (r : res_step'_separate_e hs s f ves e),
  res_step' hs s f es.

(* TODO use some ltacs from progress/preservation? invert_typeof_vcs etc *)

(* TODO auto instantiate lh, k? *)
(* TODO better name *)
Ltac solve_lfilled_0 :=
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
  repeat rewrite size_cat; try rewrite size_rev; rewrite size_map; simpl; lias.

Lemma vs_to_es_cons : forall v ves,
  vs_to_es ves ++ [:: AI_basic (BI_const v)] = vs_to_es (v :: ves).
Proof.
  intros.
  unfold vs_to_es. rewrite rev_cons. rewrite cats1. unfold v_to_e_list. rewrite map_rcons.
  by apply f_equal.
Qed.

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
        try solve_lfilled_0; apply r_simple
  end.

Lemma error_rec : forall s f e es es' es'' ves,
  es' = e :: es'' ->
  split_vals_e es = (ves, es') ->
  ~ (exists C t1s t2s t1s',
      rev [seq typeof i | i <- rev ves] = t1s' ++ t1s /\
      inst_typing s (f_inst f) C /\
      store_typing s /\ e_typing s C [:: e] (Tf t1s t2s)) ->
  ~ (exists C t,
      inst_typing s (f_inst f) C /\ store_typing s /\ e_typing s C es t).
Proof.
  (* TODO consistent naming: Hsplit / Hesves *)
  intros s f e es es' es'' ves ? Hsplit Hrec [C [[t1s t2s] [? [? Hetype]]]].
  apply split_vals_e_v_to_e_duality in Hsplit. subst es es'.
  apply e_composition_typing in Hetype as [ts [t1s' [t2s' [t3s [? [? [Hetypeves Hetype]]]]]]].
  rewrite <- cat1s in Hetype.
  apply e_composition_typing in Hetype as [ts' [t1s'' [t2s'' [t3s' [? [? [? _]]]]]]].
  apply Hrec.
  exists C, t1s'', t3s', ts'.
  repeat split => //.
  apply et_to_bet in Hetypeves as Hbtype;
    last by apply const_list_is_basic; apply v_to_e_is_const_list.
  apply Const_list_typing in Hbtype.
  rewrite <- H3. (* TODO fragile name *)
  rewrite Hbtype.
Admitted.

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
  - solve_lfilled_0. by rewrite <- catA.
  - by solve_lfilled_0.
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
    try by solve_lfilled_0.
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

(* TODO consistent lemma naming *)
(* TODO add comments to separate lemmas for different instrs? *)
(* AI_basic BI_unreachable *)
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
    (es' := [::]); try by solve_lfilled_0.
  apply r_simple. by apply rs_nop.
Qed.

(* TODO extend simpl_reduce_simple to handle this? *)
Lemma reduce_drop : forall (hs : host_state) s f v ves',
  reduce
    hs s f (vs_to_es (v :: ves') ++ [:: AI_basic BI_drop])
    hs s f (vs_to_es ves').
Proof.
  intros ??? v ves'.
  eapply r_label with
    (k := 0) (lh := (LH_base (vs_to_es ves') [::]))
    (es := vs_to_es [:: v] ++ [:: AI_basic BI_drop])
    (es' := [::]); try by solve_lfilled_0.
  apply r_simple. by apply rs_drop.
Qed.

Lemma drop_error : forall s inst ves,
  ves = [::] ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic BI_drop] (Tf t1s t2s).
Proof.
  intros s inst ves Heqves [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
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

Lemma select_error_i32 : forall s inst v3 v2 v1 ves ves',
  typeof v3 <> T_i32 ->
  ves = v3 :: v2 :: v1 :: ves' ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic BI_select] (Tf t1s t2s).
Proof.
  intros s inst v3 v2 v1 ves ves' Hv Heqves [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Select_typing in Hbtype as [? [? [??]]]. subst t1s t2s.

  (* TODO move this into the ltac? *)
  replace ([:: x0; x0; T_i32]) with ([:: x0; x0] ++ [:: T_i32]) in Ht1s => //.
  by cats1_last_eq Ht1s.
Qed.

Lemma select_error_size : forall s inst ves,
  size ves < 3 ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic BI_select] (Tf t1s t2s).
Proof.
  intros s inst ves ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
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
  - by solve_lfilled_0.
  - solve_lfilled_0. apply List.app_inj_tail_iff. by split; subst m.
Qed.

Lemma block_error : forall s inst ves bt1s bt2s es,
  size ves < size bt1s ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_block (Tf bt1s bt2s) es)] (Tf t1s t2s).
Proof.
  intros s inst ves bt1s bt2s es ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
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
    by destruct (size t1s < size ves) eqn:? => //; lias.
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
  - solve_lfilled_0.
    replace (v_to_e_list (rev ves))
      with (v_to_e_list (rev ves'') ++ v_to_e_list (rev ves')).
    * by rewrite <- catA.
    * rewrite <- (cat_take_drop (length t1s) ves).
      repeat rewrite v_to_e_rev.
      rewrite <- v_to_e_cat.
      rewrite <- rev_cat.
      by subst ves' ves''.
  - solve_lfilled_0. by rewrite Hlen'.
Qed.

Lemma loop_error : forall s inst ves lt1s lt2s es,
  size lt1s > size ves ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_loop (Tf lt1s lt2s) es)] (Tf t1s t2s).
Proof.
  intros s inst ves lt1s lt2s es Hlen [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
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
  - solve_lfilled_0.
    (* TODO can this be simplified? *)
    replace c with (Wasm_int.int_zero i32m) => //.
    symmetry. by apply/eqP.
  - by solve_lfilled_0.
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
    try by solve_lfilled_0.
  apply r_simple. apply rs_if_true with (n := c).
  apply/eqP. by lias.
Qed.

Lemma if_error_0 : forall s inst ves tf es1 es2,
  ves = [::] ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_if tf es1 es2)] (Tf t1s t2s).
Proof.
  intros s inst ves tf es1 es2 ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  subst ves. destruct tf.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply If_typing in Hbtype as [? [? [? [??]]]]. subst t1s.
  by size_unequal Ht1s.
Qed.

Lemma if_error_typeof : forall s inst v ves ves' tf es1 es2,
  typeof v <> T_i32 ->
  ves = v :: ves' ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_if tf es1 es2)] (Tf t1s t2s).
Proof.
  intros s inst v ves ves' tf es1 es2 ?? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  subst ves. destruct tf.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply If_typing in Hbtype as [? [? [? [??]]]]. subst t1s.
  by cats1_last_eq Ht1s.
Qed.

Lemma break_br : forall j ves,
  exists k m vs0 lh es,
    k + j = m /\
    lfilled k lh (vs0 ++ [:: AI_basic (BI_br m)]) es /\
    v_to_e_list ves = rev vs0.
Proof.
  intros j ves.
  exists 0, j, (rev (v_to_e_list ves)).
  exists ((LH_base (vs_to_es ves) [::])).
  eexists.
  repeat split; try by solve_lfilled_0.
Qed.

Lemma reduce_br_if_true : forall (hs : host_state) s f c ves' j,
  c != Wasm_int.int_zero i32m ->
  reduce
    hs s f (vs_to_es (VAL_int32 c :: ves') ++ [:: AI_basic (BI_br_if j)])
    hs s f (vs_to_es ves' ++ [:: AI_basic (BI_br j)]).
Proof.
  intros ??? c ves' j ?.
  (* TODO make simpl_reduce_simple applicable? *)
  apply r_label with
    (k := 0) (lh := (LH_base (vs_to_es ves') [::]))
    (es := vs_to_es [::VAL_int32 c] ++ [:: AI_basic (BI_br_if j)])
    (es' := [:: AI_basic (BI_br j)]);
    try by solve_lfilled_0.
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
    try by solve_lfilled_0.
  apply r_simple. apply rs_br_if_false. by apply/eqP.
Qed.

Lemma br_if_error_0 : forall s inst ves j,
  ves = [::] ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_br_if j)] (Tf t1s t2s).
Proof.
  intros s inst ves j ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Br_if_typing in Hbtype as [ts [ts' [? [? [??]]]]]. subst t1s t2s.
  by apply_cat0_inv Ht1s.
Qed.

Lemma br_if_error_i32 : forall s inst v ves ves' j,
  typeof v <> T_i32 ->
  ves = v :: ves' ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_br_if j)] (Tf t1s t2s).
Proof.
  intros s inst v ves ves' j ?? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
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
    try by by solve_lfilled_0.
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
    try by solve_lfilled_0.
  apply r_simple. by apply rs_br_table_length.
Qed.

Lemma br_table_error_0 : forall s inst ves js j,
  ves = [::] ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_br_table js j)] (Tf t1s t2s).
Proof.
  intros s inst ves js j ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Br_table_typing in Hbtype as [ts [ts' [??]]]. subst t1s.
  by apply_cat0_inv Ht1s.
Qed.

Lemma br_table_error_kth : forall s inst c ves ves' k js j,
  ves = VAL_int32 c :: ves' ->
  k = Wasm_int.nat_of_uint i32m c ->
  k < length js ->
  List.nth_error js k = None ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_br_table js j)] (Tf t1s t2s).
Proof.
  intros s inst c ves ves' k js j ??? Hkth [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  subst ves k.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Br_table_typing in Hbtype as [? [? [??]]]. subst t1s.
  apply List.nth_error_None in Hkth.
  by lias.
Qed.

Lemma br_table_error_i32 : forall s inst v ves ves' js j,
  typeof v <> T_i32 ->
  ves = v :: ves' ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_br_table js j)] (Tf t1s t2s).
Proof.
  intros s inst v ves ves' js j ?? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
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
    try by solve_lfilled_0.
  apply r_call with (a := a) (i := j) => //.
Qed.

Lemma call_error : forall (hs : host_state) s f ves j,
  List.nth_error (inst_funcs f.(f_inst)) j = None ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_call j)] (Tf t1s t2s).
Proof.
  intros s f v ves j Hjth [C [t1s [t2s [t1s' [Ht1s [Hitype [? Hetype]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Call_typing host_instance) in Hbtype as [? [t1s'' [t2s'' [? [? [??]]]]]].
  apply func_context_store with (j := j) (x := Tf t1s'' t2s'') in Hitype
    as [? Hjth'] => //.
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
    try by solve_lfilled_0.
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
    try by solve_lfilled_0.
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
    try by solve_lfilled_0.
  by apply r_call_indirect_failure2.
Qed.

Lemma call_indirect_error_0 : forall s f ves j,
  ves = [::] ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_call_indirect j)] (Tf t1s t2s).
Proof.
  intros s f ves j ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]]. subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Call_indirect_typing host_instance) in Hbtype as [? [? [? [? [? [? [??]]]]]]].
  subst t1s. by size_unequal Ht1s.
Qed.

Lemma call_indirect_error_typeof : forall s f v ves ves' j,
  typeof v <> T_i32 ->
  ves = v :: ves' ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_call_indirect j)] (Tf t1s t2s).
Proof.
  intros s f v ves ves' j Hv ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]]. subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Call_indirect_typing host_instance) in Hbtype as [? [? [? [? [? [? [??]]]]]]].
  subst t1s. by cats1_last_eq Ht1s.
Qed.

Lemma call_indirect_error_ath : forall s f c ves ves' j a,
  ves = VAL_int32 c :: ves' ->
  stab_addr s f (Wasm_int.nat_of_uint i32m c) = Some a ->
  List.nth_error s.(s_funcs) a = None ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_call_indirect j)] (Tf t1s t2s).
Proof.
  intros s f c ves ves' j a ?? Hath [C [t1s [t2s [t1s' [Ht1s [Hitype [? Hetype]]]]]]]. subst ves.
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
  - by solve_lfilled_0.
  - by solve_lfilled_0.
Qed.

Lemma get_local_error_jth_none : forall s f ves j,
  List.nth_error f.(f_locs) j = None ->
  j < length f.(f_locs) ->  (* TODO unused? *)
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_get_local j)] (Tf t1s t2s).
Proof.
  (* TODO rename Hitype to Hitype everywhere *)
  intros s f ves j Hjth ? [C [t1s [t2s [t1s' [? [Hitype [? Hetype]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Get_local_typing host_instance) in Hbtype as [? [Hjth' [??]]].
  apply inst_t_context_local_empty in Hitype.
  rewrite Hitype in Hjth'.
  destruct j => //.
Qed.

Lemma get_local_error_length : forall s f ves j,
  j >= length f.(f_locs) ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_get_local j)] (Tf t1s t2s).
Proof.
  intros s f ves j Hlen [C [t1s [t2s [t1s' [? [Hitype [? Hetype]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Get_local_typing host_instance) in Hbtype as [? [? [? Hlen']]].
  apply inst_t_context_local_empty in Hitype.
  rewrite Hitype in Hlen'. by destruct j => //.
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
  - by solve_lfilled_0.
  - by solve_lfilled_0.
Qed.

Lemma set_local_error_0 : forall (hs : host_state) s f ves j,
  ves = [::] ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_set_local j)] (Tf t1s t2s).
Proof.
  intros hs s f ves j ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]]. subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply_cat0_inv Ht1s.
  apply (Set_local_typing host_instance) in Hbtype as [? [? [??]]].
  by destruct t2s => //.
Qed.

Lemma set_local_error_length : forall (hs : host_state) s f v ves ves' j,
  ves = v :: ves' ->
  (j < length f.(f_locs)) = false ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_set_local j)] (Tf t1s t2s).
Proof.
  intros hs s f v ves ves' j ? Hlen [C [t1s [t2s [t1s' [? [Hitype [? Hetype]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Set_local_typing host_instance) in Hbtype as [? [? [? Hlen']]].
  apply inst_t_context_local_empty in Hitype.
  rewrite Hitype in Hlen'. by destruct j => //.
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
  - by solve_lfilled_0.
  - by solve_lfilled_0.
Qed.

Lemma tee_local_error_0 : forall (hs : host_state) s f ves j,
  ves = [::] ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_tee_local j)] (Tf t1s t2s).
Proof.
  intros hs s f ves j ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]]. subst ves.
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
  - by solve_lfilled_0.
  - by solve_lfilled_0.
Qed.

Lemma get_global_error : forall (hs : host_state) s f ves j,
  sglob_val s f.(f_inst) j = None ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_get_global j)] (Tf t1s t2s).
Proof.
  intros hs s f ves j Hjth [C [t1s [t2s [t1s' [Ht1s [Hitype [? Hetype]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Get_global_typing host_instance) in Hbtype as [t [Hjth' [??]]].
  destruct (List.nth_error (tc_global C) j) eqn:Heqg => //.
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
  - by solve_lfilled_0.
  - by solve_lfilled_0.
Qed.

Lemma set_global_error_0 : forall (hs : host_state) s f ves j,
  ves = [::] ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_set_global j)] (Tf t1s t2s).
Proof.
  intros hs s f ves j ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]]. subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply_cat0_inv Ht1s.
  apply (Set_global_typing host_instance) in Hbtype as [? [? [? [? [? [??]]]]]].
  by destruct t2s => //.
Qed.

Lemma set_global_error_jth : forall (hs : host_state) s f v ves ves' j,
  ves = v :: ves' ->
  supdate_glob s f.(f_inst) j v = None ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_set_global j)] (Tf t1s t2s).
Proof.
  intros hs s f v ves ves' j ? Hjth [C [t1s [t2s [t1s' [Ht1s [Hitype [? Hetype]]]]]]].
  subst ves.
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
    try by solve_lfilled_0.
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
    try by solve_lfilled_0.
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
    try by solve_lfilled_0.
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
    try by solve_lfilled_0.
  by apply r_load_failure with (i := j) (m := mem_s_j).
Qed.

Lemma load_error_0 : forall s f ves t tp_sx a off,
  ves = [::] ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_load t tp_sx a off)] (Tf t1s t2s).
Proof.
  intros s f ves t tp_sx a off ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  subst ves. apply_cat0_inv Ht1s.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  by apply (Load_typing host_instance) in Hbtype as [[|] [? [? [??]]]].
Qed.

Lemma load_error_typeof : forall s f v ves ves' t tp_sx a off,
  typeof v <> T_i32 ->
  ves = v :: ves' ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_load t tp_sx a off)] (Tf t1s t2s).
Proof.
  intros s f v ves ves' t tp_sx a off Hv ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Load_typing host_instance) in Hbtype as [? [? [? [??]]]]. subst t1s t2s.
  by cats1_last_eq Ht1s.
Qed.

Lemma load_error_jth : forall s f ves ves' c t tp_sx a off j,
  ves = VAL_int32 c :: ves' ->
  smem_ind s f.(f_inst) = Some j ->
  List.nth_error s.(s_mems) j = None ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_load t tp_sx a off)] (Tf t1s t2s).
Proof.
  intros s f ves ves' c t tp_sx a off j ? Hsmem Hjth [C [t1s [t2s [t1s' [Ht1s [Hitype [? Hetype]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Load_typing host_instance) in Hbtype as [? [? [? [??]]]].
  apply mem_context_store in Hitype as [j' [Hsmem' Hjth']] => //.
  rewrite Hsmem in Hsmem'. injection Hsmem' as Hsmem'. subst j'.
  by apply Hjth'.
Qed.

Lemma load_error_smem_ind : forall s f ves ves' c t tp_sx a off,
  ves = VAL_int32 c :: ves' ->
  smem_ind s f.(f_inst) = None ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_load t tp_sx a off)] (Tf t1s t2s).
Proof.
  intros s f ves ves' c t tp_sx a off ? Hsmem [C [t1s [t2s [t1s' [Ht1s [Hitype [? Hetype]]]]]]].
  subst ves.
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
  - by solve_lfilled_0.
  - by solve_lfilled_0.
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
    try by solve_lfilled_0.
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
  - by solve_lfilled_0.
  - by solve_lfilled_0.
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
    try by solve_lfilled_0.
  by apply r_store_failure
    with (i := j) (m := mem_s_j) (k := c) (off := off) (t := t) (v := v).
Qed.

Lemma store_error_size : forall s inst ves t tp a off,
  size ves < 2 ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_store t tp a off)] (Tf t1s t2s).
Proof.
  intros s inst ves t tp a off ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Store_typing host_instance) in Hbtype as [? [??]].
  subst t1s. by size_unequal Ht1s.
Qed.

Lemma store_error_typeof : forall s inst v v' ves ves' t tp a off,
  ves = v :: v' :: ves' ->
  typeof v' <> T_i32 ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_store t tp a off)] (Tf t1s t2s).
Proof.
  intros s inst v v' ves ves' t tp a off ?? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Store_typing host_instance) in Hbtype as [? [??]].
  subst t1s.
  (* TODO move this into the ltac? *)
  replace [:: T_i32; t] with ([:: T_i32] ++ [:: t]) in Ht1s => //.
  by repeat cats1_last_eq Ht1s.
Qed.

Lemma store_error_types_disagree : forall s inst v c ves ves' t tp a off,
  ves = v :: VAL_int32 c :: ves' ->
  types_agree t v = false ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_store t tp a off)] (Tf t1s t2s).
Proof.
  intros s inst v c ves ves' t tp a off ?? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
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
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_store t tp a off)] (Tf t1s t2s).
Proof.
  intros s inst v c ves ves' t tp a off j ?? Hsmem ?
    [C [t1s [t2s [t1s' [Ht1s [Hitype [? Hetype]]]]]]].
  subst ves.
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
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_store t tp a off)] (Tf t1s t2s).
Proof.
  intros s inst v c ves ves' t tp a off ?? Hsmem [C [t1s [t2s [t1s' [Ht1s [Hitype [? Hetype]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Store_typing host_instance) in Hbtype as [? [??]].
  apply mem_context_store in Hitype as [? [Hsmem' ?]] => //.
  by rewrite Hsmem in Hsmem'.
Qed.

Lemma reduce_current_memory : forall (hs : host_state) s f v ves s_mem_s_j j,
  smem_ind s (f_inst f) = Some j ->
  List.nth_error (s_mems s) j = Some s_mem_s_j ->
  v = VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j))) ->
  reduce
    hs s f (vs_to_es ves ++ [:: AI_basic BI_current_memory])
    hs s f (vs_to_es (v :: ves)).
Proof.
  intros hs s f v ves s_mem_s_j j ???. subst v.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves) [::]));
    try by solve_lfilled_0.
  (* TODO rename s_mem_s_j to m? *)
  by apply r_current_memory with (i := j) (m := s_mem_s_j).
Qed.

Lemma current_memory_error_jth : forall s f ves j,
  smem_ind s f.(f_inst) = Some j ->
  List.nth_error (s_mems s) j = None ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic BI_current_memory] (Tf t1s t2s).
Proof.
  intros s f ves j Hsmem ? [C [t1s [t2s [t1s' [Ht1s [Hitype [? Hetype]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Current_memory_typing host_instance) in Hbtype as [??] => //.
  apply mem_context_store in Hitype as [j' [Hsmem' Hjth]] => //.
  rewrite Hsmem' in Hsmem. injection Hsmem as Hsmem. subst j'.
  by apply Hjth.
Qed.

Lemma current_memory_error_smem : forall s f ves,
  smem_ind s f.(f_inst) = None ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic BI_current_memory] (Tf t1s t2s).
Proof.
  intros s f ves Hsmem [C [t1s [t2s [t1s' [Ht1s [Hitype [? Hetype]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Current_memory_typing host_instance) in Hbtype as [??] => //.
  apply mem_context_store in Hitype as [? [Hsmem' ?]] => //.
  by rewrite Hsmem' in Hsmem.
Qed.

(* TODO extend simpl_reduce_simple to handle this? *)
Lemma reduce_grow_memory : forall (hs : host_state) s s' f c v ves' mem'' s_mem_s_j j l,
  smem_ind s (f_inst f) = Some j ->
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
    try by solve_lfilled_0.
  by apply r_grow_memory_success with (m := s_mem_s_j) (c := c).
Qed.

Lemma reduce_grow_memory_failure : forall (hs : host_state) s f c ves' s_mem_s_j j l,
  smem_ind s (f_inst f) = Some j ->
  List.nth_error (s_mems s) j = Some s_mem_s_j ->
  l = mem_size s_mem_s_j ->
  mem_grow s_mem_s_j (Wasm_int.N_of_uint i32m c) = None ->
  reduce
    hs s f (vs_to_es (VAL_int32 c :: ves') ++ [:: AI_basic BI_grow_memory])
    hs s f (vs_to_es (VAL_int32 int32_minus_one :: ves')).
Proof.
  intros hs s f c ves' s_mem_s_j j l ????. subst l.
  eapply r_label with (k := 0) (lh := (LH_base (vs_to_es ves') [::]));
    try by solve_lfilled_0.
  by eapply r_grow_memory_failure with (m := s_mem_s_j) (i := j).
Qed.

Lemma grow_memory_error_0 : forall s inst ves,
  ves = [::] ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic BI_grow_memory] (Tf t1s t2s).
Proof.
  intros s inst ves ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
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
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic BI_grow_memory] (Tf t1s t2s).
Proof.
  intros s f ves ves' j c ? Hsmem ? [C [t1s [t2s [t1s' [Ht1s [Hitype [? Hetype]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Grow_memory_typing host_instance) in Hbtype as [? [? [??]]] => //.
  apply mem_context_store in Hitype as [j' [Hsmem' Hjth]] => //.
  rewrite Hsmem' in Hsmem. injection Hsmem as Hsmem. subst j'.
  by apply Hjth.
Qed.

Lemma grow_memory_error_smem : forall s f ves ves' c,
  ves = VAL_int32 c :: ves' ->
  smem_ind s f.(f_inst) = None ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s f.(f_inst) C /\
    store_typing s /\
    e_typing s C [:: AI_basic BI_grow_memory] (Tf t1s t2s).
Proof.
  intros s f ves ves' c ? Hsmem [C [t1s [t2s [t1s' [Ht1s [Hitype [? Hetype]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Grow_memory_typing host_instance) in Hbtype as [? [? [??]]] => //.
  apply mem_context_store in Hitype as [? [Hsmem' ?]] => //.
  by rewrite Hsmem' in Hsmem.
Qed.

Lemma grow_memory_error_typeof : forall s inst v ves ves',
  typeof v <> T_i32 ->
  ves = v :: ves' ->
  ~ exists C t1s t2s t1s',
    rev [seq typeof i | i <- ves] = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic BI_grow_memory] (Tf t1s t2s).
Proof.
  intros s inst v ves ves' Hv Heqves [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply (Grow_memory_typing host_instance) in Hbtype as [? [? [??]]] => //. subst t1s t2s.
  by cats1_last_eq Ht1s.
Qed.

Lemma reduce_unop : forall (hs : host_state) s f t op v ves',
  reduce
    hs s f (vs_to_es (v :: ves') ++ [:: AI_basic (BI_unop t op)])
    hs s f (vs_to_es (app_unop op v :: ves')).
Proof. intros. simpl_reduce_simple. by apply rs_unop. Qed.

(* XXX could move C t1s t2s t1s' into the forall without changing semantics *)
Lemma unop_error : forall s inst ves t op,
  ves = [::] ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_unop t op)] (Tf t1s t2s).
Proof.
  intros s inst ves t op Heqves [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply_cat0_inv Ht1s.
  by apply Unop_typing in Hbtype as [? [[|] ?]].
  (* XXX which is better?
   * apply Unop_typing in Hbtype as [? [ts ?]]. by destruct ts => //. *)
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

Lemma binop_error_size : forall s inst ves t op,
  size ves < 2 ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_binop t op)] (Tf t1s t2s).
Proof.
  intros s inst ves t op ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Binop_typing in Hbtype as [? [ts' ?]].
  subst t1s t2s.
  by size_unequal Ht1s.
Qed.

(* 0 arguments given to testop *)
Lemma testop_error_0 : forall s inst ves t testop,
  ves = [::] ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_testop t testop)] (Tf t1s t2s).
Proof.
  intros s inst ves t testop ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
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

Lemma testop_i32_error : forall s inst v ves ves' testop,
  typeof v <> T_i32 ->
  ves = v :: ves' ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_testop T_i32 testop)] (Tf t1s t2s).
Proof.
  intros s inst v ves ves' testop ?? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
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

Lemma testop_i64_error : forall s inst v ves ves' testop,
  typeof v <> T_i64 ->
  ves = v :: ves' ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_testop T_i64 testop)] (Tf t1s t2s).
Proof.
  intros s inst v ves ves' testop ?? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Testop_typing in Hbtype as [? [ts' ?]].
  subst ves t1s t2s.
  by cats1_last_eq Ht1s.
Qed.

(* TODO dedupe these two (is_int_t = false)
 * or simpler to keep them separate? *)
Lemma testop_f32_error : forall s inst ves testop,
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_testop T_f32 testop)] (Tf t1s t2s).
Proof.
  intros s inst ves testop [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Testop_typing_is_int_t in Hbtype => //.
Qed.

Lemma testop_f64_error : forall s inst ves testop,
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_testop T_f64 testop)] (Tf t1s t2s).
Proof.
  intros s inst ves testop [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Testop_typing_is_int_t in Hbtype => //.
Qed.

(* XXX relop is very similar to binop, TODO dedupe *)
Lemma reduce_relop : forall (hs : host_state) s f t op v1 v2 ves',
  reduce
    hs s f (vs_to_es ([:: v2; v1] ++ ves') ++ [:: AI_basic (BI_relop t op)])
    hs s f (vs_to_es (VAL_int32 (wasm_bool (app_relop op v1 v2)) :: ves')).
Proof. intros. simpl_reduce_simple. by apply rs_relop. Qed.

Lemma relop_error_size : forall s inst ves t op,
  size ves < 2 ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_relop t op)] (Tf t1s t2s).
Proof.
  intros s inst ves t op ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
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

Lemma cvtop_error_0 : forall s inst ves t1 t2 cvtop sx,
  ves = [::] ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_cvtop t2 cvtop t1 sx)] (Tf t1s t2s).
Proof.
  intros s inst ves t1 t2 cvtop sx ? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply_cat0_inv Ht1s.
  by apply Cvtop_typing in Hbtype as [[|] [??]].
Qed.

Lemma cvtop_error_types_disagree : forall s inst v ves ves' t1 t2 cvtop sx,
  ves = v :: ves' ->
  types_agree t1 v = false ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_cvtop t2 cvtop t1 sx)] (Tf t1s t2s).
Proof.
  intros s inst v ves ves' t1 t2 cvtop sx ? Hdisagree [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
  subst ves.
  apply et_to_bet in Hetype as Hbtype; last by auto_basic.
  apply Cvtop_typing in Hbtype as [? [??]].
  subst t1s. cats1_last_eq Ht1s.
  unfold types_agree in Hdisagree.
  destruct (typeof v == t1) eqn:Hv => //.
  assert (Hv' : typeof v <> t1). { apply/eqP. by rewrite Hv. } by apply Hv'.
Qed.

Lemma cvtop_error_reinterpret_sx : forall s inst v ves ves' t1 t2 sx,
  ves = v :: ves' ->
  types_agree t1 v = true ->
  ~ exists C t1s t2s t1s',
    rev (map typeof ves) = t1s' ++ t1s /\
    inst_typing s inst C /\
    store_typing s /\
    e_typing s C [:: AI_basic (BI_cvtop t2 CVO_reinterpret t1 (Some sx))] (Tf t1s t2s).
Proof.
  intros s inst v ves ves' t1 t2 sx ?? [C [t1s [t2s [t1s' [Ht1s [? [? Hetype]]]]]]].
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

(* TODO many of the eqn:* can be removed by using partial application of RS_* *)
Theorem run_step_with_fuel'' hs s f es (fuel : fuel) (d : depth) : res_step' hs s f es
with run_one_step'' hs s f ves e (fuel : fuel) (d : depth) : res_step'_separate_e hs s f ves e.
Proof.
  (* NOTE: not indenting the two main subgoals - XXX use {}? *)
  (* run_step_with_fuel'' *)
  destruct fuel as [|fuel].
  - (* 0 *)
    by apply RS'_exhaustion.
  - (* fuel.+1 *)
    (** Framing out constants. **)
    destruct (split_vals_e es) as [ves es'] eqn:Heqes.
    destruct es' as [|e es''] eqn:Heqes'.
    * (* es' = [::] *)
      apply RS'_value. by apply value_split_0 with (ves := ves).
    * (* es' = e :: es'' *)
      destruct (e_is_trap e) eqn:?.
      + destruct ((es'' != [::]) || (ves != [::])) eqn:?.
        -- apply <<hs, s, f, [:: AI_trap]>>.
           by apply reduce_trap with (e := e) (es'' := es'') (ves := ves).
        -- apply RS'_value.
           by apply value_trap with (e := e) (es'' := es'') (ves := ves).
      + remember (run_one_step'' hs s f (rev ves) e fuel d) as r.
        destruct r as [| | | |hs' s' f' res Hreduce] eqn:?.
        -- (* RS''_exhaustion *)
           by apply RS'_exhaustion.
        -- (* RS''_error *)
           apply RS'_error.
           by eapply error_rec with (es' := es') (ves := ves) => //; subst es'.
        -- (* RS''_break *)
           by apply (coerce_res _ r).
        -- (* RS''_return *)
           by apply (coerce_res _ r).
        -- (* RS''_normal hs' s' f' res *)
           apply <<hs', s', f', (res ++ es'')>>.
           by eapply reduce_rec with (es' := es') (ves := ves); subst es'.

  (* run_one_step'' *)
  (* initial es, useful as an arg for reduce *)
  remember ((vs_to_es ves) ++ [::e]) as es0 eqn:Heqes0.
  destruct fuel as [|fuel].
  - (* 0 *)
    by apply RS''_exhaustion.
  - (* fuel.+1 *)
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
        (* TODO use size or length in the lemmas? *)
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
      (* apply break(j, ves'). *)
      by apply admitted_TODO.

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
      apply (RS''_return _ _ _ _ _ ves).
      by apply admitted_TODO.

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
      (* XXX this branch is fairly complicated,
       * would moving it out into a separate function be justified?
       * perhaps use a convoy pattern match there?  *)
      (* XXX do we ever have to handle r_grow_memory_failure? *)
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
      (* XXX this won't happen if ves has been correctly split(?) *)
      by apply admitted_TODO.

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
      (* NOTE trap is 'terminal/value form' *)
      by apply admitted_TODO.

    * (* AI_invoke a *)
      by apply admitted_TODO.
    * (* AI_label ln les es *)
      by apply admitted_TODO.
    * (* AI_local ln lf es *)
      by apply admitted_TODO.
Defined.

(***************************************)

Fixpoint run_step_with_fuel (fuel : fuel) (d : depth) (cfg : config_tuple) : res_tuple :=
  let: (hs, s, f, es) := cfg in
  match fuel with
  | 0 => (hs, s, f, RS_crash C_exhaustion)
  | fuel.+1 =>
    let: (ves, es') := split_vals_e es in (** Framing out constants. **)
    match es' with
    | [::] => (hs, s, f, crash_error)
    | e :: es'' =>
      if e_is_trap e
      then
        if (es'' != [::]) || (ves != [::])
        then (hs, s, f, RS_normal [::AI_trap])
        else (hs, s, f, crash_error)
      else
        let: (hs', s', f', r) := run_one_step fuel d (hs, s, f, (rev ves)) e in
        if r is RS_normal res
        then (hs', s', f', RS_normal (res ++ es''))
        else (hs', s', f', r)
    end
  end

with run_one_step (fuel : fuel) (d : depth) (cfg : config_one_tuple_without_e) (e : administrative_instruction) : res_tuple :=
  let: (hs, s, f, ves) := cfg in
  match fuel with
  | 0 => (hs, s, f, RS_crash C_exhaustion)
  | fuel.+1 =>
    match e with
    (* unop *)
    | AI_basic (BI_unop t op) =>
      if ves is v :: ves' then
        (hs, s, f, RS_normal (vs_to_es (app_unop op v :: ves')))
      else (hs, s, f, crash_error)
    (* binop *)
    | AI_basic (BI_binop t op) =>
      if ves is v2 :: v1 :: ves' then
        expect (app_binop op v1 v2)
               (fun v => (hs, s, f, RS_normal (vs_to_es (v :: ves'))))
               (hs, s, f, RS_normal ((vs_to_es ves') ++ [::AI_trap]))
      else (hs, s, f, crash_error)
    (* testops *)
    | AI_basic (BI_testop T_i32 testop) =>
      if ves is (VAL_int32 c) :: ves' then
        (hs, s, f, RS_normal (vs_to_es ((VAL_int32 (wasm_bool (@app_testop_i i32t testop c))) :: ves')))
      else (hs, s, f, crash_error)
    | AI_basic (BI_testop T_i64 testop) =>
      if ves is (VAL_int64 c) :: ves' then
        (hs, s, f, RS_normal (vs_to_es ((VAL_int32 (wasm_bool (@app_testop_i i64t testop c))) :: ves')))
      else (hs, s, f, crash_error)
    | AI_basic (BI_testop _ _) => (hs, s, f, crash_error)
    (* relops *)
    | AI_basic (BI_relop t op) =>
      if ves is v2 :: v1 :: ves' then
        (hs, s, f, RS_normal (vs_to_es (VAL_int32 (wasm_bool (app_relop op v1 v2)) :: ves')))
      else (hs, s, f, crash_error)
    (* convert & reinterpret *)
    | AI_basic (BI_cvtop t2 CVO_convert t1 sx) =>
      if ves is v :: ves' then
        if types_agree t1 v
        then
          expect (cvt t2 sx v) (fun v' =>
               (hs, s, f, RS_normal (vs_to_es (v' :: ves'))))
            (hs, s, f, RS_normal ((vs_to_es ves') ++ [::AI_trap]))
        else (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic (BI_cvtop t2 CVO_reinterpret t1 sx) =>
      if ves is v :: ves' then
        if types_agree t1 v && (sx == None)
        then (hs, s, f, RS_normal (vs_to_es (wasm_deserialise (bits v) t2 :: ves')))
        else (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    (**)
    | AI_basic BI_unreachable => (hs, s, f, RS_normal ((vs_to_es ves) ++ [::AI_trap]))
    | AI_basic BI_nop => (hs, s, f, RS_normal (vs_to_es ves))
    | AI_basic BI_drop =>
      if ves is v :: ves' then
        (hs, s, f, RS_normal (vs_to_es ves'))
      else (hs, s, f, crash_error)
    | AI_basic BI_select =>
      if ves is (VAL_int32 c) :: v2 :: v1 :: ves' then
        if c == Wasm_int.int_zero i32m
        then (hs, s, f, RS_normal (vs_to_es (v2 :: ves')))
        else (hs, s, f, RS_normal (vs_to_es (v1 :: ves')))
      else (hs, s, f, crash_error)
    | AI_basic (BI_block (Tf t1s t2s) es) =>
      if length ves >= length t1s
      then
        let: (ves', ves'')  := split_n ves (length t1s) in
        (hs, s, f, RS_normal (vs_to_es ves''
                ++ [::AI_label (length t2s) [::] (vs_to_es ves' ++ to_e_list es)]))
      else (hs, s, f, crash_error)
    | AI_basic (BI_loop (Tf t1s t2s) es) =>
      if length ves >= length t1s
      then
        let: (ves', ves'') := split_n ves (length t1s) in
        (hs, s, f, RS_normal (vs_to_es ves''
                ++ [::AI_label (length t1s) [::AI_basic (BI_loop (Tf t1s t2s) es)]
                        (vs_to_es ves' ++ to_e_list es)]))
      else (hs, s, f, crash_error)
    | AI_basic (BI_if tf es1 es2) =>
      if ves is VAL_int32 c :: ves' then
        if c == Wasm_int.int_zero i32m
        then (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_block tf es2)]))
        else (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_block tf es1)]))
      else (hs, s, f, crash_error)
    | AI_basic (BI_br j) => (hs, s, f, RS_break j ves)
    | AI_basic (BI_br_if j) =>
      if ves is VAL_int32 c :: ves' then
        if c == Wasm_int.int_zero i32m
        then (hs, s, f, RS_normal (vs_to_es ves'))
        else (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br j)]))
      else (hs, s, f, crash_error)
    | AI_basic (BI_br_table js j) =>
      if ves is VAL_int32 c :: ves' then
        let: k := Wasm_int.nat_of_uint i32m c in
        if k < length js
        then
          expect (List.nth_error js k) (fun js_at_k =>
              (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br js_at_k)])))
            (hs, s, f, crash_error)
        else (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_basic (BI_br j)]))
      else (hs, s, f, crash_error)
    | AI_basic (BI_call j) =>
      if List.nth_error f.(f_inst).(inst_funcs) j is Some a then
        (hs, s, f, RS_normal (vs_to_es ves ++ [::AI_invoke a]))
      else (hs, s, f, crash_error)
    | AI_basic (BI_call_indirect j) =>
      if ves is VAL_int32 c :: ves' then
        match stab_addr s f (Wasm_int.nat_of_uint i32m c) with
        | Some a =>
          match List.nth_error s.(s_funcs) a with
          | Some cl =>
            if stypes s f.(f_inst) j == Some (cl_type cl)
            then (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_invoke a]))
            else (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))        
          | None => (hs, s, f, crash_error)
          end
        | None => (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
        end
      else (hs, s, f, crash_error)
    | AI_basic BI_return => (hs, s, f, RS_return ves)
    | AI_basic (BI_get_local j) =>
      if j < length f.(f_locs)
      then
        expect (List.nth_error f.(f_locs) j) (fun vs_at_j =>
            (hs, s, f, RS_normal (vs_to_es (vs_at_j :: ves))))
          (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic (BI_set_local j) =>
      if ves is v :: ves' then
        if j < length f.(f_locs)
        then (hs, s, Build_frame (update_list_at f.(f_locs) j v) f.(f_inst), RS_normal (vs_to_es ves'))
        else (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic (BI_tee_local j) =>
      if ves is v :: ves' then
        (hs, s, f, RS_normal (vs_to_es (v :: ves) ++ [::AI_basic (BI_set_local j)]))
      else (hs, s, f, crash_error)
    | AI_basic (BI_get_global j) =>
      if sglob_val s f.(f_inst) j is Some xx
      then (hs, s, f, RS_normal (vs_to_es (xx :: ves)))
      else (hs, s, f, crash_error)
    | AI_basic (BI_set_global j) =>
      if ves is v :: ves' then
        if supdate_glob s f.(f_inst) j v is Some xx
        then (hs, xx, f, RS_normal (vs_to_es ves'))
        else (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic (BI_load t None a off) =>
      if ves is VAL_int32 k :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load (mem_s_j) (Wasm_int.N_of_uint i32m k) off (t_length t))
                 (fun bs => (hs, s, f, RS_normal (vs_to_es (wasm_deserialise bs t :: ves'))))
                 (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
             else (hs, s, f, crash_error))
          (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic (BI_load t (Some (tp, sx)) a off) =>
      if ves is VAL_int32 k :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load_packed sx (mem_s_j) (Wasm_int.N_of_uint i32m k) off (tp_length tp) (t_length t))
                 (fun bs => (hs, s, f, RS_normal (vs_to_es (wasm_deserialise bs t :: ves'))))
                 (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
             else (hs, s, f, crash_error))
          (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic (BI_store t None a off) =>
      if ves is v :: VAL_int32 k :: ves' then
        if types_agree t v
        then
          expect
            (smem_ind s f.(f_inst))
            (fun j =>
               if List.nth_error s.(s_mems) j is Some mem_s_j then
                 expect
                   (store mem_s_j (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t))
                   (fun mem' =>
                      (hs, upd_s_mem s (update_list_at s.(s_mems) j mem'), f, RS_normal (vs_to_es ves')))
                   (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
               else (hs, s, f, crash_error))
            (hs, s, f, crash_error)
        else (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic (BI_store t (Some tp) a off) =>
      if ves is v :: VAL_int32 k :: ves' then
        if types_agree t v
        then
          expect
            (smem_ind s f.(f_inst))
            (fun j =>
               if List.nth_error s.(s_mems) j is Some mem_s_j then
                 expect
                   (store_packed mem_s_j (Wasm_int.N_of_uint i32m k) off (bits v) (tp_length tp))
                   (fun mem' =>
                      (hs, upd_s_mem s (update_list_at s.(s_mems) j mem'), f, RS_normal (vs_to_es ves')))
                   (hs, s, f, RS_normal (vs_to_es ves' ++ [::AI_trap]))
               else (hs, s, f, crash_error))
            (hs, s, f, crash_error)
        else (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic BI_current_memory =>
      expect
        (smem_ind s f.(f_inst))
        (fun j =>
           if List.nth_error s.(s_mems) j is Some s_mem_s_j then
             (hs, s, f, RS_normal (vs_to_es (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j))) :: ves)))
           else (hs, s, f, crash_error))
        (hs, s, f, crash_error)
    | AI_basic BI_grow_memory =>
      if ves is VAL_int32 c :: ves' then
        expect
          (smem_ind s f.(f_inst))
          (fun j =>
            if List.nth_error s.(s_mems) j is Some s_mem_s_j then
              let: l := mem_size s_mem_s_j in
              let: mem' := mem_grow s_mem_s_j (Wasm_int.N_of_uint i32m c) in
              if mem' is Some mem'' then
                (hs, upd_s_mem s (update_list_at s.(s_mems) j mem''), f,
                 RS_normal (vs_to_es (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat l)) :: ves')))
              else (hs, s, f, crash_error)
            else (hs, s, f, crash_error))
          (hs, s, f, crash_error)
      else (hs, s, f, crash_error)
    | AI_basic (BI_const _) => (hs, s, f, crash_error)
    | AI_invoke a =>
      match List.nth_error s.(s_funcs) a with
      | Some cl => 
        match cl with
        | FC_func_native i (Tf t1s t2s) ts es =>
            let: n := length t1s in
            let: m := length t2s in
            if length ves >= n
            then
            let: (ves', ves'') := split_n ves n in
            let: zs := n_zeros ts in
            (hs, s, f, RS_normal (vs_to_es ves''
                    ++ [::AI_local m (Build_frame (rev ves' ++ zs) i) [::AI_basic (BI_block (Tf [::] t2s) es)]]))
            else (hs, s, f, crash_error)
        | FC_func_host (Tf t1s t2s) cl' =>
            let: n := length t1s in
            let: m := length t2s in
            if length ves >= n
            then
            let: (ves', ves'') := split_n ves n in
            match host_application_impl hs s (Tf t1s t2s) cl' (rev ves') with
            | (hs', Some (s', rves)) =>
                (hs', s', f, RS_normal (vs_to_es ves'' ++ (result_to_stack rves)))
            | (hs', None) => (hs', s, f, RS_normal (vs_to_es ves ++ [::AI_invoke a]))
            end
            else (hs, s, f, crash_error)
        end
      | None => (hs, s, f, crash_error)
      end
    | AI_label ln les es =>
      if es_is_trap es
      then (hs, s, f, RS_normal (vs_to_es ves ++ [::AI_trap]))
      else
        if const_list es
        then (hs, s, f, RS_normal (vs_to_es ves ++ es))
        else
          let: (hs', s', f', res) := run_step_with_fuel fuel d (hs, s, f, es) in
          match res with
          | RS_break 0 bvs =>
            if length bvs >= ln
            then (hs', s', f', RS_normal ((vs_to_es ((take ln bvs) ++ ves)) ++ les))
            else (hs', s', f', crash_error)
          | RS_break (n.+1) bvs => (hs', s', f', RS_break n bvs)
          | RS_return rvs => (hs', s', f', RS_return rvs)
          | RS_normal es' =>
            (hs', s', f', RS_normal (vs_to_es ves ++ [::AI_label ln les es']))
          | RS_crash error => (hs', s', f', RS_crash error)
          end
    | AI_local ln lf es =>
      if es_is_trap es
      then (hs, s, f, RS_normal (vs_to_es ves ++ [::AI_trap]))
      else
        if const_list es
        then
          if length es == ln
          then (hs, s, f, RS_normal (vs_to_es ves ++ es))
          else (hs, s, f, crash_error)
        else
          let: (hs', s', f', res) := run_step_with_fuel fuel d (hs, s, lf, es) in
          match res with
          | RS_return rvs =>
            if length rvs >= ln
            then (hs', s', f, RS_normal (vs_to_es (take ln rvs ++ ves)))
            else (hs', s', f, crash_error)
          | RS_normal es' =>
            (hs', s', f, RS_normal (vs_to_es ves ++ [::AI_local ln f' es']))
          | RS_crash error => (hs', s', f, RS_crash error)
          | RS_break _ _ => (hs', s', f, crash_error)
          end
    | AI_trap => (hs, s, f, crash_error)
    end
  end.

(** Enough fuel so that [run_one_step] does not run out of exhaustion. **)
Definition run_one_step_fuel : administrative_instruction -> nat.
Proof.
  move=> es. induction es using administrative_instruction_rect';
    let rec aux v :=
      lazymatch goal with
      | F : TProp.Forall _ _ |- _ =>
        apply TProp.max in F;
        move: F;
        let n := fresh "n" in
        move=> n;
        aux (n + v)
      | |- _ => exact (v.+1)
      end in
    aux (1 : nat).
Defined.

(** Enough fuel so that [run_step] does not run out of exhaustion. **)
Definition run_step_fuel (cfg : config_tuple) : nat :=
  let: (hs, s, f, es) := cfg in
  1 + List.fold_left max (List.map run_one_step_fuel es) 0.

Definition run_step (d : depth) (cfg : config_tuple) : res_tuple :=
  run_step_with_fuel (run_step_fuel cfg) d cfg.

Fixpoint run_v (fuel : fuel) (d : depth) (cfg : config_tuple) : ((host_state * store_record * res)%type) :=
  let: (hs, s, f, es) := cfg in
  match fuel with
  | 0 => (hs, s, R_crash C_exhaustion)
  | fuel.+1 =>
    if es_is_trap es
    then (hs, s, R_trap)
    else
      if const_list es
      then (hs, s, R_value (fst (split_vals_e es)))
      else
        let: (hs', s', f', res) := run_step d (hs, s, f, es) in
        match res with
        | RS_normal es' => run_v fuel d (hs', s', f', es')
        | RS_crash error => (hs', s', R_crash error)
        | _ => (hs', s', R_crash C_error)
        end
  end.

(** Main proof for the [RS_break] case. **)
Lemma reduce_label_break: forall (hs : host_state) s f es es' es'' hs' s' f' n,
  (exists m vs0 lh es,
    lfilled m lh (vs0 ++ [:: AI_basic (BI_br m)]) es /\
    v_to_e_list es'' = rev vs0) ->
  n <= size es'' ->
  reduce
    hs s f ([:: AI_label n es es'])
    hs' s' f' (v_to_e_list (rev (take n es'')) ++ es).
Proof.
  intros hs s f es es' es'' hs' s' f' n [m [vs0 [lh [es''' [HLF HES'']]]]] ?.
  destruct m.
  - move/lfilledP in HLF. inversion HLF. subst. admit.
Admitted.

End Host_func.
