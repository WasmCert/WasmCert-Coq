(** Proof of preservation **)

From Wasm Require Export common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program.Equality NArith ZArith_base.
From Wasm Require Export typing opsem properties contexts typing_inversion tactic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Variable host_function : eqType.

Let store_record := store_record host_function.
Let function_closure := function_closure host_function.
Let e_typing : store_record -> t_context -> seq administrative_instruction -> function_type -> Prop :=
  @e_typing _.
Let inst_typing : store_record -> instance -> t_context -> bool := @inst_typing _.

Let host := host host_function.

Variable host_instance : host.

Let host_state := host_state host_instance.

Let reduce : host_state -> store_record -> frame -> seq administrative_instruction ->
             host_state -> store_record -> frame -> seq administrative_instruction -> Prop
  := @reduce _ _.

Let s_globals : store_record -> seq global := @s_globals _.
Let s_mems : store_record -> seq memory := @s_mems _.
Let functions_agree : seq function_closure -> nat -> function_type -> bool := @functions_agree _.
Let cl_type : function_closure -> function_type := @cl_type _.
Let func_extension := @func_extension host_function.
Let frame_typing := @frame_typing host_function.


Ltac et_dependent_ind H :=
  repeat lazymatch (type of H) with
  | e_typing _ _ _ _ =>
      unfold e_typing in H
  | _ => et_dependent_ind' H
  end.

Definition t_be_value bes : Prop :=
  const_list (to_e_list bes).

Ltac b_to_a_revert :=
  repeat lazymatch goal with
         | H:  to_e_list ?bes = _ |- _ =>
           apply b_e_elim in H; destruct H
         end.

Lemma b_e_elim: forall bes es,
    to_e_list bes = es ->
    bes = to_b_list es /\ es_is_basic es.
Proof.
  by apply properties.b_e_elim.
Qed.

Lemma app_binop_type_preserve: forall op v1 v2 v,
    app_binop op v1 v2 = Some v ->
    typeof v = typeof v1.
Proof.
  move => op v1 v2 v.
  by elim: op; elim: v1; elim: v2 => //=; move => c1 c2 op H; destruct op; remove_bools_options.
Qed.

Lemma t_Unop_preserve: forall C v t op be tf,
    be_typing C [:: BI_const v; BI_unop t op] tf ->
    reduce_simple (to_e_list [::BI_const v; BI_unop t op]) (to_e_list [::be]) ->
    be_typing C [::be] tf.
Proof.
  move => C v t op be tf HType HReduce.
  destruct tf as [ts1 ts2].
  inversion HReduce; b_to_a_revert; subst.
  invert_be_typing.
  rewrite catA.
  apply bet_weakening_empty_1.
  replace (typeof v) with (typeof (app_unop op v)); first by apply bet_const.
  by destruct op; destruct v.
Qed.

Lemma t_Binop_preserve_success: forall C v1 v2 t op be tf,
    be_typing C [:: BI_const v1; BI_const v2; BI_binop t op] tf ->
    reduce_simple (to_e_list [::BI_const v1; BI_const v2; BI_binop t op]) (to_e_list [::be]) ->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 t op be tf HType HReduce.
  destruct tf as [ts1 ts2].
  inversion HReduce; b_to_a_revert; subst.
  invert_be_typing.
  repeat rewrite catA.
  apply bet_weakening_empty_1.
  apply app_binop_type_preserve in H0.
  rewrite -H1. rewrite -H0.
  by apply bet_const.
Qed.

Lemma t_Testop_i32_preserve: forall C c testop tf,
    be_typing C [::BI_const (VAL_int32 c); BI_testop T_i32 testop] tf ->
    be_typing C [::BI_const (VAL_int32 (wasm_bool (app_testop_i testop c)))] tf.
Proof.
  move => C c testop tf HType.
  gen_ind_subst HType.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1. simpl.
    apply bet_const.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType.
Qed.

Lemma t_Testop_i64_preserve: forall C c testop tf,
    be_typing C [::BI_const (VAL_int64 c); BI_testop T_i64 testop] tf ->
    be_typing C [::BI_const (VAL_int32 (wasm_bool (app_testop_i testop c)))] tf.
Proof.
  move => C c testop tf HType.
  gen_ind_subst HType.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1. simpl.
    by apply bet_const.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType.
Qed.

Lemma t_Relop_preserve: forall C v1 v2 t be op tf,
    be_typing C [::BI_const v1; BI_const v2; BI_relop t op] tf ->
    reduce_simple [:: AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] [::AI_basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 t be op tf HType HReduce.
  destruct tf as [ts1 ts2].
  inversion HReduce; subst.
  invert_be_typing.
  replace ([::t;t]) with ([::t] ++ [::t]) in H1_relop => //.
  invert_be_typing.
  repeat rewrite catA.
  apply bet_weakening_empty_1.
  by apply bet_const.
Qed.

Lemma typeof_deserialise: forall v t,
  typeof (wasm_deserialise v t) = t.
Proof.
  move=> v. by case.
Qed.

Lemma be_typing_const_deserialise: forall C v t,
    be_typing C [:: BI_const (wasm_deserialise (bits v) t)] (Tf [::] [:: t]).
Proof.
  move => C v t.
  assert (be_typing C [:: BI_const (wasm_deserialise (bits v) t)] (Tf [::] [:: typeof (wasm_deserialise (bits v) t)])); first by apply bet_const.
  by rewrite typeof_deserialise in H.
Qed.

Lemma t_Convert_preserve: forall C v t1 t2 sx be tf,
    be_typing C [::BI_const v; BI_cvtop t2 CVO_convert t1 sx] tf ->
    reduce_simple [::AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] [::AI_basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v t1 t2 sx be tf HType HReduce.
  inversion HReduce; subst. rename H5 into E.
  gen_ind_subst HType.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1.
    by destruct t2; simpl in E;
      match type of E with
        option_map _ ?e = _ => destruct e eqn:HDestruct => //=
      end; inversion E; apply bet_const.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType; eauto.
Qed.

Lemma t_Reinterpret_preserve: forall C v t1 t2 be tf,
    be_typing C [::BI_const v; BI_cvtop t2 CVO_reinterpret t1 None] tf ->
    reduce_simple [::AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] [::AI_basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v t1 t2 be tf HType HReduce.
  inversion HReduce; subst.
  gen_ind_subst HType.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1.
    apply be_typing_const_deserialise.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType; eauto.
Qed.

Lemma t_Drop_preserve: forall C v tf,
    be_typing C [::BI_const v; BI_drop] tf ->
    be_typing C [::] tf.
Proof.
  move => C v tf HType.
  gen_ind_subst HType.
  - invert_be_typing.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - apply bet_weakening. by eapply IHHType.
Qed.

Lemma t_Select_preserve: forall C v1 v2 n tf be,
    be_typing C [::BI_const v1; BI_const v2; BI_const (VAL_int32 n); BI_select] tf ->
    reduce_simple [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select] [::AI_basic be]->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 n tf be HType HReduce.
  inversion HReduce; subst.
  - (* n = 0 : Select second *)
    gen_ind_subst HType => //=.
    + (* Composition *)
      invert_be_typing.
      apply concat_cancel_last_n in H1_select => //.
      remove_bools_options.
      inversion H2. subst.
      apply bet_weakening_empty_1.
      by apply bet_const.
    + apply bet_weakening. by eapply IHHType => //=.
  - (* n = 1 : Select first *)
    gen_ind_subst HType => //=.
    + (* Composition *)
      invert_be_typing.
      apply concat_cancel_last_n in H1_select => //.
      remove_bools_options.
      inversion H3. subst.
      apply bet_weakening_empty_1.
      rewrite H6.
      by apply bet_const.
    + apply bet_weakening. by eapply IHHType => //=.
Qed.

Lemma t_If_be_preserve: forall C c tf0 es1 es2 tf be,
  be_typing C ([::BI_const (VAL_int32 c); BI_if tf0 es1 es2]) tf ->
  reduce_simple (to_e_list [::BI_const (VAL_int32 c); BI_if tf0 es1 es2]) [::AI_basic be] ->
  be_typing C [::be] tf.
Proof.
  move => C c tf0 es1 es2 tf be HType HReduce. destruct tf. destruct tf0.
  inversion HReduce; subst.
  - (* if_0 *)
    gen_ind_subst HType => //=.
    + (* Composition *)
      invert_be_typing.
      apply bet_weakening.
      by apply bet_block.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
  - (* if_n0 *)
    gen_ind_subst HType => //=.
    + (* Composition *)
      invert_be_typing.
      apply bet_weakening.
      by apply bet_block.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
Qed.

Lemma t_Br_if_true_preserve: forall C c i tf be,
    be_typing C ([::BI_const (VAL_int32 c); BI_br_if i]) tf ->
    reduce_simple (to_e_list [::BI_const (VAL_int32 c); BI_br_if i]) [::AI_basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C c i tf be HType HReduce.
  inversion HReduce; subst.
  gen_ind_subst HType => //=.
  - (* Composition *)
    invert_be_typing.
    by apply bet_br => //=. (* Surprisingly convenient! *)
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType => //=.
Qed.

Lemma t_Br_if_false_preserve: forall C c i tf,
    be_typing C ([::BI_const (VAL_int32 c); BI_br_if i]) tf ->
    reduce_simple (to_e_list [::BI_const (VAL_int32 c); BI_br_if i]) [::] ->
    be_typing C [::] tf.
Proof.
  move => C c i tf HType HReduce.
  inversion HReduce; subst.
  gen_ind_subst HType => //=.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType => //=.
Qed.

Lemma t_Br_table_preserve: forall C c ids i0 tf be,
    be_typing C ([::BI_const (VAL_int32 c); BI_br_table ids i0]) tf ->
    reduce_simple (to_e_list [::BI_const (VAL_int32 c); BI_br_table ids i0]) [::AI_basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C c ids i0 tf be HType HReduce.
  inversion HReduce; subst.
  (* in range *)
  - dependent induction HType => //=.
    + (* Composition *)
      invert_be_typing. subst.
      move/allP in H2_brtable.
      assert (HInd: (j < length (tc_label C)) && plop2 C j ts'_brtable).
      -- apply H2_brtable. rewrite mem_cat. apply/orP. left. apply/inP.
         eapply List.nth_error_In. by eauto.
      remove_bools_options.
      by apply bet_br => //.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
  (* out of range *)
  - dependent induction HType => //=.
    + (* Composition *)
      invert_be_typing. subst.
      move/allP in H2_brtable.
      assert (HInd: (i0 < length (tc_label C)) && plop2 C i0 ts'_brtable).
      -- apply H2_brtable. rewrite mem_cat. apply/orP. right. by rewrite mem_seq1.
      remove_bools_options.
      by apply bet_br => //.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
Qed.

Lemma t_Tee_local_preserve: forall C v i tf,
    be_typing C ([::BI_const v; BI_tee_local i]) tf ->
    be_typing C [::BI_const v; BI_const v; BI_set_local i] tf.
Proof.
  move => C v i tf HType.
  gen_ind_subst HType => //=.
  - (* Composition *)
    invert_be_typing.
    replace ([::BI_const v; BI_const v; BI_set_local i]) with ([::BI_const v] ++ [::BI_const v] ++ [::BI_set_local i]) => //.
    repeat (try rewrite catA; eapply bet_composition) => //.
    + instantiate (1 := (ts_teelocal ++ [::typeof v])).
      apply bet_weakening_empty_1. by apply bet_const.
    + instantiate (1 := (ts_teelocal ++ [::typeof v] ++ [::typeof v])).
      apply bet_weakening. apply bet_weakening_empty_1. by apply bet_const.
    + apply bet_weakening. apply bet_weakening_empty_2. by apply bet_set_local.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType => //=.
Qed.

(*
  Preservation for all be_typeable simple reductions.
*)

Theorem t_be_simple_preservation: forall bes bes' es es' C tf,
    be_typing C bes tf ->
    reduce_simple es es' ->
    es_is_basic es ->
    es_is_basic es' ->
    to_e_list bes = es ->
    to_e_list bes' = es' ->
    be_typing C bes' tf.
Proof.
  move => bes bes' es es' C tf HType HReduce HAI_basic1 HAI_basic2 HBES1 HBES2.
  destruct tf.
  inversion HReduce; b_to_a_revert; subst; simpl in HType => //; basic_inversion.
  - (* Unop *)
    by eapply t_Unop_preserve; eauto => //=.
  - (* Binop_success *)
    by eapply t_Binop_preserve_success; eauto => //=.
  - (* testop_i T_i32 *)
    by apply t_Testop_i32_preserve => //.
  - (* testop_i T_i64 *)
    by apply t_Testop_i64_preserve => //.
  - (* relop *)
    by eapply t_Relop_preserve => //=; eauto.
  - (* Cvtop Convert success *)
    eapply t_Convert_preserve => //=.
    apply HType.
    by apply rs_convert_success => //=.
  - (* Cvtop Reinterpret *)
    eapply t_Reinterpret_preserve => //=.
    apply HType.
    by apply rs_reinterpret => //=.
  - (* Nop *)
    apply Nop_typing in HType; subst => /=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - (* Drop *)
    eapply t_Drop_preserve => //=.
    by apply HType.
  - (* Select_false *)
    eapply t_Select_preserve => //=.
    + by apply HType.
    + by apply rs_select_false.
  - (* Select_true *)
    eapply t_Select_preserve => //=.
    + by apply HType.
    + by apply rs_select_true.
  - (* If_0 *)
    eapply t_If_be_preserve => //=.
    + by apply HType.
    + by apply rs_if_false.
  - (* If_n0 *)
    eapply t_If_be_preserve => //=.
    + by apply HType.
    + by apply rs_if_true.
  - (* br_if_0 *)
    eapply t_Br_if_false_preserve => //=.
    + by apply HType.
    + by apply rs_br_if_false.
  - (* br_if_n0 *)
    eapply t_Br_if_true_preserve => //=.
    + by apply HType.
    + by apply rs_br_if_true.
  - (* br_table -- in range *)
    eapply t_Br_table_preserve => //=.
    + by apply HType.
    + by apply rs_br_table.
  - (* br_table -- out of range default *)
    eapply t_Br_table_preserve => //=.
    + by apply HType.
    + by apply rs_br_table_length.
  - (* tee_local *)
    unfold is_const in H.
    destruct v => //. destruct b => //.
    eapply t_Tee_local_preserve => //=.
Qed.

Lemma t_const_ignores_context: forall s s' C C' es tf,
    const_list es ->
    e_typing s C es tf ->
    e_typing s' C' es tf.
Proof.
  move => s s' C C' es tf HConst HType.
  apply et_to_bet in HType => //; last by apply const_list_is_basic.
  apply ety_a'; first by apply const_list_is_basic.

  (* A trick on doing induction from tail since composition needs that... *)
  remember (rev es) as es'.
  assert (es = rev es'). rewrite Heqes'. symmetry. by apply revK.
  rewrite H.
  generalize dependent tf. generalize dependent es.

  induction es' => //=; move => es HConst HRev1 HRev2 tf HType; destruct tf.
  - subst. simpl in HType. apply empty_typing in HType; subst.
    apply bet_weakening_empty_both. by apply bet_empty.
  - subst.
    rewrite -to_b_list_rev.
    simpl. rewrite rev_cons. rewrite -cats1.
    rewrite -to_b_list_rev in HType.
    simpl in HType. rewrite rev_cons in HType. rewrite -cats1 in HType.
    apply composition_typing in HType.
    destruct HType as [ts [t1s' [t2s' [t3s H]]]].
    destruct H as [H1 [H2 [H3 H4]]].
    subst.
    apply bet_weakening.
    rewrite rev_cons in HConst. rewrite -cats1 in HConst.
    apply const_list_split in HConst. destruct HConst.
    eapply bet_composition.
    + rewrite to_b_list_rev.
      eapply IHes' => //.
      -- by apply H.
      -- by rewrite revK.
      -- rewrite to_b_list_rev in H3. by apply H3.
    + (* The main reason that this holds *)
      simpl in H0. move/andP in H0. destruct H0.
      destruct a => //=.
      destruct b => //=.
      simpl in H4. apply BI_const_typing in H4. subst.
      apply bet_weakening_empty_1.
      by apply bet_const.
Qed.

Theorem t_simple_preservation: forall s i es es' C loc lab ret tf,
    inst_typing s i C ->
    e_typing s (upd_label (upd_local_return C loc ret) lab) es tf ->
    reduce_simple es es' ->
    e_typing s (upd_label (upd_local_return C loc ret) lab) es' tf.
Proof.
  move => s i es es' C loc lab ret tf HInstType HType HReduce.
  inversion HReduce; subst; try (by (apply et_to_bet in HType => //; auto_basic; apply ety_a' => //; auto_basic; eapply t_be_simple_preservation; try by eauto; auto_basic)); try by apply ety_trap.
  - (* Block *)
    destruct tf.
    apply et_to_bet in HType.
    2: {
      apply basic_split => //=.
      + by apply const_list_is_basic.
      + split => //=. unfold e_is_basic. by eauto.
      }
    rewrite to_b_list_concat in HType. simpl in HType.
    apply composition_typing in HType.
    destruct HType as [ts [t1s' [t2s' [t3s [H2 [H3 [H4 H5]]]]]]]. subst.
    apply const_es_exists in H. destruct H. subst.
    apply Const_list_typing in H4. subst.
    apply Block_typing in H5.
    destruct H5 as [t3s [H6 [H7 H8]]].
    subst.
    repeat rewrite length_is_size in H1. rewrite v_to_e_size in H1.
    assert ((t1s' == t3s) && ((vs_to_vts x) == t1s)) => //=.
    + apply concat_cancel_last_n => //=. by rewrite size_map.
    + move/andP in H. destruct H.
      move/eqP in H. move/eqP in H0. subst. clear H6. clear H1.
      rewrite catA. apply et_weakening_empty_1.
      eapply ety_label.
      -- apply ety_a' => //=.
         instantiate (1:= t2s).
         apply bet_weakening_empty_both.
         by apply bet_empty.
      -- apply ety_a' => //=.
         ++ apply basic_split.
            * apply const_list_is_basic. by apply v_to_e_const.
            * by apply to_e_list_basic.
         ++ rewrite to_b_list_concat. simpl in H8.
            eapply bet_composition'; first by apply Const_list_typing_empty.
            remember (operations.to_e_list es0) as es'.
            symmetry in Heqes'.
            apply properties.b_e_elim in Heqes'.
            destruct Heqes'. by subst.
      -- by [].
  - (* Loop *)
    destruct tf.
    apply et_to_bet in HType.
    2: {
      apply basic_split => //=.
      + by apply const_list_is_basic.
      + split => //=. unfold e_is_basic. by eauto.
    }
    rewrite to_b_list_concat in HType. simpl in HType.
    apply composition_typing in HType.
    destruct HType as [ts [t1s' [t2s' [t3s [H2 [H3 [H4 H5]]]]]]]. subst.
    apply const_es_exists in H. destruct H. subst.
    apply Const_list_typing in H4. subst.
    apply Loop_typing in H5.
    destruct H5 as [t3s [H6 [H7 H8]]]. subst.
    repeat rewrite length_is_size in H1. rewrite v_to_e_size in H1.
    assert ((t1s' == t3s) && ((vs_to_vts x) == t1s)) => //=.
    + apply concat_cancel_last_n => //=. by rewrite size_map.
    + move/andP in H. destruct H.
      move/eqP in H. move/eqP in H0. subst. clear H6. clear H1.
      rewrite catA. apply et_weakening_empty_1.
      eapply ety_label.
      -- apply ety_a' => //=.
         ++ split => //=. unfold e_is_basic. by eauto.
         ++ by apply bet_loop.
      -- apply ety_a' => //=.
         ++ apply basic_split.
            * apply const_list_is_basic. by apply v_to_e_const.
            * by apply to_e_list_basic.
         ++ rewrite to_b_list_concat. simpl in H8.
            eapply bet_composition'; first by apply Const_list_typing_empty.
            remember (operations.to_e_list es0) as es'.
            symmetry in Heqes'.
            apply b_e_elim in Heqes'.
            destruct Heqes'. by subst.
      -- repeat rewrite length_is_size.
         unfold vs_to_vts. rewrite size_map.
         by rewrite v_to_e_size.
  - (* Label_const *)
    et_dependent_ind HType => //; try by (inversion Hremtf; subst; apply ety_weakening; eapply IHHType).
    + (* ety_a *)
      assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
      rewrite Hremes in H1. by basic_inversion.
    + (* ety_composition *)
      apply extract_list1 in Hremes. destruct Hremes. subst.
      apply et_to_bet in HType1 => //.
      simpl in HType1. apply empty_typing in HType1. subst.
      by eapply IHHType2 => //.
    + (* ety_weakening *)
      apply ety_weakening.
      by eapply IHHType => //.
    + (* ety_label *)
      inversion Hremes; subst.
      by eapply t_const_ignores_context; eauto.
  - (* Label_lfilled_Break *)
    et_dependent_ind HType => //; try by (inversion Hremtf; subst; apply ety_weakening; eapply IHHType).
    + (* ety_a *)
      assert (es_is_basic (operations.to_e_list bes)) as Hbasic; first by apply to_e_list_basic.
      rewrite Hremes in Hbasic. by basic_inversion.
    + (* ety_composition *)
      apply extract_list1 in Hremes. destruct Hremes. subst.
      apply et_to_bet in HType1 => //.
      simpl in HType1. apply empty_typing in HType1. subst.
      by eapply IHHType2 => //=.
    + (* ety_weakening *)
      apply ety_weakening.
      by eapply IHHType => //.
    + (* ety_label *)
      inversion Hremes; subst.
      eapply et_composition'; eauto => //=.
      eapply Lfilled_break_typing; eauto.
      instantiate (2 := nil) => /=.
      rewrite addn0.
      by apply HType2.
  - (* Local_const *)
    et_dependent_ind HType => //; try by (inversion Hremtf; subst; apply ety_weakening; eapply IHHType).
    + (* ety_a *)
      assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
      rewrite Hremes in H1. by basic_inversion.
    + (* ety_composition *)
      apply extract_list1 in Hremes. destruct Hremes. subst.
      apply et_to_bet in HType1 => //.
      simpl in HType1. apply empty_typing in HType1. subst.
      by eapply IHHType2 => //.
    + (* ety_weakening *)
      apply ety_weakening.
      by eapply IHHType => //.
    + (* ety_local *)
      inversion Hremes; inversion H; inversion H0; subst.
      by eapply t_const_ignores_context; eauto.
  - (* Local_lfilled_Return *)
    by eapply Local_return_typing; eauto.
  - (* Tee_local -- actually a simple reduction *)
    destruct v => //.
    destruct b => //.
    apply et_to_bet in HType => //; auto_basic.
    apply ety_a' => //; auto_basic.
    by eapply t_be_simple_preservation; try by eauto; auto_basic.
Qed.

Lemma globs_agree_function: forall s,
    function (globals_agree (s_globals s)).
Proof.
  move => s. unfold function. move => x y1 y2 [H1 H2].
  unfold globals_agree in H1. unfold globals_agree in H2.
  remove_bools_options.
  unfold global_agree in H3. unfold global_agree in H4.
  remove_bools_options.
  destruct y1; destruct y2 => //.
  simpl in H0. simpl in H2. simpl in H3. simpl in H4. by subst.
Qed.

Lemma functions_agree_function: forall s,
    function (functions_agree (s_funcs s)).
Proof.
  move => s. unfold function. move => x y1 y2 [H1 H2].
  unfold functions_agree in H1. unfold typing.functions_agree in H1.
  unfold functions_agree in H2. unfold typing.functions_agree in H2.
  by remove_bools_options.
Qed.

Lemma tc_func_reference1: forall j k i s f C tf,
  List.nth_error (inst_funcs i) j = Some k ->
  List.nth_error (s_funcs s) k = Some f ->
  inst_typing s i C ->
  List.nth_error (tc_func_t C) j = Some tf ->
  tf = cl_type f.
Proof.
  move => j k i s f C tf HN1 HN2 HInstType HN3.
  unfold inst_typing in HInstType.
  destruct i => //=.
  destruct C => //=.
  destruct tc_local => //=.
  destruct tc_label => //=.
  destruct tc_return => //=.
  move/andP in HInstType. destruct HInstType.
  repeat (move/andP in H; destruct H).
  simpl in HN1. simpl in HN3.
  eapply all2_projection in H3; eauto.
  unfold functions_agree in H3. move/andP in H3. destruct H3.
  unfold option_map in H4.
  rewrite HN2 in H4. move/eqP in H4.
  by inversion H4.
Qed.

Lemma tc_func_reference2: forall s C i j cl tf,
  List.nth_error (inst_types i) j = Some (cl_type cl) ->
  inst_typing s i C ->
  List.nth_error (tc_types_t C) j = Some tf ->
  tf = cl_type cl.
Proof.
  move => s C i j cl tf HN1 HIT HN2.
  unfold inst_typing in HIT.
  destruct i => //=.
  destruct C => //=.
  destruct tc_local => //=.
  destruct tc_label => //=.
  destruct tc_return => //=.
  move/andP in HIT. destruct HIT.
  repeat (move/andP in H; destruct H).
  simpl in HN1. simpl in HN2.
  move/eqP in H. subst.
  rewrite HN1 in HN2.
  by inversion HN2.
Qed.

Lemma upd_label_unchanged: forall C lab,
    tc_label C = lab ->
    upd_label C lab = C.
Proof.
  move => C lab HLab.
  rewrite -HLab. unfold upd_label. by destruct C.
Qed.

Lemma upd_label_unchanged_typing: forall s C es tf,
    e_typing s C es tf ->
    e_typing s (upd_label C (tc_label C)) es tf.
Proof.
  move => s C es tf HType.
  by rewrite upd_label_unchanged.
Qed.

Lemma upd_label_upd_local_return_combine: forall C loc lab ret,
    upd_label (upd_local_return C loc ret) lab =
    upd_local_label_return C loc lab ret.
Proof.
  by [].
Qed.

Lemma set_nth_same_unchanged: forall {X:Type} (l:seq X) e i vd,
    List.nth_error l i = Some e ->
    set_nth vd l i e = l.
Proof.
  move => X l e i.
  generalize dependent l. generalize dependent e.
  induction i; move => e l vd HNth => //=.
  - destruct l => //=.
    simpl in HNth. by inversion HNth.
  - destruct l => //=.
    f_equal. apply IHi.
    by simpl in HNth.
Qed.

Lemma set_nth_map: forall {X Y:Type} (l:seq X) e i vd {f: X -> Y},
    i < size l ->
    map f (set_nth vd l i e) = set_nth (f vd) (map f l) i (f e).
Proof.
  move => X Y l e i.
  generalize dependent l. generalize dependent e.
  induction i; move => e l vd f HSize => //=.
  - by destruct l => //=.
  - destruct l => //=.
    f_equal.
    apply IHi.
    by simpl in HSize.
Qed.

Lemma n_zeros_typing: forall ts,
    map typeof (n_zeros ts) = ts.
Proof.
  induction ts => //=.
  by destruct a => //=; f_equal.
Qed.

Lemma global_agree_extension: forall g0 g1 g,
    global_agree g0 g ->
    glob_extension g0 g1 ->
    global_agree g1 g.
Proof.
  move => g0 g1 g H1 H2.
  unfold global_agree.
  unfold global_agree in H1. unfold glob_extension in H2.
  destruct g => //=.
  destruct g0 => //=.
  destruct g1 => //=.
  simpl in H2. simpl in H1.
  remove_bools_options; subst; first by rewrite H0; lias.
  by destruct g_mut => //=; remove_bools_options;
    apply/andP => //=; subst; split => //=;
    destruct g_mut0 => //=; destruct g_val => //=; destruct g_val0 => //=.
Qed.

Lemma glob_extension_C: forall sg sg' ig tcg,
    all2 (globals_agree sg) ig tcg ->
    comp_extension sg sg' glob_extension ->
    all2 (globals_agree sg') ig tcg.
Proof.
  move => sg sg' ig tcg Hagree Hext.
  eapply all2_weaken; try apply Hagree.
  move => x y Hgagree.
  unfold globals_agree in *.
  unfold comp_extension in Hext.
  remove_bools_options.
  destruct (List.nth_error sg' x) as [g' |] eqn:Hnth; last by apply List.nth_error_None in Hnth; lias.
  simpl in *.
  apply (nth_error_take (k := length sg)) in Hnth => //.
  apply/andP; split; first by lias.
  specialize (all2_projection H2 Hoption Hnth) as Hproj.
  eapply global_agree_extension in Hproj; last by apply H4.
  by apply/eqP; f_equal; lias.
Qed.

Lemma mem_typing_extension: forall m m' y,
    mem_typing m y ->
    mem_extension m m' ->
    mem_typing m' y.
Proof.
  move => m m' y Htype Hext.
  unfold mem_typing in *.
  unfold mem_extension in Hext.
  remove_bools_options.
  apply/andP; split; last by apply/eqP; rewrite -H2 -H0.
  { apply/N.leb_spec0.
    move/N.leb_spec0 in H.
    move/N.leb_spec0 in H1.
    by lias.
  }
Qed.

Lemma mem_extension_C: forall sm sm' im tcm,
    all2 (memi_agree sm) im tcm ->
    comp_extension sm sm' mem_extension ->
    all2 (memi_agree sm') im tcm.
Proof.
  move => sm sm' im tcm Hagree Hext.
  eapply all2_weaken; try apply Hagree.
  move => x y Hmagree.
  unfold memi_agree in *.
  unfold comp_extension in Hext.
  remove_bools_options.
  destruct (List.nth_error sm' x) as [m' |] eqn:Hnth; last by apply List.nth_error_None in Hnth; lias.
  apply (nth_error_take (k := length sm)) in Hnth => //.
  apply/andP; split; first by lias.
  specialize (all2_projection H2 Hoption Hnth) as Hproj.
  by eapply mem_typing_extension; eauto.
Qed.

Lemma tab_typing_extension: forall t t' y,
    tab_typing t y ->
    tab_extension t t' ->
    tab_typing t' y.
Proof.
  move => t t' y Htype Hext.
  unfold tab_typing in *.
  unfold tab_extension in Hext.
  remove_bools_options.
  apply/andP; split; last by apply/eqP; rewrite -H0; lias.
  by lias.
Qed.

Lemma tab_extension_C: forall st st' it tct,
    all2 (tabi_agree st) it tct ->
    comp_extension st st' tab_extension ->
    all2 (tabi_agree st') it tct.
Proof.
  move => st st' it tct Hagree Hext.
  eapply all2_weaken; try apply Hagree.
  move => x y Htagree.
  unfold tabi_agree in *.
  unfold comp_extension in Hext.
  remove_bools_options.
  destruct (List.nth_error st' x) as [t' |] eqn:Hnth; last by apply List.nth_error_None in Hnth; lias.
  apply (nth_error_take (k := length st)) in Hnth => //.
  apply/andP; split; first by lias.
  specialize (all2_projection H2 Hoption Hnth) as Hproj.
  by eapply tab_typing_extension; eauto.
Qed.

Lemma func_agree_extension: forall f0 f1 n f,
    typing.functions_agree f0 n f ->
    comp_extension f0 f1 func_extension ->
    typing.functions_agree f1 n f.
Proof.
  move => f0 f1 n f Hagree Hext.
  unfold comp_extension, func_extension, operations.func_extension in Hext.
  unfold typing.functions_agree in *.
  remove_bools_options.
  apply/andP; split; first lias.
  assert (List.nth_error f1 n = Some f2) as Hnth; last by rewrite Hnth.
  assert (f1 = (take (length f0) f1) ++ (drop (length f0) f1)) as Hcat; first by rewrite cat_take_drop.
  rewrite -> Hcat.
  remember (take (length f0) f1) as f0'.
  assert (f0 = f0') as ->.
  { clear - H0. move : f0' H0.
    induction f0; move => f0' H0; destruct f0' => //=.
    simpl in *.
    remove_bools_options; subst.
    f_equal.
    by apply IHf0.
  }
  rewrite List.nth_error_app1 => //.
  by lias.
Qed.
  
Lemma func_extension_C: forall sf sf' fi tcf,
    all2 (typing.functions_agree sf) fi tcf ->
    comp_extension sf sf' func_extension ->
    all2 (typing.functions_agree sf') fi tcf.
Proof.
  move => sf sf' fi.
  move: sf sf'.
  induction fi; move => sf sf' tcf HA Hext => //=; destruct tcf => //=.
  simpl in HA. remove_bools_options.
  apply/andP; split => //=; last by eapply IHfi; eauto.
  by eapply func_agree_extension; eauto.
Qed.
  
Lemma inst_typing_extension: forall s s' i C,
    store_extension s s' ->
    inst_typing s i C ->
    inst_typing s' i C.
Proof.
  move => s s' i C HST HIT.
  unfold store_extension in HST. unfold operations.store_extension in HST.
  unfold inst_typing in HIT. unfold typing.inst_typing in HIT.
  unfold inst_typing. unfold typing.inst_typing.
  destruct i => //=.
  destruct C => //=.
  destruct tc_local => //. destruct tc_label => //. destruct tc_return => //.
  remove_bools_options. 
  repeat (apply/andP; split => //=; subst => //=).
  - by eapply func_extension_C; eauto.
  - by eapply glob_extension_C; eauto.
  - by eapply tab_extension_C; eauto.
  - by eapply mem_extension_C; eauto.
Qed.

Lemma frame_typing_extension: forall s s' f C,
    store_extension s s' ->
    frame_typing s f C ->
    frame_typing s' f C.
Proof.
  move => s s' f C HST HIT.
  unfold store_extension in HST. unfold operations.store_extension in HST.
  inversion HIT. subst.
  eapply inst_typing_extension in H; eauto.
  by eapply mk_frame_typing; eauto.
Qed.

Ltac convert_et_to_bet:=
  lazymatch goal with
  | H: e_typing _ _ _ _ |- _ =>
    apply et_to_bet in H; try auto_basic; simpl in H
  end.

(* TODO: find better fixes than the current duplication. *)
Ltac split_et_composition:=
  lazymatch goal with
  | H: e_typing _ _ (_ ++ _) _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let t2s := fresh "t2s" in
    let t3s := fresh "t3s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply e_composition_typing in H;
    destruct H as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]]; subst
  | H: typing.e_typing _ _ (_ ++ _) _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let t2s := fresh "t2s" in
    let t3s := fresh "t3s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply e_composition_typing in H;
    destruct H as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]]; subst
  end.

Ltac invert_e_typing:=
  repeat lazymatch goal with
  | H: e_typing _ _ (_ ++ _) _ |- _ =>
    split_et_composition
  | H: typing.e_typing _ _ (_ ++ _) _ |- _ =>
    split_et_composition
  | H: e_typing _ _ [::AI_label _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Label_typing in H;
    destruct H as [ts [t1s [H1 [H2 [H3 H4]]]]]; subst
  | H: typing.e_typing _ _ [::AI_label _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    eapply Label_typing in H; eauto;
    destruct H as [ts [t1s [H1 [H2 [H3 H4]]]]]; subst
  end.

Lemma lfilled_es_type_exists {k}: forall (lh: lholed k) es les s C tf,
    lfill lh es = les ->
    e_typing s C les tf ->
    exists lab t1s t2s, e_typing s (upd_label C lab) es (Tf t1s t2s).
Proof.
  elim.
  - move => vs es es' LI s C [ts1 ts2] <- /= Htype.
    invert_e_typing.
    exists (tc_label C); repeat eexists => //=.
    by rewrite upd_label_unchanged; eauto.
  - move => k' vs n es lh IH es' es'' LI s C [ts1 ts2] <- /= Htype.
    rewrite -cat1s in Htype.
    invert_e_typing.
    by edestruct IH; eauto.
Qed.

Lemma store_extension_cl_typing: forall (s s': store_record) cl tf,
    store_extension s s' ->
    cl_typing s cl tf ->
    cl_typing s' cl tf.
Proof.
  move => s s' cl tf Hext HType.
  inversion HType; subst.
  - eapply cl_typing_native; eauto.
    by eapply inst_typing_extension; eauto.
  - by eapply cl_typing_host; eauto.
Qed.

Lemma store_extension_e_typing: forall s s' C es tf,
    store_typing s ->
    store_typing s' ->
    store_extension s s' ->
    e_typing s C es tf -> e_typing s' C es tf.
Proof.
  move=> s s' C es tf HST1 HST2 Hext HType. move: s' HST1 HST2 Hext.
  apply e_typing_ind' with (e := HType)
    (P := fun s C es tf (_ : e_typing s C es tf) => forall s',
            store_typing s ->
            store_typing s' ->
            store_extension s s' ->
            e_typing s' C es tf)
    (P0 := fun s rs f es ts (_ : s_typing s rs f es ts) => forall s',
             store_typing s ->
             store_typing s' ->
             store_extension s s' ->
             s_typing s' rs f es ts); clear HType s C es tf.
  - move=> s C bes tf HType s' HST1 HST2 Hext.
    apply ety_a'; first by apply to_e_list_basic.
    replace (operations.to_b_list (operations.to_e_list bes)) with bes => //.
    by apply b_e_elim.
  - move=> s C bes tf r1 r2 r3 HType1 IHHType1 IH2 IHHType2 s' HST1 HST2 Hext.
    eapply ety_composition.
    + by apply IHHType1.
    + by apply IHHType2.
  - move=> s C es tf t1s t2s HType IHHType s' HST1 HST2 Hext.
    eapply ety_weakening. by apply IHHType.
  - move=> s C tf s' HST1 HST2 Hext.
    by apply ety_trap.
  - move=> s C n f es ts HType IHHType E s' HST1 HST2 Hext.
    apply ety_local => //.
    by eapply IHHType; try apply HST1 => //.
  - move=> s a C cl tf HNth HCLType s' HST1 HST2 Hext.
    eapply ety_invoke; eauto => //; first by eapply store_extension_lookup_func; eauto.
    by eapply store_extension_cl_typing; eauto.
  - move=> s C es es' t1s t2s n HType1 IHHType1 HType2 IHHType2 E s' HST1 HST2 Hext.
    eapply ety_label => //; eauto.
    + by apply IHHType1.
    + by apply IHHType2.
  - move=> s f es rs ts C C' HFType HContext HType IHHType E' s' HST1 HST2 Hext.
    eapply mk_s_typing; eauto.
    + by eapply frame_typing_extension; eauto.
    + by apply IHHType.
Defined.

Lemma glob_extension_update_nth: forall sglobs n g g',
  List.nth_error sglobs n = Some g ->
  glob_extension g g' ->
  all2 glob_extension sglobs (set_nth g' sglobs n g').
Proof.
  move => sglobs n.
  generalize dependent sglobs.
  induction n; move => sglobs g g' HN Hext => //=; destruct sglobs => //.
  - simpl in HN. inversion HN. subst.
    apply/andP; split => //=.
    by apply all2_glob_extension_same.
  - assert ((n.+1 < length (g0 :: sglobs))%coq_nat); first by rewrite -List.nth_error_Some; rewrite HN.
    simpl.
    apply/andP. split.
    + by apply glob_extension_refl. 
    + by eapply IHn; eauto.
Qed.

Lemma tc_reference_glob_type: forall s i C n m gt g,
    inst_typing s i C ->
    List.nth_error i.(inst_globs) n = Some m ->
    List.nth_error s.(s_globals) m = Some g ->
    List.nth_error C.(tc_global) n = Some gt ->
    global_agree g gt.
Proof.
  move => s i C n m gt g HIT HN1 HN2 HN3.
  unfold inst_typing in HIT. unfold typing.inst_typing in HIT.
  destruct i => //=.
  destruct C => //=.
  destruct tc_local => //=.
  destruct tc_label => //=.
  destruct tc_return => //=.
  remove_bools_options.
  eapply all2_projection in H2; eauto.
  unfold globals_agree in H2.
  unfold s_globals in HN2.
  by remove_bools_options.
Qed.

Lemma mem_extension_update_nth: forall smems n m m',
  List.nth_error smems n = Some m ->
  mem_extension m m' ->
  all2 mem_extension smems (set_nth m' smems n m').
Proof.
  move => smems n.
  generalize dependent smems.
  induction n; move => smems m m' HN Hext => //=; destruct smems => //.
  - simpl in HN. inversion HN. subst.
    apply/andP. split; first apply Hext.
   by apply all2_mem_extension_same.
  - assert ((n.+1 < length (m0 :: smems))%coq_nat); first by rewrite -List.nth_error_Some; rewrite HN.
    simpl.
    apply/andP. split.
    + unfold mem_extension. apply/andP; split => //.
      apply N.leb_le; by lias.
    + by eapply IHn; eauto.
Qed.

Lemma bytes_takefill_size: forall c l vs,
    size (bytes_takefill c l vs) = l.
Proof.
  move => c l. induction l => //=.
  by destruct vs => //=; f_equal.
Qed.

Lemma bytes_replicate_size: forall n b,
    size (bytes_replicate n b) = n.
Proof.
  induction n => //=.
  by move => b; f_equal.
Qed.

Lemma div_le: forall a b, b > 0 -> a/b <= a.
Proof.
  move => a b H.
  destruct b => //.
  destruct b => //; first by rewrite Nat.div_1_r; lias.
  destruct a => //.
  assert (a.+1/b.+2 < a.+1)%coq_nat.
  { by apply Nat.div_lt; lias. }
  by lias.
Qed.

(* Start of proof to write_bytes preserving memory type *)

Lemma list_fold_left_rev_prop: forall {X Y: Type} P f (l: seq X) (a1 a2: Y),
    List.fold_left f l a1 = a2 ->
    P a2 ->
    (forall a e a', P a' -> f a e = a' -> P a) ->
    P a1.
Proof.
  move => X Y P f l.
  elim: l => //=.
  - move => a1 a2 H. by subst.
  - move => e l IH a1 a2 HFold HP HNec.
    assert (HPF: P (f a1 e)); first by eapply IH; eauto.
    by eapply HNec; eauto.
Qed.
    
Lemma list_fold_left_restricted_trans: forall {X Y: Type} P R f (l: seq X) (a1 a2: Y),
    List.fold_left f l a1 = a2 ->
    P a1 ->
    P a2 ->
    (forall a e a', P a -> P a' -> f a e = a' -> R a a') ->
    (forall a, P a -> R a a) ->
    (forall a1 a2 a3, P a1 -> P a2 -> P a3 -> R a1 a2 -> R a2 a3 -> R a1 a3) ->
    (forall a e a', P a' -> f a e = a' -> P a) ->
    R a1 a2.
Proof.
  move => X Y P R f l.
  elim: l => //=.
  - move => a1 a2 H HP1 HP2 HF HRefl HTrans HNec. subst.
    by apply HRefl.
  - move => e l IH a1 a2 HFold HP1 HP2 HF HRefl HTrans HNec.
    assert (HPF: P (f a1 e)); first by eapply list_fold_left_rev_prop; eauto.
    assert (HRf2: R (f a1 e) a2); first by apply IH.
    assert (HR1f: R a1 (f a1 e)); first by eapply HF; eauto.
    by eapply HTrans; eauto.
Qed.
    
Definition proj2_some (acc: nat * option memory_list.memory_list) : Prop :=
  let (n, om) := acc in
  exists m, om = Some m.

Definition mem_type_proj2_preserve (acc1 acc2: nat * option memory_list.memory_list) : Prop :=
  let (n1, om1) := acc1 in
  let (n2, om2) := acc2 in
  (exists m1 m2,
      om1 = Some m1 /\
      om2 = Some m2 /\
      memory_list.mem_length m1 = memory_list.mem_length m2).

Lemma mem_type_proj2_preserve_trans: forall a1 a2 a3,
    proj2_some a1 ->
    proj2_some a2 ->
    proj2_some a3 ->
    mem_type_proj2_preserve a1 a2 ->
    mem_type_proj2_preserve a2 a3 ->
    mem_type_proj2_preserve a1 a3.
Proof.
  unfold mem_type_proj2_preserve, proj2_some.
  move => a1 a2 a3 HP1 HP2 HP3 HR12 HR23.
  destruct a1, a2, a3 => /=.
  destruct HP1, HP2, HP3, HR12, HR23. subst.
  repeat eexists; eauto.
  destruct H2 as [m2 [H21 [H22 HLen1]]].
  destruct H3 as [m2' [H31 [H32 HLen2]]].
  inversion H21. inversion H22. inversion H31. inversion H32. subst.
  by lias.
Qed.

Lemma write_bytes_preserve_type: forall m pos str m',
  write_bytes m pos str = Some m' ->
  (mem_size m = mem_size m') /\ (mem_max_opt m = mem_max_opt m').
Proof.
  unfold write_bytes, fold_lefti.
  move => m pos str m' H.
  remove_bools_options.
  match goal with | H : ?T = _ |- _ =>
                    match T with context [List.fold_left ?f ?str ?nom] => remember (List.fold_left f str nom) as fold_res
                    end
  end.
  assert (HPreserve: mem_type_proj2_preserve (0, Some (mem_data m)) fold_res).
  symmetry in Heqfold_res.
  destruct fold_res; subst.
  eapply list_fold_left_restricted_trans with (P := proj2_some); unfold proj2_some; eauto.
  - move => a e a' HP1 HP2 HF.
    unfold mem_type_proj2_preserve.
    destruct a as [n1 m1]. destruct a' as [n2 m2].
    destruct HP1 as [m3 HP1]; destruct HP2 as [m4 HP2].
    subst.
    repeat eexists.
    injection HF. move => H1 H2. subst. clear HF.
    (* TODO: Use mem_ax_length_constant_update to prove this after porting in the 
         parameterized memory branch *)
    unfold memory_list.mem_update in H1.
    destruct (pos + N.of_nat n1 <? N.of_nat (length (memory_list.ml_data m3)))%N eqn:HMemSize => //=.
    injection H1. move => H2. clear H1. subst.
    unfold memory_list.mem_length => /=.
    repeat rewrite length_is_size.
    repeat rewrite size_cat => /=.
    rewrite size_take. rewrite size_drop.
    apply N.ltb_lt in HMemSize.
    rewrite length_is_size in HMemSize.
    assert (N.to_nat (pos+N.of_nat n1) < size (memory_list.ml_data m3)); first by lias.
    rewrite H.
    by lias.
  - move => a HP. destruct a as [n1 m1].
    destruct HP as [m2 HP]. subst.
    unfold mem_type_proj2_preserve.
    by repeat eexists.
  - by apply mem_type_proj2_preserve_trans.
  - move => a e a' HP HF.
    destruct a as [n1 m1]. destruct a' as [n2 m2].
    destruct HP as [m3 HP]. subst.
    destruct m1; inversion HF => //=; subst.
    by eexists.
  - simpl in HPreserve. destruct fold_res. subst.
    destruct HPreserve as [m1 [m2 [H1 [H2 HLen]]]].
    inversion H1; inversion H2; subst; clear H1; clear H2.
    split => //.
    unfold mem_size, mem_length => /=.
    by rewrite HLen.
Qed.
  
Lemma mem_extension_store: forall m k off v tlen mem,
    store m k off (bits v) tlen = Some mem ->
    mem_extension m mem.
Proof.
  move => m k off v tlen mem HStore.
  unfold mem_extension.
  unfold store in HStore.
  destruct ((k + off + N.of_nat tlen <=? mem_length m)%N) eqn:HMemSize => //.
  remove_bools_options.
  apply write_bytes_preserve_type in HStore; destruct HStore as [H1 H2]; rewrite H1; rewrite H2.
  apply/andP; split => //=.
  apply N.leb_le.
  by lias.
Qed.

Lemma mem_extension_grow_memory: forall m c mem,
    mem_grow m c = (Some mem) ->
    mem_extension m mem.
Proof.
  move => m c mem HMGrow.
  unfold mem_extension.
  unfold mem_grow in HMGrow.
  destruct (mem_size m + c <=? page_limit)%N eqn:HLP => //.
  - destruct (mem_max_opt m) eqn:HLimMax => //=.
    destruct ((mem_size m + c <=? n)%N) eqn:HLT => //.
    move : HMGrow.
    case: mem => mem_data_ mem_max_opt_ H.
    inversion H. subst. clear H.
    simpl.
    apply/andP.
    split => //.
    (* TODO: Add a lemma for size of mem_grow, and use it to prove this after porting 
         in the parameterized memory branch *)
    { unfold mem_size, mem_length, memory_list.mem_length in *.
      simpl.
      repeat rewrite length_is_size.
      rewrite size_cat.
      apply N.leb_le.
      apply N.div_le_mono => //.
      by lias.
      }
  - inversion HMGrow; subst; clear HMGrow.
    unfold mem_size, mem_length, memory_list.mem_length.
    simpl.
    apply/andP; split => //.
    apply N.leb_le.
    repeat rewrite length_is_size.
    rewrite size_cat.
    apply N.div_le_mono => //.
    by lias.
Qed.
  
Lemma store_global_extension_store_typed: forall s s',
    store_typing s ->
    store_extension s s' ->
    (s_funcs s = s_funcs s') ->
    (s_tables s = s_tables s') ->
    (s_mems s = s_mems s') ->
    store_typing s'.
Proof.
  move => s s' HST Hext HF HT.
  remember HST as HST'. clear HeqHST'.
  unfold store_typing in HST.
  unfold store_typing.
  destruct s => //=.
  destruct s' => //=.
  destruct HST.
  rewrite -> List.Forall_forall in H.
  rewrite -> List.Forall_forall in H0.
  split => //; remove_bools_options; simpl in HF; simpl in HT; subst.
  - rewrite -> List.Forall_forall. move => x HIN.
    apply H in HIN. unfold cl_type_check_single in HIN.
    destruct HIN.
    unfold cl_type_check_single.
    exists x0. by eapply store_extension_cl_typing; eauto.
  - split => //.
    + rewrite -> List.Forall_forall. move => x HIN.
      apply H0 in HIN. unfold tab_agree in HIN.
      destruct HIN.
      rewrite -> List.Forall_forall in H1.
      unfold tab_agree.
      by rewrite -> List.Forall_forall.
    + unfold store_extension in Hext. simpl in Hext.
      remove_bools_options.
      rewrite List.Forall_forall.
      move => x HIN.
      destruct HST' as [_ [_ H8]].
      rewrite -> List.Forall_forall in H8.
      apply List.In_nth_error in HIN.
      destruct HIN as [n HN].
      apply H8. by eapply List.nth_error_In; eauto.
Qed.

Lemma store_memory_extension_store_typed: forall s s',
    store_typing s ->
    store_extension s s' ->
    (s_funcs s = s_funcs s') ->
    (s_tables s = s_tables s') ->
    List.Forall mem_agree (s_mems s') ->
    store_typing s'.
Proof.
  move => s s' HST Hext HF HT HMem.
  remember HST as HST'. clear HeqHST'.
  unfold store_typing in HST.
  unfold store_typing.
  destruct s => //=.
  destruct s' => //=.
  destruct HST.
  rewrite -> List.Forall_forall in H.
  rewrite -> List.Forall_forall in H0.
  split => //; remove_bools_options; simpl in HF; simpl in HT; subst.
  - rewrite -> List.Forall_forall. move => x HIN.
    apply H in HIN. unfold cl_type_check_single in HIN.
    destruct HIN.
    unfold cl_type_check_single.
    exists x0. by eapply store_extension_cl_typing; eauto.
  - split => //.
    rewrite -> List.Forall_forall. move => x HIN.
    apply H0 in HIN. unfold tab_agree in HIN.
    destruct HIN.
    rewrite -> List.Forall_forall in H1.
    unfold tab_agree.
    by rewrite -> List.Forall_forall.
Qed.

Lemma nth_error_map: forall {X Y:Type} l n (f: X -> Y) fv,
    List.nth_error (map f l) n = Some fv ->
    exists v,
      List.nth_error l n = Some v /\
      f v = fv.
Proof.
  move => X Y l n.
  generalize dependent l.
  induction n => //=; move => l f fv HNth; destruct l => //=.
  - destruct (map f (x::l)) eqn:HMap => //=.
    inversion HNth; subst.
    simpl in HMap. inversion HMap. subst.
    by eexists.
  - destruct (map f (x::l)) eqn:HMap => //=.
    simpl in HMap. inversion HMap. subst.
    by apply IHn.
Qed.

Lemma nth_error_nth: forall {X: Type} l n {x:X},
  n < length l ->
  List.nth_error l n = Some (nth x l n).
Proof.
  induction l; destruct n => //=.
  by apply IHl.
Qed.

Lemma nth_error_set_nth_length: forall {X: Type} l n {x0 x xd: X},
  List.nth_error l n = Some x0 ->
  length (set_nth xd l n x) = length l.
Proof.
  move => X l n x0 x xd Hnth.
  apply nth_error_Some_length in Hnth.
  repeat rewrite length_is_size.
  rewrite size_set_nth -length_is_size.
  unfold maxn.
  destruct (n.+1 < _) eqn:Hlt => //.
  by lias.
Qed.

Lemma nth_error_set_eq: forall {X:Type} l n {x xd:X},
    n < length l ->
    List.nth_error (set_nth xd l n x) n = Some x.
Proof.
  move => X l n x xd Hlen.
  rewrite -> nth_error_nth with (x := xd); first by rewrite nth_set_nth /= eq_refl.
  rewrite length_is_size size_set_nth -length_is_size.
  unfold maxn.
  by destruct (n.+1 < length l).
Qed.

Lemma nth_error_set_neq: forall {X:Type} l n m {x xd:X},
    n <> m ->
    n < length l ->
    List.nth_error (set_nth xd l n x) m = List.nth_error l m.
Proof.
  move => X l n. move: l.
  induction n => //=; move => l m x Hne HLength.
  - destruct m => //=.
    by destruct l => //=.
  - destruct m => //=.
    + by destruct l => //=.
    + destruct l => //=.
      simpl in HLength.
      by apply IHn; lias.
Qed.

Lemma Forall_set: forall {X:Type} f l n {x xd:X},
    List.Forall f l ->
    f x ->
    n < length l ->
    List.Forall f (set_nth xd l n x).
Proof.
  move => X f l. induction l; destruct n; move => x xd Hall Hf Hlen => //; constructor => //=; try by inversion Hall.
  apply IHl => //.
  by inversion Hall.
Qed.

Lemma store_typed_mem_agree: forall s n m,
    store_typing s ->
    List.nth_error (s_mems s) n = Some m ->
    mem_agree m.
Proof.
  move => s n m HST HN.
  unfold store_typing in HST.
  destruct s => //=.
  destruct HST as [_ [_ H]].
  rewrite -> List.Forall_forall in H.
  simpl in HN.
  apply H. by eapply List.nth_error_In; eauto.
Qed.

Lemma store_mem_agree: forall s n m k off vs tl mem,
    store_typing s ->
    List.nth_error (s_mems s) n = Some m ->
    store m k off vs tl = Some mem ->
    tl > 0 ->
    mem_agree mem.
Proof.
  move => s n m k off vs tl mem HST HN HStore HTL.
  unfold store in HStore.
  destruct ((k+off+N.of_nat tl <=? mem_length m)%N) eqn:H => //=.
  apply write_bytes_preserve_type in HStore.
  destruct HStore as [HMemSize HMemLim].
  assert (mem_agree m); first by eapply store_typed_mem_agree; eauto.
  unfold mem_agree in H0. rewrite HMemLim in H0.
  unfold mem_agree => //=.
  destruct (mem_max_opt mem) eqn:HLimMax => //=.
  by rewrite HMemSize in H0.
Qed.

Lemma mem_grow_mem_agree: forall s n m c mem,
    store_typing s ->
    List.nth_error (s_mems s) n = Some m ->
    mem_grow m c = Some mem ->
    mem_agree mem.
Proof.
  move => s n m c mem HST HN HGrow.
  assert (mem_agree m); first by eapply store_typed_mem_agree; eauto.
  unfold mem_grow in HGrow.
  unfold mem_agree. simpl.
  unfold mem_agree in H.
  destruct (mem_size m + c <=? page_limit)%N eqn:HLP => //.
  - destruct (mem_max_opt m) eqn:HLimMax => //=.
    destruct ((mem_size m + c <=? n0)%N) eqn:H1 => //.
    inversion HGrow. unfold mem_size, mem_length, memory_list.mem_length in *. simpl in *. subst. clear HGrow.
    rewrite length_is_size. rewrite size_cat.
    repeat rewrite - length_is_size. rewrite List.repeat_length.
    rewrite - N.div_add in H1 => //.
    apply N.leb_le in H1.
    by lias.
  - by inversion HGrow.
Qed.
    
Lemma reduce_inst_unchanged: forall hs s f es hs' s' f' es',
    reduce hs s f es hs' s' f' es' ->
    f.(f_inst) = f'.(f_inst).
Proof.
  move => hs s f es hs' s' f' es' HReduce.
  by induction HReduce.
Qed.

Lemma store_extension_mem: forall s i mem mem',
  List.nth_error s.(s_mems) i = Some mem ->
  mem_extension mem mem' ->
  store_extension s (upd_s_mem s (set_nth mem' (s_mems s) i mem')).
Proof.
  move => s i mem mem' Hnth Hext.
  unfold store_extension => //=.
  repeat (apply/andP; split) => //=.
  - by rewrite length_is_size take_size; apply all2_func_extension_same.
  - by rewrite length_is_size take_size; apply all2_tab_extension_same.
  - apply nth_error_Some_length in Hnth.
    repeat rewrite length_is_size.
    rewrite size_set_nth - length_is_size.
    unfold maxn.
    destruct (i.+1 < length (datatypes.s_mems s)) eqn:Hlt => //.
    by lias.
  - match goal with
    | |- context [take ?n ?l] => remember l as l'
    | _ => idtac
    end.
    assert (length l' = length s.(s_mems)) as Hlen.
    { subst l'.
      by eapply nth_error_set_nth_length; eauto.
    }
    rewrite - Hlen.
    rewrite length_is_size take_size.
    subst l'.
    eapply mem_extension_update_nth; eauto => //=.
  - by rewrite length_is_size take_size; apply all2_glob_extension_same.
Qed. 

Lemma store_extension_reduce: forall s f es s' f' es' C tf loc lab ret hs hs',
    reduce hs s f es hs' s' f' es' ->
    inst_typing s f.(f_inst) C ->
    e_typing s (upd_label (upd_local_return C loc ret) lab) es tf ->
    store_typing s ->
    store_extension s s' /\ store_typing s'.
Proof.
  move => s f es s' f' es' C tf loc lab ret hs hs' HReduce.
  generalize dependent C. generalize dependent tf.
  generalize dependent loc. generalize dependent lab. generalize dependent ret.
  induction HReduce => //; try move => ret lab loc tf C HIT HType HST; try intros; destruct tf; try by (split => //; apply store_extension_same).
  - (* invoke *)
    destruct host_instance.
    split.
    + by eapply host_application_extension; eauto.
    + by eapply host_application_typing; eauto.
  - (* update glob *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::BI_const v; BI_set_global i] with ([::BI_const v] ++ [::BI_set_global i]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]]. subst.
    invert_be_typing.
    unfold supdate_glob in H.
    unfold option_bind in H.
    unfold supdate_glob_s in H.
    unfold option_map in H.
    assert (store_extension s s') as Hext.
    { remove_bools_options.
      unfold sglob_ind in Hoption.
      eapply tc_reference_glob_type in HIT; eauto.
      destruct g, g_setglobal => //.
      unfold global_agree in HIT. simpl in *.
      unfold is_mut in H3_setglobal. simpl in H3_setglobal. remove_bools_options. subst.
      simpl. unfold store_extension => //=.
      repeat (apply/andP; split) => //=.
      - by rewrite length_is_size take_size; apply all2_func_extension_same.
      - by rewrite length_is_size take_size; apply all2_tab_extension_same.
      - by rewrite length_is_size take_size; apply all2_mem_extension_same.
      - by erewrite nth_error_set_nth_length; eauto.
      - match goal with
        | |- context [take ?n ?l] => remember l as l'
        | _ => idtac
        end.
        assert (length l' = length s.(s_globals)) as Hlen.
        { subst l'.
          by erewrite nth_error_set_nth_length; eauto.
        }
        rewrite - Hlen.
        rewrite length_is_size take_size.
        subst l'.
        eapply glob_extension_update_nth; eauto => //=.
        unfold glob_extension => //=.
        by destruct v => //=; destruct g_val => //=.
    }
    split => //.
    by eapply store_global_extension_store_typed; eauto;
    destruct s => //=; destruct s' => //=; remove_bools_options.
  - (* update memory : store none *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::BI_const (VAL_int32 k); BI_const v; BI_store t None a off] with ([::BI_const (VAL_int32 k); BI_const v] ++ [::BI_store t None a off]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    invert_be_typing.
    remove_bools_options.
    assert (store_extension s (upd_s_mem s (set_nth mem' (s_mems s) i mem'))) as Hext.
    { eapply store_extension_mem => //; first by rewrite H1.
      by eapply mem_extension_store; eauto.
    }
    split => //.
    eapply store_memory_extension_store_typed; eauto => //=.
    remember HST as HST2. clear HeqHST2.
    unfold store_typing in HST.
    destruct s => //=.
    destruct HST as [_ [_ H11]].
    simpl in H1.
    assert (i < length s_mems0)%coq_nat.
    { apply List.nth_error_Some. by rewrite H1. }
    inversion H0; subst. clear H0.
    apply Forall_set => //=.
    eapply store_mem_agree; eauto.
    * by destruct t.
    * by move/ltP in H3.
  - (* another update memory : store some *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::BI_const (VAL_int32 k); BI_const v; BI_store t (Some tp) a off] with ([::BI_const (VAL_int32 k); BI_const v] ++ [::BI_store t (Some tp) a off]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    invert_be_typing.
    remove_bools_options.
    assert (store_extension s (upd_s_mem s (set_nth mem' (s_mems s) i mem'))) as Hext.
    { eapply store_extension_mem => //; first by rewrite H1.
      by eapply mem_extension_store; eauto.
    }
    split => //.
    eapply store_memory_extension_store_typed; eauto => //=.
    remember HST as HST2. clear HeqHST2.
    unfold store_typing in HST.
    destruct s => //=.
    destruct HST as [_ [_ H11]].
    simpl in H1.
    assert (i < length s_mems0)%coq_nat.
    { apply List.nth_error_Some. by rewrite H1. }
    apply Forall_set => //=.
    eapply store_mem_agree; eauto.
    * by destruct tp => //=.
    * by move/ltP in H3.
  - (* again update memory : grow_memory *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::BI_const (VAL_int32 c); BI_grow_memory] with ([::BI_const (VAL_int32 c)] ++ [::BI_grow_memory]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    invert_be_typing.
    assert (store_extension s (upd_s_mem s (set_nth mem' (s_mems s) i mem'))) as Hext.
    { eapply store_extension_mem => //; first by rewrite H0.
      by eapply mem_extension_grow_memory; eauto.
    }
    split => //.
    eapply store_memory_extension_store_typed; eauto => //=.
    remember HST as HST2. clear HeqHST2.
    unfold store_typing in HST.
    destruct s => //=.
    destruct HST as [_ [_ H11]].
    simpl in H0.
    assert (i < length s_mems0)%coq_nat.
    { apply List.nth_error_Some. by rewrite H0. }
    apply Forall_set => //=.
    eapply mem_grow_mem_agree; eauto. by move/ltP in H1.
  - (* r_label *)
    eapply lfilled_es_type_exists in HType; eauto.
    destruct HType as [lab' [t1s [t2s HType]]].
    eapply IHHReduce; eauto.
    rewrite upd_label_overwrite in HType. by apply HType.
  - (* r_local *)
    apply Local_typing in HType.
    destruct HType as [ts [H1 [H2 H3]]]. subst.
    inversion H2. inversion H. subst.
    apply upd_label_unchanged_typing in H1.
    eapply IHHReduce => //=; eauto.
Qed.

Lemma result_e_type: forall r ts s C,
    result_types_agree ts r ->
    e_typing s C (result_to_stack r) (Tf [::] ts).
Proof.
  move => r ts s C HResType.
  destruct r => //=; last by apply ety_trap.
  generalize dependent ts.
  induction l => //=; move => ts HResType; simpl in HResType.
  - destruct ts => //=.
    apply ety_a' => //=.
    by apply bet_empty.
  - destruct ts => //=.
    simpl in HResType.
    remove_bools_options.
    unfold types_agree in H.
    rewrite -cat1s.
    eapply et_composition'; eauto => //=.
    + apply ety_a'; auto_basic.
      by apply bet_const.
    + remove_bools_options. subst.
      rewrite -cat1s.
      replace (typeof a :: ts) with ([::typeof a] ++ ts) => //.
      apply ety_weakening.
      by apply IHl.
Qed.

Lemma t_preservation_vs_type: forall s f es s' f' es' C C' lab ret t1s t2s hs hs',
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s f.(f_inst) C ->
    inst_typing s' f.(f_inst) C' ->
    e_typing s (upd_label (upd_local_return C (tc_local C ++ map typeof f.(f_locs)) ret) lab) es (Tf t1s t2s) ->
    map typeof f.(f_locs) = map typeof f'.(f_locs).
Proof.
  move => s f es s' f' es' C C' lab ret t1s t2s hs hs' HReduce HST1 HST2 HIT1 HIT2 HType.
  generalize dependent t2s. generalize dependent t1s.
  generalize dependent lab.
  induction HReduce => //; move => lab t1s t2s HType.
  - convert_et_to_bet.
    replace [::BI_const v; BI_set_local i] with ([::BI_const v] ++ [::BI_set_local i]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [? [? [? Hbet]]]]]]]; subst.
    invert_be_typing.
    replace (tc_local C) with ([::]: list value_type) in *; last by symmetry; eapply inst_t_context_local_empty; eauto.
    rewrite H1.
    rewrite set_nth_map => //.
    by rewrite set_nth_same_unchanged.
  - assert (exists lab' t1s' t2s', e_typing s (upd_label (upd_label (upd_local_return C (tc_local C ++ map typeof f.(f_locs)) ret) lab) lab') es (Tf t1s' t2s')); first eapply lfilled_es_type_exists; eauto.
    destruct H1 as [lab' [t1s' [t2s' Het]]].
    rewrite upd_label_overwrite in Het.
    by eapply IHHReduce; eauto.
Qed.

Lemma inst_typing_func: forall s i j C a,
  inst_typing s i C ->
  List.nth_error i.(inst_funcs) j = Some a ->
  exists cl, List.nth_error s.(s_funcs) a = Some cl.
Proof.
  move => s i j C a HIT HNth.
    destruct s; destruct i; destruct C; destruct tc_local; destruct tc_label; destruct tc_return; unfold inst_typing, typing.inst_typing in * => //=; remove_bools_options; simpl in * => //=.
    remove_bools_options.
    unfold typing.functions_agree in H3.
    specialize (all2_element H3 HNth) as [? HNth'].
    eapply all2_projection in H3; eauto.
    remove_bools_options; by eauto.
Qed.

Lemma inst_typing_tab: forall s i j C a,
  inst_typing s i C ->
  List.nth_error i.(inst_tab) j = Some a ->
  a < length s.(s_tables).
Proof.
  move => s i j C a HIT HNth.
    destruct s; destruct i; destruct C; destruct tc_local; destruct tc_label; destruct tc_return; unfold inst_typing, typing.inst_typing in * => //=; remove_bools_options; simpl in * => //=.
    remove_bools_options.
    specialize (all2_element H1 HNth) as [? HNth'].
    unfold tabi_agree in H1.
    eapply all2_projection in H1; eauto.
    remove_bools_options; by eauto.
Qed.

Lemma inst_typing_mem: forall s i j C a,
  inst_typing s i C ->
  List.nth_error i.(inst_memory) j = Some a ->
  a < length s.(s_mems).
Proof.
  move => s i j C a HIT HNth.
    destruct s; destruct i; destruct C; destruct tc_local; destruct tc_label; destruct tc_return; unfold inst_typing, typing.inst_typing in * => //=; remove_bools_options; simpl in * => //=.
    remove_bools_options.
    specialize (all2_element H0 HNth) as [? HNth'].
    unfold memi_agree in H0.
    eapply all2_projection in H0; eauto.
    remove_bools_options; by eauto.
Qed.

Lemma inst_typing_glob: forall s i j C a,
  inst_typing s i C ->
  List.nth_error i.(inst_globs) j = Some a ->
  a < length s.(s_globals).
Proof.
  move => s i j C a HIT HNth.
    destruct s; destruct i; destruct C; destruct tc_local; destruct tc_label; destruct tc_return; unfold inst_typing, typing.inst_typing in * => //=; remove_bools_options; simpl in * => //=.
    remove_bools_options.
    specialize (all2_element H2 HNth) as [? HNth'].
    unfold globals_agree in H2.
    eapply all2_projection in H2; eauto.
    remove_bools_options; by eauto.
Qed.

Lemma t_preservation_e: forall s f es s' f' es' C t1s t2s lab ret hs hs',
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s f.(f_inst) C ->
    inst_typing s' f.(f_inst) C ->
    e_typing s (upd_label (upd_local_return C (tc_local C ++ map typeof f.(f_locs)) ret) lab) es (Tf t1s t2s) ->
    e_typing s' (upd_label (upd_local_return C (tc_local C ++ map typeof f'.(f_locs)) ret) lab) es' (Tf t1s t2s).
Proof.
  move => s f es s' f' es' C t1s t2s lab ret hs hs' HReduce HST1 HST2.
  move: C ret lab t1s t2s.
  induction HReduce; move => C ret lab tx ty HIT1 HIT2 HType; subst; try eauto; try by apply ety_trap.
  - (* reduce_simple *)
    by eapply t_simple_preservation; eauto.
  - (* Call *)
    convert_et_to_bet.
    invert_be_typing.
    apply ety_weakening.
    eapply inst_typing_func in HIT1; eauto. destruct HIT1 as [cl HNthFunc].
    eapply ety_invoke; eauto.
    assert ((Tf ts1'_call ts2'_call) = cl_type cl) as HFType; first by eapply tc_func_reference1; eauto.
    rewrite HFType.
    by eapply store_typed_cl_typed; eauto.
  - (* Call_indirect *)
    convert_et_to_bet.
    replace [::BI_const (VAL_int32 c); BI_call_indirect i] with ([::BI_const (VAL_int32 c)] ++ [::BI_call_indirect i]) in HType => //=.
    invert_be_typing.
    simpl in *.
    repeat apply ety_weakening.
    eapply ety_invoke; eauto.
    unfold stypes in H1.
    assert ((Tf ts_callindirect ts1'_callindirect) = cl_type cl) as HFType; first by eapply tc_func_reference2; eauto.
    rewrite HFType.
    by eapply store_typed_cl_typed; eauto.
  - (* Invoke native *)
    invert_e_typing.
    eapply Invoke_func_native_typing in H0; eauto.
    destruct H0 as [ts2 [C2 [H9 [H10 [H11 H12]]]]]. subst.
    apply et_to_bet in H3; last by apply const_list_is_basic; apply v_to_e_const.
    apply Const_list_typing in H3.
    apply concat_cancel_last_n in H3; last by (repeat rewrite length_is_size in H2; rewrite size_map).
    remove_bools_options. subst.
    simpl in *.
    apply ety_weakening. apply et_weakening_empty_1.
    assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
    rewrite HCEmpty. simpl.
    apply ety_local => //.
    eapply mk_s_typing; eauto.
    eapply mk_frame_typing; eauto.
    apply ety_a'; auto_basic => //=.
    assert (HC2Empty: tc_label C2 = [::]); first by eapply inst_t_context_label_empty; eauto.
    rewrite HC2Empty in H12.
    apply bet_block. simpl.
    rewrite HC2Empty.
    rewrite H8.
    rewrite map_cat => //=.
    rewrite n_zeros_typing.
    by destruct C2.
  - (* Invoke host *)
    apply e_composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H5' [H6 [H7 H8]]]]]]].
    subst.
    eapply Invoke_func_host_typing in H8; eauto.
    destruct H8 as [ts [H8 H9]]. subst.
    apply et_to_bet in H7; last by apply const_list_is_basic; apply v_to_e_const.
    apply Const_list_typing in H7.
    apply concat_cancel_last_n in H7; last by (repeat rewrite length_is_size in H2; rewrite size_map).
    remove_bools_options. subst.
    (* We require an axiomatic correctness assumption about the host. *)
    assert (result_types_agree t2s r).
    {
      destruct host_instance. apply host_application_respect in H5 => //.
      unfold types_agree.
      clear.
      induction vcs => //=.
      by apply/andP => //=.
    }
    rewrite catA. apply et_weakening_empty_1.
    by apply result_e_type.
  - (* Get_local *)
    convert_et_to_bet.
    invert_be_typing.
    apply ety_a'; auto_basic => //=.
    assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
    rewrite -> HCEmpty in *.
    simpl in *.
    apply nth_error_map in H1_getlocal as [v' [HNth Hvt]]. subst.
    apply bet_weakening_empty_1.
    rewrite H in HNth. inversion HNth; subst.
    by apply bet_const.
  - (* Set_local *)
    convert_et_to_bet.
    replace [::BI_const v; BI_set_local i] with ([::BI_const v] ++ [::BI_set_local i]) in HType => //=.
    invert_be_typing.
    apply ety_a'; auto_basic => //=.
    assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
    rewrite -> HCEmpty in *. simpl in *.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - (* Get_global *)
    convert_et_to_bet.
    invert_be_typing.
    apply ety_a'; auto_basic => //=.
    assert (tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
    rewrite -> H0 in *; simpl in *.
    assert (typeof v = ts_getglobal); first by eapply global_type_reference; eauto.
    apply bet_weakening_empty_1.
    subst.
    by apply bet_const.
  - (* Set_Global *)
    convert_et_to_bet.
    replace [::BI_const v; BI_set_global i] with ([::BI_const v] ++ [::BI_set_global i]) in HType => //=.
    invert_be_typing.
    apply ety_a'; auto_basic => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - (* Load None *)
    convert_et_to_bet.
    replace [::BI_const (VAL_int32 k); BI_load t None a off] with ([::BI_const (VAL_int32 k)] ++ [::BI_load t None a off]) in HType => //=.
    invert_be_typing.
    eapply t_const_ignores_context => //=.
    instantiate (2 := s).
    apply ety_a'; auto_basic.
    simpl.
    assert (be_typing C [::BI_const (wasm_deserialise bs t)] (Tf [::] [:: typeof (wasm_deserialise bs t)])); first by apply bet_const.
    rewrite catA. apply bet_weakening_empty_1.
    rewrite typeof_deserialise in H2. by apply H2.
  - (* Load Some *)
    convert_et_to_bet.
    replace [::BI_const (VAL_int32 k); BI_load t (Some (tp, sx)) a off] with ([::BI_const (VAL_int32 k)] ++ [::BI_load t (Some (tp, sx)) a off]) in HType => //=.
    invert_be_typing.
    eapply t_const_ignores_context => //=.
    instantiate (2 := s).
    apply ety_a'; auto_basic.
    simpl.
    assert (be_typing C [::BI_const (wasm_deserialise bs t)] (Tf [::] [:: typeof (wasm_deserialise bs t)])); first by apply bet_const.
    rewrite catA. apply bet_weakening_empty_1.
    rewrite typeof_deserialise in H2. by apply H2.
  - (* Store None *)
    + convert_et_to_bet.
      replace [::BI_const (VAL_int32 k); BI_const v; BI_store t None a off] with ([::BI_const (VAL_int32 k); BI_const v] ++ [::BI_store t None a off]) in HType => //=.
      invert_be_typing.
      apply concat_cancel_last_n in H1_store => //.
      remove_bools_options; subst.
      apply ety_a'; auto_basic => //=.
      apply bet_weakening_empty_both.
      by apply bet_empty.
  - (* Store Some *)
    + convert_et_to_bet.
      simpl in HType.
      replace [::BI_const (VAL_int32 k); BI_const v; BI_store t (Some tp) a off] with ([::BI_const (VAL_int32 k); BI_const v] ++ [::BI_store t (Some tp) a off]) in HType => //=.
      invert_be_typing.
      apply concat_cancel_last_n in H1_store => //.
      remove_bools_options; subst.
      apply ety_a'; auto_basic => //.
      apply bet_weakening_empty_both.
      by apply bet_empty.
  - (* Current_memory *)
    convert_et_to_bet.
    invert_be_typing.
    apply ety_a'; auto_basic.
    apply bet_weakening_empty_1.
    by apply bet_const.
  - (* Grow_memory success *)
    convert_et_to_bet.
    replace [::BI_const (VAL_int32 c); BI_grow_memory] with ([::BI_const (VAL_int32 c)] ++ [::BI_grow_memory]) in HType => //.
    invert_be_typing => /=.
    apply ety_a'; auto_basic.
    rewrite catA.
    apply bet_weakening_empty_1.
    by apply bet_const.
  - (* Grow_memory fail *)
    convert_et_to_bet.
    replace [::BI_const (VAL_int32 c); BI_grow_memory] with ([::BI_const (VAL_int32 c)] ++ [::BI_grow_memory]) in HType => //.
    invert_be_typing => /=.
    apply ety_a'; auto_basic.
    rewrite catA.
    apply bet_weakening_empty_1.
    by apply bet_const.
  - (* r_label *)
    remember (lfill lh es) as les.
    remember (lfill lh es') as les'.
    generalize dependent les'.
    generalize dependent les.
    move: lh lab tx ty.
    elim.
    + move => vs es0 lab tx ty ? -> /=Hetype ? ->.
      invert_e_typing.
      eapply et_composition'; eauto.
      * instantiate (1 := ts ++ ts0 ++ t1s0).
        apply ety_weakening.
        eapply t_const_ignores_context; eauto; last by apply v_to_e_const.
      * eapply et_composition'.
        { instantiate (1 := ts ++ ts0 ++ t3s0).
          do 2 apply ety_weakening.
          by apply IHHReduce => //.
        }
        { do 2 apply ety_weakening.
          assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
          rewrite HCEmpty in H5. rewrite HCEmpty.
          replace (map typeof f'.(f_locs)) with (map typeof f.(f_locs)); last by eapply t_preservation_vs_type; eauto.
          eapply store_extension_e_typing; try apply HST1 => //; try by [].
          eapply store_extension_reduce; eauto.
        }
    + move => k0 vs n es1 lh' IH es2 lab tx ty ? -> /=Hetype ? ->.
      rewrite -cat1s in Hetype.
      replace (map typeof f'.(f_locs)) with (map typeof f.(f_locs)) in * => //; last first.
      { 
        invert_e_typing.
        eapply lfilled_es_type_exists in H4 as [lab' [? [? Htype]]]; eauto.
        simpl in *.
        repeat rewrite upd_label_overwrite in Htype.
        by eapply t_preservation_vs_type; eauto.
      }
      assert (store_extension s s') as Hext.
      { invert_e_typing.
        eapply lfilled_es_type_exists in H4 as [lab' [? [? Htype]]]; eauto.
        simpl in *.
        repeat rewrite upd_label_overwrite in Htype.
        by eapply store_extension_reduce; eauto.
      }
      invert_e_typing.
      eapply et_composition'.
      * instantiate (1 := ts ++ ts0 ++ t1s0).
        apply ety_weakening.
        eapply t_const_ignores_context; eauto; last by apply v_to_e_const.
      * rewrite -cat1s.
        do 2 apply ety_weakening.
        eapply et_composition'.
        { instantiate (1 := t1s0 ++ t1s1).
          apply et_weakening_empty_1.
          eapply ety_label; eauto.
          - assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
            rewrite HCEmpty in H2. rewrite HCEmpty.
            simpl in *.
            eapply lfilled_es_type_exists in H4 as [lab' [? [? Htype]]]; eauto.
            repeat rewrite upd_label_overwrite in Htype.
            eapply store_extension_e_typing; try apply HST1 => //; try by [].
          - simpl in *.
            by eapply IH; eauto.
        }
        {
          eapply store_extension_e_typing; try apply HST1 => //; by eauto.
        }
  - (* r_local *)
    apply Local_typing in HType.
    destruct HType as [ts [H1 [H2 H3]]]. subst.
    apply et_weakening_empty_1.
    apply ety_local => //.
    inversion H2. inversion H. subst.
    apply upd_label_unchanged_typing in H1.
    eapply mk_s_typing; eauto.
    + eapply mk_frame_typing => //.
      eapply inst_typing_extension; eauto.
      eapply store_extension_reduce; eauto.
      replace (f_inst f') with (f_inst f); eauto; first by eapply reduce_inst_unchanged; eauto.
    + fold_upd_context.
      eapply IHHReduce; eauto.
      eapply inst_typing_extension; eauto.
      eapply store_extension_reduce; eauto.
Qed.
  
Theorem t_preservation: forall s f es s' f' es' ts hs hs',
    reduce hs s f es hs' s' f' es' ->
    config_typing s f es ts ->
    config_typing s' f' es' ts.
Proof.
  move => s f es s' f' es' ts hs hs' HReduce HType.
  inversion HType. inversion H0. inversion H5. subst.
  assert (store_extension s s' /\ store_typing s').
  { apply upd_label_unchanged_typing in H7.
    by eapply store_extension_reduce; eauto. }
  destruct H1.
  assert (inst_typing s' (f_inst f) C1); first by eapply inst_typing_extension; eauto.
  apply mk_config_typing; eauto.
  eapply mk_s_typing; eauto.
  eapply mk_frame_typing; eauto.
  replace (f_inst f') with (f_inst f); eauto; first by eapply reduce_inst_unchanged; eauto.
  fold_upd_context.
  by eapply t_preservation_e; eauto.
Qed.

End Host.
