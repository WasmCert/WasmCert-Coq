(** Proof of preservation **)
(* (C) Rao Xiaojia, M. Bodin - see LICENSE.txt *)

From Wasm Require Export common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program.Equality NArith Omega.
From Wasm Require Export operations typing type_checker datatypes_properties typing opsem properties.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Variable host_function : eqType.

Let store_record := store_record host_function.
Let function_closure := function_closure host_function.
Let administrative_instruction := administrative_instruction host_function.

Let to_e_list : seq basic_instruction -> seq administrative_instruction := @to_e_list _.
Let to_b_list : seq administrative_instruction -> seq basic_instruction := @to_b_list _.
Let e_typing : store_record -> t_context -> seq administrative_instruction -> function_type -> Prop :=
  @e_typing _.
Let inst_typing : store_record -> instance -> t_context -> bool := @inst_typing _.
Let reduce_simple : seq administrative_instruction -> seq administrative_instruction -> Prop :=
  @reduce_simple _.
Let const_list : seq administrative_instruction -> bool := @const_list _.
Let lholed := lholed host_function.
Let lfilled : depth -> lholed -> seq administrative_instruction -> seq administrative_instruction -> bool :=
  @lfilled _.
Let es_is_basic : seq administrative_instruction -> Prop := @es_is_basic _.

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
Let store_extension: store_record -> store_record -> Prop := @store_extension _.

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

Lemma upd_label_overwrite: forall C l1 l2,
    upd_label (upd_label C l1) l2 = upd_label C l2.
Proof.
  by [].
Qed.

(*
  These proofs are largely similar.
  A sensible thing to do is to make tactics for all of them.
  However, some of the proofs depend on the previous ones...
*)

Lemma EConst_typing: forall C econst t1s t2s,
    be_typing C [::EConst econst] (Tf t1s t2s) ->
    t2s = t1s ++ [::typeof econst].
Proof.
  move => C econst t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.

Lemma EConst2_typing: forall C econst1 econst2 t1s t2s,
    be_typing C [::EConst econst1; EConst econst2] (Tf t1s t2s) ->
    t2s = t1s ++ [::typeof econst1; typeof econst2].
Proof.
  move => C econst1 econst2 t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list2 in H1; inversion H1; subst.
    apply EConst_typing in HType1; subst.
    apply EConst_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.

Lemma EConst3_typing: forall C econst1 econst2 econst3 t1s t2s,
    be_typing C [::EConst econst1; EConst econst2; EConst econst3] (Tf t1s t2s) ->
    t2s = t1s ++ [::typeof econst1; typeof econst2; typeof econst3].
Proof.
  move => C econst1 econst2 econst3 t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list3 in H1; inversion H1; subst.
    apply EConst2_typing in HType1; subst.
    apply EConst_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.

Lemma Const_list_typing_empty: forall C vs,
    be_typing C (to_b_list (v_to_e_list vs)) (Tf [::] (vs_to_vts vs)).
Proof.
  move => C vs.
  remember (rev vs) as vs'.
  assert (vs = rev vs'). rewrite Heqvs'. symmetry. by apply revK.
  rewrite H.

  generalize dependent vs.

  induction vs' => //=; move => vs HRev1 HRev2.
  - by apply bet_empty.
  - rewrite rev_cons. rewrite -cats1.
    rewrite -v_to_e_cat /to_b_list.
    rewrite to_b_list_concat.
    eapply bet_composition.
    + eapply IHvs' => //.
      symmetry. by apply revK.
    + simpl.
      rewrite vs_to_vts_cat.
      apply bet_weakening_empty_1.
      by apply bet_const.
Qed.

Lemma Unop_typing: forall C t op t1s t2s,
    be_typing C [::Unop t op] (Tf t1s t2s) ->
    t1s = t2s /\ exists ts, t1s = ts ++ [::t].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - split => //=. by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    split => //=.
    destruct H0 as [ts' H0].
    exists (ts ++ ts').
    rewrite - catA.
    by rewrite H0.
Qed.

Lemma Binop_typing: forall C t op t1s t2s,
    be_typing C [::Binop t op] (Tf t1s t2s) ->
    t1s = t2s ++ [::t] /\ exists ts, t2s = ts ++ [::t].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - split => //=. by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    split => //=.
    + destruct H0 as [ts' H0].
      by rewrite - catA.
    + destruct H0 as [ts' H0].
      exists (ts ++ ts').
      subst.
      by rewrite - catA.
Qed.

Lemma Testop_typing: forall C t op t1s t2s,
    be_typing C [::Testop t op] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::t] /\ t2s = ts ++ [::T_i32].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

Lemma Relop_typing: forall C t op t1s t2s,
    be_typing C [::Relop t op] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::t; t] /\ t2s = ts ++ [::T_i32].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

Lemma Cvtop_typing: forall C t1 t2 op sx t1s t2s,
    be_typing C [::Cvtop t2 op t1 sx] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::t1] /\ t2s = ts ++ [::t2].
Proof.
  move => C t1 t2 op sx t1s t2s HType.
  gen_ind_subst HType.
  - by exists [::].
  - by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

Lemma Nop_typing: forall C t1s t2s,
    be_typing C [::Nop] (Tf t1s t2s) ->
    t1s = t2s.
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list1 in Econs; destruct Econs; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - f_equal. by eapply IHHType.
Qed.

Lemma Drop_typing: forall C t1s t2s,
    be_typing C [::Drop] (Tf t1s t2s) ->
    exists t, t1s = t2s ++ [::t].
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //=.
  - by eauto.
  - apply extract_list1 in Econs; destruct Econs; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    exists x. repeat rewrite -catA. by f_equal.
Qed.

Lemma Select_typing: forall C t1s t2s,
    be_typing C [::Select] (Tf t1s t2s) ->
    exists ts t, t1s = ts ++ [::t; t; T_i32] /\ t2s = ts ++ [::t].
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //.
  - by exists [::], t.
  - apply extract_list1 in Econs; destruct Econs; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    edestruct H as [x2 [H3 H4]]; subst.
    exists (ts ++ x), x2. by split; repeat rewrite -catA.
Qed.

Lemma If_typing: forall C t1s t2s e1s e2s ts ts',
    be_typing C [::If (Tf t1s t2s) e1s e2s] (Tf ts ts') ->
    exists ts0, ts = ts0 ++ t1s ++ [::T_i32] /\ ts' = ts0 ++ t2s /\
                be_typing (upd_label C ([:: t2s] ++ tc_label C)) e1s (Tf t1s t2s) /\
                be_typing (upd_label C ([:: t2s] ++ tc_label C)) e2s (Tf t1s t2s).
Proof.
  move => C t1s t2s e1s e2s ts ts' HType.
  gen_ind_subst HType.
  - by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1. subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    destruct H as [H1 [H2 [H3 H4]]]. subst.
    exists (ts ++ x).
    repeat rewrite -catA.
    repeat split => //=.
Qed.

Lemma Br_if_typing: forall C ts1 ts2 i,
    be_typing C [::Br_if i] (Tf ts1 ts2) ->
    exists ts ts', ts2 = ts ++ ts' /\ ts1 = ts2 ++ [::T_i32] /\ i < length (tc_label C) /\ plop2 C i ts'.
Proof.
  move => C ts1 ts2 i HType.
  gen_ind_subst HType.
  - unfold plop2 in H0.
    by exists [::], ts2.
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - rewrite -catA. f_equal => //=.
    edestruct IHHType => //=.
    destruct H as [ts' [H1 [H2 [H3 H4]]]].
    exists (ts ++ x), ts'. subst.
    split.
    + repeat rewrite -catA. by f_equal.
    + split => //=.
Qed.

Lemma Br_table_typing: forall C ts1 ts2 ids i0,
    be_typing C [::Br_table ids i0] (Tf ts1 ts2) ->
    exists ts1' ts, ts1 = ts1' ++ ts ++ [::T_i32] /\
                         all (fun i => (i < length (tc_label C)) && (plop2 C i ts)) (ids ++ [::i0]).
Proof.
  move => C ts1 ts2 ids i0 HType.
  gen_ind_subst HType.
  - by exists t1s, ts.
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [ts' [H1 H2]].
    exists (ts ++ x), ts'. subst.
    split => //=.
    + repeat rewrite -catA. by f_equal => //=.
Qed.

Lemma Tee_local_typing: forall C i ts1 ts2,
    be_typing C [::Tee_local i] (Tf ts1 ts2) ->
    exists ts t, ts1 = ts2 /\ ts1 = ts ++ [::t] /\ i < length (tc_local C) /\
                 List.nth_error (tc_local C) i = Some t.
Proof.
  move => C i ts1 ts2 HType.
  gen_ind_subst HType.
  - by exists [::], t.
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [t [H1 [H2 [H3 H4]]]]. subst.
    exists (ts ++ x), t. subst.
    repeat (try split => //=).
    by rewrite -catA.
Qed.

Lemma Const_list_typing: forall C vs t1s t2s,
    be_typing C (to_b_list (v_to_e_list vs)) (Tf t1s t2s) ->
    t2s = t1s ++ (map typeof vs).
Proof.
  move => C vs.
  remember (rev vs) as vs'.
  generalize dependent vs.
  induction vs'.
  - move => vs H t1s t2s HType. destruct vs => //=.
    + simpl in HType.
      apply empty_typing in HType. subst. by rewrite cats0.
    + rewrite rev_cons in H. rewrite -cats1 in H.
      by destruct (rev vs) => //=.
  - move => vs H t1s t2s HType.
    assert (vs = rev (a::vs')).
    { rewrite H. symmetry. by apply revK. }
    rewrite rev_cons in H0. rewrite -cats1 in H0.
    rewrite H0 in HType.
    rewrite -v_to_e_cat in HType.
    rewrite /to_b_list to_b_list_concat in HType.
    apply composition_typing in HType.
    destruct HType as [ts [ts1' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]].
    apply IHvs' in H3; last by (symmetry; apply revK). subst.
    simpl in H4.
    apply EConst_typing in H4. subst.
    repeat rewrite -catA. repeat f_equal.
    by rewrite map_cat.
Qed.
(*
  Unlike the above proofs which have a linear dependent structure therefore hard
    to factorize into a tactic, the following proofs are independent of each other
    and should therefore be easily refactorable.
*)

Ltac invert_be_typing:=
  repeat lazymatch goal with
  | H: (?es ++ [::?e])%list = [::_] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _; _] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _; _; _] |- _ =>
    extract_listn
  | H: be_typing _ [::] _ |- _ =>
    apply empty_typing in H; subst
  | H: be_typing _ [:: EConst _] _ |- _ =>
    apply EConst_typing in H; subst
  | H: be_typing _ [:: EConst _; EConst _] _ |- _ =>
    apply EConst2_typing in H; subst
  | H: be_typing _ [:: EConst _; EConst _; EConst _] _ |- _ =>
    apply EConst3_typing in H; subst
  | H: be_typing _ [::Unop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Unop_typing in H; destruct H as [H1 [ts H2]]; subst
  | H: be_typing _ [::Binop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Binop_typing in H; destruct H as [H1 [ts H2]]; subst
  | H: be_typing _ [::Testop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Testop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::Relop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Relop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::Cvtop _ _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Cvtop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::Drop] _ |- _ =>
    apply Drop_typing in H; destruct H; subst
  | H: be_typing _ [::Select] _ |- _ =>
    let ts := fresh "ts" in
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Select_typing in H; destruct H as [ts [t [H1 H2]]]; subst
  | H: be_typing _ [::If _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply If_typing in H; destruct H as [ts [H1 [H2 [H3 H4]]]]; subst
  | H: be_typing _ [::Br_if _] _ |- _ =>
    let ts := fresh "ts" in
    let ts' := fresh "ts'" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Br_if_typing in H; destruct H as [ts [ts' [H1 [H2 [H3 H4]]]]]; subst
  | H: be_typing _ [::Br_table _ _] _ |- _ =>
    let ts := fresh "ts" in
    let ts' := fresh "ts'" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Br_table_typing in H; destruct H as [ts [ts' [H1 H2]]]; subst
  | H: be_typing _ [::Tee_local _] _ |- _ =>
    let ts := fresh "ts" in
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Tee_local_typing in H; destruct H as [ts [t [H1 [H2 [H3 H4]]]]]; subst
  | H: be_typing _ (_ ++ _) _ |- _ =>
    let ts1 := fresh "ts1" in
    let ts2 := fresh "ts2" in
    let ts3 := fresh "ts3" in
    let ts4 := fresh "ts4" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply composition_typing in H; destruct H as [ts1 [ts2 [ts3 [ts4 [H1 [H2 [H3 H4]]]]]]]
  | H: be_typing _ [::_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: be_typing _ [::_;_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: be_typing _ [::_;_;_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: _ ++ [::_] = _ ++ [::_] |- _ =>
    apply concat_cancel_last in H; destruct H; subst
  end.

Lemma app_binop_type_preserve: forall op v1 v2 v,
    app_binop op v1 v2 = Some v ->
    typeof v = typeof v1.
Proof.
  move => op v1 v2 v.
  by elim: op; elim: v1; elim: v2 => //=; move => c1 c2 op H; destruct op; remove_bools_options.
Qed.

Lemma t_Unop_preserve: forall C v t op be tf,
    be_typing C [:: EConst v; Unop t op] tf ->
    reduce_simple (to_e_list [::EConst v; Unop t op]) (to_e_list [::be]) ->
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
    be_typing C [:: EConst v1; EConst v2; Binop t op] tf ->
    reduce_simple (to_e_list [::EConst v1; EConst v2; Binop t op]) (to_e_list [::be]) ->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 t op be tf HType HReduce.
  destruct tf as [ts1 ts2].
  inversion HReduce; b_to_a_revert; subst.
  invert_be_typing.
  rewrite catA in H1. apply concat_cancel_last in H1. destruct H1; subst.
  repeat rewrite catA.
  apply bet_weakening_empty_1.
  apply app_binop_type_preserve in H0.
  rewrite -H1. rewrite -H0.
  by apply bet_const.
Qed.

(* It seems very hard to refactor the i32 and i64 cases into one because of
     the polymorphism of app_testop_i. *)
Lemma t_Testop_i32_preserve: forall C c testop tf,
    be_typing C [::EConst (ConstInt32 c); Testop T_i32 testop] tf ->
    be_typing C [::EConst (ConstInt32 (wasm_bool (app_testop_i testop c)))] tf.
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
    be_typing C [::EConst (ConstInt64 c); Testop T_i64 testop] tf ->
    be_typing C [::EConst (ConstInt32 (wasm_bool (app_testop_i testop c)))] tf.
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
    be_typing C [::EConst v1; EConst v2; Relop t op] tf ->
    reduce_simple [:: Basic (EConst v1); Basic (EConst v2); Basic (Relop t op)] [::Basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 t be op tf HType HReduce.
  destruct tf as [ts1 ts2].
  inversion HReduce; subst.
  invert_be_typing.
  replace ([::t;t]) with ([::t] ++ [::t]) in H2 => //.
  rewrite catA in H2.
  apply concat_cancel_last in H2. destruct H2 as [H3 H4]. subst.
  rewrite catA in H1.
  apply concat_cancel_last in H1. destruct H1 as [H5 H6]. subst.
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
    be_typing C [:: EConst (wasm_deserialise (bits v) t)] (Tf [::] [:: t]).
Proof.
  move => C v t.
  assert (be_typing C [:: EConst (wasm_deserialise (bits v) t)] (Tf [::] [:: typeof (wasm_deserialise (bits v) t)])); first by apply bet_const.
  by rewrite typeof_deserialise in H.
Qed.

Lemma t_Convert_preserve: forall C v t1 t2 sx be tf,
    be_typing C [::EConst v; Cvtop t2 Convert t1 sx] tf ->
    reduce_simple [::Basic (EConst v); Basic (Cvtop t2 Convert t1 sx)] [::Basic be] ->
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
    be_typing C [::EConst v; Cvtop t2 Reinterpret t1 None] tf ->
    reduce_simple [::Basic (EConst v); Basic (Cvtop t2 Reinterpret t1 None)] [::Basic be] ->
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
    be_typing C [::EConst v; Drop] tf ->
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
    be_typing C [::EConst v1; EConst v2; EConst (ConstInt32 n); Select] tf ->
    reduce_simple [::Basic (EConst v1); Basic (EConst v2); Basic (EConst (ConstInt32 n)); Basic Select] [::Basic be]->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 n tf be HType HReduce.
  inversion HReduce; subst.
  - (* n = 0 : Select second *)
    gen_ind_subst HType => //=.
    + (* Composition *)
      invert_be_typing.
      apply concat_cancel_last_n in H1 => //.
      remove_bools_options.
      inversion H2. subst.
      apply bet_weakening_empty_1.
      by apply bet_const.
    + apply bet_weakening. by eapply IHHType => //=.
  - (* n = 1 : Select first *)
    gen_ind_subst HType => //=.
    + (* Composition *)
      invert_be_typing.
      apply concat_cancel_last_n in H2 => //.
      remove_bools_options.
      inversion H3. subst.
      apply bet_weakening_empty_1.
      rewrite H6.
      by apply bet_const.
    + apply bet_weakening. by eapply IHHType => //=.
Qed.

Lemma t_If_be_preserve: forall C c tf0 es1 es2 tf be,
  be_typing C ([::EConst (ConstInt32 c); If tf0 es1 es2]) tf ->
  reduce_simple (to_e_list [::EConst (ConstInt32 c); If tf0 es1 es2]) [::Basic be] ->
  be_typing C [::be] tf.
Proof.
  move => C c tf0 es1 es2 tf be HType HReduce. destruct tf. destruct tf0.
  inversion HReduce; subst.
  - (* if_0 *)
    gen_ind_subst HType => //=.
    + (* Composition *)
      invert_be_typing.
      rewrite catA in H1. apply concat_cancel_last in H1. destruct H1. subst.
      apply bet_weakening.
      by apply bet_block.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
  - (* if_n0 *)
    gen_ind_subst HType => //=.
    + (* Composition *)
      invert_be_typing.
      rewrite catA in H2. apply concat_cancel_last in H2. destruct H2. subst.
      apply bet_weakening.
      by apply bet_block.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
Qed.

Lemma t_Br_if_true_preserve: forall C c i tf be,
    be_typing C ([::EConst (ConstInt32 c); Br_if i]) tf ->
    reduce_simple (to_e_list [::EConst (ConstInt32 c); Br_if i]) [::Basic be] ->
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
    be_typing C ([::EConst (ConstInt32 c); Br_if i]) tf ->
    reduce_simple (to_e_list [::EConst (ConstInt32 c); Br_if i]) [::] ->
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
    be_typing C ([::EConst (ConstInt32 c); Br_table ids i0]) tf ->
    reduce_simple (to_e_list [::EConst (ConstInt32 c); Br_table ids i0]) [::Basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C c ids i0 tf be HType HReduce.
  inversion HReduce; subst.
  (* in range *)
  - dependent induction HType => //=.
    + (* Composition *)
      invert_be_typing.
      rewrite catA in H0. apply concat_cancel_last in H0. destruct H0. subst.
      move/allP in H2.
      assert (HInd: (j < length (tc_label C)) && plop2 C j ts').
      -- apply H2. rewrite mem_cat. apply/orP. left. apply/inP.
         eapply List.nth_error_In. by eauto.
      remove_bools_options.
      by apply bet_br => //.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
  (* out of range *)
  - dependent induction HType => //=.
    + (* Composition *)
      invert_be_typing.
      rewrite catA in H1. apply concat_cancel_last in H1. destruct H1. subst.
      move/allP in H2.
      assert (HInd: (i0 < length (tc_label C)) && plop2 C i0 ts').
      -- apply H2. rewrite mem_cat. apply/orP. right. by rewrite mem_seq1.
      remove_bools_options.
      by apply bet_br => //.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
Qed.

Lemma t_Tee_local_preserve: forall C v i tf,
    be_typing C ([::EConst v; Tee_local i]) tf ->
    be_typing C [::EConst v; EConst v; Set_local i] tf.
Proof.
  move => C v i tf HType.
  dependent induction HType => //.
  - (* Composition *)
    invert_be_typing.
    replace ([::EConst v; EConst v; Set_local i]) with ([::EConst v] ++ [::EConst v] ++ [::Set_local i]) => //.
    repeat (try rewrite catA; eapply bet_composition) => //.
    + instantiate (1 := (ts ++ [::typeof v])).
      apply bet_weakening_empty_1. by apply bet_const.
    + instantiate (1 := (ts ++ [::typeof v] ++ [::typeof v])).
      apply bet_weakening. apply bet_weakening_empty_1. by apply bet_const.
    + apply bet_weakening. apply bet_weakening_empty_2. by apply bet_set_local.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType => //=.
Qed.
 (*
Ltac invert_non_be:=
  repeat lazymatch goal with
  | H: exists e, _ = Basic e |- _ =>
    try by destruct H
  end.
*)
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
  move => bes bes' es es' C tf HType HReduce HBasic1 HBasic2 HBES1 HBES2.
  destruct tf.
  inversion HReduce; b_to_a_revert; subst; simpl in HType => //; basic_inversion.
(* The proof itself should be refactorable further into tactics as well. *)
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

Ltac auto_basic :=
  repeat lazymatch goal with
  | |- es_is_basic [::Basic _; Basic _; Basic _; Basic _] =>
    simpl; repeat split
  | |- es_is_basic [::Basic _; Basic _; Basic _] =>
    simpl; repeat split
  | |- es_is_basic [::Basic _; Basic _] =>
    simpl; repeat split
  | |- es_is_basic [::Basic _] =>
    simpl; repeat split
  | |- operations.es_is_basic [::Basic _; Basic _; Basic _; Basic _] =>
    simpl; repeat split
  | |- operations.es_is_basic [::Basic _; Basic _; Basic _] =>
    simpl; repeat split
  | |- operations.es_is_basic [::Basic _; Basic _] =>
    simpl; repeat split
  | |- operations.es_is_basic [::Basic _] =>
    simpl; repeat split
  | |- operations.e_is_basic (Basic ?e) =>
    by unfold e_is_basic; exists e
end.

(* We need this version for dealing with the version of predicate with host. *)
Ltac basic_inversion' :=
   repeat lazymatch goal with
         | H: True |- _ =>
           clear H
         | H: es_is_basic (_ ++ _) |- _ =>
           let Ha := fresh H in
           let Hb := fresh H in
           apply basic_concat in H; destruct H as [Ha Hb]
         | H: es_is_basic [::] |- _ =>
           clear H
         | H: es_is_basic [::_] |- _ =>
           let H1 := fresh H in
           let H2 := fresh H in
           try by (unfold es_is_basic in H; destruct H as [H1 H2]; inversion H1)
         | H: e_is_basic _ |- _ =>
           inversion H; try by []
         end.

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
      simpl in H4. apply EConst_typing in H4. subst.
      apply bet_weakening_empty_1.
      by apply bet_const.
Qed.


Lemma Block_typing: forall C t1s t2s es tn tm,
    be_typing C [::Block (Tf t1s t2s) es] (Tf tn tm) ->
    exists ts, tn = ts ++ t1s /\ tm = ts ++ t2s /\
               be_typing (upd_label C ([::t2s] ++ (tc_label C))) es (Tf t1s t2s).
Proof.
  move => C t1s t2s es tn tm HType.
  dependent induction HType => //=.
  - by exists [::].
  - invert_be_typing.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists (ts ++ x).
    repeat rewrite -catA.
    by repeat split => //=.
Qed.

Lemma Loop_typing: forall C t1s t2s es tn tm,
    be_typing C [::Loop (Tf t1s t2s) es] (Tf tn tm) ->
    exists ts, tn = ts ++ t1s /\ tm = ts ++ t2s /\
               be_typing (upd_label C ([::t1s] ++ (tc_label C))) es (Tf t1s t2s).
Proof.
  move => C t1s t2s es tn tm HType.
  dependent induction HType => //=.
  - by exists [::].
  - invert_be_typing.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists (ts ++ x).
    repeat rewrite -catA.
    by repeat split => //=.
Qed.

Lemma Break_typing: forall n C t1s t2s,
    be_typing C [::Br n] (Tf t1s t2s) ->
    exists ts ts0, n < size (tc_label C) /\
               plop2 C n ts /\
               t1s = ts0 ++ ts.
Proof.
  move => n C t1s t2s HType.
  dependent induction HType => //=.
  - by exists ts, t1s0.
  - invert_be_typing.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [ts0 [H1 [H2 H3]]]. subst.
    exists x, (ts ++ ts0).
    repeat split => //=.
    by rewrite -catA.
Qed.

Ltac et_dependent_ind H :=
  let Ht := type of H in
  lazymatch Ht with
  | e_typing ?s ?C ?es (Tf ?t1s ?t2s) =>
    let s2 := fresh "s2" in
    let C2 := fresh "C2" in
    let es2 := fresh "es2" in
    let tf2 := fresh "tf2" in
    remember s as s2 eqn:Hrems;
    remember C as C2 eqn:HremC;
    remember es as es2 eqn:Hremes;
    remember (Tf t1s t2s) as tf2 eqn:Hremtf;
    generalize dependent Hrems;
    generalize dependent HremC;
    generalize dependent Hremtf;
    generalize dependent s; generalize dependent C;
    generalize dependent t1s; generalize dependent t2s;
    induction H
  | e_typing ?s ?C ?es ?tf =>
    let s2 := fresh "s2" in
    let C2 := fresh "C2" in
    let es2 := fresh "es2" in
    remember s as s2 eqn:Hrems;
    remember C as C2 eqn:HremC;
    remember es as es2 eqn:Hremes;
    generalize dependent Hrems;
    generalize dependent HremC;
    generalize dependent s; generalize dependent C;
    induction H
  | _ => fail "hypothesis not an e_typing relation"
  end; intros; subst.

Lemma Label_typing: forall s C n es0 es ts1 ts2,
    e_typing s C [::Label n es0 es] (Tf ts1 ts2) ->
    exists ts ts2', ts2 = ts1 ++ ts2' /\
                    e_typing s C es0 (Tf ts ts2') /\
                    e_typing s (upd_label C ([::ts] ++ (tc_label C))) es (Tf [::] ts2') /\
                    length ts = n.
Proof.
  move => s C n es0 es ts1 ts2 HType.
(*  (* Without the powerful generalize_dependent tactic, we need to manually remember
     the dependent terms. However, it's very easy to mess up the induction hypothesis
     if variables are not correctly generalized.
     Reading source: https://stackoverflow.com/questions/58349365/coq-how-to-correctly-remember-dependent-values-without-messing-up-the-inductio 
     ( the missing letter n at the end of link is not a typo )
   *)
  remember ([::Label n es0 es]) as les.
  remember (Tf ts1 ts2) as tf.
  generalize dependent Heqtf. generalize dependent ts1. generalize dependent ts2.*)
  et_dependent_ind HType => //.
(*  induction HType => //. *)
  - (* ety_a *)
    assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
    rewrite Hremes in H0. by basic_inversion'.
  - (* ety_composition *)
    apply extract_list1 in Hremes. destruct Hremes. subst.
    apply et_to_bet in HType1 => //.
    simpl in HType1. apply empty_typing in HType1. subst.
    by eapply IHHType2 => //.
  - (* ety_weakening *)
    edestruct IHHType => //.
    inversion Hremtf; subst.
    destruct H as [ts2' [H1 [H2 [H3 H4]]]]. subst.
    by exists x, ts2'; try rewrite catA.     
  - (* ety_label *)
    inversion Hremes. inversion Hremtf. subst.
    by exists ts, ts2.
Qed.

(*
  Looking at what we want to prove in the Lfilled_break case, it might be tempting to
    prove the following:

Lemma Lfilled_break_typing: forall n lh vs LI ts s C t2s,
    e_typing s (upd_label C ([::ts] ++ tc_label C)) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfilled n lh (vs ++ [::Basic (Br n)]) LI ->
    e_typing s C vs (Tf [::] ts).

  The lemma itself is definitely correct, and an apparent approach is to do induction
    on n (or induction on the lfilled hypothesis).

  However, this will *NOT* work: the culprit is that there is no inductive relationship
    that changes the instruction (Br n+1) into (Br n), and we will get a useless
    induction hypothesis that can never be applied.

  We need to somehow avoid getting the parameter of Br into induction. By the lfilled
    hypothesis, we know LI is a nested Label which, at the innermost level, has (Br n)
    as its first non-constant instruction, and vs at the top of the value stack.

  Recall that (Br n) looks at the nth entry in the label of the typing context and
    needs to consume that type. Since we can only induct on the depth of lfilled
    (but not the n in the instruction), they have to be two separate numbers, say
    n and m. Now if n is 0, the instruction will basically look at the mth entry;
    what if n is not 0? In that case if we trace the expansion of LI and simulate
    how the typing is evaluated, we realize that there will be n entries prepended
    to the label of the typing context, after which we'll then find the mth element
    of it due to the (Br m).

  So a more sensible lemma to prove is the following, which the original lemma we
    wanted is a special case of:
*)

Lemma Lfilled_break_typing: forall n m k lh vs LI ts s C t2s tss,
    e_typing s (upd_label C (tss ++ [::ts] ++ tc_label C)) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfilled n lh (vs ++ [::Basic (Br m)]) LI ->
    length tss = k ->
    n + k = m ->
    e_typing s C vs (Tf [::] ts).
Proof.
  move => n m k lh vs LI ts s C ts2 tss HType HConst HLength HLF HTSSLength HSum.
  apply const_es_exists in HConst. destruct HConst. subst.
  move/lfilledP in HLF.
  generalize dependent ts.
  generalize dependent ts2.
  generalize dependent LI.
  generalize dependent tss.
  generalize dependent lh.
  induction n.
  - move => lh tss LI HLF ts2 ts HType HTSSLength.
    rewrite add0n in HLF.
    repeat rewrite catA in HType.
    inversion HLF.
    apply const_es_exists in H. destruct H. subst.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    subst. clear H1.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H5 [H6 [H7 H8]]]]]]].
    subst.
    apply e_composition_typing in H7.
    destruct H7 as [ts0'' [t1s'' [t2s'' [t3s'' [H9 [H10 [H11 H12]]]]]]].
    subst.
    apply et_to_bet in H12; try auto_basic.
    apply Break_typing in H12.
    destruct H12 as [ts0 [ts1 [H13 [H14 H15]]]]. clear H13.
    unfold plop2 in H14. simpl in H14. move/eqP in H14. inversion H14. subst.
    clear H14.
    apply et_to_bet in H11; last by (apply const_list_is_basic; apply v_to_e_is_const_list).
    apply Const_list_typing in H11.
    repeat rewrite length_is_size in HTSSLength.
    rewrite -catA in H0. rewrite list_nth_prefix in H0. inversion H0. subst. clear H0.
    assert ((ts1 == t1s'') && (ts0 == vs_to_vts x)).
    + apply concat_cancel_last_n => //=. rewrite size_map.
      by rewrite v_to_e_size in HTSSLength.
    + move/andP in H. destruct H.
      move/eqP in H0. subst.
      apply ety_a'; first by apply const_list_is_basic; apply v_to_e_is_const_list.
      by apply Const_list_typing_empty.
  - move => lh tss LI HLF ts2 ts HType HTSSLength.
    inversion HLF. subst.
    repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H2 [H3 [H4 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    clear H2. clear H3.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H6 [H7 [H8 H9]]]]]]].
    destruct ts0' => //=.
    destruct t1s' => //=.
    clear H6. clear H7.
    apply Label_typing in H9.
    destruct H9 as [ts0'' [t2s'' [H10 [H11 [H12 H13]]]]]. subst.
    simpl in H12.
    rewrite upd_label_overwrite in H12.
    rewrite -cat1s in H12. repeat rewrite catA in H12.
    remember ([::ts0''] ++ tss) as tss'. rewrite -catA in H12.
    replace (n.+1+length tss) with (n + length tss') in H1.
    eapply IHn => //=.
    + by apply H1.
    + by apply H12.
    (* replace *)
    assert (length tss' = length tss + 1).
    { rewrite Heqtss'. rewrite cat1s. simpl. by rewrite addn1. }
    by lias.
Qed.

(*
  And yes, the above observation was obviously the result of some futile attempt
    to prove the unprovable version of the lemma.

Lemma Lfilled_break_typing: forall n lh vs LI ts s C t2s,
    e_typing s (upd_label C ([::ts] ++ tc_label C)) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfilled n lh (vs ++ [::Basic (Br n)]) LI ->
    e_typing s C vs (Tf [::] ts).
Proof.
  move => n lh vs LI ts s C ts2 HType HConst HLength HLF.
  apply const_es_exists in HConst. destruct HConst. subst.
  move/lfilledP in HLF.
  generalize dependent ts2.
  generalize dependent LI.
  induction n.
  - move => LI HLF ts2 HType.
    repeat rewrite catA in HType.
    inversion HLF.
    apply const_es_exists in H. destruct H. subst.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    subst. clear H1.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H5 [H6 [H7 H8]]]]]]].
    subst.
    apply e_composition_typing in H7.
    destruct H7 as [ts0'' [t1s'' [t2s'' [t3s'' [H9 [H10 [H11 H12]]]]]]].
    subst.
    apply et_to_bet in H12; last by auto_basic.
    apply Break_typing in H12.
    destruct H12 as [ts0 [ts1 [H13 [H14 H15]]]]. clear H13.
    unfold plop2 in H14. simpl in H14. move/eqP in H14. inversion H14. subst.
    clear H14.
    apply et_to_bet in H11; last by (apply const_list_is_basic; apply v_to_e_is_const_list).
    apply Const_list_typing in H11.
    repeat rewrite length_is_size in HLength.
    assert ((ts1 == t1s'') && (ts0 == vs_to_vts x)).
    + apply concat_cancel_last_n => //=. rewrite size_map.
      by rewrite v_to_e_size in HLength.
    + move/andP in H. destruct H.
      move/eqP in H0. subst.
      apply ety_a'; first by apply const_list_is_basic; apply v_to_e_is_const_list.
      by apply Const_list_typing_empty.
  - move => LI HLF ts2 HType.
    inversion HLF. subst.
    repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H2 [H3 [H4 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    clear H2. clear H3.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H6 [H7 [H8 H9]]]]]]].
    destruct ts0' => //=.
    destruct t1s' => //=.
    clear H6. clear H7.
    apply Label_typing in H9.
    destruct H9 as [ts0'' [t2s'' [H10 [H11 [H12 H13]]]]]. subst.
    simpl in H12.

 *)

Lemma Local_typing: forall s C n f es t1s t2s,
    e_typing s C [::Local n f es] (Tf t1s t2s) ->
    exists ts, t2s = t1s ++ ts /\
               s_typing s (Some ts) f es ts /\
               length ts = n.
Proof.
  move => s C n f es t1s t2s HType.
  remember ([::Local n f es]) as les.
  remember (Tf t1s t2s) as tf.
  generalize dependent Heqtf. generalize dependent t1s. generalize dependent t2s.
  induction HType; subst => //.
  - (* ety_a *)
    assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
    rewrite Heqles in H0. by basic_inversion'.
  - (* ety_composition *)
    apply extract_list1 in Heqles. destruct Heqles. subst.
    apply et_to_bet in HType1 => //.
    simpl in HType1. apply empty_typing in HType1. subst.
    by eapply IHHType2 => //.
  - (* ety_weakening *)
    move => ts2 ts1 HTf.
    inversion HTf. subst.
    edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst. 
    exists x.
    repeat split => //=.
    by rewrite catA.
  - (* ety_local *)
    inversion Heqles. subst.
    move => t2s t1s HTf. inversion HTf. subst.
    by exists t2s.
Qed.

Lemma Return_typing: forall C t1s t2s,
    be_typing C [::Return] (Tf t1s t2s) ->
    exists ts ts', t1s = ts' ++ ts /\
                   tc_return C = Some ts.
Proof.
  move => C t1s t2s HType.
  dependent induction HType => //=.
  - by exists ts, t1s0.
  - invert_be_typing.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [ts' [H1 H2]]. subst.
    exists x, (ts ++ ts').
    split => //=.
    by rewrite -catA.
Qed.

(*
  Similarly, Local does not involve in induction either. So what we want to prove
    is also slightly different from what we desire. However, this one is easier
    to observe.

  The only thing that got me stuck for a while is to observe that label of the
    typing context plays no role in typing for this case; this is required since
    we'll get an extra label update from inverting the Label instruction.
 *)

Lemma Lfilled_return_typing: forall n lh vs LI ts s C lab t2s,
    e_typing s (upd_label C lab) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfilled n lh (vs ++ [::Basic Return]) LI ->
    Some ts = tc_return C ->
    e_typing s C vs (Tf [::] ts).
Proof.
  induction n; move => lh vs LI ts s C lab t2s HType HConst HLength HLF HReturn; move/lfilledP in HLF; inversion HLF; subst => //=.
  - repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H1 [H2 [H3 H4]]]]]]].
    destruct ts0 => //=.
    destruct t1s0 => //=.
    subst. clear H1.
    apply e_composition_typing in H3.
    destruct H3 as [ts1 [t1s1 [t2s1 [t3s1 [H5 [H6 [H7 H8]]]]]]].
    destruct ts1 => //=.
    destruct t1s1 => //=.
    subst. clear H5.
    apply e_composition_typing in H7.
    destruct H7 as [ts2 [t1s2 [t2s2 [t3s2 [H9 [H10 [H11 H12]]]]]]].
    destruct ts2 => //=.
    destruct t1s2 => //=.
    subst. clear H9. simpl in H8. simpl in H4.
    apply et_to_bet in H8; auto_basic. apply Return_typing in H8.
    destruct H8 as [ts1 [ts2 [H13 H14]]]. subst.
    apply et_to_bet in H12; last by apply const_list_is_basic.
    apply const_es_exists in HConst. destruct HConst. subst.
    apply Const_list_typing in H12.
    rewrite -HReturn in H14. inversion H14. subst. clear H14.
    assert ((ts2 == t3s2) && (ts1 == vs_to_vts x)).
    + apply concat_cancel_last_n => //=.
      repeat rewrite length_is_size in HLength.
      rewrite v_to_e_size in HLength.
      by rewrite size_map.
    + move/andP in H0. destruct H0.
      move/eqP in H1. subst.
      apply ety_a'; first by apply const_list_is_basic; apply v_to_e_is_const_list.
      by apply Const_list_typing_empty.
  - repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H2 [H3 [H4 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s0 => //=.
    subst. clear H2.
    apply e_composition_typing in H4.
    destruct H4 as [ts1 [t1s1 [t2s1 [t3s1 [H6 [H7 [H8 H9]]]]]]].
    destruct ts1 => //=.
    destruct t1s1 => //=.
    subst. clear H6.
    apply Label_typing in H9.
    destruct H9 as [ts' [ts2' [H10 [H11 [H12 H13]]]]].
    subst. simpl in H5.
    eapply IHn => //.
    simpl in H12.
    apply H12.
    apply/lfilledP.
    by apply H1.
Qed.

Lemma Local_return_typing: forall s C vs f LI tf n lh,
    e_typing s C [:: Local (length vs) f LI] tf ->
    const_list vs ->
    lfilled n lh (vs ++ [::Basic Return]) LI ->
    e_typing s C vs tf.
Proof.
  move => s C vs f LI tf n lh HType HConst HLF.
  destruct tf as [t1s t2s].
  apply Local_typing in HType.
  destruct HType as [ts [H1 [H2 H3]]]. subst.
  inversion H2. inversion H. subst. clear H4. clear H2. clear H.
  apply et_weakening_empty_1.
  assert (HET: e_typing s (upd_local_return C2 (tc_local C2 ++ map typeof f.(f_locs)) (Some ts)) vs (Tf [::] ts)).
  { eapply Lfilled_return_typing; eauto. }
  apply et_to_bet in HET; last by apply const_list_is_basic.
  apply const_es_exists in HConst. destruct HConst. subst.
  apply Const_list_typing in HET; subst => /=.
  apply ety_a'; first by apply const_list_is_basic; apply v_to_e_is_const_list.
  by apply Const_list_typing_empty.
Qed.

Theorem t_simple_preservation: forall s i es es' C loc lab ret tf,
    inst_typing s i C ->
    e_typing s (upd_label (upd_local_return C loc ret) lab) es tf ->
    reduce_simple es es' ->
    e_typing s (upd_label (upd_local_return C loc ret) lab) es' tf.
Proof.
  move => s i es es' C loc lab ret tf HInstType HType HReduce.
  inversion HReduce; subst; try (by (apply et_to_bet in HType => //; auto_basic; apply ety_a' => //; auto_basic; eapply t_be_simple_preservation; try by eauto; auto_basic)); try by apply ety_trap.
  (* Though only a few cases, these cases are expected to be much more difficult. *)
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
            * apply const_list_is_basic. by apply v_to_e_is_const_list.
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
            * apply const_list_is_basic. by apply v_to_e_is_const_list.
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
 (*   Check HType.
    dependent induction HType.
    Print e_typing.
    gen_ind_pre HType.
    Set Ltac Debug.
    Check Datatypes.cons.
    gen_ind_gen HType.
    gen_ind_subst HType.*)
 (* After several futile attempts to fix gen_ind_gen, I gave up on it and 
      made a more cumbersome et_dependent_ind that only works for e_typing.

    For future reference: the reason gen_ind_gen fails here is because when we get to
      the second last term 
          [::Label n es0 es'] 
      which is effectively
          cons (Label n es0 es') nil
      we first try to generalize the token 'cons', which obviously cannot be 
        generalized (which is fine); but then when we try to look at the term 'Label',
        the tactic somehow wants to generalize on the type of it, i.e.
          'administrative_instruction', 
        which is unfortunately redefined with host to be 
          'administrative_instruction host_function'
        which means we will generalize host_function which is what we tried to avoid.
 *)
    et_dependent_ind HType => //.
    + (* ety_a *)
      assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
      rewrite Hremes in H1. by basic_inversion'.
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
    et_dependent_ind HType => //.
    + (* ety_a *)
      assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
      rewrite Hremes in H2. by basic_inversion'.
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
      eapply et_composition' => //=.
      -- eapply Lfilled_break_typing => //=.
         ++ instantiate (4 := [::]). rewrite cat0s.
            by apply HType2.
         ++ by [].
         ++ simpl. rewrite addn0. by apply H1.
      -- by apply HType1.
  - (* Local_const *)
    et_dependent_ind HType => //.
    + (* ety_a *)
      assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
      rewrite Hremes in H1. by basic_inversion'.
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

Lemma Call_typing: forall j C t1s t2s,
    be_typing C [::Call j] (Tf t1s t2s) ->
    exists ts t1s' t2s', j < length (tc_func_t C) /\
    List.nth_error (tc_func_t C) j = Some (Tf t1s' t2s') /\
                         t1s = ts ++ t1s' /\
                         t2s = ts ++ t2s'.
Proof.
  move => j C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::], t1s, t2s.
  - invert_be_typing.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [t1s' [t2s' [H1 [H2 [H3 H4]]]]].
    subst.
    exists (ts ++ x), t1s', t2s'.
    repeat rewrite -catA.
    by repeat (split => //=).
Qed.

Lemma Call_indirect_typing: forall i C t1s t2s,
    be_typing C [::Call_indirect i] (Tf t1s t2s) ->
    exists tn tm ts, tc_table C <> nil /\
    i < length (tc_types_t C) /\
    List.nth_error (tc_types_t C) i = Some (Tf tn tm) /\
    t1s = ts ++ tn ++ [::T_i32] /\ t2s = ts ++ tm.
Proof.
  move => i C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t1s0, t2s, [::].
  - invert_be_typing.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [tm [ts' [H1 [H2 [H3 [H4 H5]]]]]]. subst.
    exists x, tm, (ts ++ ts').
    by repeat rewrite -catA.
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
  List.nth_error (i_funcs i) j = Some k ->
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
  List.nth_error (i_types i) j = Some (cl_type cl) ->
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

Lemma Invoke_func_native_typing: forall s i C tn tm ts es t1s t2s,
    e_typing s C [::Invoke (Func_native i (Tf tn tm) ts es)] (Tf t1s t2s) ->
    exists ts' C', t1s = ts' ++ tn /\ t2s = ts' ++ tm /\
                inst_typing s i C' /\
               be_typing (upd_local_label_return C' (tc_local C' ++ tn ++ ts) ([::tm] ++ tc_label C') (Some tm)) es (Tf [::] tm).
Proof.
  move => s i C tn tm ts es t1s t2s HType.
  et_dependent_ind HType => //.
  - by destruct bes => //=.
  - apply extract_list1 in Hremes. destruct Hremes. subst.
    apply et_to_bet in HType1 => //=.
    apply empty_typing in HType1. subst.
    by eapply IHHType2 => //=.
  - inversion Hremtf; subst.
    edestruct IHHType => //=.
    destruct H as [C' [H1 [H2 [H3 H4]]]]. subst.
    exists (ts0 ++ x), C'.
    by repeat split => //; rewrite catA.
  - inversion Hremes; subst.
    inversion H; subst. 
    inversion H8; subst.
    by exists [::], C.
Qed.

Lemma Invoke_func_host_typing: forall s C h tn tm t1s t2s,
    e_typing s C [::Invoke (Func_host (Tf tn tm) h)] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ tn /\ t2s = ts ++ tm.
Proof.
  move => s C h tn tm t1s t2s HType.
  et_dependent_ind HType => //.
  - by destruct bes => //=.
  - apply extract_list1 in Hremes. destruct Hremes. subst.
    apply et_to_bet in HType1 => //=.
    apply empty_typing in HType1. subst.
    by eapply IHHType2 => //=.
  - inversion Hremtf; subst.
    edestruct IHHType => //=.
    exists (ts ++ x). destruct H. subst.
    by split; repeat rewrite catA.
  - inversion Hremes; subst.
    inversion H; subst.
     by exists [::].
Qed.

Lemma Get_local_typing: forall C i t1s t2s,
    be_typing C [::Get_local i] (Tf t1s t2s) ->
    exists t, List.nth_error (tc_local C) i = Some t /\
    t2s = t1s ++ [::t] /\
    i < length (tc_local C).
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - invert_be_typing.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists x.
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Set_local_typing: forall C i t1s t2s,
    be_typing C [::Set_local i] (Tf t1s t2s) ->
    exists t, List.nth_error (tc_local C) i = Some t /\
    t1s = t2s ++ [::t] /\
    i < length (tc_local C).
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - invert_be_typing.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists x.
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Get_global_typing: forall C i t1s t2s,
    be_typing C [::Get_global i] (Tf t1s t2s) ->
    exists t, option_map tg_t (List.nth_error (tc_global C) i) = Some t /\
    t2s = t1s ++ [::t] /\
    i < length (tc_global C).
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - invert_be_typing.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists x.
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Set_global_typing: forall C i t1s t2s,
    be_typing C [::Set_global i] (Tf t1s t2s) ->
    exists g t, List.nth_error (tc_global C) i = Some g /\
    tg_t g = t /\
    is_mut g /\
    t1s = t2s ++ [::t] /\
    i < length (tc_global C).
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists g, (tg_t g).
  - invert_be_typing.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [t [H1 [H2 [H3 [H4 H5]]]]]. subst.
    exists x, (tg_t x).
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Load_typing: forall C t a off tp_sx t1s t2s,
    be_typing C [::Load t tp_sx a off] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::T_i32] /\ t2s = ts ++ [::t] /\
                    tc_memory C <> nil /\
                    load_store_t_bounds a (option_projl tp_sx) t.
Proof.
  move => C t a off tp_sx t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::].
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 [H3 H4]]]. subst.
    exists (ts ++ x).
    by repeat rewrite -catA.
Qed.

Lemma Store_typing: forall C t a off tp t1s t2s,
    be_typing C [::Store t tp a off] (Tf t1s t2s) ->
    t1s = t2s ++ [::T_i32; t] /\
    tc_memory C <> nil /\
    load_store_t_bounds a tp t.
Proof.
  move => C t a off tp t1s t2s HType.
  dependent induction HType; subst => //=.
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=. subst.
    by repeat rewrite -catA.
Qed.

Lemma Current_memory_typing: forall C t1s t2s,
    be_typing C [::Current_memory] (Tf t1s t2s) ->
    tc_memory C <> nil /\ t2s = t1s ++ [::T_i32].
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=. subst.
    by repeat rewrite -catA.
Qed.

Lemma Grow_memory_typing: forall C t1s t2s,
    be_typing C [::Grow_memory] (Tf t1s t2s) ->
    exists ts, tc_memory C <> nil /\ t2s = t1s /\ t1s = ts ++ [::T_i32].
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::].
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists (ts ++ x).
    by repeat rewrite -catA.
Qed.

Lemma store_typed_cl_typed: forall s n f,
    List.nth_error (s_funcs s) n = Some f ->
    store_typing s ->
    cl_typing s f (cl_type f).
Proof.
  move => s n f HN HST.
  unfold store_typing in HST.
  destruct s => //=.
  remove_bools_options.
  simpl in HN.
  destruct HST.
  (* arrow actually required to avoid ssreflect hijacking the rewrite tactic! *)
  rewrite -> List.Forall_forall in H.
  apply List.nth_error_In in HN.
  apply H in HN. unfold cl_type_check_single in HN. destruct HN.
  by inversion H1; subst.
Qed.

Lemma inst_t_context_local_empty: forall s i C,
    inst_typing s i C ->
    tc_local C = [::].
Proof.
  move => s i C HInstType.
  unfold inst_typing in HInstType.
  destruct i => //=.
  destruct C => //=.
  by destruct tc_local.
Qed.

Lemma inst_t_context_label_empty: forall s i C,
    inst_typing s i C ->
    tc_label C = [::].
Proof.
  move => s i C HInstType.
  unfold inst_typing in HInstType.
  destruct i => //=.
  destruct C => //=.
  by destruct tc_local; destruct tc_label.
Qed.

Lemma global_type_reference: forall s i j C v t,
    inst_typing s i C ->
    sglob_val s i j = Some v ->
    option_map tg_t (List.nth_error (tc_global C) j) = Some t ->
    typeof v = t.
Proof.
  move => s i j C v t HInstType Hvref Htref.
  unfold sglob_val in Hvref.
  unfold sglob in Hvref.
  unfold sglob_ind in Hvref.
  destruct (List.nth_error (i_globs i) j) eqn:Hi => //=.
  remove_bools_options.
  unfold option_bind in Hoption0.
  remove_bools_options.
  unfold inst_typing in HInstType.
  destruct i => //=. destruct C => //=.
  destruct tc_local => //=. destruct tc_label => //=. destruct tc_return => //=.
  move/andP in HInstType. destruct HInstType.
  remove_bools_options.
  eapply all2_projection in H2; eauto.
  unfold globals_agree in H2. move/andP in H2. destruct H2.
  remove_bools_options.
  simpl in Hi. simpl in Hoption.
  unfold global_agree in H6.
  by remove_bools_options.
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
  by destruct g_mut => //=; remove_bools_options;
    apply/andP => //=; subst; split => //=;
    destruct g_mut0 => //=; destruct g_val => //=; destruct g_val0 => //=.
Qed.

Lemma glob_extension_C: forall sg sg' ig tcg,
    all2 (globals_agree sg) ig tcg ->
    all2 glob_extension sg sg' ->
    all2 (globals_agree sg') ig tcg.
Proof.
  move => sg sg' ig.
  generalize dependent sg; generalize dependent sg'.
  induction ig; move => sg' sg tcg HA Hext => //=; destruct tcg => //=.
  - simpl in HA. remove_bools_options.
    edestruct IHig; eauto.
    unfold globals_agree in H. remove_bools_options.
    assert (size sg = size sg'); first by eapply all2_size; eauto.
    assert (a < length sg')%coq_nat.
    {
        rewrite length_is_size in H. rewrite length_is_size.
        rewrite -H1. by lias.
    }
    remember H2 as H5. clear HeqH5.
    rewrite <- List.nth_error_Some in H2.
    destruct (List.nth_error sg' a) eqn:HGlob => //=; eauto. clear H2.
    remember Hext as Hext1. clear HeqHext1.
    eapply all2_projection in Hext1; eauto.
    apply/andP. split => //=.
    + unfold globals_agree. apply/andP; split => //=; first by lias.
      unfold option_map. rewrite HGlob.
      apply/eqP. f_equal.
      by eapply global_agree_extension; eauto.
    + by eapply IHig; eauto.
Qed.

Lemma memi_agree_extension: forall m0 m1 n m,
    memi_agree m0 n m ->
    all2 mem_extension m0 m1 ->
    memi_agree m1 n m.
Proof.
  move => m0 m1 n m H1 H2.
  assert (size m0 = size m1) as HSize; first by eapply all2_size; eauto.
  unfold memi_agree.
  unfold memi_agree in H1. unfold mem_extension in H2.
  destruct m => //=.
  remove_bools_options.
  rewrite length_is_size in H.
  apply/andP; split => //=; first by rewrite HSize in H.
  rewrite HSize in H.
  rewrite -length_is_size in H.
  move/ltP in H.
  rewrite <- List.nth_error_Some in H.
  destruct (List.nth_error m1 n) eqn:HN => //=.
  unfold mem_typing. simpl.
  eapply all2_projection in H2; [| by apply Hoption | by apply HN ].
  unfold mem_typing in H0. simpl in H0.
  remove_bools_options.
  apply/andP; split.
  - by lias.
  - rewrite H3 in H2. rewrite H2. by apply/eqP.
Qed.

Lemma mem_extension_C: forall sm sm' im tcm,
    all2 (memi_agree sm) im tcm ->
    all2 mem_extension sm sm' ->
    all2 (memi_agree sm') im tcm.
Proof.
  move => sm sm' im.
  generalize dependent sm; generalize dependent sm'.
  induction im; move => sm' sm tcm HA Hext => //=; destruct tcm => //=.
  simpl in HA. remove_bools_options.
  apply/andP; split => //=; last by eapply IHim; eauto.
  by eapply memi_agree_extension; eauto.
Qed.

Lemma tabi_agree_extension: forall t0 t1 n t,
    tabi_agree t0 n t ->
    all2 tab_extension t0 t1 ->
    tabi_agree t1 n t.
Proof.
  move => t0 t1 n t H1 H2.
  assert (size t0 = size t1) as HSize; first by eapply all2_size; eauto.
  unfold tabi_agree.
  unfold tabi_agree in H1. unfold tab_extension in H2.
  unfold tab_size in H2.
  destruct t => //=.
  destruct t0 => //=.
  destruct t1 => //=.
  simpl in H2. simpl in H1.
  remove_bools_options.
  unfold tab_typing in H3.
  remove_bools_options.
  simpl in H3. simpl in H4.
  unfold tab_typing. simpl.
  simpl in HSize. inversion HSize. subst. clear HSize.
  apply/andP; split => //=.
  - rewrite length_is_size in H1. rewrite length_is_size. by rewrite H6 in H1.
  - assert (List.nth_error (t1 :: t2) n <> None).
    { apply List.nth_error_Some. rewrite length_is_size. simpl. rewrite -H6.
      by lias. }
    destruct (List.nth_error (t1 :: t2) n) eqn:HN => //=.
    destruct n => //=.
    + simpl in HN. simpl in Hoption. inversion HN. inversion Hoption. subst.
      apply/andP; split => //=; last by rewrite -H2.
      unfold tab_size. unfold tab_size in H3. by lias.
    + simpl in HN. simpl in Hoption.
      eapply all2_projection in H0; eauto.
      remove_bools_options.
      apply/andP; split => //=; last by rewrite -H7.
      unfold tab_size. unfold tab_size in H3. by lias.
Qed.

Lemma tab_extension_C: forall st st' it tct,
    all2 (tabi_agree st) it tct ->
    all2 tab_extension st st' ->
    all2 (tabi_agree st') it tct.
Proof.
  move => st st' it.
  generalize dependent st; generalize dependent st'.
  induction it; move => st' st tct HA Hext => //=; destruct tct => //=.
  simpl in HA. remove_bools_options.
  apply/andP; split => //=; last by eapply IHit; eauto.
  by eapply tabi_agree_extension; eauto.
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
  remove_bools_options. rewrite - H4.
  repeat (apply/andP; split => //=; subst => //=).
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

Lemma reflexive_all2_same: forall {X:Type} f (l: seq X),
    reflexive f ->
    all2 f l l.
Proof.
  move => X f l.
  induction l; move => H; unfold reflexive in H => //=.
  apply/andP. split => //=.
  by apply IHl.
Qed.

Lemma all2_tab_extension_same: forall t,
    all2 tab_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive. move => x. unfold tab_extension.
  by apply/andP.
Qed.

Lemma all2_mem_extension_same: forall t,
    all2 mem_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive. move => x. unfold mem_extension.
  by apply/andP.
Qed.

Lemma all2_glob_extension_same: forall t,
    all2 glob_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive. move => x. unfold glob_extension.
  destruct (g_mut x) => //=.
  by destruct (g_val x).
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
  | H: e_typing _ _ [::Label _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Label_typing in H;
    destruct H as [ts [t1s [H1 [H2 [H3 H4]]]]]; subst
  | H: typing.e_typing _ _ [::Label _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    eapply Label_typing in H; eauto;
    destruct H as [ts [t1s [H1 [H2 [H3 H4]]]]]; subst
  end.

Lemma lfilled_es_type_exists: forall k lh es les s C tf,
    lfilled k lh es les ->
    e_typing s C les tf ->
    exists lab t1s t2s, e_typing s (upd_label C lab) es (Tf t1s t2s).
Proof.
  move => k lh es les s C tf HLF.
  generalize dependent tf.
  generalize dependent C.
  move/lfilledP in HLF.
  induction HLF; move => C tf HType; destruct tf.
  - invert_e_typing.
    exists (tc_label C), t1s0, t3s0 => //=.
    by rewrite upd_label_unchanged.
  - invert_e_typing.
    edestruct IHHLF; first by apply H4.
    destruct H0 as [t1s' t2s'].
    by eauto.
Qed.

Lemma store_extension_same: forall s,
    store_extension s s.
Proof.
  move => s. unfold store_extension.
  repeat (apply/andP; split).
  + by apply/eqP.
  + by apply all2_tab_extension_same.
  + by apply all2_mem_extension_same.
  + by apply all2_glob_extension_same.
Qed.

(* This is the only questionable lemma that I'm not >99% sure of it's correctness.
   But it seems to be absolutely required. Maybe I'm 98% sure. *)
(*
   UPD: oops, this is in fact completely nonsense and in no way required --
          I overlooked another possibility here. This is now abandoned and
          replaced by a correct version.

Lemma store_reduce_same_es_typing: forall s vs es i s' vs' es' es0 C C' loc lab ret tf,
    reduce s vs es i s' vs' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s i C ->
    inst_typing s' i C' ->
    e_typing s (upd_label (upd_local_return C loc ret) lab) es0 tf ->
    e_typing s' (upd_label (upd_local_return C' loc ret) lab) es0 tf.
Proof.
 *)

Lemma store_extension_cl_typing: forall s s' cl tf,
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

(*
  The correct version. We need a mutual induction on e_typing and s_typing
    since they were defined with a mutual induction.
 *)

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
  - move=> s C cl tf Cl s' HST1 HST2 Hext.
    apply ety_invoke => //.
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
  all2 glob_extension sglobs (update_list_at sglobs n g').
Proof.
  move => sglobs n.
  generalize dependent sglobs.
  induction n; move => sglobs g g' HN Hext => //=; destruct sglobs => //.
  - simpl in HN. inversion HN. subst.
    apply/andP; split => //=.
    by apply all2_glob_extension_same.
  - assert ((n.+1 < length (g0 :: sglobs))%coq_nat); first by rewrite -List.nth_error_Some; rewrite HN.
    rewrite -update_list_at_is_set_nth; last by lias.
    simpl.
    apply/andP. split.
    + unfold glob_extension. destruct (g_mut g0) => //=. by destruct (g_val g0).
    + rewrite update_list_at_is_set_nth.
      * by eapply IHn; eauto.
      * simpl in H. rewrite length_is_size in H. by lias.
Qed.

Lemma tc_reference_glob_type: forall s i C n m gt g,
    inst_typing s i C ->
    List.nth_error (i_globs i) n = Some m ->
    List.nth_error (s_globals s) m = Some g ->
    List.nth_error (tc_global C) n = Some gt ->
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

(* same here *)

Lemma mem_extension_update_nth: forall smems n m m',
  List.nth_error smems n = Some m ->
  mem_extension m m' ->
  all2 mem_extension smems (update_list_at smems n m').
Proof.
  move => smems n.
  generalize dependent smems.
  induction n; move => smems m m' HN Hext => //=; destruct smems => //.
  - simpl in HN. inversion HN. subst.
    apply/andP. split; first apply Hext.
   by apply all2_mem_extension_same.
  - assert ((n.+1 < length (m0 :: smems))%coq_nat); first by rewrite -List.nth_error_Some; rewrite HN.
    rewrite -update_list_at_is_set_nth; last by lias.
    (* it seems that simpl is the culprit? *)
    simpl.
    apply/andP. split.
    + unfold mem_extension. by lias.
    + rewrite update_list_at_is_set_nth.
      * by eapply IHn; eauto.
      * simpl in H. rewrite length_is_size in H. by lias.
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
  { apply Nat.div_lt; omega. (* lias doesn't solve this. *) }
  by lias.
Qed.

Lemma mem_extension_store: forall m k off v tlen mem,
    store m k off (bits v) tlen = Some mem ->
    mem_extension m mem.
Proof.
  move => m k off v tlen mem HStore.
  unfold mem_extension.
  unfold store in HStore.
  destruct ((k + off + N.of_nat tlen <=? mem_length m)%N) eqn:HMemSize => //.
  inversion HStore; clear HStore.
  by apply/andP; split => //=.
Qed.

Lemma mem_extension_grow_memory: forall m c mem,
    mem_grow m c = (Some mem) ->
    mem_extension m mem.
Proof.
  move => m c mem HMGrow.
  unfold mem_extension.
  unfold mem_grow in HMGrow.
  destruct (mem_max_opt m) eqn:HLimMax => //=.
  - destruct ((mem_length m + c <=? n)%N) eqn:HLT => //.
    move : HMGrow.
    case: mem => mem_data_ mem_max_opt_ [H1 H2].
    simpl.
    apply/andP.
    split.
    { unfold mem_size, mem_length.
      simpl.
      case: mem_data_ H1 => dv_len dv_arr [H3 H4].
      simpl.
      rewrite -H3.
      unfold mem_length.
      admit. (* TODO: lias *) }
    {
      apply/eqP; done.
    }
  - inversion HMGrow; subst; clear HMGrow.
    admit.
Admitted.

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
      rewrite -> List.Forall_forall.
      split => //=.
      move => x' HIN'.
      apply H1 in HIN'.
      unfold tabcl_agree in HIN'.
      unfold tabcl_agree.
      destruct x' => //=.
      simpl in HIN'. destruct (List.nth_error s_funcs0 n) => //=.
      unfold cl_type_check_single in HIN'.
      destruct HIN'.
      unfold cl_type_check_single.
      exists x0. by eapply store_extension_cl_typing; eauto.
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
    rewrite -> List.Forall_forall.
    split => //=.
    move => x' HIN'.
    apply H1 in HIN'.
    unfold tabcl_agree in HIN'.
    unfold tabcl_agree.
    destruct x' => //=.
    simpl in HIN'. destruct (List.nth_error s_funcs0 n) => //=.
    unfold cl_type_check_single in HIN'.
    destruct HIN'.
    unfold cl_type_check_single.
    exists x0. by eapply store_extension_cl_typing; eauto.
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
    
Lemma nth_error_update_list_hit: forall {X:Type} l n {x:X},
    n < length l ->
    List.nth_error (update_list_at l n x) n = Some x.
Proof.
  move => X l n. generalize dependent l.
  induction n => //=; destruct l => //=.
  - move => x' HLength.
    simpl. rewrite -cat1s.
    assert (n < length l); first by lias.
    assert (length (take n l) = n).
    { rewrite length_is_size. rewrite length_is_size in H.
      rewrite size_take. by rewrite H. }
    assert (List.nth_error (take n l ++ [:: x'] ++ List.skipn (n+1)%Nrec l) (length (take n l)) = Some x'); first by apply list_nth_prefix.
    by rewrite H0 in H1.
Qed.

Lemma nth_error_update_list_others: forall {X:Type} l n m {x:X},
    n <> m ->
    n < length l ->
    List.nth_error (update_list_at l n x) m = List.nth_error l m.
Proof.
  move => X l n. generalize dependent l.
  induction n => //=; move => l m x Hne HLength.
  - destruct m => //=.
    by destruct l => //=.
  - destruct m => //=.
    + by destruct l => //=.
    + destruct l => //=.
      simpl in HLength.
      by apply IHn; lias.
Qed.

Lemma Forall_update: forall {X:Type} f l n {x:X},
    List.Forall f l ->
    f x ->
    n < length l ->
    List.Forall f (update_list_at l n x).
Proof.
  move => X f l n x HA Hf HLength.
  rewrite -> List.Forall_forall in HA.
  rewrite List.Forall_forall.
  move => x0 HIN.
  apply List.In_nth_error in HIN.
  destruct HIN as [n' HN].
  assert (n' < length (update_list_at l n x))%coq_nat.
  { rewrite <- List.nth_error_Some. by rewrite HN. }
  move/ltP in H.
  destruct (n == n') eqn:H1 => //=.
  - move/eqP in H1. subst.
    rewrite nth_error_update_list_hit in HN => //=. by inversion HN; subst.
  - move/eqP in H1.
    rewrite nth_error_update_list_others in HN => //=.
    apply HA.
    by eapply List.nth_error_In; eauto.
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
  inversion HStore. subst. clear HStore.
  unfold mem_agree => //=.
  destruct (mem_max_opt m) eqn:HLimMax => //=.
  unfold mem_size. unfold mem_length => /=.
  assert (mem_agree m); first by eapply store_typed_mem_agree; eauto.
  unfold mem_agree in H0. by rewrite HLimMax in H0.
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
  destruct (mem_max_opt m) eqn:HLimMax => //=.
  - destruct ((mem_size m + c <=? n0)%N) eqn:H1 => //.
    by inversion HGrow; subst.
  - by inversion HGrow; subst.
Qed.

Lemma reduce_inst_unchanged: forall hs s f es hs' s' f' es',
    reduce hs s f es hs' s' f' es' ->
    f.(f_inst) = f'.(f_inst).
Proof.
  move => hs s f es hs' s' f' es' HReduce.
  by induction HReduce.
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
    replace [::EConst v; Set_global i] with ([::EConst v] ++ [::Set_global i]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]]. subst.
    invert_be_typing.
    apply Set_global_typing in H4.
    destruct H4 as [g [t [H5 [H6 [H7 [H8 H9]]]]]].
    apply concat_cancel_last in H8. destruct H8. subst.
    unfold supdate_glob in H.
    unfold option_bind in H.
    unfold supdate_glob_s in H.
    unfold option_map in H.
    assert (store_extension s s') as Hext.
    remove_bools_options.
    unfold sglob_ind in Hoption. simpl in H5.
    eapply tc_reference_glob_type in H5; eauto.
    destruct g => //.
    destruct g0 => //.
    simpl in H1. unfold global_agree in H5. simpl in H5.
    unfold is_mut in H7. simpl in H7. remove_bools_options. subst.
    + simpl. unfold store_extension => //=.
      repeat (apply/andP; split) => //=.
      -- by apply all2_tab_extension_same.
      -- by apply all2_mem_extension_same.
      -- eapply glob_extension_update_nth; eauto => //=.
         unfold glob_extension => //=.
         by destruct v => //=; destruct g_val => //=.
    split => //.
    by eapply store_global_extension_store_typed; eauto;
      destruct s => //=; destruct s' => //=; remove_bools_options.
  - (* update memory : store none *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::EConst (ConstInt32 k); EConst v; Store t None a off] with ([::EConst (ConstInt32 k); EConst v] ++ [::Store t None a off]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    invert_be_typing.
    apply Store_typing in H6.
    destruct H6 as [H7 [H8 H9]]. subst.
    apply concat_cancel_last_n in H7 => //.
    remove_bools_options.
    inversion H4. subst. clear H4.
    assert (store_extension s (upd_s_mem s (update_list_at (s_mems s) i mem'))) as Hext.
    + unfold store_extension => //=.
      repeat (apply/andP; split) => //=.
      * by apply all2_tab_extension_same.
        eapply mem_extension_update_nth; eauto => //=.
      * by eapply mem_extension_store; eauto.
      * by apply all2_glob_extension_same.
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
    apply Forall_update => //=.
    eapply store_mem_agree; eauto.
    * by destruct v => //=.
    * by move/ltP in H3.
  - (* another update memory : store some *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::EConst (ConstInt32 k); EConst v; Store t (Some tp) a off] with ([::EConst (ConstInt32 k); EConst v] ++ [::Store t (Some tp) a off]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    invert_be_typing.
    apply Store_typing in H6.
    destruct H6 as [H7 [H8 H9]]. subst.
    apply concat_cancel_last_n in H7 => //.
    remove_bools_options.
    inversion H4. subst. clear H4.
    assert (store_extension s (upd_s_mem s (update_list_at (s_mems s) i mem'))) as Hext.
    + unfold store_extension => //=.
      repeat (apply/andP; split) => //=.
      * by apply all2_tab_extension_same.
      * eapply mem_extension_update_nth; eauto => //=.
        by eapply mem_extension_store; eauto.
      * by apply all2_glob_extension_same.
    split => //.
    eapply store_memory_extension_store_typed; eauto => //=.
    remember HST as HST2. clear HeqHST2.
    unfold store_typing in HST.
    destruct s => //=.
    destruct HST as [_ [_ H11]].
    simpl in H1.
    assert (i < length s_mems0)%coq_nat.
    { apply List.nth_error_Some. by rewrite H1. }
    apply Forall_update => //=.
    eapply store_mem_agree; eauto.
    * by destruct tp => //=.
    * by move/ltP in H3.
  - (* again update memory : grow_memory *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::EConst (ConstInt32 c); Grow_memory] with ([::EConst (ConstInt32 c)] ++ [::Grow_memory]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    invert_be_typing.
    apply Grow_memory_typing in H6.
    destruct H6 as [ts' [H7 [H8 H9]]]. subst.
    apply concat_cancel_last in H9 => //. destruct H9. subst.
    assert (store_extension s (upd_s_mem s (update_list_at (s_mems s) i mem'))) as Hext.
    + unfold store_extension => //=.
      repeat (apply/andP; split) => //=.
      * by apply all2_tab_extension_same.
      * eapply mem_extension_update_nth; eauto => //=.
        by eapply mem_extension_grow_memory; eauto.
      * by apply all2_glob_extension_same.
    split => //.
    eapply store_memory_extension_store_typed; eauto => //=.
    remember HST as HST2. clear HeqHST2.
    unfold store_typing in HST.
    destruct s => //=.
    destruct HST as [_ [_ H11]].
    simpl in H0.
    assert (i < length s_mems0)%coq_nat.
    { apply List.nth_error_Some. by rewrite H0. }
    apply Forall_update => //=.
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
    replace [::EConst v; Set_local i] with ([::EConst v] ++ [::Set_local i]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Set_local_typing in H10.
    destruct H10 as [t [H4 [H5 H6]]]. subst.
    apply concat_cancel_last in H5. destruct H5. subst.
    assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
    rewrite HCEmpty in H4. rewrite HCEmpty in H6.
    simpl in H4. simpl in H6.
    rewrite length_is_size in H6. rewrite size_map in H6.
    rewrite H0.
    rewrite set_nth_map => //.
    by rewrite set_nth_same_unchanged.
  - assert (exists lab' t1s' t2s', e_typing s (upd_label (upd_label (upd_local_return C (tc_local C ++ map typeof f.(f_locs)) ret) lab) lab') es (Tf t1s' t2s')); first eapply lfilled_es_type_exists; eauto.
    destruct H1 as [lab' [t1s' [t2s' H1]]].
    rewrite upd_label_overwrite in H1.
    by eapply IHHReduce; eauto.
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
  generalize dependent t2s. generalize dependent t1s.
  generalize dependent lab. generalize dependent ret.
  generalize dependent C.
  induction HReduce; move => C ret lab tx ty HIT1 HIT2 HType; subst; try eauto; try by apply ety_trap.
  - (* reduce_simple *)
    by eapply t_simple_preservation; eauto.
  - (* Call *)
    convert_et_to_bet.
    apply Call_typing in HType.
    destruct HType as [ts [t1s' [t2s' [H1 [H2 [H3 H4]]]]]].
    subst. simpl in H1. simpl in H2.
    unfold sfunc in H.
    unfold option_bind in H.
    destruct (sfunc_ind s f.(f_inst) i) eqn:HSF => //=.
    unfold sfunc_ind in HSF.
    apply ety_weakening.
    apply ety_invoke.
    assert ((Tf t1s' t2s') = cl_type cl) as HFType; first by eapply tc_func_reference1; eauto.
    rewrite HFType.
    by eapply store_typed_cl_typed; eauto.
  - (* Call_indirect *)
    convert_et_to_bet.
    replace [::EConst (ConstInt32 c); Call_indirect i] with ([::EConst (ConstInt32 c)] ++ [::Call_indirect i]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]].
    subst.
    invert_be_typing.
    apply Call_indirect_typing in H4.
    destruct H4 as [tn [tm [ts [H5 [H6 [H7 [H8 H9]]]]]]].
    rewrite catA in H8. apply concat_cancel_last in H8. destruct H8. subst. clear H2.
    simpl in H5. simpl in H6. simpl in H7.
    repeat apply ety_weakening.
    apply ety_invoke.
    unfold stypes in H0.
    assert ((Tf tn tm) = cl_type cl) as HFType; first by eapply tc_func_reference2; eauto.
    rewrite HFType.
    unfold stab in H.
    destruct (i_tab f.(f_inst)) eqn:HiTab => //.
    destruct (stab_s s t (Wasm_int.nat_of_uint i32m c)) eqn:Hstab => //.
    inversion H. subst. clear H.
    unfold stab_s in Hstab.
    unfold option_bind in Hstab.
    destruct (stab_index s t (Wasm_int.nat_of_uint i32m c)) eqn:Hstabi => //.
    unfold stab_index in Hstabi.
    unfold option_bind in Hstabi.
    destruct (List.nth_error (s_tables s) t) eqn:HN1 => //.
    destruct (List.nth_error (table_data t0) (Wasm_int.nat_of_uint i32m c)) eqn:HN2 => //.
    subst.
    by eapply store_typed_cl_typed; eauto.
  - (* Invoke native *)
    invert_e_typing.
    apply Invoke_func_native_typing in H4.
    destruct H4 as [ts2 [C2 [H9 [H10 [H11 H12]]]]]. subst.
    apply et_to_bet in H0; last by apply const_list_is_basic; apply v_to_e_is_const_list.
    apply Const_list_typing in H0.
    apply concat_cancel_last_n in H0; last by (repeat rewrite length_is_size in H2; rewrite size_map).
    move/andP in H0. destruct H0.
    move/eqP in H. move/eqP in H0. subst.
    simpl in H12.
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
    rewrite H7.
    rewrite map_cat => //=.
    rewrite n_zeros_typing.
    by destruct C2.
  - (* Invoke host *)
    apply e_composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H5 [H6 [H7 H8]]]]]]].
    subst.
    apply Invoke_func_host_typing in H8.
    destruct H8 as [ts [H8 H9]]. subst.
    apply et_to_bet in H7; last by apply const_list_is_basic; apply v_to_e_is_const_list.
    apply Const_list_typing in H7.
    apply concat_cancel_last_n in H7; last by (repeat rewrite length_is_size in H2; rewrite size_map).
    remove_bools_options. subst.
    (* We require more knowledge of the host at this point. *)
    (* UPD: made it an axiom. *)
    assert (result_types_agree t2s r).
    {
      destruct host_instance. apply host_application_respect in H4 => //.
      unfold types_agree.
      clear H4. clear H2.
      induction vcs => //=.
      by apply/andP.
    }
    rewrite catA. apply et_weakening_empty_1.
    by apply result_e_type.
  - (* Get_local *)
    convert_et_to_bet.
    apply Get_local_typing in HType.
    destruct HType as [t [H1 [H2 H3]]]. subst.
    apply ety_a'; auto_basic => //=.
    assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
    rewrite HCEmpty in H1. rewrite HCEmpty in H3. rewrite HCEmpty.
    simpl in H1. simpl in H3. simpl.
    apply nth_error_map in H1. destruct H1 as [v' [HNth Hvt]]. subst.
    apply bet_weakening_empty_1.
    rewrite H in HNth. inversion HNth; subst.
    by apply bet_const.
  - (* Set_local *)
    convert_et_to_bet.
    replace [::EConst v; Set_local i] with ([::EConst v] ++ [::Set_local i]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Set_local_typing in H10.
    destruct H10 as [t [H4 [H5 H6]]]. subst.
    apply ety_a'; auto_basic => //=.
    assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
    rewrite HCEmpty in H6. rewrite HCEmpty in H4. rewrite HCEmpty.
    simpl in H6. simpl in H5. simpl in H4. simpl.
    apply concat_cancel_last in H5. destruct H5. subst.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - (* Get_global *)
    convert_et_to_bet.
    apply Get_global_typing in HType.
    destruct HType as [t [H4 [H5 H6]]]. subst.
    apply ety_a'; auto_basic => //=.
    assert (tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
    rewrite H0 in H6. rewrite H0 in H4. rewrite H0.
    simpl in H6. simpl in H4. simpl.
    assert (typeof v = t); first by eapply global_type_reference; eauto.
    rewrite -H1.
    apply bet_weakening_empty_1.
    by apply bet_const.
  - (* Set_Global *)
    convert_et_to_bet.
    replace [::EConst v; Set_global i] with ([::EConst v] ++ [::Set_global i]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Set_global_typing in H10.
    destruct H10 as [g [t [H4 [H5 [H6 [H7 H8]]]]]]. subst.
    apply ety_a'; auto_basic => //=.
    simpl in H8. simpl in H4. simpl.
    apply concat_cancel_last in H7. destruct H7. subst.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - (* Load None *)
    convert_et_to_bet.
    replace [::EConst (ConstInt32 k); Load t None a off] with ([::EConst (ConstInt32 k)] ++ [::Load t None a off]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Load_typing in H10.
    destruct H10 as [ts  [H11 [H12 [H13 H14]]]].
    apply concat_cancel_last in H11. destruct H11. subst.
    eapply t_const_ignores_context => //=.
    instantiate (2 := s).
    apply ety_a'; auto_basic.
    simpl.
    assert (be_typing C [::EConst (wasm_deserialise bs t)] (Tf [::] [:: typeof (wasm_deserialise bs t)])); first by apply bet_const.
    rewrite catA.
    apply bet_weakening_empty_1.
    rewrite typeof_deserialise in H2. by apply H2.
  - (* Load Some *)
    convert_et_to_bet.
    replace [::EConst (ConstInt32 k); Load t (Some (tp, sx)) a off] with ([::EConst (ConstInt32 k)] ++ [::Load t (Some (tp, sx)) a off]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Load_typing in H10.
    destruct H10 as [ts [H11 [H12 [H13 H14]]]].
    apply concat_cancel_last in H11. destruct H11. subst.
    eapply t_const_ignores_context => //=.
    instantiate (2 := s).
    apply ety_a'; auto_basic.
    simpl.
    assert (be_typing C [::EConst (wasm_deserialise bs t)] (Tf [::] [:: typeof (wasm_deserialise bs t)])); first by apply bet_const.
    rewrite catA. apply bet_weakening_empty_1.
    rewrite typeof_deserialise in H2. by apply H2.
  - (* Store None *)
    + convert_et_to_bet.
      simpl in HType.
      replace [::EConst (ConstInt32 k); EConst v; Store t None a off] with ([::EConst (ConstInt32 k); EConst v] ++ [::Store t None a off]) in HType => //=.
      apply composition_typing in HType.
      destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
      invert_be_typing.
      apply Store_typing in H10.
      destruct H10 as [H11 [H12 H13]].
      apply concat_cancel_last_n in H11 => //.
      move/andP in H11. destruct H11. move/eqP in H3. subst.
      apply ety_a'; auto_basic => //=.
      apply bet_weakening_empty_both.
      by apply bet_empty.
  - (* Store Some *)
    + convert_et_to_bet.
      simpl in HType.
      replace [::EConst (ConstInt32 k); EConst v; Store t (Some tp) a off] with ([::EConst (ConstInt32 k); EConst v] ++ [::Store t (Some tp) a off]) in HType => //=.
      apply composition_typing in HType.
      destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
      invert_be_typing.
      apply Store_typing in H10.
      destruct H10 as [H11 [H12 H13]].
      apply concat_cancel_last_n in H11 => //.
      move/andP in H11. destruct H11. move/eqP in H3. subst.
      apply ety_a'; auto_basic => //.
      apply bet_weakening_empty_both.
      by apply bet_empty.
  - (* Current_memory *)
    convert_et_to_bet.
    apply Current_memory_typing in HType.
    destruct HType as [H5 H6]. subst.
    simpl.
    apply ety_a'; auto_basic.
    apply bet_weakening_empty_1.
    by apply bet_const.
  - (* Grow_memory success *)
    convert_et_to_bet.
    replace [::EConst (ConstInt32 c); Grow_memory] with ([::EConst (ConstInt32 c)] ++ [::Grow_memory]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Grow_memory_typing in H10.
    destruct H10 as [ts [H11 [H12 H13]]]. subst.
    simpl.
    apply ety_a'; auto_basic.
    rewrite catA.
    apply bet_weakening_empty_1.
    by apply bet_const.
  - (* Grow_memory fail *)
    convert_et_to_bet.
    replace [::EConst (ConstInt32 c); Grow_memory] with ([::EConst (ConstInt32 c)] ++ [::Grow_memory]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Grow_memory_typing in H10.
    destruct H10 as [ts [H11 [H12 H13]]]. subst.
    simpl.
    apply ety_a'; auto_basic.
    rewrite catA.
    apply bet_weakening_empty_1.
    by apply bet_const.
  (* From the structure, it seems that some form of induction is required to prove these
   2 cases. *)
  - (* r_label *)
    generalize dependent lh. generalize dependent les. generalize dependent les'.
    generalize dependent ty. generalize dependent tx. generalize dependent lab.
    induction k; move => lab tx ty les' les HType lh HLF1 HLF2; move/lfilledP in HLF1; move/lfilledP in HLF2.
    + inversion HLF1. inversion HLF2. subst. clear HLF1. clear HLF2.
      inversion H5. subst. clear H5. clear H0.
      apply e_composition_typing in HType.
      destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H2 [H3 [H4 H5]]]]]]]. subst.
      apply e_composition_typing in H5.
      destruct H5 as [ts1 [t1s1 [t2s1 [t3s1 [H6 [H7 [H8 H9]]]]]]]. subst.
      eapply et_composition'.
      -- instantiate (1 := ts0 ++ ts1 ++ t1s1).
         apply ety_weakening.
         by eapply t_const_ignores_context; eauto.
      -- eapply et_composition'; eauto.
         ++ instantiate (1 := ts0 ++ ts1 ++ t3s1).
            repeat apply ety_weakening.
            by eapply IHHReduce; eauto => //.
         ++ repeat apply ety_weakening.
            assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
            rewrite HCEmpty in H9. rewrite HCEmpty.
            replace (map typeof f'.(f_locs)) with (map typeof f.(f_locs)) => //.
            eapply store_extension_e_typing; try apply HST1 => //; try by [].
            eapply store_extension_reduce; eauto.
            by eapply t_preservation_vs_type; eauto.
    + inversion HLF1. inversion HLF2. subst.
      inversion H8. subst. clear H8.
      clear H6.
      move/lfilledP in H1. move/lfilledP in H7.
      apply e_composition_typing in HType.
      destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H2 [H3 [H4 H5]]]]]]]. subst.
      apply e_composition_typing in H5.
      destruct H5 as [ts1 [t1s1 [t2s1 [t3s1 [H10 [H11 [H12 H13]]]]]]]. subst.
      apply Label_typing in H12.
      destruct H12 as [ts2 [t2s2 [H14 [H15 [H16 H17]]]]]. subst.
      eapply et_composition'.
      -- instantiate (1 := ts0 ++ ts1 ++ t1s1).
         apply ety_weakening.
         by eapply t_const_ignores_context; eauto.
      -- eapply et_composition'; eauto.
         ++ instantiate (1 := ts0 ++ ts1 ++ t1s1 ++ t2s2).
            repeat apply ety_weakening.
            apply et_weakening_empty_1.
            eapply ety_label; eauto.
            * assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
              rewrite HCEmpty in H15. rewrite HCEmpty.
              simpl in H16. rewrite upd_label_overwrite in H16.
              eapply lfilled_es_type_exists in H16; eauto.
              destruct H16 as [lab' [t1s' [t2s' H16]]].
              rewrite upd_label_overwrite in H16.
              replace (map typeof f'.(f_locs)) with (map typeof f.(f_locs)) => //.
              eapply store_extension_e_typing; try apply HST1 => //; try by [].
              eapply store_extension_reduce; eauto.
              by eapply t_preservation_vs_type; eauto.
            * simpl.
              simpl in H16.
              by eapply IHk; eauto.
         ++ repeat apply ety_weakening.
            assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
            rewrite HCEmpty in H13. rewrite HCEmpty.
            simpl in H16. rewrite upd_label_overwrite in H16.
            eapply lfilled_es_type_exists in H16; eauto.
            destruct H16 as [lab' [t1s' [t2s' H16]]].
            rewrite upd_label_overwrite in H16.
            replace (map typeof f'.(f_locs)) with (map typeof f.(f_locs)) => //.
            eapply store_extension_e_typing; try apply HST1 => //; try by [].
            eapply store_extension_reduce; eauto.
            by eapply t_preservation_vs_type; eauto.
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
