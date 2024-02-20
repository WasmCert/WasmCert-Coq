(** Typing inversion lemmas **)

From Wasm Require Export common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program.Equality NArith ZArith_base.
From Wasm Require Export properties.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Typing_inversion_be.

Hint Constructors be_typing : core.

Lemma upd_label_overwrite: forall C l1 l2,
    upd_label (upd_label C l1) l2 = upd_label C l2.
Proof.
  by [].
Qed.

Ltac resolve_compose Hcat Hempty IH :=
  apply extract_list1 in Hcat; destruct Hcat; subst;
  apply empty_typing in Hempty; subst; try by eapply IH.

Ltac resolve_weaken :=
  repeat eexists; repeat split; eauto => /=; subst; repeat rewrite -catA => //.

Lemma BI_const_num_typing: forall C econst t1s t2s,
    be_typing C [::BI_const_num econst] (Tf t1s t2s) ->
    t2s = t1s ++ [::T_num (typeof_num econst)].
Proof.
  move => C econst t1s t2s HType.
  gen_ind_subst HType => //.
  - by resolve_compose Econs HType1 IHHType2.
  - rewrite - catA -cat_app.
    f_equal.
    by eapply IHHType.
Qed.

Lemma BI_const_vec_typing: forall C econst t1s t2s,
    be_typing C [::BI_const_vec econst] (Tf t1s t2s) ->
    t2s = t1s ++ [::T_vec (typeof_vec econst)].
Proof.
  move => C econst t1s t2s HType.
  gen_ind_subst HType => //.
  - by resolve_compose Econs HType1 IHHType2.
  - rewrite - catA -cat_app.
    f_equal.
    by eapply IHHType.
Qed.

Lemma BI_const_num2_typing: forall C econst1 econst2 t1s t2s,
    be_typing C [::BI_const_num econst1; BI_const_num econst2] (Tf t1s t2s) ->
    t2s = t1s ++ [::T_num (typeof_num econst1); T_num (typeof_num econst2)].
Proof.
  move => C econst1 econst2 t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list2 in H1; inversion H1; subst.
    apply BI_const_num_typing in HType1; subst.
    apply BI_const_num_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA -cat_app.
    f_equal.
    by eapply IHHType.
Qed.

Lemma BI_const_num3_typing: forall C econst1 econst2 econst3 t1s t2s,
    be_typing C [::BI_const_num econst1; BI_const_num econst2; BI_const_num econst3] (Tf t1s t2s) ->
    t2s = t1s ++ [::T_num (typeof_num econst1); T_num (typeof_num econst2); T_num (typeof_num econst3)].
Proof.
  move => C econst1 econst2 econst3 t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list3 in H1; inversion H1; subst.
    apply BI_const_num2_typing in HType1; subst.
    apply BI_const_num_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA -cat_app.
    f_equal.
    by eapply IHHType.
Qed.

Lemma Unop_typing: forall C t op t1s t2s,
    be_typing C [::BI_unop t op] (Tf t1s t2s) ->
    t1s = t2s /\ exists ts, t1s = ts ++ [::T_num t].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - by split => //=; exists nil.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [?[??]] => //=; subst.
    split => //.
    by eexists; rewrite -cat_app catA.
Qed.

Lemma Binop_typing: forall C t op t1s t2s,
    be_typing C [::BI_binop t op] (Tf t1s t2s) ->
    t1s = t2s ++ [::T_num t] /\ exists ts, t2s = ts ++ [::T_num t].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - split => //=. by exists [::].
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [?[??]] => //=; subst.
    repeat rewrite -cat_app; repeat rewrite catA.
    split => //=.
    by eexists.
Qed.

Lemma Testop_typing: forall C t op t1s t2s,
    be_typing C [::BI_testop t op] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::T_num t] /\ t2s = ts ++ [::T_num T_i32] /\ is_int_t t.
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - by exists [::].
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [?[?[??]]] => //=; subst.
    repeat rewrite -cat_app; repeat rewrite catA.
    by eexists.
Qed.

Lemma Relop_typing: forall C t op t1s t2s,
    be_typing C [::BI_relop t op] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::T_num t; T_num t] /\ t2s = ts ++ [::T_num T_i32].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - by exists [::].
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [?[??]] => //=; subst.
    repeat rewrite -cat_app; repeat rewrite catA.
    by eexists.
Qed.

Lemma Cvtop_typing: forall C t1 t2 op sx t1s t2s,
    be_typing C [::BI_cvtop t2 op t1 sx] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::T_num t1] /\ t2s = ts ++ [::T_num t2] /\ (op = CVO_reinterpret -> sx = None).
Proof.
  move => C t1 t2 op sx t1s t2s HType.
  gen_ind_subst HType; try by exists nil.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [?[?[??]]] => //=; subst.
    repeat rewrite -cat_app; repeat rewrite catA.
    by eexists.
Qed.

Lemma Nop_typing: forall C t1s t2s,
    be_typing C [::BI_nop] (Tf t1s t2s) ->
    t1s = t2s.
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //.
  - by resolve_compose Econs HType1 IHHType2.
  - f_equal. by eapply IHHType.
Qed.

Lemma Drop_typing: forall C t1s t2s,
    be_typing C [::BI_drop] (Tf t1s t2s) ->
    exists t, t1s = t2s ++ [::t].
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //=.
  - by eauto.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType => //=; subst.
    by resolve_weaken.
Qed.

Lemma Select_typing: forall C t1s t2s ot,
    be_typing C [::BI_select ot] (Tf t1s t2s) ->
    exists ts t,
      t1s = ts ++ [::t; t; T_num T_i32] /\
        t2s = ts ++ [::t] /\
        (ot = Some [::t] \/ is_numeric_type t).
Proof.
  move => C t1s t2s ot HType.
  gen_ind_subst HType => //.
  - exists [::], t; repeat split => //; by left.
  - exists [::], t; repeat split => //; by right.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [? [?[?[??]]]] => //=; subst.
    repeat rewrite -cat_app; repeat rewrite catA.
    by repeat eexists.
Qed.

Lemma If_typing: forall C tb e1s e2s ts ts',
    be_typing C [::BI_if tb e1s e2s] (Tf ts ts') ->
    exists ts0 ts1 ts2,
      expand_t C tb = Some (Tf ts1 ts2) /\
        ts = ts0 ++ ts1 ++ [::T_num T_i32] /\ ts' = ts0 ++ ts2 /\
        be_typing (upd_label C ([:: ts2] ++ tc_labels C)) e1s (Tf ts1 ts2) /\
        be_typing (upd_label C ([:: ts2] ++ tc_labels C)) e2s (Tf ts1 ts2).
Proof.
  move => C tb e1s e2s ts ts' HType.
  gen_ind_subst HType => //=.
  - by exists [::], tn, ts'.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [ts0 [ts1 [ts2 [? [? [? [??]]]]]]] => //=; subst.
    exists (ts ++ ts0), ts1, ts2.
    split => //.
    by resolve_weaken.
Qed.

Lemma Br_if_typing: forall C ts1 ts2 i,
    be_typing C [::BI_br_if i] (Tf ts1 ts2) ->
    exists ts ts', ts2 = ts ++ ts' /\ ts1 = ts2 ++ [::T_num T_i32] /\ lookup_N C.(tc_labels) i = Some ts'.
Proof.
  move => C ts1 ts2 i HType.
  gen_ind_subst HType => //=.
  - by exists nil, ts2.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [ts0 [? [? [? ?]]]] => //=; subst.
    exists (ts ++ ts0).
    by resolve_weaken.
Qed.

Lemma Br_table_typing: forall C ts1 ts2 ids i0,
    be_typing C [::BI_br_table ids i0] (Tf ts1 ts2) ->
    exists ts1' ts, ts1 = ts1' ++ ts ++ [::T_num T_i32] /\
                         List.Forall (fun i => lookup_N C.(tc_labels) i = Some ts) (ids ++ [::i0]).
Proof.
  move => C ts1 ts2 ids i0 HType.
  gen_ind_subst HType.
  - by exists t1s, ts.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [ts0 [ts' [??]]] => //=; subst.
    exists (ts ++ ts0), ts'.
    by resolve_weaken.
Qed.

Lemma Tee_local_typing: forall C i ts1 ts2,
    be_typing C [::BI_local_tee i] (Tf ts1 ts2) ->
    exists ts t, ts1 = ts2 /\ ts1 = ts ++ [::t] /\ lookup_N (tc_locals C) i = Some t.
Proof.
  move => C i ts1 ts2 HType.
  gen_ind_subst HType.
  - by exists [::], t.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [ts0 [t [? [? ?]]]] => //=.
    exists (ts ++ ts0), t.
    by resolve_weaken.
Qed.

Lemma Get_local_typing: forall C i t1s t2s,
    be_typing C [::BI_local_get i] (Tf t1s t2s) ->
    exists t, lookup_N (tc_locals C) i = Some t /\
    t2s = t1s ++ [::t].
Proof.
  move => ???? HType.
  gen_ind_subst HType => //=.
  - by eexists; eauto.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [?[??]]; eauto => //=.
    by resolve_weaken.
Qed.

Lemma Set_local_typing: forall C i t1s t2s,
    be_typing C [::BI_local_set i] (Tf t1s t2s) ->
    exists t, lookup_N (tc_locals C) i = Some t /\
    t1s = t2s ++ [::t].
Proof.
  move => ???? HType.
  gen_ind_subst HType => //=.
  - by eexists; eauto.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [?[??]]; eauto => //=.
    by resolve_weaken.
Qed.
  
Lemma Get_global_typing: forall C i t1s t2s,
    be_typing C [::BI_global_get i] (Tf t1s t2s) ->
    exists t, option_map tg_t (lookup_N (tc_globals C) i) = Some t /\
    t2s = t1s ++ [::t].
Proof.
  move => ???? HType.
  gen_ind_subst HType => //=.
  - by eexists; eauto.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [?[??]]; eauto => //=.
    by resolve_weaken.
Qed.

Lemma Set_global_typing: forall C i t1s t2s,
    be_typing C [::BI_global_set i] (Tf t1s t2s) ->
    exists g t, lookup_N (tc_globals C) i = Some g /\
    tg_t g = t /\
    is_mut g /\
    t1s = t2s ++ [::t].
Proof.
  intros ???? HType.
  gen_ind_subst HType => //=.
  - by do 2 eexists; eauto.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [? [? [? [? [? ?]]]]]; subst=> //=.
    by resolve_weaken.
Qed.

Lemma Load_typing: forall C t a off tp_sx t1s t2s,
    be_typing C [::BI_load t tp_sx a off] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::T_num T_i32] /\ t2s = ts ++ [::T_num t] /\
                    tc_mems C <> nil /\
                    load_store_t_bounds a (option_projl tp_sx) t.
Proof.
  intros ??????? HType.
  gen_ind_subst HType => //=.
  - by exists nil; eauto.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [ts0 [? [? [? ?]]]]; subst => //=.
    exists (ts ++ ts0).
    by resolve_weaken.
Qed.

Lemma Store_typing: forall C t a off tp t1s t2s,
    be_typing C [::BI_store t tp a off] (Tf t1s t2s) ->
    t1s = t2s ++ [::T_num T_i32; T_num t] /\
    tc_mems C <> nil /\
    load_store_t_bounds a tp t.
Proof.
  intros ??????? HType.
  gen_ind_subst HType => //=.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [? [??]]; subst=> //=.
    by resolve_weaken.
Qed.

Lemma Memory_size_typing: forall C t1s t2s,
    be_typing C [::BI_memory_size] (Tf t1s t2s) ->
    tc_mems C <> nil /\ t2s = t1s ++ [::T_num T_i32].
Proof.
  intros ??? HType.
  gen_ind_subst HType => //=.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType; subst=> //=.
    by resolve_weaken.
Qed.

Lemma Memory_grow_typing: forall C t1s t2s,
    be_typing C [::BI_memory_grow] (Tf t1s t2s) ->
    exists ts, tc_mems C <> nil /\ t2s = t1s /\ t1s = ts ++ [::T_num T_i32].
Proof.
  intros ??? HType.
  gen_ind_subst HType => //=.
  - by exists nil; eauto.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [ts0 [? [? ?]]]; subst => //=.
    exists (ts ++ ts0).
    by resolve_weaken.
Qed.

Lemma Block_typing: forall C tb es tn tm,
    be_typing C [::BI_block tb es] (Tf tn tm) ->
    exists ts ts1 ts2, expand_t C tb = Some (Tf ts1 ts2) /\ tn = ts ++ ts1 /\ tm = ts ++ ts2 /\
               be_typing (upd_label C ([::ts2] ++ (tc_labels C))) es (Tf ts1 ts2).
Proof.
  intros ????? HType.
  gen_ind_subst HType => //=.
  - by exists nil, tn0, tm0; eauto.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [ts0 [ts1 [ts2 [? [? [? ?]]]]]]; subst => //=.
    exists (ts ++ ts0).
    by resolve_weaken.
Qed.

Lemma Loop_typing: forall C tb es tn tm,
    be_typing C [::BI_loop tb es] (Tf tn tm) ->
    exists ts ts1 ts2, expand_t C tb = Some (Tf ts1 ts2) /\ tn = ts ++ ts1 /\ tm = ts ++ ts2 /\
               be_typing (upd_label C ([::ts1] ++ (tc_labels C))) es (Tf ts1 ts2).
Proof.
  intros ????? HType.
  gen_ind_subst HType => //=.
  - by exists nil, tn0, tm0; eauto.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [ts0 [ts1 [ts2 [? [? [??]]]]]]; subst => //=.
    exists (ts ++ ts0).
    by resolve_weaken.
Qed.

Lemma Branch_typing: forall n C t1s t2s,
    be_typing C [::BI_br n] (Tf t1s t2s) ->
    exists ts ts0, lookup_N C.(tc_labels) n = Some ts /\
               t1s = ts0 ++ ts.
Proof.
  intros ???? HType.
  gen_ind_subst HType => //=.
  - by do 2 eexists; eauto.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [ts0 [ts' [? ?]]]; subst => //=.
    exists ts0, (ts ++ ts').
    by resolve_weaken.
Qed.

Lemma Return_typing: forall C t1s t2s,
    be_typing C [::BI_return] (Tf t1s t2s) ->
    exists ts ts', t1s = ts' ++ ts /\ tc_return C = Some ts.
Proof.
  intros ??? HType.
  gen_ind_subst HType => //=.
  - by do 2 eexists; eauto.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [ts0 [ts' [? ?]]]; subst => //=.
    exists ts0, (ts ++ ts').
    by resolve_weaken.
Qed.

Lemma Call_typing: forall j C t1s t2s,
    be_typing C [::BI_call j] (Tf t1s t2s) ->
    exists ts t1s' t2s',
    lookup_N (tc_funcs C) j = Some (Tf t1s' t2s') /\
                         t1s = ts ++ t1s' /\
                         t2s = ts ++ t2s'.
Proof.
  intros ???? HType.
  gen_ind_subst HType => //=.
  - by exists nil; do 2 eexists; eauto.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [ts0 [ts1' [ts2' [?[??]]]]]; subst => //=.
    exists (ts ++ ts0), ts1', ts2'.
    by resolve_weaken.
Qed.

Lemma Call_indirect_typing: forall x y C t1s t2s,
    be_typing C [::BI_call_indirect x y] (Tf t1s t2s) ->
    exists tn tm tabtype ts,
      lookup_N (tc_tables C) x = Some tabtype /\
        tt_elem_type tabtype = T_funcref /\
        lookup_N (tc_types C) y = Some (Tf tn tm) /\
        t1s = ts ++ tn ++ [::T_num T_i32] /\ t2s = ts ++ tm.
Proof.
  intros ????? HType.
  gen_ind_subst HType => //=.
  - by do 3 eexists; exists nil; eauto.
  - by resolve_compose Econs HType1 IHHType2.
  - edestruct IHHType as [ts0 [ts1' [tabt [ts2' [?[?[?[??]]]]]]]]; subst => //=.
    exists ts0, ts1', tabt, (ts ++ ts2').
    by resolve_weaken.
Qed.

(** A helper tactic for proving [composition_typing_single]. **)
Ltac auto_prove_bet:=
  repeat lazymatch goal with
  | H: _ |- exists t3s, be_typing _ [::] (Tf ?tx _) /\ _ =>
    try exists tx; try eauto
  | H: _ |- _ /\ _ =>
    split => //=; try eauto
  | H: _ |- be_typing _ [::] (Tf ?es ?es) =>
    apply bet_weakening_empty_both; try by []
  end.

Lemma be_composition_typing_single: forall C es1 e t1s t2s,
    be_typing C (es1 ++ [::e]) (Tf t1s t2s) ->
    exists t3s, be_typing C es1 (Tf t1s t3s) /\
           be_typing C [::e] (Tf t3s t2s).
Proof.
  move => C es1 e t1s t2s HType.
  gen_ind_subst HType; extract_listn; auto_prove_bet.
  + by destruct es1 => //=.
  + apply concat_cancel_last in Ecat as [-> ->].
    by exists t2s.
  + edestruct IHHType as [t3s [??]]; eauto; subst.
    exists (ts ++ t3s).
    by split; apply bet_weakening.
Qed.

Lemma be_composition_typing: forall C es1 es2 t1s t2s,
    be_typing C (es1 ++ es2) (Tf t1s t2s) ->
    exists t3s, be_typing C es1 (Tf t1s t3s) /\
           be_typing C es2 (Tf t3s t2s).
Proof.
  move => C es1 es2.
  move: es1.
  induction es2 using List.rev_ind; move => es1 t1s t2s HType.
  - rewrite cats0 in HType.
    exists t2s.
    repeat split => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - rewrite catA in HType.
    apply be_composition_typing_single in HType as [ts3 [Hbet1 Hbet2]].
    apply IHes2 in Hbet1 as [ts3' [Hbet3 Hbet4]].
    exists ts3'.
    repeat split => //.
    by eapply bet_composition; eauto.
Qed.

Lemma bet_composition': forall C es1 es2 t1s t2s t3s,
    be_typing C es1 (Tf t1s t2s) ->
    be_typing C es2 (Tf t2s t3s) ->
    be_typing C (es1 ++ es2) (Tf t1s t3s).
Proof.
  move => C es1 es2.
  move: es1.
  induction es2 using List.rev_ind; move => es1 t1s t2s t3s Hbet1 Hbet2.
  - apply empty_typing in Hbet2; by rewrite cats0; subst.
  - apply be_composition_typing in Hbet2 as [ts3 [Hbet3 Hbet4]].
    rewrite catA. eapply bet_composition; last by eauto.
    by eapply IHes2; eauto.
Qed.

Lemma bet_composition_front: forall C e es t1s t2s t3s,
    be_typing C [::e] (Tf t1s t2s) ->
    be_typing C es (Tf t2s t3s) ->
    be_typing C (e :: es) (Tf t1s t3s).
Proof.
  intros.
  rewrite - cat1s.
  by eapply bet_composition'; eauto.
Qed.

(*
Lemma Const_list_typing: forall C vs t1s t2s,
    be_typing C (v_to_b_list vs) (Tf t1s t2s) ->
    t2s = t1s ++ (map typeof vs).
Proof.
  move => C vs.
  induction vs => //=; move => t1s t2s HType.
  - apply empty_typing in HType. subst. by rewrite cats0.
  - rewrite -cat1s in HType.
    rewrite -cat1s.
    apply be_composition_typing in HType as [ts3 [Hbet1 Hbet2]].
    apply BI_const_typing in Hbet1.
    apply IHvs in Hbet2.
    subst.
    by repeat rewrite catA.
Qed.

Lemma Const_list_typing_empty: forall C vs,
    be_typing C (to_b_list (v_to_e_list vs)) (Tf [::] (vs_to_vts vs)).
Proof.
  move => C.
  induction vs => //=.
  rewrite - cat1s.
  replace (typeof a :: vs_to_vts vs) with ([::typeof a] ++ vs_to_vts vs) => //.
  eapply bet_composition'; eauto.
  by apply bet_weakening_empty_1.
Qed.
*)

End Typing_inversion_be.

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
  | H: be_typing _ [:: BI_const_num _] _ |- _ =>
    apply BI_const_num_typing in H; subst
  | H: be_typing _ [:: BI_const_vec _] _ |- _ =>
    apply BI_const_vec_typing in H; subst
  | H: be_typing _ [:: BI_const_num _; BI_const_num _] _ |- _ =>
    apply BI_const_num2_typing in H; subst
  | H: be_typing _ [:: BI_const_num _; BI_const_num _; BI_const_num _] _ |- _ =>
    apply BI_const_num3_typing in H; subst
  | H: be_typing _ [::BI_unop _ _] _ |- _ =>
    let ts := fresh "ts_unop" in
    let H1 := fresh "H1_unop" in
    let H2 := fresh "H2_unop" in
    apply Unop_typing in H; destruct H as [H1 [ts H2]]; subst
  | H: be_typing _ [::BI_binop _ _] _ |- _ =>
    let ts := fresh "ts_binop" in
    let H1 := fresh "H1_binop" in
    let H2 := fresh "H2_binop" in
    apply Binop_typing in H; destruct H as [H1 [ts H2]]; subst
  | H: be_typing _ [::BI_testop _ _] _ |- _ =>
    let ts := fresh "ts_testop" in
    let H1 := fresh "H1_testop" in
    let H2 := fresh "H2_testop" in
    let H3 := fresh "H3_testop" in
    apply Testop_typing in H; destruct H as [ts [H1 [H2 H3]]]; subst
  | H: be_typing _ [::BI_relop _ _] _ |- _ =>
    let ts := fresh "ts_relop" in
    let H1 := fresh "H1_relop" in
    let H2 := fresh "H2_relop" in
    apply Relop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::BI_cvtop _ _ _ _] _ |- _ =>
    let ts := fresh "ts_cvtop" in
    let H1 := fresh "H1_cvtop" in
    let H2 := fresh "H2_cvtop" in
    let H3 := fresh "H3_cvtop" in
    apply Cvtop_typing in H; destruct H as [ts [H1 [H2 H3]]]; subst
  | H: be_typing _ [::BI_nop] _ |- _ =>
    apply Nop_typing in H; destruct H; subst
  | H: be_typing _ [::BI_drop] _ |- _ =>
    apply Drop_typing in H; destruct H; subst
  | H: be_typing _ [::BI_select] _ |- _ =>
    let ts := fresh "ts_select" in
    let t := fresh "t_select" in
    let H1 := fresh "H1_select" in
    let H2 := fresh "H2_select" in
    let H3 := fresh "H3_select" in
    apply Select_typing in H; destruct H as [ts [t [H1 [H2 H3]]]]; subst
  | H: be_typing _ [::BI_if _ _ _] _ |- _ =>
    let ts := fresh "ts_if" in
    let ts1 := fresh "ts1_if" in
    let ts2 := fresh "ts2_if" in
    let Hexpand := fresh "Hexpand_if" in
    let H1 := fresh "H1_if" in
    let H2 := fresh "H2_if" in
    let H3 := fresh "H3_if" in
    let H4 := fresh "H4_if" in
    apply If_typing in H; destruct H as [ts [ts1 [ts2 [Hexpand [H1 [H2 [H3 H4]]]]]]]; subst
  | H: be_typing _ [::BI_br_if _] _ |- _ =>
    let ts := fresh "ts_brif" in
    let ts' := fresh "ts'_brif" in
    let H1 := fresh "H1_brif" in
    let H2 := fresh "H2_brif" in
    let H3 := fresh "H3_brif" in
    apply Br_if_typing in H; destruct H as [ts [ts' [H1 [H2 H3]]]]; subst
  | H: be_typing _ [::BI_br_table _ _] _ |- _ =>
    let ts := fresh "ts_brtable" in
    let ts' := fresh "ts'_brtable" in
    let H1 := fresh "H1_brtable" in
    let H2 := fresh "H2_brtable" in
    apply Br_table_typing in H; destruct H as [ts [ts' [H1 H2]]]; subst
  | H: be_typing _ [::BI_local_tee _] _ |- _ =>
    let ts := fresh "ts_teelocal" in
    let t := fresh "t_teelocal" in
    let H1 := fresh "H1_teelocal" in
    let H2 := fresh "H2_teelocal" in
    let H3 := fresh "H3_teelocal" in
    apply Tee_local_typing in H; destruct H as [ts [t [H1 [H2 H3]]]]; subst
  | H: be_typing _ [::BI_local_get _] _ |- _ =>
    let ts := fresh "ts_getlocal" in
    let H1 := fresh "H1_getlocal" in
    let H2 := fresh "H2_getlocal" in
    apply Get_local_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::BI_local_set _] _ |- _ =>
    let ts := fresh "ts_setlocal" in
    let H1 := fresh "H1_setlocal" in
    let H2 := fresh "H2_setlocal" in
    apply Set_local_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::BI_global_get _] _ |- _ =>
    let ts := fresh "ts_getglobal" in
    let H1 := fresh "H1_getglobal" in
    let H2 := fresh "H2_getglobal" in
    apply Get_global_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::BI_global_set _] _ |- _ =>
    let g := fresh "g_setglobal" in
    let t := fresh "t_setglobal" in
    let H1 := fresh "H1_setglobal" in
    let H2 := fresh "H2_setglobal" in
    let H3 := fresh "H3_setglobal" in
    let H4 := fresh "H4_setglobal" in
    apply Set_global_typing in H; destruct H as [g [t [H1 [H2 [H3 H4]]]]]; subst
  | H: be_typing _ [::BI_load _ _ _ _] _ |- _ =>
    let ts := fresh "ts_load" in
    let H1 := fresh "H1_load" in
    let H2 := fresh "H2_load" in
    let H3 := fresh "H3_load" in
    let H4 := fresh "H4_load" in
    apply Load_typing in H; destruct H as [ts [H1 [H2 [H3 H4]]]]; subst
  | H: be_typing _ [::BI_store _ _ _ _] _ |- _ =>
    let H1 := fresh "H1_store" in
    let H2 := fresh "H2_store" in
    let H3 := fresh "H3_store" in
    apply Store_typing in H; destruct H as [H1 [H2 H3]]; subst
  | H: be_typing _ [::BI_memory_size] _ |- _ =>
    let H1 := fresh "H1_memorysize" in
    let H2 := fresh "H2_memorysize" in
    apply Memory_size_typing in H; destruct H as [H1 H2]; subst
  | H: be_typing _ [::BI_memory_grow] _ |- _ =>
    let ts := fresh "ts_growmemory" in
    let H1 := fresh "H1_growmemory" in
    let H2 := fresh "H2_growmemory" in
    let H3 := fresh "H3_growmemory" in
    apply Memory_grow_typing in H; destruct H as [ts [H1 [H2 H3]]]; subst
  | H: be_typing _ [::BI_block _ _] _ |- _ =>
    let ts := fresh "ts_block" in
    let ts1 := fresh "ts1_block" in
    let ts2 := fresh "ts2_block" in
    let H1 := fresh "H1_block" in
    let H2 := fresh "H2_block" in
    let H3 := fresh "H3_block" in
    apply Block_typing in H; destruct H as [ts [ts1 [ts2 [Hexpand [H1 [H2 H3]]]]]]; subst
  | H: be_typing _ [::BI_loop _ _] _ |- _ =>
    let ts := fresh "ts_loop" in
    let ts1 := fresh "ts1_loop" in
    let ts2 := fresh "ts2_loop" in
    let H1 := fresh "H1_loop" in
    let H2 := fresh "H2_loop" in
    let H3 := fresh "H3_loop" in
    apply Loop_typing in H; destruct H as [ts [ts1 [ts2 [Hexpand [H1 [H2 H3]]]]]]; subst
  | H: be_typing _ [::BI_br _] _ |- _ =>
    let ts := fresh "ts_br" in
    let ts0 := fresh "ts0_br" in
    let H1 := fresh "H1_br" in
    let H2 := fresh "H2_br" in
    apply Branch_typing in H; destruct H as [ts [ts0 [H1 H2]]]; subst
  | H: be_typing _ [::BI_return] _ |- _ =>
    let ts := fresh "ts_return" in
    let ts0 := fresh "ts0_return" in
    let H1 := fresh "H1_return" in
    let H2 := fresh "H2_return" in
    apply Return_typing in H; destruct H as [ts [ts0 [H1 H2]]]; subst
  | H: be_typing _ [::BI_call _] _ |- _ =>
    let ts := fresh "ts_call" in
    let ts1' := fresh "ts1'_call" in
    let ts2' := fresh "ts2'_call" in
    let H1 := fresh "H1_call" in
    let H2 := fresh "H2_call" in
    let H3 := fresh "H3_call" in
    apply Call_typing in H; destruct H as [ts [ts1' [ts2' [H1 [H2 H3]]]]]; subst
 (* | H: be_typing _ (to_b_list (v_to_e_list _)) _ |- _ =>
    apply Const_list_typing in H *)
  | H: be_typing _ [::BI_call_indirect _ _] _ |- _ =>
    let ts := fresh "ts_callindirect" in
    let ts1' := fresh "ts1'_callindirect" in
    let tabt := fresh "tabt_callindirect" in
    let ts2' := fresh "ts2'_callindirect" in
    let H1 := fresh "H1_callindirect" in
    let H2 := fresh "H2_callindirect" in
    let H3 := fresh "H3_callindirect" in
    let H4 := fresh "H4_callindirect" in
    let H5 := fresh "H5_callindirect" in
    apply Call_indirect_typing in H; destruct H as [ts [ts1' [tabt [ts2' [H1 [H2 [H3 [H4 H5]]]]]]]]; subst
  | H: be_typing _ (_ ++ _) _ |- _ =>
    let ts3 := fresh "ts3_comp" in
    let H1 := fresh "H1_comp" in
    let H2 := fresh "H2_comp" in
    apply be_composition_typing in H; destruct H as [ts3 [H1 H2]]
  | H: be_typing _ [::_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: be_typing _ [::_;_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: be_typing _ [::_;_;_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: _ ++ [::_] = _ ++ [::_] |- _ =>
    apply concat_cancel_last in H; destruct H; subst
  | H: _ ++ [::_] = _ ++ _ ++ [::_] |- _ =>
    rewrite catA in H; apply concat_cancel_last in H; destruct H; subst
  | H: _ ++ _ ++ [::_] = _ ++ [::_] |- _ =>
    rewrite catA in H; apply concat_cancel_last in H; destruct H; subst
  end.

Section Typing_inversion_e.

Variable host_function : eqType.

Let store_record := store_record host_function.
Let funcinst := funcinst host_function.
Let e_typing := @e_typing host_function.
Let inst_typing := @inst_typing host_function.

Lemma e_composition_typing_single: forall s C es1 e t1s t2s,
    e_typing s C (es1 ++ [::e]) (Tf t1s t2s) ->
    exists t3s, e_typing s C es1 (Tf t1s t3s) /\
           e_typing s C [::e] (Tf t3s t2s).
Proof.
  move => s C es1 es2 t1s t2s HType.
  gen_ind_subst HType; extract_listn.
  - (* basic *)
    apply b_e_elim in H3. destruct H3. subst.
    rewrite to_b_list_concat in H.
    invert_be_typing.
    apply basic_concat in H1. move/andP in H1. destruct H1.
    exists ts3_comp.
    by repeat split => //=; apply ety_a' => //=.
  - (* composition *)
    apply concat_cancel_last in H2. destruct H2. subst.
    by exists t2s.
  - (* weakening *)
    edestruct IHHType as [ts3 [Het1 Het2]]; eauto.
    exists (ts ++ ts3).
    by repeat split => //; apply ety_weakening.
  - (* Trap *)
    exists t1s.
    repeat split => //=.
    + apply ety_a' => //. apply bet_weakening_empty_both. by apply bet_empty.
    + by apply ety_trap.
  - (* Ref_extern *)
    exists nil; repeat split => //.
    + by apply ety_a' => //; apply bet_empty.
    + by econstructor.
  - (* Ref *)
    exists nil; repeat split => //.
    + by apply ety_a' => //; apply bet_empty.
    + by eapply ety_ref; eauto.
  - (* Invoke *)
    exists t1s. repeat split => //=.
    + apply ety_a' => //. apply bet_weakening_empty_both. by apply bet_empty.
    + by eapply ety_invoke; eauto.
  - (* Label *)
    exists nil. repeat split => //=.
    + by apply ety_a' => //; apply bet_empty.
    + by eapply ety_label; eauto.
  - (* Frame *)
    exists nil. repeat split => //=.
    + by apply ety_a' => //; apply bet_empty.
    + by apply ety_frame.
Qed.

Lemma e_composition_typing: forall s C es1 es2 t1s t2s,
    e_typing s C (es1 ++ es2) (Tf t1s t2s) ->
    exists t3s, e_typing s C es1 (Tf t1s t3s) /\
           e_typing s C es2 (Tf t3s t2s).
Proof.
  move => s C es1 es2.
  move: es1.
  induction es2 using List.rev_ind; move => es1 ts1 ts2 HType.
  - rewrite cats0 in HType.
    exists ts2.
    repeat split => //=.
    apply ety_a' => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - rewrite catA in HType.
    apply e_composition_typing_single in HType as [ts3 [Het1 Het2]].
    apply IHes2 in Het1 as [ts3' [Het3 Het4]].
    exists ts3'.
    repeat split => //.
    by eapply ety_composition; eauto.
Qed.

Lemma et_composition': forall s C es1 es2 t1s t2s t3s,
    e_typing s C es1 (Tf t1s t2s) ->
    e_typing s C es2 (Tf t2s t3s) ->
    e_typing s C (es1 ++ es2) (Tf t1s t3s).
Proof.
  move => s C es1 es2.
  move: es1.
  induction es2 using List.rev_ind; move => es1 ts1 ts2 ts3 Het1 Het2.
  - apply et_to_bet in Het2 => //. apply empty_typing in Het2.
    rewrite cats0.
    by subst.
  - apply e_composition_typing in Het2 as [ts3' [Het3 Het4]].
    rewrite catA. eapply ety_composition => //=.
    eapply IHes2; eauto.
    by eauto.
Qed.

Lemma Label_typing: forall s C n es0 es ts1 ts2,
    e_typing s C [::AI_label n es0 es] (Tf ts1 ts2) ->
    exists ts ts2', ts2 = ts1 ++ ts2' /\
                    e_typing s C es0 (Tf ts ts2') /\
                    e_typing s (upd_label C ([::ts] ++ (tc_labels C))) es (Tf [::] ts2') /\
                    length ts = n.
Proof.
  move => s C n es0 es ts1 ts2 HType.
  gen_ind_subst HType.
  - (* ety_a *)
    assert (es_is_basic (operations.to_e_list bes)) as Hb; first by apply to_e_list_basic.
    rewrite Econs in Hb. by basic_inversion.
  - (* ety_composition *)
    apply extract_list1 in Econs. destruct Econs. subst.
    apply et_to_bet in HType1 => //.
    simpl in HType1. apply empty_typing in HType1. subst.
    by eapply IHHType2 => //.
  - (* ety_weakening *)
    edestruct IHHType as [ts1 [ts2 [H2 [H3 H4]]]]; eauto; subst.
    by exists ts1, ts2; try rewrite catA.     
  - (* ety_label *)
    by exists ts, ts2.
Qed.

Lemma Frame_typing: forall s C n f es t1s t2s,
    e_typing s C [::AI_frame n f es] (Tf t1s t2s) ->
    exists ts, t2s = t1s ++ ts /\
               thread_typing s (Some ts) (f, es) ts /\
               length ts = n.
Proof.
  move => s C n f es ts1 ts2 HType.
  gen_ind_subst HType.
  - (* ety_a *)
    assert (es_is_basic (operations.to_e_list bes)) as Hb; first by apply to_e_list_basic.
    rewrite Econs in Hb. by basic_inversion.
  - (* ety_composition *)
    apply extract_list1 in Econs. destruct Econs. subst.
    apply et_to_bet in HType1 => //.
    simpl in HType1. apply empty_typing in HType1. subst.
    by eapply IHHType2 => //.
  - (* ety_weakening *)
    edestruct IHHType as [ts2 [??]]; eauto. subst. 
    exists ts2.
    repeat split => //=.
    by rewrite catA.
  - (* ety_frame *)
    by exists ts2.
Qed.

End Typing_inversion_e.

Ltac invert_e_typing :=
  repeat lazymatch goal with
  | H: @e_typing _ _ _ (_ ++ _) _ |- _ =>
    let ts3 := fresh "ts3_comp" in
    let H1 := fresh "H1_comp" in
    let H2 := fresh "H2_comp" in
    apply e_composition_typing in H;
    destruct H as [ts3 [H1 H2]]; subst
  | H: @e_typing _ _ _ [::AI_label _ _ _] _ |- _ =>
    let ts := fresh "ts_label" in
    let ts1 := fresh "ts1_label" in
    let H1 := fresh "H1_label" in
    let H2 := fresh "H2_label" in
    let H3 := fresh "H3_label" in
    let H4 := fresh "H4_label" in
    eapply Label_typing in H; eauto;
    destruct H as [ts [ts1 [H1 [H2 [H3 H4]]]]]; subst
  | H: @e_typing _ _ _ [::AI_frame _ _ _] _ |- _ =>
    let ts := fresh "ts_frame" in
    let H1 := fresh "H1_frame" in
    let H2 := fresh "H2_frame" in
    let H3 := fresh "H3_frame" in
    eapply Frame_typing in H; eauto;
    destruct H as [ts [H1 [H2 H3]]]; subst
  end.

Section Typing_inversion_e.

Variable host_function : eqType.

Let store_record := store_record host_function.
Let funcinst := funcinst host_function.
Let funcinst_valid := @funcinst_valid host_function.
Let e_typing := @e_typing host_function.
Let inst_typing := @inst_typing host_function.

Ltac invert_e_typing' :=
  unfold e_typing in *; invert_e_typing.

Hint Transparent e_typing: core.

Let host := host host_function.

Variable host_moduleinst : host.

Let host_state := host_state host_moduleinst.

Let reduce : host_state -> store_record -> frame -> seq administrative_instruction ->
             host_state -> store_record -> frame -> seq administrative_instruction -> Prop
  := @reduce _ _.

Let s_globals : store_record -> seq globalinst := @s_globals _.
Let s_mems : store_record -> seq meminst := @s_mems _.
Let cl_type : funcinst -> function_type := @cl_type _.
Let store_extension: store_record -> store_record -> Prop := @store_extension _.

Lemma Invoke_func_typing: forall s C a t1s t2s,
    e_typing s C [::AI_invoke a] (Tf t1s t2s) ->
    exists cl, lookup_N s.(s_funcs) a = Some cl.
Proof.
  move => s C a t1s t2s HType.
  gen_ind_subst HType => //.
  - by destruct bes => //=.
  - apply extract_list1 in Econs. destruct Econs. subst.
    by eapply IHHType2 => //=.
  - by eapply IHHType => //=.
  - unfold ext_func_typing in H; remove_bools_options.
    by exists f.
Qed.

Lemma Invoke_func_native_typing: forall s C a ts1 ts2,
    e_typing s C [::AI_invoke a] (Tf ts1 ts2) ->
    exists ts tn tm,
      ext_func_typing s a = Some (Tf tn tm) /\
        ts1 = ts ++ tn /\
        ts2 = ts ++ tm.
Proof.
  move => s C a ts1 ts2 HType.
  gen_ind_subst HType => //.
  - by destruct bes => //=.
  - apply extract_list1 in Econs. destruct Econs. subst.
    apply et_to_bet in HType1 => //=.
    apply empty_typing in HType1. subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType as [ts' [tn [tm [? [??]]]]]; eauto. subst.
    exists (ts ++ ts'), tn, tm.
    by repeat split => //; rewrite catA.
  - exists nil; by repeat eexists.
Qed.

Lemma store_typed_cl_typed: forall s n f,
    lookup_N (s_funcs s) n = Some f ->
    store_typing s ->
    funcinst_valid s f.
Proof.
  move => s n f HN HST.
  unfold store_typing in HST.
  destruct s => //=.
  remove_bools_options.
  simpl in HN.
  destruct HST.
  rewrite -> List.Forall_forall in H.
  apply List.nth_error_In in HN.
  by apply H in HN.
Qed.

(* inst_typing inversion *)
Lemma inst_t_context_local_empty: forall s i C,
    inst_typing s i = Some C ->
    tc_locals C = [::].
Proof.
  move => s i C HInstType.
  unfold inst_typing, typing.inst_typing in HInstType.
  destruct i => //=.
  by remove_bools_options.
Qed.

Lemma inst_t_context_label_empty: forall s i C,
    inst_typing s i = Some C ->
    tc_labels C = [::].
Proof.
  move => s i C HInstType.
  unfold inst_typing, typing.inst_typing in HInstType.
  destruct i => //=.
  by remove_bools_options.
Qed.

Lemma global_type_reference: forall s i j C v t,
    inst_typing s i = Some C ->
    sglob_val s i j = Some v ->
    option_map tg_t (lookup_N (tc_globals C) j) = Some t ->
    typeof v = t.
Proof.
  move => s i j C v t HInstType Hvref Htref.
  unfold sglob_val in Hvref.
  unfold sglob in Hvref.
  unfold sglob_ind in Hvref.
  destruct (List.nth_error i.(inst_globs) j) eqn:Hi => //=.
  remove_bools_options.
  unfold option_bind in Hoption0.
  remove_bools_options.
  unfold inst_typing in HInstType.
  destruct i => //=. destruct C => //=.
  destruct tc_locals => //=. destruct tc_labels => //=. destruct tc_return => //=.
  move/andP in HInstType. destruct HInstType.
  remove_bools_options.
  eapply all2_projection in H2; eauto.
  unfold globals_agree in H2. move/andP in H2. destruct H2.
  remove_bools_options.
  simpl in Hi. simpl in Hoption.
  unfold global_agree in H6.
  by remove_bools_options.
Qed.

Lemma func_context_store: forall s i C j x,
    inst_typing s i C ->
    j < length (tc_funcs C) ->
    List.nth_error (tc_funcs C) j = Some x ->
    exists a, List.nth_error i.(inst_funcs) j = Some a.
Proof.
  move => s i C j x HIT HLength HN.
  unfold sfunc. unfold operations.sfunc. unfold option_bind.
  unfold sfunc_ind.
  unfold inst_typing, typing.inst_typing in HIT.
  destruct i => //=. destruct C => //=.
  destruct tc_locals => //=. destruct tc_labels => //=. destruct tc_return => //=.
  remove_bools_options.
  remember H3 as H4. clear HeqH4.
  apply all2_size in H3.
  repeat rewrite -length_is_size in H3.
  simpl in HLength.
  rewrite -H3 in HLength.
  move/ltP in HLength.
  apply List.nth_error_Some in HLength.
  destruct (List.nth_error inst_funcs j) eqn:HN1 => //=.
  by eexists.
Qed.

Lemma glob_context_store: forall s i C j g,
    inst_typing s i C ->
    j < length (tc_globals C) ->
    List.nth_error (tc_globals C) j = Some g ->
    sglob s i j <> None.
Proof.
  move => s i C j g HIT HLength HN.
  unfold sglob. unfold operations.sglob. unfold option_bind.
  unfold sglob_ind.
  unfold inst_typing, typing.inst_typing in HIT.
  destruct i => //=. destruct C => //=.
  destruct tc_locals => //=. destruct tc_labels => //=. destruct tc_return => //=.
  remove_bools_options.
  remember H2 as H4. clear HeqH4.
  apply all2_size in H2.
  repeat rewrite -length_is_size in H2.
  simpl in HLength.
  rewrite -H2 in HLength.
  move/ltP in HLength.
  apply List.nth_error_Some in HLength.
  destruct (List.nth_error inst_globs j) eqn:HN1 => //=.
  apply List.nth_error_Some.
  unfold globals_agree in H4.
  eapply all2_projection in H4; eauto.
  remove_bools_options.
  by move/ltP in H4.
Qed.

Lemma mem_context_store: forall s i C,
    inst_typing s i C ->
    tc_mems C <> [::] ->
    exists n, smem_ind s i = Some n /\
              List.nth_error (s_mems s) n <> None.
Proof.
  move => s i C HIT HMemory.
  unfold inst_typing, typing.inst_typing in HIT.
  destruct i => //=. destruct C => //=.
  destruct tc_locals => //=. destruct tc_labels => //=. destruct tc_return => //=.
  remove_bools_options.
  simpl in HMemory. unfold smem_ind. simpl.
  remember H0 as H4. clear HeqH4.
  apply all2_size in H0.
  destruct inst_memory => //=; first by destruct tc_mems.
  exists m. split => //.
  destruct tc_mems => //.
  simpl in H4.
  unfold memi_agree in H4.
  unfold s_mems.
  by remove_bools_options.
Qed.

Lemma store_typing_stabaddr: forall s f C c a,
  stab_addr s f c = Some a ->
  inst_typing s f.(f_inst) C ->
  store_typing s ->
  exists cl, List.nth_error s.(s_funcs) a = Some cl.
Proof.
  move => s f C c a HStab HIT HST.
  unfold inst_typing, typing.inst_typing in HIT.
  unfold store_typing, tab_agree, tabcl_agree in HST.
  unfold stab_addr in HStab.
  destruct s => //=. destruct f => //=. destruct f_inst. destruct f_inst. destruct C => //=.
  destruct tc_locals => //=. destruct tc_labels => //=. destruct tc_return => //=.
  remove_bools_options.
  simpl in *. destruct inst_tab0 => //=.
  unfold stab_index in HStab. unfold option_bind in HStab.
  remove_bools_options.
  subst. simpl in *.
  destruct tc_tables => //=.
  remove_bools_options.
  destruct HST.
  destruct H5.
  rewrite -> List.Forall_forall in H5.
  assert (HIN1: List.In t0 s_tables).
  { by apply List.nth_error_In in Hoption0. }
  apply H5 in HIN1. destruct HIN1 as [HIN1 _].
  rewrite -> List.Forall_forall in HIN1.
  assert (HIN2: List.In (Some a) (table_data t0)).
  { by apply List.nth_error_In in Hoption. }
  apply HIN1 in HIN2.
  move/ltP in HIN2.
  apply List.nth_error_Some in HIN2.
  destruct (List.nth_error s_funcs a) eqn:HNth => //.
  by eexists.
Qed.

Ltac auto_basic :=
  repeat lazymatch goal with
  | |- es_is_basic [::AI_basic _; AI_basic _; AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- es_is_basic [::AI_basic _; AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- es_is_basic [::AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- es_is_basic [::AI_basic _] =>
    simpl; repeat split
  | |- operations.es_is_basic [::AI_basic _; AI_basic _; AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- operations.es_is_basic [::AI_basic _; AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- operations.es_is_basic [::AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- operations.es_is_basic [::AI_basic _] =>
    simpl; repeat split
  | |- operations.e_is_basic (AI_basic ?e) =>
    by unfold e_is_basic; exists e
end.

Lemma Lfilled_break_typing: forall n m k (lh: lholed n) vs LI ts s C t2s tss,
    e_typing s (upd_label C (tss ++ [::ts] ++ tc_labels C)) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfill lh (vs ++ [::AI_basic (BI_br m)]) = LI ->
    length tss = k ->
    n + k = m ->
    e_typing s C vs (Tf [::] ts).
Proof.
  move => n m k lh vs LI ts s C ts2 tss HType HConst HLength HLF <- HSum.
  subst m.
  apply const_es_exists in HConst as [xs ->].
  generalize dependent ts.
  move: ts2.
  generalize dependent LI.
  move: lh tss.
  elim.
  - move => vs es tss LI /= <- ts2 ts HType HTSSLength.
    rewrite add0n in HType.
    repeat rewrite catA in HType.
    invert_e_typing'.
    apply et_to_bet in H2_comp0; last by auto_basic.
    apply et_to_bet in H1_comp; last by (apply const_list_is_basic; apply v_to_e_const).
    apply et_to_bet in H2_comp1; last by (apply const_list_is_basic; apply v_to_e_const).
    simpl in *.
    invert_be_typing; simpl in *; subst.
    unfold plop2 in H2_br. simpl in H2_br. move/eqP in H2_br.
    rewrite list_nth_prefix in H2_br.
    injection H2_br as <-.
    apply concat_cancel_last_n in H2_comp1.
    + apply ety_a'; first (by apply const_list_is_basic, v_to_e_const) => //.
      remove_bools_options; subst.
      by apply Const_list_typing_empty.
    + repeat rewrite length_is_size in HTSSLength.
      rewrite size_map in HTSSLength.
      by rewrite size_map.
  - move => k0 vs m es lh' IH es' tss LI /= <- ts2 ts HType HTSSLength.
    rewrite - (cat1s _ es') in HType.
    invert_e_typing'.
    simpl in *.
    rewrite upd_label_overwrite -cat1s catA in H3_label.
    remember ([::ts_label] ++ tss) as tss'.
    replace (k0.+1+length tss) with (k0 + length tss') in H3_label; first by eapply IH; eauto => //=.
    subst tss' => /=. by rewrite addSn addnS.
Qed.

Lemma Lfilled_return_typing {k}: forall (lh: lholed k) vs LI ts s C0 C t2s,
    e_typing s C0 LI (Tf [::] t2s) ->
    tc_return C = tc_return C0 ->
    const_list vs ->
    length ts = length vs ->
    lfill lh (vs ++ [::AI_basic BI_return]) = LI ->
    Some ts = tc_return C ->
    e_typing s C vs (Tf [::] ts).
Proof.
  induction lh; move => vs LI ts s C0 C t2s HType Heqret HConst HLength /=HLF HReturn; subst => //=.
  - invert_e_typing'.
    apply et_to_bet in H2_comp; auto_basic.
    apply Return_typing in H2_comp as [ts3 [t1s3 [-> Hret]]]. 

    assert (ts = ts3). { rewrite -HReturn Hret in Heqret. by inversion Heqret. }
    subst ts3. clear Hret.

    (* from H11 : typing.e_typing s (upd_label C lab) vs0 (Tf [::] t3s2) *)
    (* show : t3s2 = map typeof vs0' *)
    apply et_to_bet in H1_comp; last by apply const_list_is_basic, v_to_e_const.
    apply et_to_bet in H1_comp1; last by apply const_list_is_basic.
    apply const_es_exists in HConst as [? ->].
    invert_be_typing; simpl in *; subst.

    apply concat_cancel_last_n in H1_comp1; remove_bools_options; subst.
    + apply ety_a'; first by apply const_list_is_basic; apply v_to_e_const.
      by apply Const_list_typing_empty.
    + repeat rewrite length_is_size in HLength.
      rewrite size_map in HLength.
      by rewrite size_map.
  - rewrite - cat1s in HType.
    invert_e_typing'.
    simpl in *.
    by eapply IHlh; eauto.
Qed.

Lemma Frame_return_typing {k}: forall s C vs f LI tf (lh: lholed k),
    e_typing s C [:: AI_frame (length vs) f LI] tf ->
    const_list vs ->
    lfill lh (vs ++ [::AI_basic BI_return]) = LI ->
    e_typing s C vs tf.
Proof.
  move => s C vs f LI tf lh HType HConst Hlf.
  destruct tf as [t1s t2s].
  invert_e_typing'.
  inversion H2_local as [s' f' es' ovs rs C1 C2 Hftype -> Hetype [ _ | ]]; subst => //; clear H2_local.
  apply et_weakening_empty_1.
  apply const_es_exists in HConst as [? ->].
  apply ety_a'; first by apply const_list_is_basic; apply v_to_e_const.
  eapply Lfilled_return_typing in Hetype; eauto; last by apply v_to_e_const.
  apply et_to_bet in Hetype; last by apply const_list_is_basic, v_to_e_const.
  apply Const_list_typing in Hetype; subst; simpl in *.
  by apply Const_list_typing_empty.
Qed.

End Typing_inversion_e.
