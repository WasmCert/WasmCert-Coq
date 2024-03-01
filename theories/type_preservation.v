(** Proof of preservation **)

From Wasm Require Export common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program.Equality NArith ZArith_base.
From Wasm Require Export typing opsem properties contexts typing_inversion tactic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Context `{ho: host}.
  
Lemma app_binop_type_preserve: forall op v1 v2 v,
    app_binop op v1 v2 = Some v ->
    typeof_num v = typeof_num v1.
Proof.
  move => op v1 v2 v.
  by elim: op; elim: v1; elim: v2 => //=; move => c1 c2 op H; destruct op; remove_bools_options.
Qed.

Lemma eval_cvt_type_preserve: forall op t1 t2 sx v1 v2,
    cvtop_valid t2 op t1 sx ->
    typeof_num v1 = t1 ->
    eval_cvt t2 op sx v1 = Some v2 ->
    typeof_num v2 = t2.
Proof.
  move => op t1 t2 sx v1 v2 Hcvtvalid Htype Heval.
  (* Just use brute force -- probably sledgehammer in some other theorem prover *)
  destruct op, t1, t2 => //; destruct sx as [[|] |] => //; cbn in Hcvtvalid => //; destruct v1 => //; simpl in * => //; by remove_bools_options => //=; inversion Heval.
Qed.

(* Not completely agnostic now -- since reference typings are dependent on the store. *)
Lemma et_const_agnostic: forall s C C' es tf,
    const_list es ->
    e_typing s C es tf ->
    e_typing s C' es tf.
Proof.
  move => s C C' es [ts1 ts2] HConst HType.
  apply const_es_exists in HConst as [vs Hve]; subst.
  apply Values_typing_inversion in HType as [ts [-> Hvts]].
  apply et_weakening_empty_1.
  by apply et_values_typing.
Qed.

Theorem t_simple_preservation: forall s es es' C tf,
    e_typing s C es tf ->
    reduce_simple es es' ->
    e_typing s C es' tf.
Proof.
  move => s es es' C [ts1 ts2] HType HReduce.
  inversion HReduce; subst; (try by apply ety_trap); invert_e_typing; resolve_e_typing => //.
  (* Unop *)
  - by destruct op, v.
  (* Binop_success *)
  - apply app_binop_type_preserve in H.
    unfold value_num_typing.
    by rewrite H -H1.
  - (* Cvtop *)
    by eapply eval_cvt_type_preserve in H3_cvtop; eauto; subst.
  - (* If_true *)
    apply ety_weakening.
    by apply ety_a', bet_block => //=.
  - (* If_false *)
    apply ety_weakening.
    by apply ety_a', bet_block => //=.
  - (* Br *)
    eapply et_composition'; eauto.
    eapply Lfilled_break_typing with (tss := nil) => /=; eauto; last by lias.
    by apply v_to_e_const.
  - (* Br_if_true *)
    apply ety_a' => //=.
    eapply bet_br in H3_brif.
    by apply H3_brif.
  - (* Br_br_table *)
    apply ety_a' => //=.
    rewrite List.Forall_forall in H2_brtable.
    apply bet_br.
    apply H2_brtable.
    unfold lookup_N in *.
    simpl in *.
    rewrite Z_N_nat in H0.
    apply List.nth_error_In with (n := Z.to_nat (Wasm_int.Int32.unsigned c)).
    rewrite List.nth_error_app1 => //.
    apply List.nth_error_Some; by rewrite H0.
  - (* Br_br_table_oob *)
    apply ety_a' => //=.
    rewrite List.Forall_forall in H2_brtable.
    apply bet_br.
    apply H2_brtable.
    apply List.in_or_app; by right; constructor.
  - (* Frame_const *)
    inversion H2_frame; subst.
    by invert_e_typing.
  - (* Local_tee *)
    apply ety_a' => //=.
    rewrite -(cat1s ts_value).
    apply bet_weakening_empty_2.
    by constructor.
  - (* Frame_return *)
    inversion H2_frame; subst.
    eapply Lfilled_return_typing in H6; (try reflexivity); eauto; first by invert_e_typing.
    by apply v_to_e_const.
Qed.

(*
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
*)

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
  destruct a => //=; f_equal => //.
  - by destruct n.
  - by destruct v.
Qed.

(*
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
  unfold limit_match in *.
  remove_bools_options; simpl in *.
  - apply/andP; split => /=.
    { move/N.leb_spec0 in H.
      move/N.leb_spec0 in H1.
      apply/N.leb_spec0.
      by lias.
    }
    by rewrite - H0 Hoption0.
  - move/N.leb_spec0 in H.
    move/N.leb_spec0 in H1.
    rewrite Bool.andb_true_r.
    apply/N.leb_spec0.
    by lias.
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
  unfold limit_match in *.
  simpl in *.
  remove_bools_options; cbn.
  - apply/andP; split.
    { move/N.leb_spec0 in H1.
      apply/N.leb_spec0.
      by lias.
    }
    by rewrite -H0.
  - move/N.leb_spec0 in H1.
    rewrite Bool.andb_true_r.
    apply/N.leb_spec0.
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
*)

Lemma ext_func_typing_extension: forall s s' a tf,
    store_extension s s' ->
    ext_func_typing s a = Some tf ->
    ext_func_typing s' a = Some tf.
Proof.
  move => s s' a tf Hext Htype.
  unfold ext_func_typing in *.
  remove_bools_options.
  eapply store_extension_lookup_func in Hoption; eauto.
  by rewrite Hoption.
Qed.
  
Lemma ext_table_typing_extension: forall s s' a tf,
    store_extension s s' ->
    ext_table_typing s a = Some tf ->
    ext_table_typing s' a = Some tf.
Proof.
  move => s s' a tf Hext Htype.
  unfold ext_table_typing in *.
  remove_bools_options.
  eapply store_extension_lookup_table in Hoption; eauto.
  destruct Hoption as [? [Hnth Htableext]].
  rewrite Hnth.
  unfold table_extension in Htableext.
  remove_bools_options.
  by rewrite H.
Qed.

Lemma ext_mem_typing_extension: forall s s' a tf,
    store_extension s s' ->
    ext_mem_typing s a = Some tf ->
    ext_mem_typing s' a = Some tf.
Proof.
  move => s s' a tf Hext Htype.
  unfold ext_mem_typing in *.
  remove_bools_options.
  eapply store_extension_lookup_mem in Hoption; eauto.
  destruct Hoption as [? [Hnth Hmemext]].
  rewrite Hnth.
  unfold mem_extension in Hmemext.
  remove_bools_options.
  by rewrite H.
Qed.

Lemma ext_global_typing_extension: forall s s' a tf,
    store_extension s s' ->
    ext_global_typing s a = Some tf ->
    ext_global_typing s' a = Some tf.
Proof.
  move => s s' a tf Hext Htype.
  unfold ext_global_typing in *.
  remove_bools_options.
  eapply store_extension_lookup_global in Hoption; eauto.
  destruct Hoption as [? [Hnth Hglobalext]].
  rewrite Hnth.
  unfold global_extension in Hglobalext.
  remove_bools_options.
  by rewrite H.
Qed.

Lemma value_ref_typing_extension: forall s s' v t,
    store_extension s s' ->
    value_ref_typing s v = Some t ->
    value_ref_typing s' v = Some t.
Proof.
  move => s s' v t Hext Htype.
  destruct v; simpl in * => //=.
  remove_bools_options.
  eapply ext_func_typing_extension in Hoption; eauto.
  by rewrite Hoption.
Qed.
  
Lemma value_typing_extension: forall s s' v t,
    store_extension s s' ->
    value_typing s v = Some t ->
    value_typing s' v = Some t.
Proof.
  move => s s' v t Hext Htype.
  destruct v; simpl in * => //=.
  remove_bools_options.
  eapply value_ref_typing_extension in Hoption; eauto.
  by rewrite Hoption.
Qed.
  
Lemma values_typing_extension: forall s s' vs ts,
    store_extension s s' ->
    values_typing s vs = Some ts ->
    values_typing s' vs = Some ts.
Proof.
  move => s s'; elim => //=.
  move => v vs IH => //=; case.
  - move => HST Hvt => //=; by apply values_typing_length in Hvt.
  - move => t ts Hext; unfold values_typing; repeat rewrite -those_those0 => /=.
    move => Hvt.
    remove_bools_options.
    eapply value_typing_extension in Hoption; eauto.
    unfold value_typing in *.
    rewrite Hoption => /=.
    rewrite -> those_those0 in *.
    apply IH in Hoption0 => //.
    unfold values_typing in Hoption0.
    by rewrite Hoption0.
Qed.  

Lemma eleminst_typing_extension: forall s s' a a' tf,
    store_extension s s' ->
    elem_extension a a' ->
    eleminst_typing s a = Some tf ->
    eleminst_typing s' a' = Some tf.
Proof.
  move => s s' [et ei] [et' ei'] tf Hsext Hext Htype.
  unfold eleminst_typing in *.
  unfold elem_extension in *.
  move: ei' Hext.
  induction ei; move => ei' Hext; simpl in *; remove_bools_options => //.
  simpl in *.
  eapply value_ref_typing_extension in H1; eauto.
  rewrite H1 => /=.
  rewrite eq_refl => /=.
  apply IHei; first by rewrite H2.
  repeat rewrite eq_refl.
  by lias.
Qed.
  
Lemma datainst_typing_extension: forall s s' a tf,
    store_extension s s' ->
    datainst_typing s a = Some tf ->
    datainst_typing s' a = Some tf.
Proof.
  move => s s' d tf Hext Htype.
  by unfold datainst_typing in *.
Qed.

Lemma those_map_impl {T T': Type}: forall f g (l: list T) (l': list T'),
    (forall x y, f x = Some y -> g x = Some y) ->
    those (map f l) = Some l' ->
    those (map g l) = Some l'.
Proof.
  move => f g.
  setoid_rewrite <- those_those0.
  elim => //=.
  move => x l IH l' Hmap Hf.
  remove_bools_options.
  erewrite Hmap; eauto.
  by erewrite IH; eauto.
Qed.

Lemma inst_typing_extension: forall s s' i C,
    store_extension s s' ->
    inst_typing s i = Some C ->
    inst_typing s' i = Some C.
Proof.
  move => s s' i C HST HIT.
  unfold inst_typing in *.
  destruct i.
  remove_bools_options.
  erewrite those_map_impl; last (by apply Hoption); last by intros; eapply ext_func_typing_extension; eauto.
  erewrite those_map_impl; last (by apply Hoption0); last by intros; eapply ext_table_typing_extension; eauto.
  erewrite those_map_impl; last (by apply Hoption1); last by intros; eapply ext_mem_typing_extension; eauto.
  erewrite those_map_impl; last (by apply Hoption2); last by intros; eapply ext_global_typing_extension; eauto.
  erewrite those_map_impl; last (by apply Hoption3) => /=; last first.
  {
    move => a t Hn.
    cbn in Hn.
    remove_bools_options.
    unfold eleminst_typing in Hn.
    eapply store_extension_lookup_elem in Hoption5; eauto.
    destruct Hoption5 as [elem [Hnth Hext]].
    rewrite Hnth.
    by eapply eleminst_typing_extension in Hn; eauto.
  }
  erewrite those_map_impl; last (by apply Hoption4) => /=; last first.
  {
    move => a t Hn.
    cbn in Hn.
    remove_bools_options.
    eapply store_extension_lookup_data in Hoption5; eauto.
    destruct Hoption5 as [elem [Hnth Hext]].
    rewrite Hnth.
    by eapply datainst_typing_extension in Hn; eauto.
  }
  done.
Qed.

Lemma frame_typing_extension: forall s s' f C,
    store_extension s s' ->
    frame_typing s f = Some C ->
    frame_typing s' f = Some C.
Proof.
  move => s s' f C HST HIT.
  unfold frame_typing in *.
  remove_bools_options.
  eapply inst_typing_extension in Hoption; eauto.
  rewrite Hoption.
  eapply values_typing_extension in Hoption0; eauto.
  by rewrite Hoption0.
Qed.

Lemma lfilled_es_type_exists {k}: forall (lh: lholed k) es les s C tf,
    lfill lh es = les ->
    e_typing s C les tf ->
    exists lab t1s t2s, e_typing s (upd_label C lab) es (Tf t1s t2s).
Proof.
  elim.
  - move => vs es es' LI s C [ts1 ts2] <- /= Htype.
    invert_e_typing.
    exists (tc_labels C); repeat eexists => //=.
    uapply H1_comp0.
    by destruct C.
  - move => k' vs n es lh IH es' es'' LI s C [ts1 ts2] <- /= Htype.
    rewrite -cat1s in Htype.
    invert_e_typing.
    by edestruct IH; eauto.
Qed.

Lemma store_extension_e_typing: forall s s' C es tf,
    store_typing s ->
    store_typing s' ->
    store_extension s s' ->
    e_typing s C es tf ->
    e_typing s' C es tf.
Proof.
  move=> s s' C es tf HST1 HST2 Hext HType. move: s' HST1 HST2 Hext.
  eapply e_typing_ind' with (e := HType)
    (P := fun s C es tf (_ : e_typing s C es tf) => forall s',
            store_typing s ->
            store_typing s' ->
            store_extension s s' ->
            e_typing s' C es tf)
    (P0 := fun s rs th ts (_ : thread_typing s rs th ts) => forall s',
             store_typing s ->
             store_typing s' ->
             store_extension s s' ->
             thread_typing s' rs th ts); clear HType s C es tf.
  (* basic *)
  - move=> s C bes tf HType s' HST1 HST2 Hext.
    apply ety_a'; first by apply to_e_list_basic.
    replace (to_b_list (to_e_list bes)) with bes => //.
    by apply b_e_elim.
  (* composition *)
  - move=> s C bes tf r1 r2 r3 HType1 IHHType1 IH2 IHHType2 s' HST1 HST2 Hext.
    eapply ety_composition.
    + by apply IHHType1.
    + by apply IHHType2.
  (* weakening *)
  - move=> s C es tf t1s t2s HType IHHType s' HST1 HST2 Hext.
    eapply ety_weakening. by apply IHHType.
  (* trap *)
  - move=> s C tf s' HST1 HST2 Hext.
    by apply ety_trap.
  (* ref_extern *)
  - move=> s C tf s' HST1 HST2 Hext.
    by apply ety_ref_extern.
  (* ref *)
  - move=> s C a tf Hextfunc s' HST1 HST2 Hext.
    eapply ety_ref; eauto.
    by eapply ext_func_typing_extension; eauto.
  (* invoke *)
  - move=> s a C tf Hextfunc s' HST1 HST2 Hext.
    eapply ety_invoke; eauto => //.
    by eapply ext_func_typing_extension; eauto.
  (* Label *)
  - move=> s C es es' t1s t2s n HType1 IHHType1 HType2 IHHType2 E s' HST1 HST2 Hext.
    by eapply ety_label => //; eauto.
  (* Frame *)
  - move=> s C n f es ts HType IHHType E s' HST1 HST2 Hext.
    apply ety_frame => //.
    by eapply IHHType; try apply HST1 => //.
  (* Thread *)
  - move=> s f es rs ts C C' HFType HContext HType IHHType s' HST1 HST2 Hext.
    remove_bools_options.
    eapply mk_thread_typing; eauto.
    + apply/eqP.
      by eapply frame_typing_extension; eauto.
Qed.
      
Lemma glob_extension_update_nth: forall sglobs n g g',
  List.nth_error sglobs n = Some g ->
  global_extension g g' ->
  all2 global_extension sglobs (set_nth g' sglobs n g').
Proof.
  move => sglobs n.
  generalize dependent sglobs.
  induction n; move => sglobs g g' HN Hext => //=; destruct sglobs => //.
  - simpl in HN. inversion HN. subst.
    apply/andP; split => //=.
    by apply all2_global_extension_same.
  - assert ((n.+1 < length (g0 :: sglobs))%coq_nat); first by rewrite -List.nth_error_Some; rewrite HN.
    simpl.
    apply/andP. split.
    + by apply global_extension_refl. 
    + by eapply IHn; eauto.
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
    + unfold mem_extension. by apply/andP; split => //.
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
  m.(meminst_type) = m'.(meminst_type) /\ mem_length m = mem_length m'.
Proof.
  unfold write_bytes, fold_lefti.
  move => m pos str m' H.
  remove_bools_options.
  match goal with | H : ?T = _ |- _ =>
                    match T with context [List.fold_left ?f ?str ?nom] => remember (List.fold_left f str nom) as fold_res
                    end
  end.
  assert (HPreserve: mem_type_proj2_preserve (0, Some (meminst_data m)) fold_res).
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
    by inversion H1; inversion H2; subst; clear H1; clear H2.
Qed.
  
Lemma mem_extension_store: forall m k off v tlen mem,
    store m k off (bits v) tlen = Some mem ->
    mem_extension m mem.
Proof.
  move => m k off v tlen mem HStore.
  unfold mem_extension.
  unfold store in HStore.
  remove_bools_options.
  apply write_bytes_preserve_type in HStore as [H1 H2]; subst; rewrite H1 H2.
  by lias.
Qed.

Lemma mem_extension_grow_memory: forall m c mem,
    mem_grow m c = (Some mem) ->
    mem_extension m mem.
Proof.
  move => m c mem HMGrow.
  unfold mem_extension.
  unfold mem_grow in HMGrow.
  unfold mem_length, memory_list.mem_length.
  remove_bools_options; rewrite eq_refl => /=; rewrite List.app_length List.repeat_length Nat2N.inj_add nat_of_add_bin; by lias.
Qed.

(*
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

Lemma store_memory_extension_store_typed: forall s s' mems,
    store_typing s ->
    store_extension s s' ->
    (s_funcs s = s_funcs s') ->
    (s_tables s = s_tables s') ->
    (s_globals s = s_globals s') ->
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
 *)

(*
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
*)

(*
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
*)
    
Lemma reduce_inst_unchanged: forall hs s f es hs' s' f' es',
    reduce hs s f es hs' s' f' es' ->
    f.(f_inst) = f'.(f_inst).
Proof.
  move => hs s f es hs' s' f' es' HReduce.
  by induction HReduce.
Qed.

Ltac resolve_store_extension :=
  repeat lazymatch goal with
  | |- context [ component_extension (@operations.func_extension _) ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := func_extension); last by apply func_extension_refl
  | |- context [ component_extension table_extension ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := table_extension); last by apply table_extension_refl
  | |- context [ component_extension mem_extension ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := mem_extension); last by apply mem_extension_refl
  | |- context [ component_extension global_extension ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := global_extension); last by apply global_extension_refl
  | |- context [ component_extension elem_extension ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := elem_extension); last by apply elem_extension_refl
  | |- context [ component_extension data_extension ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := data_extension); last by apply data_extension_refl
    | _ => repeat rewrite andbT
    end; cbn.

Lemma store_extension_mem: forall s i mem mem',
  List.nth_error s.(s_mems) i = Some mem ->
  mem_extension mem mem' ->
  store_extension s (upd_s_mem s (set_nth mem' (s_mems s) i mem')).
Proof.
  move => s i mem mem' Hnth Hext.
  unfold store_extension => /=; resolve_store_extension.
  - apply nth_error_Some_length in Hnth.
    repeat rewrite andbT.
    unfold component_extension.
    apply/andP; split.
    + admit.
    + admit.
Admitted.

Lemma store_extension_reduce: forall s f es s' f' es' C C' tf hs hs',
    reduce hs s f es hs' s' f' es' ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C' ->
    e_typing s C' es tf ->
    store_typing s ->
    store_extension s s'.
Proof.
  move => s f es s' f' es' C C' tf hs hs' HReduce.
  move: tf C C'.
  induction HReduce => //; subst; try (move => tf C C' HIT Hmatch HType HST; intros; destruct tf; invert_e_typing => //; (try by apply store_extension_same)); unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup.
  - (* Invoke host *)
    by eapply host_application_extension; eauto.
  - (* global_set *)
    destruct g0.
    remove_bools_options.
    move/eqP in Hif0.
    unfold lookup_N in *.
    eapply component_extension_update; eauto; first by apply global_extension_refl.
    unfold global_extension => /=.
    rewrite eq_refl => /=.
    destruct gt.
    unfold value_typing in *.
    simpl in *.
    apply/orP; left.
    unfold value_typing in *.
    admit.
  - (* table update *)
    admit.
  - (* table grow *)
    admit.
  - (* elem drop *)
    (*
    unfold store_extension => /=.
    resolve_store_extension.
    
  - (* update memory : store none *)
    apply et_to_bet in HType; simpl in HType.
    replace [::BI_const (VAL_int32 k); BI_const v; BI_store t None a off] with ([::BI_const (VAL_int32 k); BI_const v] ++ [::BI_store t None a off]) in HType => //.
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
*)
Admitted.

Lemma store_typing_reduce: forall s f es s' f' es' C C' tf hs hs',
    reduce hs s f es hs' s' f' es' ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C' ->
    e_typing s C' es tf ->
    store_typing s ->
    store_typing s'.
Proof.
Admitted.
  
Lemma inst_typing_reduce: forall hs s f es hs' s' f' es' C C' tf,
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C' ->
    e_typing s C' es tf ->
    inst_typing s' f'.(f_inst) = Some C.
Proof.
  move => hs s f es hs' s' f' es' C C' tf Hreduce Hst Hit Hmatch Htype.
  erewrite <- reduce_inst_unchanged; eauto.
  eapply inst_typing_extension; eauto.
  eapply store_extension_reduce in Hreduce; eauto.
Qed.

Lemma result_e_type: forall r ts s C,
    result_types_agree s ts r ->
    e_typing s C (result_to_stack r) (Tf [::] ts).
Proof.
  move => r ts s C HResType.
  destruct r => /=; last by apply ety_trap.
  simpl in *.
  by apply et_values_typing.
Qed.

Lemma t_preservation_locs_type_aux: forall s f es s' f' es' C C0 ts t1s t2s hs hs',
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C0 ->
    C0.(tc_locals) = ts ->
    e_typing s C0 es (Tf t1s t2s) ->
    values_typing s f.(f_locs) = Some ts ->
    values_typing s f'.(f_locs) = Some ts.
Proof.
  move => s f es s' f' es' C C0 ts t1s t2s hs hs' HReduce HST HIT Hmatch Hlocs HType Hvaltype.
  move: C0 t1s t2s Hmatch Hlocs HType Hvaltype.
  induction HReduce => //; move => C0 t1s t2s Hmatch Hlocs HType Hvaltype; invert_e_typing.
  - rewrite H1.
    simpl in *.
    unfold values_typing in *.
    rewrite set_nth_map => //=.
    rewrite set_nth_same_unchanged => //.
    unfold lookup_N in *.
    eapply those_lookup_inv in H1_local_set; eauto.
    rewrite H1_local_set.
    by rewrite H2_value.
  - eapply lfilled_es_type_exists in HType; eauto.
    destruct HType as [lab' [ts1 [ts2 Hetype]]].
    by eapply IHHReduce; (try apply Hetype); eauto.
Qed.

Lemma t_preservation_locs_type: forall s f es s' f' es' C C0 ts t1s t2s hs hs',
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C0 ->
    C0.(tc_locals) = ts ->
    e_typing s C0 es (Tf t1s t2s) ->
    values_typing s f.(f_locs) = Some ts ->
    values_typing s' f'.(f_locs) = Some ts.
Proof.
  move => s f es s' f' es' C C0 ts t1s t2s hs hs' HReduce HST HIT Hmatch Hlocs HType Hvaltype.
  eapply t_preservation_locs_type_aux in Hvaltype; eauto.
  eapply values_typing_extension; eauto.
  eapply store_extension_reduce; eauto.
Qed.

Lemma t_preservation_e: forall s f es s' f' es' C t1s t2s lab ret hs hs',
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    store_typing s' ->
    frame_typing s f = Some C ->
    e_typing s (upd_return (upd_label C lab) ret) es (Tf t1s t2s) ->
    e_typing s' (upd_return (upd_label C lab) ret) es' (Tf t1s t2s).
Proof.
  move => s f es s' f' es' C t1s t2s lab ret hs hs' HReduce HST1 HST2.
  move: C ret lab t1s t2s.
  induction HReduce; move => C ret lab tx ty HFT1 HType; subst; try eauto; try (by apply ety_trap); invert_e_typing; unfold frame_typing in *; remove_bools_options; simpl in *; resolve_e_typing; resolve_store_inst_lookup => //.
  - (* reduce_simple *)
    by eapply t_simple_preservation; eauto.
  - (* Ref_func *)
    eapply inst_typing_func_lookup in H; eauto.
    destruct H as [tf [Hext Hnth]].
    by eapply ety_ref; eauto.
  - (* Block *)
    erewrite <- inst_typing_expand_eq in Hexpand_block; eauto; last by unfold inst_match; destruct t; lias.
    rewrite Hexpand_block in H; injection H as <- <-.
    apply concat_cancel_last_n in H1_values; last first.
    { apply values_typing_length in H2_values.
      rewrite v_to_e_length in H2.
      by rewrite H2_values in H2.
    }
    {
      remove_bools_options; subst.
      apply et_weakening_empty_1.
      eapply ety_label => //=; eauto.
      - apply ety_a' => //=.
        by apply bet_weakening_empty_both; constructor.
      - eapply et_composition'; first by apply et_values_typing; eauto.
        by eapply ety_a in H3_block; eauto.
    }
  - (* Loop *)
    remember Hexpand_block as Het; clear HeqHet.
    erewrite <- inst_typing_expand_eq in Hexpand_block; eauto; last by unfold inst_match; destruct t; lias.
    rewrite Hexpand_block in H; injection H as <- <-.
    apply concat_cancel_last_n in H1_values; last first.
    { apply values_typing_length in H2_values.
      rewrite v_to_e_length in H2.
      by rewrite H2_values in H2.
    }
    {
      remove_bools_options; subst.
      apply et_weakening_empty_1.
      eapply ety_label => //=; eauto.
      - apply ety_a' => //=.
        by apply bet_loop.
      - eapply et_composition'; first by apply et_values_typing; eauto.
        by eapply ety_a in H3_loop; eauto.
    }
  - (* Call *)
    apply ety_weakening, ety_invoke.
    eapply inst_typing_func_lookup in H; eauto.
    destruct H as [t0 [Hft Hnth]].
    rewrite Hnth in H1_call.
    by injection H1_call as <-.
  - (* Call_indirect *)
    apply ety_weakening, ety_invoke.
    unfold stab_elem in H.
    remove_bools_options.
    rewrite Hteq in H3_callindirect; injection H3_callindirect as <-.
    unfold ext_func_typing.
    by rewrite H0.
  - (* Invoke native *)
    unfold ext_func_typing in H3_invoke.
    remove_bools_options; simpl in *.
    inversion H1; subst; clear H1.
    assert (length vs = length ts_values) as Hlen; first by apply values_typing_length in H2_values.
    apply concat_cancel_last_n in H1_invoke; last by repeat rewrite -length_is_size; rewrite - Hlen.
    remove_bools_options; subst.
    apply et_weakening_empty_1.
    apply ety_frame => //.
    destruct Hft as [Hcltype [_ Hfunctype]].
    simpl in *.
    remove_bools_options.
    destruct f0.
    destruct Hfunctype as [Hctype Hexprtype].
    injection Hctype as <-<-.
    unfold expr_typing in Hexprtype; subst.
    econstructor; eauto.
    + unfold frame_typing; rewrite Hoption2 => /=.
      erewrite values_typing_cat; eauto.
      by eapply default_values_typing.
    + eapply ety_label; eauto.
      * apply ety_a' => //=; by apply bet_weakening_empty_both, bet_empty.
      * apply ety_a with (s := s) in Hexprtype.
        uapply Hexprtype => /=.
        erewrite inst_t_context_label_empty; eauto.
        erewrite inst_t_context_local_empty; eauto.
        by rewrite cats0.
  - (* Invoke host *)
    unfold typing.ext_func_typing in H3_invoke.
    remove_bools_options; simpl in *.
    inversion H1; subst; clear H1.
    assert (length vcs = length ts_values) as Hlen; first by apply values_typing_length in H2_values.
    apply concat_cancel_last_n in H1_invoke; last by repeat rewrite -length_is_size; rewrite - Hlen.
    remove_bools_options; subst.
    apply et_weakening_empty_1.
    destruct Hft as [Hcltype _]; subst.
    (* We require an axiomatic correctness assumption about the host. *)
    assert (result_types_agree s' ts3_invoke r).
    {
      by eapply host_application_respect; eauto.
    }
    by apply result_e_type.
  - (* Local_get *)
    unfold lookup_N in *.
    eapply those_map_lookup in Hoption0; eauto.
    destruct Hoption0 as [vt [Hvaltype Hnth]].
    erewrite nth_error_app_Some in H1_local_get; eauto.
    by injection H1_local_get as <-.
  - (* Global_get *)
    destruct g0.
    remove_bools_options.
    move/eqP in Hif0.
    simpl in *.
    by rewrite Hoption in Hnthgt; injection Hnthgt as ->.
  - (* Table_get *)
    destruct t1; remove_bools_options.
    simpl in *.
    rewrite Hnthtabt in H3_table_get.
    injection H3_table_get as <-.
    eapply all_projection in Hif1; eauto.
    move/eqP in Hif1.
    by rewrite Hif1.
  - (* Table fill *)
    destruct tab; simpl in *.
    remove_bools_options.
    rewrite Hnthtabt in H2_table_fill.
    injection H2_table_fill as <-.
    simpl in *.
    rewrite -cat1s; apply et_composition' with (t2s := ty).
    + resolve_e_typing.
      rewrite -catA; apply ety_a' => //; apply bet_weakening_empty_2.
      by eapply bet_table_set; eauto.
    + resolve_e_typing => //.
      apply ety_a' => //.
      repeat rewrite -catA.
      apply bet_weakening_empty_2 => /=.
      by eapply bet_table_fill; eauto.

  - (* Table copy 1 *)
    destruct taby; simpl in *.
    remove_bools_options.
    simpl in *.
    rewrite Hnthtabt in H3_table_copy; injection H3_table_copy as <-.
    rewrite -cat1s; apply et_composition' with (t2s := (ty ++ [::T_num T_i32]) ++ [::T_ref (tt_elem_type tabt)]); first by apply ety_a' => //; apply bet_weakening; eapply bet_table_get; eauto.
    rewrite -cat1s; apply et_composition' with (t2s := ty); first by apply ety_a' => //; rewrite -catA; apply bet_weakening_empty_2; eapply bet_table_set; eauto.
    resolve_e_typing => //.
    apply ety_a' => //.
    repeat rewrite -catA.
    apply bet_weakening_empty_2 => /=.
    by eapply bet_table_copy; eauto.

  - (* Table copy 2 *)
    destruct taby; simpl in *.
    remove_bools_options.
    simpl in *.
    rewrite Hnthtabt in H3_table_copy; injection H3_table_copy as <-.
    rewrite -cat1s; apply et_composition' with (t2s := (ty ++ [::T_num T_i32]) ++ [::T_ref (tt_elem_type tabt)]); first by apply ety_a' => //; apply bet_weakening; eapply bet_table_get; eauto.
    rewrite -cat1s; apply et_composition' with (t2s := ty); first by apply ety_a' => //; rewrite -catA; apply bet_weakening_empty_2; eapply bet_table_set; eauto.
    resolve_e_typing => //.
    apply ety_a' => //.
    repeat rewrite -catA.
    apply bet_weakening_empty_2 => /=.
    by eapply bet_table_copy; eauto.

  - (* Table_init *)
    destruct tab; simpl in *.
    remove_bools_options.
    simpl in *.
    rewrite Hnthtabt in H2_table_init; injection H2_table_init as <-.
    
    specialize (inst_typing_elem_lookup Hoption Hoption2) as [elemt [ei [Hselem [Helemt Hnthet]]]].

    rewrite H0 in Hselem; injection Hselem as <-.
    rewrite Hnthet in H3_table_init; injection H3_table_init as ->.

    specialize (store_typing_elem_lookup HST1 H0) as [et Het].
    rewrite Helemt in Het; injection Het as <-.
    unfold eleminst_typing, typing.eleminst_typing in Helemt.

    destruct elem.
    remove_bools_options.

    simpl in *.

    eapply all_projection in Hif2; eauto.
    move/eqP in Hif2.
    
    resolve_e_typing => //.
    rewrite -cat1s; apply et_composition' with (t2s := ty); first by apply ety_a' => //; rewrite -catA; apply bet_weakening_empty_2; eapply bet_table_set; eauto.

    resolve_e_typing => //.
    apply ety_a' => //.
    repeat rewrite -catA.
    apply bet_weakening_empty_2 => /=.
    by eapply bet_table_init; eauto.
      
  - (* Load None *)
    by destruct t.
    
  - (* Load Some *)
    by destruct t.
    
  - (* Memory fill *)
    destruct mem.
    remove_bools_options.

    rewrite -cat1s; apply et_composition' with (t2s := ty).
    + apply ety_a' => //=.
      rewrite -catA; apply bet_weakening_empty_2.
      by eapply bet_store; eauto.
    + resolve_e_typing => //.
      repeat rewrite -catA.
      apply ety_a' => //=.
      apply bet_weakening_empty_2.
      by eapply bet_memory_fill; eauto.

  - (* Memory copy 1 *)
    destruct mem.
    remove_bools_options.

    rewrite -cat1s; apply et_composition' with (t2s := (ty ++ [::T_num T_i32]) ++ [::T_num T_i32]).
    + apply ety_a' => //=.
      apply bet_weakening.
      by eapply bet_load; eauto.
    + rewrite -cat1s; apply et_composition' with (t2s := ty).
      * apply ety_a' => //=.
        simpl in *.
        rewrite -catA; apply bet_weakening_empty_2.
        by eapply bet_store; eauto.
      * resolve_e_typing => //.
        repeat rewrite -catA.
        apply ety_a' => //=.
        apply bet_weakening_empty_2.
        by eapply bet_memory_copy; eauto.
        
  - (* Memory copy 2 *)
    destruct mem.
    remove_bools_options.

    rewrite -cat1s; apply et_composition' with (t2s := (ty ++ [::T_num T_i32]) ++ [::T_num T_i32]).
    + apply ety_a' => //=.
      apply bet_weakening.
      by eapply bet_load; eauto.
    + rewrite -cat1s; apply et_composition' with (t2s := ty).
      * apply ety_a' => //=.
        rewrite -catA; apply bet_weakening_empty_2.
        by eapply bet_store; eauto.
      * resolve_e_typing => //.
        repeat rewrite -catA.
        apply ety_a' => //=.
        apply bet_weakening_empty_2.
        by eapply bet_memory_copy; eauto.

  - (* Memory init *)
    destruct mem.
    remove_bools_options.

    rewrite -cat1s; apply et_composition' with (t2s := ty).
    + apply ety_a' => //=.
      rewrite -catA; apply bet_weakening_empty_2.
      by eapply bet_store; eauto.
    + resolve_e_typing => //.
      repeat rewrite -catA.
      apply ety_a' => //=.
      apply bet_weakening_empty_2.
      by eapply bet_memory_init; eauto.
        
  - (* Label *)
    assert (store_extension s s') as Hext.
    { eapply store_extension_reduce; (try by apply HType); eauto.
      - by eapply r_label; eauto.
      - unfold inst_match => /=.
        by repeat rewrite eq_refl.
    }

    fold (typing.values_typing s f.(f_locs)) in Hoption0.
    assert (values_typing s' f'.(f_locs) = Some l) as Hvaltype.
    {
      specialize (lfilled_es_type_exists erefl HType) as Hestype.
      destruct Hestype as [lab' [ts1 [ts2 Hestype]]].
      eapply t_preservation_locs_type; eauto => /=.
      - unfold inst_match; by repeat rewrite eq_refl.
      - simpl. by erewrite inst_t_context_local_empty; eauto; rewrite cats0.
    }
    
    erewrite -> inst_t_context_local_empty in *; eauto.
    rewrite -> cats0 in *.
    
    remember (lfill lh es) as les.
    remember (lfill lh es') as les'.
    generalize dependent les'.
    generalize dependent les.
    move: lh lab tx ty.
    elim.
    + move => vs es0 lab tx ty ? -> /=Hetype ? ->.
      invert_e_typing.
      specialize (values_typing_extension Hext H2_values) as Hvalues'.
      eapply et_composition' with (t2s := tx ++ ts_values); eauto.
      * by apply et_weakening_empty_1; eapply et_values_typing; eauto.
      * eapply et_composition'; eauto.
        eapply store_extension_e_typing; (try by apply H2_comp0); done.
    + move => k0 vs n es1 lh' IH es2 lab tx ty ? -> /=Hetype ? ->.
      invert_e_typing.
      eapply et_composition' with (t2s := tx ++ ts_values); eauto.
      * apply et_weakening_empty_1.
        apply et_values_typing.
        by eapply values_typing_extension; eauto.
      * rewrite -cat1s.
        eapply et_composition'; eauto.
        { instantiate (1 := ((tx ++ ts_values) ++ ts1_label)).
          apply et_weakening_empty_1.
          eapply ety_label; eauto.
          - by eapply store_extension_e_typing in H2_label; eauto.
          - simpl in *.
            by eapply IH in H3_label; eauto.
        }
        {
          eapply store_extension_e_typing; try apply HST1 => //; by eauto.
        }
        
  - (* r_frame *)
    inversion H2_frame; subst; clear H2_frame.
    move/eqP in H1.
    unfold typing.frame_typing in H1.
    remove_bools_options.

    assert (store_extension s s') as Hext.
    { eapply store_extension_reduce; (try by apply HType); eauto.
      - unfold inst_match => /=.
        by repeat rewrite eq_refl.
    }

    fold (values_typing s f.(f_locs)) in Hoption2.
    assert (values_typing s' f'.(f_locs) = Some l0) as Hvaltype.
    {
      eapply t_preservation_locs_type; eauto => /=.
      - unfold inst_match; by repeat rewrite eq_refl.
      - simpl. by erewrite inst_t_context_local_empty; eauto; rewrite cats0.
    }
    
    erewrite -> inst_t_context_local_empty in *; eauto.
    rewrite -> cats0 in *.
    eapply inst_typing_reduce in Hoption1; eauto; last by unfold inst_match; repeat rewrite eq_refl.

    apply ety_frame => //.
    eapply mk_thread_typing; (try by apply H6); eauto.
    apply/eqP.
    unfold frame_typing.
    rewrite Hoption1 Hvaltype => /=.
    erewrite -> inst_t_context_local_empty; eauto.
    by rewrite cats0.
Qed.
  
Theorem t_preservation: forall s f es s' f' es' ts hs hs',
    reduce hs s f es hs' s' f' es' ->
    config_typing s (f, es) ts ->
    config_typing s' (f', es') ts.
Proof.
  move => s f es s' f' es' ts hs hs' HReduce HType.
  inversion HType; inversion H0; subst; clear HType.
  move/eqP in H3.
  remember H3 as Hft; clear HeqHft.
  unfold frame_typing in H3.
  remove_bools_options.
  
  assert (store_extension s s') as Hstoreext.
  { eapply store_extension_reduce; eauto.
    by unfold inst_match; repeat rewrite eq_refl.
  }
  assert (store_typing s') as Hstoretype.
  { eapply store_typing_reduce; eauto.
    by unfold inst_match; repeat rewrite eq_refl.
  }

  specialize (inst_typing_extension Hstoreext Hoption) as Hit'.
  erewrite -> reduce_inst_unchanged in Hit'; eauto.

  constructor => //.
  econstructor; eauto; last first.
  - by eapply t_preservation_e; eauto.
  - apply/eqP.
    unfold frame_typing.
    rewrite Hit'.
    erewrite -> inst_t_context_local_empty in *; eauto.
    rewrite -> cats0 in *.
    eapply t_preservation_locs_type in Hoption0; eauto.
    + rewrite Hoption0; by rewrite cats0.
    + unfold inst_match; by repeat rewrite eq_refl.
    + by destruct t.
Qed.

End Host.
