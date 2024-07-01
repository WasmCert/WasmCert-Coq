(** Proof of preservation **)

From Wasm Require Export common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program.Equality NArith ZArith_base.
From Wasm Require Export typing opsem properties typing_inversion tactic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Context `{ho: host}.
  
Definition inst_match C C' : bool :=
  (C.(tc_types) == C'.(tc_types)) &&
  (C.(tc_funcs) == C'.(tc_funcs)) &&
  (C.(tc_tables) == C'.(tc_tables)) &&
  (C.(tc_mems) == C'.(tc_mems)) &&
  (C.(tc_globals) == C'.(tc_globals)) &&
  (C.(tc_elems) == C'.(tc_elems)) &&
  (C.(tc_datas) == C'.(tc_datas)) &&
  (C.(tc_refs) == C'.(tc_refs)).

Lemma bet_skip_refcheck: forall C C' bes tf,
  C' = upd_refs C (iota_N 0 (length C.(tc_funcs))) ->
  be_typing C bes tf ->
  be_typing C' bes tf.
Proof.
  move => C C' bes [tx ty] HC' Hbet.
  move: C' HC'.
  induction Hbet; move => C' HC'; subst C' => /=; (try by econstructor; eauto).
  (* ref_func *)
  - apply bet_ref_func with (t := t) => //=.
    + apply nth_error_Some_length in H.
      apply List.nth_error_In with (n := (N.to_nat x)).
      rewrite iota_N_lookup.
      by rewrite add0n N2Nat.id.
    + by lias.
Qed.

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
  invert_e_typing.
  eapply ety_subtyping; first by apply et_values_typing; eauto.
  done.
Qed.

(* It's better to just set it opaque and unset it when necessary, since most of the times we do not want to unfold this definition by simpl. But the simpl nomatch method doesn't prevent it from being unfolded for some reason. *)
Opaque instr_subtyping.

Theorem t_simple_preservation: forall s es es' C tf,
    e_typing s C es tf ->
    reduce_simple es es' ->
    e_typing s C es' tf.
Proof.
  move => s es es' C [ts1 ts2] HType HReduce.
  inversion HReduce; subst; (try by apply ety_trap); invert_e_typing; extract_premise => //; unify_principal => //; resolve_e_typing => //.
  - (* Unop *)
    replace (typeof_num (app_unop op v)) with (typeof_num v); last by destruct op, v.
    by resolve_subtyping.
  - (* Binop_success *)
    erewrite app_binop_type_preserve; eauto.
    by resolve_subtyping.
  - (* Cvtop *)
    erewrite eval_cvt_type_preserve; eauto.
    by resolve_subtyping.
  - (* Unop_vec *)
    replace (typeof_vec (app_unop_vec op v)) with (typeof_vec v); last by destruct op, v.
    rewrite H0.
    by resolve_subtyping.
  - (* Binop_vec *)
    replace (typeof_vec (app_binop_vec op v1 v2)) with (typeof_vec v1); last by destruct op, v1, v2.
    rewrite H0.
    by resolve_subtyping.
  - (* Ternop_vec *)
    replace (typeof_vec (app_binop_vec op v1 v2)) with (typeof_vec v1); last by destruct op, v1, v2.
    rewrite H0.
    by resolve_subtyping.
  - (* Br *)
    eapply et_composition'; eauto; resolve_e_typing.
    by eapply Lfilled_break_typing with (tss := nil) in Hconjl1; eauto => //=; try (by apply v_to_e_const); last by lias.
  - (* Br_if false *)
    instantiate (1 := extr).
    instantiate (1 := nil) => /=.
    by resolve_subtyping.
  - (* Br_br_table *)
    rewrite catA size_cat addnK take_size_cat => //.
    rewrite cats0.
    apply ety_a' => //; econstructor; eauto => //.
    { unfold lookup_N in *.
      eapply Forall_lookup in Hconjr; eauto.
      rewrite List.nth_error_app1 => //; eauto.
      (* Implicit parameters *)
      unfold labelidx, u32 in H.
      by lias.
    }
  - (* Br_br_table_oob *)
    rewrite catA size_cat addnK take_size_cat => //.
    rewrite cats0.
    apply ety_a' => //; econstructor; eauto => //.
    { unfold lookup_N in *.
      eapply Forall_lookup in Hconjr; eauto.
      rewrite List.nth_error_app2 => //; eauto.
      by rewrite Nat.sub_diag.
    }
  - (* Frame_const *)
    inversion Hconjl0; subst.
    invert_e_typing.
    by resolve_e_typing.
  - (* Frame_return *)
    inversion Hconjl0; subst; clear Hconjl0.
    eapply Lfilled_return_typing in H6; (try reflexivity); eauto.
    + invert_e_typing.
      by resolve_e_typing.
    + by apply v_to_e_const.
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
    exists tf', ext_table_typing s' a = Some tf' /\
    table_type_extension tf tf'.
Proof.
  move => s s' a tf Hext Htype.
  unfold ext_table_typing in *.
  remove_bools_options.
  eapply store_extension_lookup_table in Hoption; last by apply Hext.
  destruct Hoption as [tab [Hnth Htableext]].
  rewrite Hnth.
  unfold table_extension in Htableext.
  by remove_bools_options; exists (tableinst_type tab).
Qed.

Lemma ext_mem_typing_extension: forall s s' a tf,
    store_extension s s' ->
    ext_mem_typing s a = Some tf ->
    exists tf', ext_mem_typing s' a = Some tf' /\
    limits_extension tf tf'.
Proof.
  move => s s' a tf Hext Htype.
  unfold ext_mem_typing in *.
  remove_bools_options.
  eapply store_extension_lookup_mem in Hoption; last by apply Hext.
  destruct Hoption as [mem [Hnth Hmemext]].
  rewrite Hnth.
  unfold mem_extension in Hmemext.
  by remove_bools_options; exists (meminst_type mem).
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

Lemma typeof_ref_extension: forall s s' v t,
    store_extension s s' ->
    typeof_ref s v = Some t ->
    typeof_ref s' v = Some t.
Proof.
  move => s s' v t Hext Htype.
  destruct v; simpl in * => //=.
  remove_bools_options.
  eapply ext_func_typing_extension in Hoption; eauto.
  by rewrite Hoption.
Qed.
  
Lemma value_typing_extension: forall s s' v t,
    store_extension s s' ->
    value_typing s v t ->
    value_typing s' v t.
Proof.
  move => s s' v t Hext Htype.
  destruct v; simpl in * => //=.
  remove_bools_options.
  unfold value_typing in *; simpl in *; remove_bools_options.
  eapply typeof_ref_extension in Hoption0; eauto.
  by rewrite Hoption0.
Qed.
  
Lemma values_typing_extension: forall s s' vs ts,
    store_extension s s' ->
    values_typing s vs ts ->
    values_typing s' vs ts.
Proof.
  move => s s'; elim => //=.
  move => v vs IH => //=; case.
  - move => HST Hvt => //=; by apply values_typing_length in Hvt.
  - move => t ts Hext Hvt; unfold values_typing => /=.
    remove_bools_options.
    by erewrite value_typing_extension; eauto.
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
  induction ei; move => ei' Hext; simpl in *; remove_bools_options => //=.
  erewrite value_typing_extension; (try by apply Hsext) => //=.
  apply IHei; first by rewrite H2.
  repeat rewrite eq_refl.
  by lias.
Qed.
  
Lemma datainst_typing_extension: forall s s' a a' tf,
    store_extension s s' ->
    data_extension a a' ->
    datainst_typing s a = Some tf ->
    datainst_typing s' a' = Some tf.
Proof.
  move => s s' d tf Hext Htype.
  by unfold datainst_typing in *.
Qed.

Lemma those_map_impl {T T1 T2: Type}: forall f g (r: T1 -> T2 -> bool) (l: list T) (l': list T1),
    (forall x y, f x = Some y -> exists z, g x = Some z /\ r y z) ->
    those (map f l) = Some l' ->
    exists l'', those (map g l) = Some l'' /\ all2 r l' l''.
Proof.
  move => f g r.
  setoid_rewrite <- those_those0.
  elim => //=; first by case => //; exists nil.
  move => x l IH l' Hr Hf.
  remove_bools_options.
  specialize (Hr x t Hoption) as Hz; destruct Hz as [z [Hg Hryz]].
  specialize (IH l0 Hr erefl) as Hl''; destruct Hl'' as [l'' [Hthose Hrall]].
  exists (z :: l'') => /=.
  by rewrite Hg Hthose Hryz Hrall => /=.
Qed.

Lemma inst_typing_extension: forall s s' i C,
    store_extension s s' ->
    inst_typing s i = Some C ->
    exists C',
      inst_typing s' i = Some C' /\
      context_extension C C'.
Proof.
  move => s s' i C HST HIT.
  unfold inst_typing in *.
  destruct i.
  remove_bools_options.
  (* Functions *)
  eapply those_map_impl in Hoption; last first.
  { move => x y Hext.
    exists y; eapply ext_func_typing_extension in Hext; eauto.
    split; first by apply Hext.
    by apply eq_refl.
  }
  destruct Hoption as [tfs [Hthosef Hfeq]]; rewrite Hthosef.
  rewrite -eqseq_all in Hfeq; move/eqP in Hfeq; subst.
  (* Tables *)
  eapply those_map_impl in Hoption0; last first.
  { move => x y Hext.
    by eapply ext_table_typing_extension in Hext; eauto.
  }
  destruct Hoption0 as [tts [Hthoset Htr]]; rewrite Hthoset.
  (* Memories *)
  eapply those_map_impl in Hoption1; last first.
  { move => x y Hext.
    by eapply ext_mem_typing_extension in Hext; eauto.
  }
  destruct Hoption1 as [tms [Hthosem Hmr]]; rewrite Hthosem.
  (* Globals *)
  eapply those_map_impl in Hoption2; last first.
  { move => x y Hext.
    exists y; eapply ext_global_typing_extension in Hext; eauto.
    split; first by apply Hext.
    by apply eq_refl.
  }
  destruct Hoption2 as [tgs [Hthoseg Hgeq]]; rewrite Hthoseg.
  rewrite -eqseq_all in Hgeq; move/eqP in Hgeq; subst.
  (* Elems *)
  eapply those_map_impl in Hoption3; last first.
  { move => x y Hext.
    instantiate (3 := fun x =>
                        match lookup_N (s_elems s') x with
                        | Some ei => eleminst_typing s' ei
                        | None => None
                        end
                ).
    remove_bools_options.
    eapply store_extension_lookup_elem in Hoption; eauto.
    destruct Hoption as [elem [Hnth Helemext]].
    eapply eleminst_typing_extension in Helemext; eauto.
    exists y; split; last by apply eq_refl.
    by rewrite Hnth /= Helemext.
  }
  destruct Hoption3 as [tes [Hthosee Heeq]]; rewrite Hthosee.
  rewrite -eqseq_all in Heeq; move/eqP in Heeq; subst.
  (* Datas *)
  eapply those_map_impl in Hoption4; last first.
  { move => x y Hext.
    instantiate (3 := fun x =>
                        match lookup_N (s_datas s') x with
                        | Some ei => datainst_typing s' ei
                        | None => None
                        end
                ).
    remove_bools_options.
    eapply store_extension_lookup_data in Hoption; eauto.
    destruct Hoption as [data [Hnth Hdataext]].
    eapply datainst_typing_extension in Hdataext; eauto.
    exists y; split; last by apply eq_refl.
    by rewrite Hnth /= Hdataext.
  }
  destruct Hoption4 as [tds [Hthosed Hdeq]]; rewrite Hthosed.
  rewrite -eqseq_all in Hdeq; move/eqP in Hdeq; subst.
  eexists; split; first by eauto.
  unfold context_extension => /=; repeat rewrite eq_refl => /=.
  by rewrite Htr Hmr.
Qed.  

Lemma frame_typing_extension: forall s s' f C,
    store_extension s s' ->
    frame_typing s f C ->
    exists C',
      frame_typing s' f C' /\
      context_extension C C'.
Proof.
  move => s s' f C HST HIT.
  unfold frame_typing in *.
  remove_bools_options.
  destruct HIT as [ts [-> Hvts]].
  specialize (inst_typing_extension HST Hoption) as [C' [Hit Hext]].
  erewrite -> inst_t_context_local_empty in *; eauto.
  rewrite cats0.
  exists (upd_local C' ts); split => //.
  - rewrite Hit.
    exists ts.
    eapply values_typing_extension in Hvts; eauto.
    rewrite Hvts.
    by erewrite inst_t_context_local_empty; eauto; by rewrite cats0.
  - unfold context_extension in *.
    by lias.
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

Lemma update_label_agree C C' lab:
  context_agree C C' ->
  context_agree (upd_label C lab) (upd_label C' lab).
Proof.
  unfold context_agree in *; destruct C, C'; simpl in *; intros; remove_bools_options; subst.
  repeat rewrite eq_rect => /=; lias.
Qed.

Lemma context_agree_func_type C C' n ft:
  context_agree C C' ->
  lookup_N C.(tc_funcs) n = Some ft ->
  lookup_N C'.(tc_funcs) n = Some ft.
Proof.
  move => Hext Hnth.
  unfold context_agree in Hext; remove_bools_options.
  unfold lookup_N in *.
  eapply all2_nth_impl in H9 as [ft' [Hnth' Hfext]]; eauto.
  by unfold func_agree in Hfext; remove_bools_options; subst.
Qed.
  
Lemma context_agree_table_type C C' n tabt:
  context_agree C C' ->
  lookup_N C.(tc_tables) n = Some tabt ->
  exists tabt', lookup_N C'.(tc_tables) n = Some tabt' /\
             table_agree tabt tabt'.
Proof.
  move => Hext Hnth.
  unfold context_agree in Hext; remove_bools_options.
  unfold lookup_N in *.
  by eapply all2_nth_impl in H8 as [tabt' [Hnth' Htabext]]; eauto.
Qed.

Lemma context_agree_mem_type C C' n memt:
  context_agree C C' ->
  lookup_N C.(tc_mems) n = Some memt ->
  exists memt',
    lookup_N C'.(tc_mems) n = Some memt' /\
    mem_agree memt memt'.
Proof.
  move => Hext Hnth.
  unfold context_agree in Hext; remove_bools_options.
  unfold lookup_N in *.
  by eapply all2_nth_impl in H7 as [memt' [Hnth' Hmemext]]; eauto.
Qed.

Lemma context_agree_global_type C C' n gt:
  context_agree C C' ->
  lookup_N C.(tc_globals) n = Some gt ->
  lookup_N C'.(tc_globals) n = Some gt.
Proof.
  move => Hext Hnth.
  unfold context_agree in Hext; remove_bools_options.
  unfold lookup_N in *.
  eapply all2_nth_impl in H6 as [gt' [Hnth' Hfext]]; eauto.
  by unfold global_agree in Hfext; remove_bools_options; subst.
Qed.

Ltac rewrite_context_agree:=
  repeat match goal with
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_types ?C' ] =>
        replace (tc_types C') with (tc_types C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_elems ?C' ] =>
        replace (tc_elems C') with (tc_elems C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_datas ?C' ] =>
        replace (tc_datas C') with (tc_datas C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_locals ?C' ] =>
        replace (tc_locals C') with (tc_locals C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_labels ?C' ] =>
        replace (tc_labels C') with (tc_labels C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_return ?C' ] =>
        replace (tc_return C') with (tc_return C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_refs ?C' ] =>
        replace (tc_refs C') with (tc_refs C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | _ : is_true (context_agree ?C ?C') |- is_true (context_agree (upd_label ?C ?lab) (upd_label ?C' ?lab)) =>
        by apply update_label_agree
    | Hext : is_true (context_agree ?C ?C'),
      Hnth : lookup_N ?C'.(tc_tables) ?n = Some ?t,
      Helemtype: (tt_elem_type ?t) = ?tref |- _ =>
      let Htableagree := fresh "Htableagree" in
      specialize (context_agree_table_type Hext Hnth) as [tabt_ctxext [Hnth_ctxext Htableagree]]; unfold table_agree in Htableagree; remove_bools_options; subst; try rewrite - Htableagree
    | Hext : is_true (context_agree ?C ?C'),
      Hnth : lookup_N ?C.(tc_tables) ?n = Some ?t |- _ =>
      specialize (context_agree_table_type Hext Hnth) as [tabt_ctxext [Hnth_ctxext Htableagree]]; unfold table_agree in *; remove_bools_options; subst
    | Hext : is_true (context_agree ?C ?C'),
      Hnth : lookup_N ?C.(tc_mems) ?n = Some ?t |- _ =>
      (* Not creating fresh names to make sure this only triggers once -- a bit stupid *)
      specialize (context_agree_mem_type Hext Hnth) as [memt_ctxext [Hnth_ctxext Hmemagree]]
    | Hext : is_true (context_agree ?C ?C'),
      Hnth : lookup_N ?C.(tc_funcs) ?n = Some ?t |- _ =>
      specialize (context_agree_func_type Hext Hnth) as Hnthfunc'
    | Hext : is_true (context_agree ?C ?C'),
      Hnth : lookup_N ?C.(tc_globals) ?n = Some ?t |- _ =>
      specialize (context_agree_global_type Hext Hnth) as Hnthglobal'
    end.

(* Curiously, this lemma works in both directions *)
Lemma context_agree_be_typing: forall C C' es tf,
    context_agree C C' ->
    be_typing C es tf ->
    be_typing C' es tf.
Proof.
  move => C C' es tf Hext Hetype.
  move: C' Hext.
  induction Hetype; move => C' Hext; (try by econstructor; eauto); try (by econstructor; eauto; rewrite_context_agree; eauto); try (by rewrite_context_agree; econstructor; eauto; rewrite_context_agree).
  - econstructor; eauto; unfold expand_t in *; rewrite_context_agree.
    by apply IHHetype; rewrite_context_agree.
  - econstructor; eauto; unfold expand_t in *; rewrite_context_agree.
    by apply IHHetype; by rewrite_context_agree.
  - econstructor; eauto; unfold expand_t in *; rewrite_context_agree.
    + apply IHHetype1; by rewrite_context_agree.
    + apply IHHetype2; by rewrite_context_agree.
  - rewrite_context_agree.
    econstructor; eauto.
    + by rewrite - Htableagree.
    + by rewrite_context_agree.
  - rewrite_context_agree.
    eapply context_agree_table_type in H as [tabt [Hnth Hagree]]; eauto; unfold table_agree in *; move/eqP in Hagree.
    econstructor.
    + by apply Hnth.
    + reflexivity.
    + by apply Hnth_ctxext.
    + by rewrite - Hagree - H2.
  - rewrite_context_agree.
    econstructor; first by eauto.
    + by rewrite - Htableagree.
    + by rewrite_context_agree.
Qed.

Lemma context_agree_typing: forall s C C' es tf,
    context_agree C C' ->
    e_typing s C es tf ->
    e_typing s C' es tf.
Proof.
  move => s C C' es tf Hext Hetype.
  move: C' Hext.
  induction Hetype; subst; move => C' Hext; try by econstructor; eauto.
  - (* be *)
    apply ety_a.
    by eapply context_agree_be_typing; eauto.
  - (* Label *)
    eapply ety_label; eauto.
    eapply IHHetype2.
    by rewrite_context_agree.
Qed.

Lemma context_extension_typing: forall s C C' es tf,
    context_extension C C' ->
    e_typing s C es tf ->
    e_typing s C' es tf.
Proof.
  intros.
  eapply context_agree_typing; last by eauto.
  by apply context_extension_agree.
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
    replace (to_b_list (to_e_list bes)) with bes => //; last by apply b_e_elim.
  (* composition *)
  - move=> s C bes tf r1 r2 r3 HType1 IHHType1 IH2 IHHType2 s' HST1 HST2 Hext.
    eapply ety_composition.
    + by apply IHHType1.
    + by apply IHHType2.
  (* subtyping *)
  - move=> s C es t1s t2s t1s' t2s' HType IHHType Hsub s' HST1 HST2 Hext.
    by eapply ety_subtyping; eauto.
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
    eapply frame_typing_extension in HFType; eauto.
    destruct HFType as [C'' [HFType Hcext]].
    eapply mk_thread_typing with (C := C''); eauto.
    apply context_extension_typing with (C := C') => //; last by apply IHHType.
    subst C'.
    unfold context_extension in *.
    by lias.
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

Lemma reduce_inst_unchanged: forall hs s f es hs' s' f' es',
    reduce hs s f es hs' s' f' es' ->
    f.(f_inst) = f'.(f_inst).
Proof.
  move => hs s f es hs' s' f' es' HReduce.
  by induction HReduce.
Qed.

Lemma context_extension_func_typing: forall C C' x t,
    context_extension C C' ->
    func_typing C x t ->
    func_typing C' x t.
Proof.
  move => C C' x t Hcext Hft.
  unfold func_typing in *; destruct x; remove_bools_options.
  specialize (context_extension_agree Hcext) as Hagree.
  rewrite_context_agree.
  rewrite Hoption.
  destruct f; destruct Hft as [-> [Het Hdefault]]; repeat split => //.
  eapply context_agree_be_typing; last by eauto.
  unfold context_agree in *; remove_bools_options; destruct C, C'; subst; by lias.
Qed.
  
Lemma store_extension_funcinst_typing: forall s s' x t,
    store_extension s s' ->
    funcinst_typing s x t ->
    funcinst_typing s' x t.
Proof.
  move => s s' x t Hst Hft.
  unfold funcinst_typing in *; destruct Hft as [<- Hft]; remove_bools_options; split => //.
  destruct x => //; destruct Hft as [? Hft]; split => //.
  remove_bools_options.
  eapply inst_typing_extension in Hoption; last by apply Hst.
  destruct Hoption as [C' [Hit' Hcext]].
  rewrite Hit'.
  unfold func_typing in *.
  by eapply context_extension_func_typing; eauto.
Qed.

Lemma store_extension_tableinst_typing: forall s s' x t,
    store_extension s s' ->
    tableinst_typing s x = Some t ->
    tableinst_typing s' x = Some t.
Proof.
  move => s s' x t Hst Ht.
  unfold tableinst_typing in *; destruct x; remove_bools_options.
  resolve_if_true_eq.
  apply list_all_forall.
  move => a Hin.
  move/allP in Hif1.
  move/inP in Hin.
  apply Hif1 in Hin.
  by eapply value_typing_extension in Hin; eauto.
Qed.

Lemma store_extension_meminst_typing: forall s s' x t,
    store_extension s s' ->
    meminst_typing s x = Some t ->
    meminst_typing s' x = Some t.
Proof.
  move => s s' x t Hst Ht.
  by unfold meminst_typing in *; destruct x; remove_bools_options.
Qed.

Lemma store_extension_globalinst_typing: forall s s' x t,
    store_extension s s' ->
    globalinst_typing s x = Some t ->
    globalinst_typing s' x = Some t.
Proof.
  move => s s' x t Hst Ht.
  unfold globalinst_typing in *; destruct x; remove_bools_options.
  resolve_if_true_eq.
  by eapply value_typing_extension; eauto.
Qed.

Lemma store_extension_eleminst_typing: forall s s' x t,
    store_extension s s' ->
    eleminst_typing s x = Some t ->
    eleminst_typing s' x = Some t.
Proof.
  move => s s' x t Hst Ht.
  unfold eleminst_typing in *; destruct x; remove_bools_options.
  resolve_if_true_eq.
  apply list_all_forall.
  move => a Hin.
  move/allP in Hif.
  move/inP in Hin.
  apply Hif in Hin.
  move/eqP in Hin.
  remove_bools_options.
  by eapply value_typing_extension; eauto.
Qed.

Lemma store_extension_datainst_typing: forall s s' x t,
    store_extension s s' ->
    datainst_typing s x = Some t ->
    datainst_typing s' x = Some t.
Proof.
  move => s s' x t Hst Ht.
  by unfold datainst_typing in *; destruct x; remove_bools_options.
Qed.

Lemma store_extension_funcs_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, funcinst_typing s x t) xs ->
    List.Forall (fun x => exists t, funcinst_typing s' x t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_funcinst_typing; eauto.
Qed.

Lemma store_extension_tables_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, tableinst_typing s x = Some t) xs ->
    List.Forall (fun x => exists t, tableinst_typing s' x = Some t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_tableinst_typing; eauto.
Qed.

Lemma store_extension_mems_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, meminst_typing s x = Some t) xs ->
    List.Forall (fun x => exists t, meminst_typing s' x = Some t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_meminst_typing; eauto.
Qed.

Lemma store_extension_globals_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, globalinst_typing s x = Some t) xs ->
    List.Forall (fun x => exists t, globalinst_typing s' x = Some t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_globalinst_typing; eauto.
Qed.

Lemma store_extension_elems_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, eleminst_typing s x = Some t) xs ->
    List.Forall (fun x => exists t, eleminst_typing s' x = Some t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_eleminst_typing; eauto.
Qed.

Lemma store_extension_datas_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, datainst_typing s x = Some t) xs ->
    List.Forall (fun x => exists t, datainst_typing s' x = Some t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_datainst_typing; eauto.
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

Ltac resolve_store_typing :=
  repeat split;
  repeat lazymatch goal with
  | |- List.Forall (fun x => exists t, funcinst_typing ?s x t) _ =>
      by eapply store_extension_funcs_typing; eauto
  | |- List.Forall (fun x => exists t, tableinst_typing ?s x = Some t) _ =>
      by eapply store_extension_tables_typing; eauto
  | |- List.Forall (fun x => exists t, meminst_typing ?s x = Some t) _ =>
      by eapply store_extension_mems_typing; eauto
  | |- List.Forall (fun x => exists t, globalinst_typing ?s x = Some t) _ =>
      by eapply store_extension_globals_typing; eauto
  | |- List.Forall (fun x => exists t, eleminst_typing ?s x = Some t) _ =>
      by eapply store_extension_elems_typing; eauto
  | |- List.Forall (fun x => exists t, datainst_typing ?s x = Some t) _ =>
      by eapply store_extension_datas_typing; eauto
    end.

Lemma supdate_glob_extension: forall s f i v s' C gt,
  store_typing s ->
  supdate_glob s (f_inst f) i v = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  value_typing s v (tg_t gt) ->
  lookup_N (tc_globals C) i = Some gt ->
  is_mut gt ->
  store_extension s s'.
Proof.
  move => s f i v s' C gt Hst Hupd Hinst Hvaltype Hnth Hmut.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  destruct g0.
  remove_bools_options.
  move/eqP in Hif0.
  eapply component_extension_update; eauto; first by apply global_extension_refl.
  unfold global_extension => /=.
  rewrite eq_refl => /=.
  destruct gt0.
  apply/orP; left; apply/eqP.
  simpl in *.
  rewrite Hnthgt in Hnth.
  injection Hnth as <-.
  unfold is_mut in *; simpl in *; by move/eqP in Hmut.
Qed.

Lemma supdate_glob_typing: forall s f i v s' C gt,
  store_typing s ->
  supdate_glob s (f_inst f) i v = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  value_typing s v (tg_t gt) ->
  lookup_N (tc_globals C) i = Some gt ->
  is_mut gt ->
  store_typing s'.
Proof.
  move => s f i v s' C gt Hst Hupd Hinst Hvaltype Hnth Hmut.
  assert (store_extension s s') as Hstext; first by eapply supdate_glob_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct g0; remove_bools_options; simpl in *.
  rewrite Hnthgt in Hnth; injection Hnth as ->.
  eapply value_typing_extension in Hvaltype; eauto.
  unfold store_typing in *; destruct s; simpl in *.
  unfold_store_operations; remove_bools_options.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hmt Het Hdt.
  eapply Forall_set; eauto; last by apply nth_error_Some_length in Hoption1; lias.
  eapply Forall_lookup in Hoption1; eauto; simpl in *.
  destruct Hoption1 as [t' Ht]; remove_bools_options.
  exists t'; rewrite Hvaltype.
  by resolve_subtyping.
Qed.
    
Lemma stab_update_extension: forall s f x i v s' C tabt,
  store_typing s ->
  stab_update s (f_inst f) x i v = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  value_typing s (VAL_ref v) (T_ref (tt_elem_type tabt)) ->
  lookup_N (tc_tables C) x = Some tabt ->
  store_extension s s'.
Proof.
  move => s f x i v s' C tabt Hst Hupd Hinst Hvaltype Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  destruct t0; remove_bools_options; simpl in *.
  eapply component_extension_update; eauto; first by apply table_extension_refl.
  unfold table_extension, table_type_extension, limits_extension => /=; rewrite eq_refl => /=.
  apply/andP; split; first by lias.
  unfold tab_size in *; simpl in *.
  erewrite nth_error_set_nth_length => //.
  apply nth_error_nth with (x := (VAL_ref_null T_funcref)).
  move/N.ltb_spec0 in Hif.
  by lias.
Qed.

Lemma stab_update_typing: forall s f x i v s' C tabt,
  store_typing s ->
  stab_update s (f_inst f) x i v = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  value_typing s (VAL_ref v) (T_ref (tt_elem_type tabt)) ->
  lookup_N (tc_tables C) x = Some tabt ->
  store_typing s'.
Proof.
  move => s f x i v s' C tabt Hst Hupd Hinst Hvaltype Hnth.
  assert (store_extension s s') as Hstext; first by eapply stab_update_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct t0; remove_bools_options; simpl in *.
  rewrite Hnthtabt in Hnth; injection Hnth as ->.
  unfold store_typing in *; destruct s; simpl in *.
  unfold_store_operations; remove_bools_options.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Hmt Hgt Het Hdt.
  eapply Forall_set; eauto; last by apply nth_error_Some_length in Hoption1; lias.
  eapply Forall_lookup in Hoption1; eauto; simpl in *.
  destruct Hoption1 as [vt Ht]; remove_bools_options.
  unfold tab_size in *; simpl in *.
  erewrite set_nth_length; last by lias.
  move/eqP in Hif4.
  rewrite Hif4 eq_refl.
  exists vt.
  resolve_if_true_eq.
  apply list_all_forall.
  move => a Hin.
  apply set_nth_In in Hin.
  destruct Hin as [-> | [m [Hneq Hnth]]].
  - by eapply value_typing_extension in Hvaltype; eauto.
  - eapply list_all_forall in Hif5; eauto.
    + by apply List.nth_error_In in Hnth.
    + by lias.
Qed.

Lemma stab_grow_extension: forall s f x i v s' sz C tabt,
  store_typing s ->
  stab_grow s (f_inst f) x i v = Some (s', sz) ->
  inst_typing s (f_inst f) = Some C -> 
  value_typing s (VAL_ref v) (T_ref (tt_elem_type tabt)) ->
  lookup_N (tc_tables C) x = Some tabt ->
  store_extension s s'.
Proof.
  move => s f x i v s' sz C tabt Hst Hupd Hinst Hvaltype Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  destruct t0, tabt0; simpl in *; remove_bools_options; simpl in *.
  eapply component_extension_update; eauto; first by apply table_extension_refl.
  unfold table_extension, table_type_extension, limits_extension => /=; repeat rewrite eq_refl => /=.
  clear Hif Hif3.
  move/eqP in Hif1; rewrite - Hif1.
  unfold tab_size in *; simpl in *.
  do 2 (try (apply/andP; split => //)); try by lias.
  rewrite List.app_length List.repeat_length.
  by lias.
Qed.

Lemma stab_grow_typing: forall s f x i v s' sz C tabt,
  store_typing s ->
  stab_grow s (f_inst f) x i v = Some (s', sz) ->
  inst_typing s (f_inst f) = Some C -> 
  value_typing s (VAL_ref v) (T_ref (tt_elem_type tabt)) ->
  lookup_N (tc_tables C) x = Some tabt ->
  store_typing s'.
Proof.
  move => s f x i v s' sz C tabt Hst Hupd Hinst Hvaltype Hnth.
  assert (store_extension s s') as Hstext; first by eapply stab_grow_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct t0, tabt0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthtabt in Hnth; injection Hnth as <-.
  unfold store_typing in *; destruct s; simpl in *.
  unfold_store_operations; remove_bools_options.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Hmt Hgt Het Hdt.
  unfold tab_size in *; simpl in *.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin.
  destruct Hin as [-> | [m [Hneq Hnth]]].
  - unfold tableinst_typing => /=.
    exists (Build_table_type (Build_limits (N.of_nat (length tableinst_elem) + i)%N (lim_max tt_limits)) tt_elem_type).
    unfold tabletype_valid => /=.
    rewrite Hif3 List.app_length List.repeat_length.
    replace (_ == _) with true; last first.
    { symmetry; apply/eqP. by lias. }
    { resolve_if_true_eq.
      rewrite all_cat.
      apply/andP; split => //.
      apply all_repeat.
      by eapply value_typing_extension in Hvaltype; try by apply Hstext.
    }
  - eapply List.Forall_forall in Htt; eauto.
    + by apply List.nth_error_In in Hnth.
    + by apply nth_error_Some_length in Hoption2; lias.
Qed.

Lemma selem_drop_extension: forall s f x s' C tref,
  store_typing s ->
  selem_drop s (f_inst f) x = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_elems C) x = Some tref ->
  store_extension s s'.
Proof.
  move => s f x s' C tref Hst Hupd Hit Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  destruct e0; simpl in *; remove_bools_options; simpl in *.
  eapply component_extension_update; eauto; first by apply elem_extension_refl.
  unfold elem_extension => /=; repeat rewrite eq_refl => /=.
  rewrite Hnth in Hnthet; injection Hnthet as <-.
  rewrite Hoption0 in Hnthselem; injection Hnthselem as <-.
  by lias.
Qed.

Lemma selem_drop_typing: forall s f x s' C tref,
  store_typing s ->
  selem_drop s (f_inst f) x = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_elems C) x = Some tref ->
  store_typing s'.
Proof.
  move => s f x s' C tref Hst Hupd Hit Hnth.
  assert (store_extension s s') as Hstext; first by eapply selem_drop_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct e0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthselem in Hoption0; injection Hoption0 as ->.
  rewrite Hnth in Hnthet; injection Hnthet as <-.
  unfold store_typing in *; destruct s; simpl in *.
  unfold_store_operations; remove_bools_options.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hmt Hgt Hdt.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin.
  destruct Hin as [-> | [m [Hneq Hnth']]] => //=; first by exists tref.
  - eapply List.Forall_forall in Het; eauto.
    + by apply List.nth_error_In in Hnth'.
    + by apply nth_error_Some_length in Hnthselem; lias.
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
  apply/andP; split; last by lias.
  unfold limits_extension.
  apply/andP; split; by lias.
Qed.

Lemma mem_extension_grow: forall s m c mem t,
    meminst_typing s m = Some t ->
    mem_grow m c = (Some mem) ->
    mem_extension m mem /\
      exists mt, meminst_typing s mem = Some mt.
Proof.
  move => s m c mem t Htype HMGrow.
  unfold meminst_typing in Htype; destruct m.
  remove_bools_options.
  unfold mem_extension, limits_extension.
  unfold mem_grow in HMGrow.
  unfold mem_size, mem_length, memory_list.mem_length in *.
  simpl in *.
  move/eqP in Hif0.
  unfold memtype_valid, limit_valid_range in Hif.
  remove_bools_options => /=; rewrite List.app_length List.repeat_length Nat2N.inj_add nat_of_add_bin eq_refl; split => /=; try by rewrite Hif0 N.div_mul; lias.
  - unfold memtype_valid, limit_valid_range => /=.
    rewrite Hif0 N.div_mul in Hif1 => //=.
    rewrite Hif0 N.div_mul => //.
    rewrite H1 Hif1.
    replace ((lim_min t + c <=? mem_limit_bound)%N) with true => /=; last by lias.
    exists (Build_limits (N.add (lim_min t) c) (Some u)).
    resolve_if_true_eq.
    apply/eqP.
    unfold memory_list.mem_length, memory_list.mem_grow; rewrite List.app_length List.repeat_length => /=.
    by lias.
  - unfold memtype_valid, limit_valid_range => /=.
    rewrite Hif Hif0 N.div_mul => //=.
    exists (Build_limits (N.add (lim_min t) c) None).
    resolve_if_true_eq.
    apply/eqP.
    unfold memory_list.mem_length, memory_list.mem_grow; rewrite List.app_length List.repeat_length => /=.
    by lias.
Qed.

Lemma smem_store_extension: forall s f n off v s' C t mt,
  store_typing s ->
  smem_store s (f_inst f) n off v t = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_extension s s'.
Proof.
  move => s f n off v s' C t mt Hst Hupd Hit Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  rewrite Hnth in Hnthmt; injection Hnthmt as ->.
  destruct m0; simpl in *; remove_bools_options; simpl in *.
  eapply component_extension_update; eauto; first by apply mem_extension_refl.
  by apply mem_extension_store in Hoption1.
Qed.

Lemma smem_store_typing: forall s f n off v s' C t mt,
  store_typing s ->
  smem_store s (f_inst f) n off v t = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_typing s'.
Proof.
  move => s f n off v s' C t mt Hst Hupd Hit Hnth.
  assert (store_extension s s') as Hstext; first by eapply smem_store_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct m0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthmt in Hnth; injection Hnth as <-.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hgt Het Hdt.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin.
  destruct Hin as [-> | [m0 [Hneq Hnth']]] => //=.
  - exists m1.(meminst_type).
    unfold meminst_typing => /=.
    destruct m1 => //=.
    unfold store in Hoption1; remove_bools_options.
    apply write_bytes_preserve_type in Hoption1; simpl in *.
    destruct Hoption1 as [-> Hmemlen].
    unfold mem_length in *; simpl in *.
    rewrite Hif.
    resolve_if_true_eq.
    by lias.
  - eapply List.Forall_forall in Hmt; eauto.
    + by apply List.nth_error_In in Hnth'.
    + by apply nth_error_Some_length in Hoption2; lias.
Qed.

(* Currently same as store *)
Lemma smem_store_packed_extension: forall s f n off v tp s' C mt,
  store_typing s ->
  smem_store_packed s (f_inst f) n off v tp = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_extension s s'.
Proof.
  move => s f n off v tp s' C a Hst Hupd Hit Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  rewrite Hnth in Hnthmt; injection Hnthmt as ->.
  destruct m0; simpl in *; remove_bools_options; simpl in *.
  eapply component_extension_update; eauto; first by apply mem_extension_refl.
  by apply mem_extension_store in Hoption1.
Qed.

(* Currently store_packed is the same as store *)
Lemma smem_store_packed_typing: forall s f n off v tp s' C mt,
  store_typing s ->
  smem_store_packed s (f_inst f) n off v tp = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_typing s'.
Proof.
  move => s f n off v tp s' C a Hst Hupd Hit Hnth.
  assert (store_extension s s') as Hstext; first by eapply smem_store_packed_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct m0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthmt in Hnth; injection Hnth as <-.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hgt Het Hdt.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin.
  destruct Hin as [-> | [m0 [Hneq Hnth']]] => //=.
  - exists m1.(meminst_type).
    unfold meminst_typing => /=.
    destruct m1 => //=.
    unfold store_packed, store in Hoption1; remove_bools_options.
    apply write_bytes_preserve_type in Hoption1; simpl in *.
    destruct Hoption1 as [-> Hmemlen].
    unfold mem_length in *; simpl in *.
    rewrite Hif.
    resolve_if_true_eq.
    by lias.
  - eapply List.Forall_forall in Hmt; eauto.
    + by apply List.nth_error_In in Hnth'.
    + by apply nth_error_Some_length in Hoption2; lias.
Qed.

Lemma smem_grow_extension: forall s f n s' sz C mt,
  store_typing s ->
  smem_grow s (f_inst f) n = Some (s', sz) ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_extension s s'.
Proof.
  move => s f n s' sz C a Hst Hupd Hit Hnth.
  unfold smem_grow in Hupd.
  unfold store_extension => /=; remove_bools_options; resolve_store_inst_lookup => /=.
  resolve_store_extension.
  remove_bools_options.
  destruct m0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnth in Hnthmt; injection Hnthmt as ->.
  eapply component_extension_update; eauto; first by apply mem_extension_refl.
  eapply mem_extension_grow with (s := s) (t := mt) in Hoption1 as [??]; eauto.
  unfold meminst_typing.
  by rewrite Hif Hif0.
Qed.

Lemma smem_grow_typing: forall s f n s' sz C mt,
  store_typing s ->
  smem_grow s (f_inst f) n = Some (s', sz) ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_typing s'.
Proof.
  move => s f n s' sz C a Hst Hupd Hit Hnth.
  assert (store_extension s s') as Hstext; first by eapply smem_grow_extension; eauto.
  unfold smem_grow in Hupd; remove_bools_options.
  resolve_store_inst_lookup; destruct m0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthmt in Hnth; injection Hnth as <-.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hgt Het Hdt.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin; last by apply nth_error_Some_length in Hoption2; lias.
  clear Hstext.
  destruct Hin as [-> | [m0 [Hneq Hnth']]] => //=.
  - eapply mem_extension_grow in Hoption1 as [??]; eauto.
    unfold meminst_typing.
    by rewrite Hif Hif0.
  - eapply List.Forall_forall in Hmt; eauto.
    by apply List.nth_error_In in Hnth'.
Qed.
    
Lemma sdata_drop_extension: forall s f x s' C t,
  store_typing s ->
  sdata_drop s (f_inst f) x = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_datas C) x = Some t ->
  store_extension s s'.
Proof.
  move => s f x s' C t Hst Hupd Hit Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  rewrite Hoption0 in Hnthsdata; injection Hnthsdata as ->.
  rewrite Hnth in Hnthdt; injection Hnthdt as ->.
  eapply component_extension_update; eauto; first by apply data_extension_refl.
  unfold data_extension => /=; rewrite eq_refl. by lias.
Qed.

Lemma sdata_drop_typing: forall s f x s' C t,
  store_typing s ->
  sdata_drop s (f_inst f) x = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_datas C) x = Some t ->
  store_typing s'.
Proof.
  move => s f x s' C t Hst Hupd Hit Hnth.
  assert (store_extension s s') as Hstext; first by eapply sdata_drop_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct d0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthsdata in Hoption0; injection Hoption0 as ->.
  rewrite Hnth in Hnthdt; injection Hnthdt as <-.
  unfold store_typing in *; destruct s; simpl in *.
  unfold_store_operations; remove_bools_options.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hmt Hgt Het.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin; last by apply nth_error_Some_length in Hnthsdata; lias.
  destruct Hin as [-> | [m [Hneq Hnth']]] => //=.
  - exists tt.
    by unfold datainst_typing.
  - eapply List.Forall_forall in Hdt; eauto.
    by apply List.nth_error_In in Hnthsdata; eauto.
Qed.
    
(* Note that although config_typing gives quite a stronger constraint on C', we allow much more flexibility here due to the need in inductive cases. *)
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
  induction HReduce => //; subst; try (move => tf C C' HIT Hmatch HType HST; intros; destruct tf; invert_e_typing => //; (try by apply store_extension_same)).
  - (* Invoke host *)
    by eapply host_application_extension; eauto.
  - (* global_set *)
    unify_principal; simpl in Hsubs; remove_bools_options.
    eapply supdate_glob_extension; eauto; first by resolve_value_principal_typing.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
  - (* table update *)
    unify_principal; simpl in Hsubs; remove_bools_options.
    eapply stab_update_extension; eauto; last by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
    by resolve_value_principal_typing.
  - (* table grow *)
    unify_principal; simpl in Hsubs0; remove_bools_options.
    eapply stab_grow_extension; eauto; last by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
    by resolve_value_principal_typing.
  - (* elem drop *)
    eapply selem_drop_extension; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjr; f_equal.
  - (* memory store *)
    eapply smem_store_extension; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
  - (* memory store_packed *)
    eapply smem_store_packed_extension; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
  - (* memory grow *)
    eapply smem_grow_extension; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjr; f_equal.
  - (* data drop *)
    eapply sdata_drop_extension; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjr; f_equal.
  - (* label *)
    eapply lfilled_es_type_exists in HType; eauto.
    destruct HType as [lab [t1s [t2s Hetype]]].
    by eapply IHHReduce in Hetype; eauto.
  - (* frame *)
    inversion Hconjl0 as [s2 f2 es2 ors rs C2 Hstype Hftype ? Hetype]; subst; clear Hconjl0.
    unfold frame_typing in Hftype; remove_bools_options.
    destruct Hftype as [ts [-> Hvaltype]].
    eapply IHHReduce in Hetype; eauto.
    by unfold inst_match; lias.
Qed.
    
Lemma store_typing_reduce: forall s f es s' f' es' C C' tf hs hs',
    reduce hs s f es hs' s' f' es' ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C' ->
    e_typing s C' es tf ->
    store_typing s ->
    store_typing s'.
Proof.
  move => s f es s' f' es' C C' tf hs hs' HReduce.
  move: tf C C'.
  induction HReduce => //; subst; try (move => tf C C' HIT Hmatch HType HST; intros; destruct tf; invert_e_typing => //).
  - (* host call *)
    by eapply host_application_typing; eauto.
  - (* global_set *)
    unify_principal; simpl in Hsubs; remove_bools_options.
    eapply supdate_glob_typing; eauto; first by resolve_value_principal_typing.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
  - (* table update *)
    unify_principal; simpl in Hsubs; remove_bools_options.
    eapply stab_update_typing; eauto; last by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
    by resolve_value_principal_typing.
  - (* table grow *)
    unify_principal; simpl in Hsubs0; remove_bools_options.
    eapply stab_grow_typing; eauto; last by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
    by resolve_value_principal_typing.
  - (* elem drop *)
    eapply selem_drop_typing; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjr; f_equal.
  - (* memory store *)
    eapply smem_store_typing; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
  - (* memory store_packed *)
    eapply smem_store_packed_typing; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
  - (* memory grow *)
    eapply smem_grow_typing; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjr; f_equal.
  - (* data drop *)
    eapply sdata_drop_typing; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjr; f_equal.
  - (* label *)
    eapply lfilled_es_type_exists in HType; eauto.
    destruct HType as [lab [t1s [t2s Hetype]]].
    by eapply IHHReduce in Hetype; eauto.
  - (* frame *)
    inversion Hconjl0 as [s2 f2 es2 ors rs C2 Hstype Hftype ? Hetype]; subst; clear Hconjl0.
    unfold frame_typing in Hftype; remove_bools_options.
    destruct Hftype as [ts [-> Hvaltype]].
    eapply IHHReduce in Hetype; eauto.
    by unfold inst_match; lias.
Qed.
    
Lemma inst_typing_reduce: forall hs s f es hs' s' f' es' C C' tf,
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C' ->
    e_typing s C' es tf ->
    exists C', inst_typing s' f'.(f_inst) = Some C' /\ context_extension C C'.
Proof.
  move => hs s f es hs' s' f' es' C C' tf Hreduce Hst Hit Hmatch Htype.
  erewrite <- reduce_inst_unchanged; eauto.
  eapply inst_typing_extension; last by apply Hit.
  eapply store_extension_reduce in Hreduce; by eauto.
Qed.

Lemma extensions_e_typing: forall s s' C C' es tf,
    store_typing s ->
    store_typing s' ->
    store_extension s s' ->
    context_extension C C' ->
    e_typing s C es tf ->
    e_typing s' C' es tf.
Proof.
  move => s s' C C' es tf Hst1 Hst2 Hsext Hcext Hetype.
  eapply context_extension_typing; eauto.
  by eapply store_extension_e_typing in Hetype; eauto.
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
    values_typing s f.(f_locs) ts ->
    values_typing s f'.(f_locs) ts.
Proof.
  move => s f es s' f' es' C C0 ts t1s t2s hs hs' HReduce HST HIT.
  move: C0 t1s t2s.
  induction HReduce => //; move => C0 t1s' t2s' Hmatch Hlocs HType Hvaltype; invert_e_typing; try by eexists; rewrite Hvaltype; split => //; resolve_subtyping.
  - unify_principal.
    simpl in Hsubs; remove_bools_options.
    rewrite H1.
    unfold values_typing in *.
    eapply all2_set_nth1; eauto; by resolve_value_principal_typing.
  - eapply lfilled_es_type_exists in HType; eauto.
    destruct HType as [lab' [ts1 [ts2 Hetype]]].
    by eapply IHHReduce; (try apply Hetype); eauto.
Qed.

Lemma upd_local_label_return_overwrite: forall C loc1 lab1 ret1 loc2 lab2 ret2,
    upd_local_label_return (upd_local_label_return C loc2 lab2 ret2) loc1 lab1 ret1 = upd_local_label_return C loc1 lab1 ret1.
Proof.
  done.
Qed.
  
Lemma t_preservation_locs_type: forall s f es s' f' es' C C0 ts t1s t2s hs hs',
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C0 ->
    C0.(tc_locals) = ts ->
    e_typing s C0 es (Tf t1s t2s) ->
    values_typing s f.(f_locs) ts ->
    values_typing s' f'.(f_locs) ts.
Proof.
  move => s f es s' f' es' C C0 ts t1s t2s hs hs' HReduce HST HIT Hmatch Hlocs HType Hvaltype.
  eapply t_preservation_locs_type_aux in Hvaltype; eauto.
  eapply values_typing_extension in Hvaltype; eauto.

  by eapply store_extension_reduce; eauto.
Qed.

Lemma t_preservation_e: forall s f es s' f' es' tlocs C C' t1s t2s lab ret hs hs',
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s f.(f_inst) = Some C ->
    inst_typing s' f'.(f_inst) = Some C' ->
    values_typing s f.(f_locs) tlocs ->
    e_typing s (upd_local_label_return C tlocs lab ret) es (Tf t1s t2s) ->
    e_typing s' (upd_local_label_return C' tlocs lab ret) es' (Tf t1s t2s).
Proof.
  move => s f es s' f' es' tlocs C C' t1s t2s lab ret hs hs' HReduce.
  move: C C' ret lab t1s t2s tlocs.
  induction HReduce; move => C C' ret lab tx ty tlocs HST1 HST2 HIT1 HIT2 Hloctype HType; subst; try eauto; try (by apply ety_trap); invert_e_typing; simpl in *; unify_principal; resolve_e_typing; unfold_store_operations; resolve_store_inst_lookup; remove_bools_options => //=; simpl in *; simplify_multieq; unify_principal; resolve_e_typing => //.
  - (* reduce_simple *)
    by eapply t_simple_preservation; eauto.
  - (* Ref_func *)
    eapply inst_typing_func_lookup in H; eauto.
    destruct H as [tf [Hext Hnth]].
    simplify_multieq.
    by eapply ety_ref; eauto.
  - (* Block *)
    erewrite <- inst_typing_expand_eq in Hconjl0; eauto.
    rewrite Hconjl0 in H; injection H as <- <-.
    specialize (values_typing_length H2_values) as Hlen.
    repeat rewrite length_is_size in H2.
    repeat rewrite length_is_size in Hlen.
    rewrite v_to_e_size in H2.
    specialize (instr_subtyping_compose_eq H1_values Htisub) as [Hsubi Hsubt]; first by lias.
    clear H1_values Htisub.
    eapply ety_subtyping; last by apply Hsubi.
    {
      eapply ety_label; eauto; first by apply et_empty; resolve_subtyping.
      eapply et_composition'; eauto; resolve_e_typing; first reflexivity.
      eapply ety_a in Hconjr0; eauto.
      eapply ety_subtyping; eauto.
      eapply instr_subtyping_weaken1; eauto.
      by resolve_subtyping.
    }
  - (* Loop *)
    remember Hconjl0 as Het; clear HeqHet.
    erewrite <- inst_typing_expand_eq in Hconjl0; eauto.
    rewrite Hconjl0 in H; injection H as <- <-.
    specialize (values_typing_length H2_values) as Hlen.
    repeat rewrite length_is_size in H2.
    repeat rewrite length_is_size in Hlen.
    rewrite v_to_e_size in H2.
    specialize (instr_subtyping_compose_eq H1_values Htisub) as [Hsubi Hsubt]; first by lias.
    clear H1_values Htisub.
    eapply ety_subtyping; last by apply Hsubi.
    {
      eapply ety_label; eauto.
      { apply ety_a' => //=.
        by apply bet_loop; eauto.
      }
      { eapply et_composition'; eauto; resolve_e_typing; first reflexivity.
        eapply ety_a in Hconjr0; eauto.
        eapply ety_subtyping; eauto.
        eapply instr_subtyping_weaken1; eauto.
        by resolve_subtyping.
      }
    }
  - (* Call *)
    eapply inst_typing_func_lookup in H as [t0 [Hft Hnth]]; eauto.
    destruct (cl_type f0) as [ts1 ts2] eqn:Htf.
    simplify_multieq.
    by eapply ety_subtyping; eauto; first by apply ety_invoke; eauto.
  - (* Call_indirect *)
    destruct Hft as [<- ?].
    apply ety_invoke.
    { unfold ext_func_typing.
      by rewrite H0 -Hinj => //=.
    }
    
  - (* Invoke native *)
    destruct extr as [ts1' ts2'].
    destruct Hft as [<- [Hvalid Hftype]].
    simpl in Hftype; remove_bools_options; destruct f0.
    destruct Hftype as [Heq [Hetype _]].
    injection Heq as <- <-.
    unfold ext_func_typing in Hconjr.
    rewrite H in Hconjr; simpl in Hconjr; injection Hconjr as <- <-.
    specialize (values_typing_length H2_values) as Hlen.
    repeat rewrite length_is_size in H5.
    repeat rewrite length_is_size in Hlen.
    specialize (instr_subtyping_compose_eq H1_values Htisub) as [Hsubi Hsubt]; first by lias.
    clear H1_values Htisub.
    eapply ety_subtyping; first apply ety_frame; try by eauto.
    econstructor.
    + unfold frame_typing => /=.
      rewrite Hoption.
      eexists; split; first done.
      specialize (values_typing_trans H2_values Hsubt) as Hvts.
      erewrite values_typing_cat; by [done | apply Hvts | eapply default_values_typing; eauto].
    + by erewrite -> inst_t_context_local_empty; eauto.
    + rewrite cats0.
      eapply ety_label; eauto.
      * eapply ety_subtyping with (t1s := nil) (t2s := nil); first apply et_empty; by resolve_subtyping.
      * apply ety_a with (s := s) in Hetype.
        uapply Hetype => /=.
        by erewrite inst_t_context_label_empty; eauto.
        
  - (* Invoke host *)
    unfold ext_func_typing in Hconjr.
    remove_bools_options; simpl in Hft; destruct Hft as [<- Hvalid].
    simpl cl_type in Htisub.
    assert (length vcs = length ts_values) as Hlen; first by apply values_typing_length in H2_values.
    rewrite - H3 in Hlen.
    repeat rewrite length_is_size in Hlen.
    specialize (instr_subtyping_compose_eq H1_values Htisub) as [Hsubi Hsubt]; first by lias.
    clear H1_values Htisub.
    eapply values_typing_trans in H2_values; eauto.
    by eapply ety_subtyping; first apply result_e_type; first eapply host_application_respect; eauto.
    
  - (* Local_get *)
    unfold lookup_N in *.
    eapply all2_nth_impl in Hloctype; eauto.
    destruct Hloctype as [vt [Hvaltype Hnth]].
    simplify_multieq.
    by resolve_e_typing.
  - (* Global_get *)
    destruct g; remove_bools_options; simpl in *.
    eapply et_value_typing'; eauto; reflexivity.
    
  - (* Table_get *)
    destruct t0; remove_bools_options.
    eapply all_projection in Hif1; eauto.
    by resolve_e_typing.
  - (* Table fill *)
    destruct tab; remove_bools_options.
    rewrite -cat1s.
    eapply et_composition'.
    + resolve_e_typing.
      eapply instr_subtyping_weaken1; first reflexivity.
      simpl.
      by resolve_subtyping.
    + resolve_e_typing.
      eapply instr_subtyping_weaken1; first reflexivity.
      simpl.
      by resolve_subtyping.
  - (* Table copy 1 *)
    destruct taby; simpl in *.
    remove_bools_options.
    rewrite -cat1s; apply et_composition' with (t2s := [::T_num T_i32; T_ref (tt_elem_type extr)]).
    { resolve_e_typing.
      simplify_lists.
      apply instr_subtyping_weaken; reflexivity.
    }
    rewrite -cat1s; apply et_composition' with (t2s := nil); by resolve_e_typing.
  - (* Table copy 2 *)
    destruct taby; simpl in *.
    remove_bools_options.
    rewrite -cat1s; apply et_composition' with (t2s := [::T_num T_i32; T_ref (tt_elem_type extr)]).
    { resolve_e_typing.
      simplify_lists.
      apply instr_subtyping_weaken; reflexivity.
    }
    rewrite -cat1s; apply et_composition' with (t2s := nil); by resolve_e_typing.
  - (* Table_init *)
    destruct tab; simpl in *.
    remove_bools_options.
    specialize (inst_typing_elem_lookup HIT1 Hoption0) as [elemt [ei [Hselem [Helemt Hnthet]]]].
    specialize (store_typing_elem_lookup HST1 H0) as [et Het].
    simplify_multieq.
    unfold eleminst_typing in Helemt.
    destruct ei.
    remove_bools_options.
    eapply all_projection in Hif2; eauto.   
    resolve_e_typing => //.
    rewrite -cat1s; apply et_composition' with (t2s := nil); by resolve_e_typing.
      
  - (* Load None *)
    destruct t => /=; by resolve_subtyping.
  - (* Load Some *)
    destruct t => /=; by resolve_subtyping.
  - (* Memory fill *)
    destruct mem.
    remove_bools_options.
    by rewrite -cat1s; apply et_composition' with (t2s := nil); resolve_e_typing.
  - (* Memory copy 1 *)
    destruct mem.
    remove_bools_options.
    rewrite -cat1s; apply et_composition' with (t2s := [::T_num T_i32; T_num T_i32]).
    { resolve_e_typing.
      simplify_lists.
      apply instr_subtyping_weaken; by resolve_subtyping.
    }
    by rewrite -cat1s; apply et_composition' with (t2s := nil); resolve_e_typing.
  - (* Memory copy 2 *)
    destruct mem.
    remove_bools_options.
    rewrite -cat1s; apply et_composition' with (t2s := [::T_num T_i32; T_num T_i32]).
    { resolve_e_typing.
      simplify_lists.
      apply instr_subtyping_weaken; by resolve_subtyping.
    }
    by rewrite -cat1s; apply et_composition' with (t2s := nil); resolve_e_typing.
    destruct mem.
    remove_bools_options.
  - (* Memory init *)
    by rewrite -cat1s; apply et_composition' with (t2s := nil); resolve_e_typing.
    
  - (* Label *)
    assert (store_extension s s') as Hext.
    { eapply store_extension_reduce; (try by apply HType); eauto.
      - by eapply r_label; eauto.
      - unfold inst_match => /=.
        by repeat rewrite eq_refl.
    }
    remember HIT2 as HIT3; clear HeqHIT3.
    erewrite <- reduce_inst_unchanged in HIT2; eauto.
    specialize (inst_typing_extension Hext HIT1) as [C'' [Hit Hcext]].
    simplify_multieq.
    assert (values_typing s' f'.(f_locs) tlocs) as Hvaltype.
    {
      specialize (lfilled_es_type_exists erefl HType) as Hestype.
      destruct Hestype as [lab' [ts1 [ts2 Hestype]]].
      eapply t_preservation_locs_type; eauto.
      - unfold inst_match; by repeat rewrite eq_refl.
      - done.
    }
    remember (lfill lh es) as les.
    remember (lfill lh es') as les'.
    generalize dependent les'.
    generalize dependent les.
    move: lh lab tx ty.
    elim.
    + move => vs es0 lab tx ty ? ? Hetype ? ?; subst; simpl in *.
      invert_e_typing.
      apply et_composition' with (t2s := tx ++ ts_values).
      { apply et_weakening_empty_1.
        apply et_values_typing.
        by specialize (values_typing_extension Hext H2_values) as Hvalues'.
      }
      eapply et_composition'; eauto; last first.
      { eapply extensions_e_typing; (try by apply H2_comp0); eauto.
        by unfold context_extension in *; destruct C, C''; remove_bools_options; lias.
      }
      eapply IHHReduce; eauto.
      eapply ety_subtyping; try by apply H1_comp0.
      eapply instr_subtyping_weaken1; first reflexivity.
      by apply instr_subtyping_empty1_impl' in H1_values.
    + move => k0 vs n es1 lh' IH es2 lab tx ty ? -> /=Hetype ? ->.
      invert_e_typing.
      eapply et_composition' with (t2s := tx ++ ts_values); eauto.
      { apply et_weakening_empty_1.
        apply et_values_typing.
        by eapply values_typing_extension; eauto.
      }
      rewrite -cat1s.
      eapply et_composition'; eauto; last first.
      { eapply extensions_e_typing; (try by apply H2_comp0); eauto.
        by unfold context_extension in *; destruct C, C''; remove_bools_options; lias.
      }
      eapply IH in Hconjl1; eauto.
      eapply ety_subtyping; first eapply ety_label; eauto.
      * eapply extensions_e_typing; (try by apply Hext); (try by apply Hconjl0); eauto.
        by unfold context_extension in *; destruct C, C''; remove_bools_options; lias.
      * specialize (instr_subtyping_compose_ge H1_values Htisub) as [Hsubi Hsubt]; first by lias.
        apply instr_subtyping_empty1_impl' in Hsubi.
        simpl in Hsubi; rewrite subn0 take_size in Hsubi.
        apply instr_subtyping_empty1_impl.
        by rewrite -catA.
        
  - (* r_frame *)
    inversion Hconjl0; subst; clear Hconjl0.
    unfold frame_typing in H1.
    remove_bools_options.
    destruct H1 as [ts [-> Hvaltype]].

    assert (store_extension s s') as Hext.
    { eapply store_extension_reduce; eauto.
      unfold inst_match => /=.
      by repeat rewrite eq_refl.
    }
    assert (values_typing s' f'.(f_locs) ts) as Hvaltype'.
    {
      eapply t_preservation_locs_type; eauto => /=.
      - unfold inst_match; by repeat rewrite eq_refl.
      - simpl. by erewrite inst_t_context_local_empty; eauto; rewrite cats0.
    }
    erewrite -> inst_t_context_local_empty in *; eauto.
    rewrite -> cats0 in *.
    assert (inst_match t (upd_return (upd_local t ts) (Some extr))) as Hmatch; first by unfold inst_match; lias.
    specialize (inst_typing_reduce HReduce HST1 Hoption Hmatch H6) as [C'' [Hit Hcext]].
    apply ety_frame => //.
    eapply mk_thread_typing; eauto.
    { unfold frame_typing.
      rewrite Hit.
      by erewrite -> inst_t_context_local_empty; eauto.
    }
    {
      rewrite cats0.
      unfold upd_return, upd_local in *; simpl in *.
      rewrite -> upd_local_label_return_overwrite in *.
      eapply IHHReduce; eauto.
      by erewrite -> inst_t_context_label_empty in *; eauto.
    }
Qed.

Theorem t_preservation: forall s f es s' f' es' ts hs hs',
    reduce hs s f es hs' s' f' es' ->
    config_typing s (f, es) ts ->
    config_typing s' (f', es') ts.
Proof.
  move => s f es s' f' es' ts hs hs' HReduce HType.
  inversion HType; inversion H0; subst; clear HType.
  unfold frame_typing in H3; remove_bools_options.
  destruct H3 as [tlocs [-> Hloctype]].

  assert (store_extension s s') as Hstoreext.
  { eapply store_extension_reduce; eauto.
    by unfold inst_match; repeat rewrite eq_refl.
  }
  assert (store_typing s') as Hstoretype.
  { eapply store_typing_reduce; try (by apply H8); eauto.
    by unfold inst_match; repeat rewrite eq_refl.
  }

  specialize (inst_typing_extension Hstoreext Hoption) as Hit'.
  erewrite -> reduce_inst_unchanged in Hit'; eauto.
  destruct Hit' as [C' [Hit' Hcext]].

  erewrite -> inst_t_context_local_empty in *; eauto.
  rewrite -> cats0 in *.

  constructor => //.
  econstructor; eauto.
  - unfold frame_typing.
    rewrite Hit'.
    exists tlocs.
    split; first done.
    eapply t_preservation_locs_type in Hloctype; eauto; try by [].
    unfold inst_match; destruct t => /=; by lias.
  - unfold upd_return, upd_local in *.
    rewrite -> upd_local_label_return_overwrite in *.
    simpl in *.
    erewrite -> inst_t_context_local_empty in *; eauto.
    erewrite -> inst_t_context_label_empty in *; eauto.
    rewrite -> cats0 in *.
    by eapply t_preservation_e; eauto.
Qed.

End Host.
