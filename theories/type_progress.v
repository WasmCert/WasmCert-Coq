(** Proof of progress **)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program.Equality NArith ZArith.
From Wasm Require Export operations typing datatypes_properties typing opsem properties type_preservation typing_inversion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Variable host_function : eqType.

Let store_record := store_record host_function.
Let function_closure := function_closure host_function.
Let e_typing : store_record -> t_context -> seq administrative_instruction -> function_type -> Prop :=
  @e_typing _.
Let s_typing := @s_typing host_function.
Let inst_typing := @inst_typing host_function.
Let sglob : store_record -> instance -> nat -> option global := @sglob _.
Let smem_ind : store_record -> instance -> option nat := @smem_ind _.

Let host := host host_function.

Variable host_instance : host.

Let host_state := host_state host_instance.

Let host_application := @host_application host_function host_instance.

Let reduce : host_state -> store_record -> frame -> seq administrative_instruction ->
             host_state -> store_record -> frame -> seq administrative_instruction -> Prop
  := @reduce _ _.

Definition terminal_form (es: seq administrative_instruction) :=
  const_list es \/ es = [::AI_trap].

Lemma reduce_trap_left: forall vs,
    const_list vs ->
    vs <> [::] ->
    reduce_simple (vs ++ [::AI_trap]) [::AI_trap].
Proof.
  move => vs HConst H.
  apply const_es_exists in HConst as [vs0 Heq].
  destruct vs => //=; eapply rs_trap; try by destruct vs => //=.
  instantiate (1 := (LH_base vs0 nil)) => /=; by rewrite - Heq.
Qed.

Lemma v_e_trap: forall vs es,
    const_list vs ->
    vs ++ es = [::AI_trap] ->
    vs = [::] /\ es = [::AI_trap].
Proof.
  move => vs es HConst H.
  destruct vs => //=.
  destruct vs => //=. destruct es => //=.
  simpl in H. inversion H. by subst.
Qed.

Lemma cat_split: forall {X:Type} (l l1 l2: seq X),
    l = l1 ++ l2 ->
    l1 = take (size l1) l /\
    l2 = drop (size l1) l.
Proof.
  move => X l l1.
  generalize dependent l.
  induction l1 => //=; move => l l2 HCat; subst => //=.
  - split. by rewrite take0. by rewrite drop0.
  - edestruct IHl1.
    instantiate (1 := l2). eauto.
    split => //.
    by f_equal.
Qed.

Lemma reduce_composition: forall s cs f es es0 s' f' es' hs hs',
    const_list cs ->
    reduce hs s f es hs' s' f' es' ->
    reduce hs s f (cs ++ es ++ es0) hs' s' f' (cs ++ es' ++ es0).
Proof.
  move => s cs f es es0 s' f' es' hs hs' HConst HReduce.
  apply const_es_exists in HConst as [vcs Heq].
  eapply r_label with (lh := LH_base vcs es0) => //=; eauto; by rewrite - Heq => //.
Qed.

Lemma reduce_composition_right: forall s f es es0 s' f' es' hs hs',
    reduce hs s f es hs' s' f' es' ->
    reduce hs s f (es ++ es0) hs' s' f' (es' ++ es0).
Proof.
  move => s f es es0 s' f' es' hs hs' HReduce.
  eapply reduce_composition in HReduce.
  instantiate (1 := es0) in HReduce.
  instantiate (1 := [::]) in HReduce.
  by simpl in HReduce.
  by [].
Qed.

Lemma reduce_composition_left: forall s cs f es s' f' es' hs hs',
    const_list cs ->
    reduce hs s f es hs' s' f' es' ->
    reduce hs s f (cs ++ es) hs' s' f' (cs ++ es').
Proof.
  move => s f es es0 s' f' es' hs hs' HConst HReduce.
  eapply reduce_composition in HReduce; eauto.
  instantiate (1 := [::]) in HReduce.
  by repeat rewrite cats0 in HReduce.
Qed.

Lemma terminal_form_v_e: forall vs es,
    const_list vs ->
    terminal_form (vs ++ es) ->
    terminal_form es.
Proof.
  move => vs es HConst HTerm.
  unfold terminal_form in HTerm.
  destruct HTerm.
  - unfold terminal_form. left.
    apply const_list_split in H. by destruct H.
  - destruct vs => //=.
    + simpl in H. subst. unfold terminal_form. by right.
    + destruct vs => //=. destruct es => //=.
      simpl in H. inversion H. by subst.
Qed.

Lemma terminal_trap: terminal_form [::AI_trap].
Proof.
  unfold terminal_form. by right.
Qed.

Lemma e_b_inverse: forall es,
    es_is_basic es ->
    to_e_list (to_b_list es) = es.
Proof.
  move => es HAI_basic.
  by erewrite e_b_elim; eauto.
Qed.

Lemma typeof_append: forall ts t vs,
    map typeof vs = ts ++ [::t] ->
    exists v,
      vs = take (size ts) vs ++ [::v] /\
      map typeof (take (size ts) vs) = ts /\
      typeof v = t.
Proof.
  move => ts t vs HMapType.
  apply cat_split in HMapType.
  destruct HMapType.
  rewrite -map_take in H.
  rewrite -map_drop in H0.
  destruct (drop (size ts) vs) eqn:HDrop => //=.
  destruct l => //=.
  inversion H0. subst.
  exists v.
  split => //.
  rewrite -HDrop. by rewrite cat_take_drop.
Qed.

Hint Constructors reduce_simple : core.
Hint Constructors opsem.reduce_simple : core.

Ltac invert_typeof_vcs :=
  lazymatch goal with
  | H: map typeof ?vcs = [::_; _; _] |- _ =>
    destruct vcs => //=; destruct vcs => //=; destruct vcs => //=; destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  | H: map typeof ?vcs = [::_; _] |- _ =>
    destruct vcs => //=; destruct vcs => //=; destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  | H: map typeof ?vcs = [::_] |- _ =>
    destruct vcs => //=; destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  | H: map typeof ?vcs = [::] |- _ =>
    destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  end.

Lemma nth_error_map: forall {X Y:Type} (l: seq X) n f {fx: Y},
    List.nth_error (map f l) n = Some fx ->
    exists x, List.nth_error l n = Some x /\
    f x = fx.
Proof.
  move => X Y l n.
  generalize dependent l.
  induction n => //; move => l f fx HN.
  - destruct l => //=.
    simpl in HN. inversion HN. subst. by eauto.
  - destruct l => //=.
    simpl in HN. by apply IHn.
Qed.

Definition not_lf_br (es: seq administrative_instruction) (n: nat) :=
  forall k (lh: lholed n), lfill lh [::AI_basic (BI_br k)] <> es.

Definition not_lf_return (es: seq administrative_instruction) (n: nat) :=
  forall (lh: lholed n), lfill lh [::AI_basic BI_return] <> es.

Lemma nlfbr_right: forall es n es',
    not_lf_br (es ++ es') n ->
    not_lf_br es n.
Proof.
  unfold not_lf_br.
  move => es n es' HNLF k lh HContra.
  subst es.
  rewrite -lfill_push_back_es in HNLF.
  by eapply HNLF.
Qed.

Lemma nlfret_right: forall es n es',
    not_lf_return (es ++ es') n ->
    not_lf_return es n.
Proof.
  unfold not_lf_return.
  move => es n es' HNLF lh HContra.
  subst es.
  rewrite -lfill_push_back_es in HNLF.
  by eapply HNLF.
Qed.

Lemma nlfbr_left: forall es n cs,
    const_list cs ->
    not_lf_br (cs ++ es) n ->
    not_lf_br es n.
Proof.
  unfold not_lf_br.
  move => es n cs HConst HNLF k lh ?.
  subst es.
  apply const_es_exists in HConst as [vs ->].
  erewrite <- lfill_push_front_vs in HNLF; eauto.
  by eapply HNLF.
Qed.

Lemma nlfret_left: forall es n cs,
    const_list cs ->
    not_lf_return (cs ++ es) n ->
    not_lf_return es n.
Proof.
  unfold not_lf_return.
  move => es n cs HConst HNLF lh ?; subst es.
  apply const_es_exists in HConst as [vs ->].
  erewrite <- lfill_push_front_vs in HNLF; eauto.
  by eapply HNLF.
Qed.

Ltac split_et_composition:=
  lazymatch goal with
  | H: e_typing _ _ (_ ++ _) _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let t2s := fresh "t2s" in
    let t3s := fresh "t3s" in
    let Ht1 := fresh "Ht1" in
    let Ht2 := fresh "Ht2" in
    let Ht3 := fresh "Ht3" in
    let Ht4 := fresh "Ht4" in
    apply e_composition_typing in H;
    destruct H as [ts [t1s [t2s [t3s [Ht1 [Ht2 [Ht3 Ht4]]]]]]]; subst
  | H: typing.e_typing _ _ (_ ++ _) _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let t2s := fresh "t2s" in
    let t3s := fresh "t3s" in
    let Ht1 := fresh "Ht1" in
    let Ht2 := fresh "Ht2" in
    let Ht3 := fresh "Ht3" in
    let Ht4 := fresh "Ht4" in
    apply e_composition_typing in H;
    destruct H as [ts [t1s [t2s [t3s [Ht1 [Ht2 [Ht3 Ht4]]]]]]]; subst
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
    let Ht1 := fresh "Ht1" in
    let Ht2 := fresh "Ht2" in
    let Ht3 := fresh "Ht3" in
    let Ht4 := fresh "Ht4" in
    apply Label_typing in H;
    destruct H as [ts [t1s [Ht1 [Ht2 [Ht3 Ht4]]]]]; subst
  | H: typing.e_typing _ _ [::AI_label _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let Ht1 := fresh "Ht1" in
    let Ht2 := fresh "Ht2" in
    let Ht3 := fresh "Ht3" in
    let Ht4 := fresh "Ht4" in
    eapply Label_typing in H; eauto;
    destruct H as [ts [t1s [Ht1 [Ht2 [Ht3 Ht4]]]]]; subst
         end.

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
  | |- e_is_basic (AI_basic ?e) =>
    by unfold e_is_basic; exists e
  end.

(** A common scheme in the progress proof, with a continuation. **)
Ltac solve_progress_cont cont :=
  repeat eexists;
  solve [
      apply r_simple; solve [ eauto | constructor; eauto | cont; eauto ]
    | cont ].

(** The same, but without continuation. **)
Ltac solve_progress :=
  solve_progress_cont ltac:(fail).

Lemma t_progress_be: forall C bes ts1 ts2 vcs lab ret s f hs,
    store_typing s ->
    inst_typing s f.(f_inst) C ->
    be_typing (upd_label (upd_local_return C (map typeof f.(f_locs)) ret) lab) bes (Tf ts1 ts2) ->
    map typeof vcs = ts1 ->
    not_lf_br (to_e_list bes) 0 ->
    not_lf_return (to_e_list bes) 0 ->
    const_list (to_e_list bes) \/
    exists s' f' es' hs', reduce hs s f (v_to_e_list vcs ++ to_e_list bes) hs' s' f' es'.
Proof.
  move => C bes ts1 ts2 vcs lab ret s f hs HST HIT HType HConstType HNBI_br HNRet.
  generalize dependent vcs.
  gen_ind HType; try by left.
  - (* Unop *)
    right. invert_typeof_vcs.
    by destruct v => //=; solve_progress.
  - (* Binop *)
    right. invert_typeof_vcs.
    by destruct (app_binop op v v0) eqn:HBinary; solve_progress.
  - (* testop *)
    right. invert_typeof_vcs.
    by destruct v => //=; solve_progress.
  - (* relop_i *)
    right. invert_typeof_vcs.
    by destruct v => //=; destruct v0 => //=; solve_progress.
  - (* cvtop *)
    right. invert_typeof_vcs.
    destruct (cvt t1 sx v) eqn:HConvert; destruct v => //=; solve_progress.
  - (* reinterpret *)
    right. invert_typeof_vcs.
    by destruct v => //=; solve_progress_cont ltac:(apply rs_reinterpret).
  - (* Unreachable *)
    right.
    exists s, f, (v_to_e_list vcs ++ [::AI_trap]), hs.
    apply reduce_composition_left; first by apply v_to_e_is_const_list.
    apply r_simple. by constructor.
  - (* Nop *)
    right.
    exists s, f, (v_to_e_list vcs ++ [::]), hs.
    apply reduce_composition_left; first by apply v_to_e_is_const_list.
    apply r_simple. by constructor.
  - (* Drop *)
    right. invert_typeof_vcs. solve_progress.
  - (* Select *)
    right. invert_typeof_vcs.
    destruct v1 => //=.
    by destruct (s0 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0; solve_progress.
  - (* Block *)
    right.
    exists s, f, [::AI_label (length tm) [::] (v_to_e_list vcs ++ to_e_list es)], hs.
    apply r_simple. eapply rs_block; eauto.
    + by apply v_to_e_is_const_list.
    + repeat rewrite length_is_size.
      rewrite v_to_e_size.
      subst.
      by rewrite size_map.
  - (* Loop *)
    right.
    exists s, f, [::AI_label (length vcs) [::AI_basic (BI_loop (Tf ts1 ts2) es)] (v_to_e_list vcs ++ to_e_list es)], hs.
    apply r_simple. rewrite HConstType.
    eapply rs_loop; eauto; repeat rewrite length_is_size.
    + by apply v_to_e_is_const_list.
    + by rewrite v_to_e_size.
    + rewrite -HConstType. by rewrite size_map.
  - (* if *)
    right.
    apply typeof_append in HConstType.
    destruct HConstType as [v [Ha [Hb Hc]]].
    rewrite Ha. rewrite -v_to_e_cat.
    rewrite -catA.
    destruct v => //=.
    destruct (s0 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
    + exists s, f, (v_to_e_list (take (size tn) vcs) ++ [::AI_basic (BI_block (Tf tn ts2) es2)]), hs.
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      apply r_simple. by eapply rs_if_false.
    + exists s, f, (v_to_e_list (take (size tn) vcs) ++ [::AI_basic (BI_block (Tf tn ts2) es1)]), hs.
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_simple; eauto.
  - (* BI_br *)
    subst.
    exfalso.
    unfold not_lf_br in HNBI_br.
    by apply (HNBI_br i (LH_base [::] [::])) => /=.
  - (* BI_br_if *)
    right.
    apply typeof_append in HConstType.
    destruct HConstType as [v [Ha [Hb Hc]]].
    rewrite Ha. rewrite -v_to_e_cat.
    rewrite -catA.
    destruct v => //=.
    destruct (s0 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
    + exists s, f, (v_to_e_list (take (size ts2) vcs) ++ [::]), hs.
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_simple; eauto.
    + exists s, f, (v_to_e_list (take (size ts2) vcs) ++ [::AI_basic (BI_br i)]), hs.
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_simple; eauto.
  - (* BI_br_table *)
    right.
    apply cat_split in HConstType. destruct HConstType.
    assert (Evcs : vcs = take (size t1s) vcs ++ drop (size t1s) vcs); first by rewrite cat_take_drop.
    rewrite Evcs.
    symmetry in H6. rewrite -map_drop in H6. apply typeof_append in H6.
    destruct H6 as [v [Ha [Hb Hc]]].
    destruct v => //=.
    rewrite Ha.
    repeat rewrite -v_to_e_cat.
    repeat rewrite -catA. rewrite catA.
    destruct (length ins > Wasm_int.nat_of_uint i32m s0) eqn:HLength; move/ltP in HLength.
    + remember HLength as H8. clear HeqH8.
      apply List.nth_error_Some in H8.
      destruct (List.nth_error ins (Wasm_int.nat_of_uint i32m s0)) eqn:HN => //=.
      exists s, f, ((v_to_e_list (take (size t1s) vcs) ++ v_to_e_list (take (size ts) (drop (size t1s) vcs))) ++ [::AI_basic (BI_br n)]), hs.
      apply reduce_composition_left.
      { by apply const_list_concat; apply v_to_e_is_const_list. }
      apply r_simple. apply rs_br_table => //.
      by lias.
    + assert (Inf : length ins <= Wasm_int.nat_of_uint i32m s0); first by lias.
      move/leP in Inf.
      remember Inf as Inf'. clear HeqInf'.
      apply List.nth_error_None in Inf.
      exists s, f, ((v_to_e_list (take (size t1s) vcs) ++ v_to_e_list (take (size ts) (drop (size t1s) vcs))) ++ [::AI_basic (BI_br i)]), hs.
      apply reduce_composition_left.
      { by apply const_list_concat; apply v_to_e_is_const_list. }
      apply r_simple. apply rs_br_table_length => //.
      by lias.
  - (* Return *)
    subst.
    exfalso.
    unfold not_lf_return in HNRet.
    by apply (HNRet (LH_base [::] [::])) => /=.
  - (* Call *)
    right. subst.
    simpl in *. clear H1 H2 H3 H4.
    eapply func_context_store in H; eauto. destruct H as [a H].
    exists s, f, (v_to_e_list vcs ++ [:: (AI_invoke a)]), hs.
    apply reduce_composition_left; first by apply v_to_e_is_const_list.
    by apply r_call => //. 
  - (* Call_indirect *)
    right.
    simpl in *.
    apply typeof_append in HConstType. destruct HConstType as [v [Ha [Hb Hc]]].
    destruct v => //=.
    rewrite Ha. rewrite -v_to_e_cat. rewrite -catA. subst.
    exists s, f.
    destruct (stab_addr s f (Wasm_int.nat_of_uint i32m s0)) as [a|] eqn:Hstabaddr.
    + (* Some a *)
      remember Hstabaddr as Hstabaddr2. clear HeqHstabaddr2.
      eapply store_typing_stabaddr in Hstabaddr; eauto.
      destruct Hstabaddr as [cl Hstabaddr].
      destruct (stypes s f.(f_inst) i == Some (cl_type cl)) eqn:Hclt; move/eqP in Hclt.
      * exists (v_to_e_list (take (size t1s) vcs) ++ [::AI_invoke a]), hs.
        apply reduce_composition_left; first by apply v_to_e_is_const_list.
        simpl.
        by eapply r_call_indirect_success; eauto.
      * exists (v_to_e_list (take (size t1s) vcs) ++ [::AI_trap]), hs.
        apply reduce_composition_left; first by apply v_to_e_is_const_list.
        by eapply r_call_indirect_failure1; eauto.
    + (* None *)
      exists (v_to_e_list (take (size t1s) vcs) ++ [::AI_trap]), hs.
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_call_indirect_failure2.

  - (* Get_local *)
    right. invert_typeof_vcs.
    simpl in H. simpl in H0.
    apply nth_error_map in H0.
    destruct H0 as [x' [HN HType]].
    rewrite length_is_size in H.
    rewrite size_map in H.
    exists s, f, [::AI_basic (BI_const x')], hs.
    by apply r_get_local.
      
  - (* Set_local *)
    right. invert_typeof_vcs.
    simpl in H.
    rewrite length_is_size in H. rewrite size_map in H. rewrite -length_is_size in H.
    exists s, (Build_frame (set_nth v f.(f_locs) i v) f.(f_inst)), [::], hs.
    by eapply r_set_local; eauto.

  - (* Tee_local *)
    right. invert_typeof_vcs.
    exists s, f, [::AI_basic (BI_const v); AI_basic (BI_const v); AI_basic (BI_set_local i)], hs.
    by apply r_simple; eauto.

  - (* Get_global *)
    right. invert_typeof_vcs.
    simpl in H. simpl in H0.
    unfold option_map in H0.
    destruct (List.nth_error (tc_global C0) i) eqn:HN => //=.
    eapply glob_context_store in HN; eauto.
    assert (D : sglob_val s f.(f_inst) i <> None).
    { unfold sglob_val. unfold sglob in HN. unfold option_map. by destruct (operations.sglob s f.(f_inst) i). }
    destruct (sglob_val s f.(f_inst) i) eqn:Hglobval => //=.
    exists s, f, [::AI_basic (BI_const v)], hs.
    by apply r_get_global.

  - (* Set_global *)
    right. invert_typeof_vcs.
    destruct (supdate_glob s f.(f_inst) i v) eqn:Hs.
    + exists s0, f, [::], hs.
      by apply r_set_global.
    + unfold supdate_glob in Hs. unfold option_bind in Hs.
      simpl in H. simpl in H0.
      eapply glob_context_store in H0; eauto.
      unfold sglob in H0. unfold operations.sglob in H0. unfold option_bind in H0.
      destruct (sglob_ind s f.(f_inst) i) eqn:Hglob => //.
      unfold supdate_glob_s in Hs. unfold option_map in Hs.
      destruct (List.nth_error (s_globals s) n) => //.

  - (* Load *)
    right. subst.
    simpl in H.
    exists s, f.
    invert_typeof_vcs. destruct v => //=.
    eapply mem_context_store in H; eauto.
    destruct H as [n [HMenInd HMem]].
    destruct (List.nth_error (s_mems s) n) eqn:HN => //=.
    destruct tp_sx.
    + (* Load Some *)
      destruct p as [tp sx].
      simpl in H0. remove_bools_options.
      destruct (load_packed sx m (Wasm_int.N_of_uint i32m s0) off (tp_length tp) (t_length t)) eqn:HLoadResult.
      * exists [::AI_basic (BI_const (wasm_deserialise b t))], hs.
        by eapply r_load_packed_success; eauto.
      * exists [::AI_trap], hs.
        by eapply r_load_packed_failure; eauto.
    + (* Load None *)
      simpl in H0.
      destruct (load m (Wasm_int.N_of_uint i32m s0) off (t_length t)) eqn:HLoadResult.
      * exists [::AI_basic (BI_const (wasm_deserialise b t))], hs.
        by eapply r_load_success; eauto.
      * exists [::AI_trap], hs.
        by eapply r_load_failure; eauto.

  - (* Store *)
    right. subst.
    simpl in H.
    invert_typeof_vcs. destruct v => //=.
    eapply mem_context_store in H; eauto.
    destruct H as [n [HMenInd HMem]].
    destruct (List.nth_error (s_mems s) n) eqn:HN => //=.
    destruct tp as [tp |].
    + (* Store Some *)
      simpl in H0. remove_bools_options.
      destruct (store_packed m (Wasm_int.N_of_uint i32m s0) off (bits v0) (tp_length tp)) eqn:HStoreResult.
      * exists (upd_s_mem s (set_nth m0 s.(s_mems) n m0)), f, [::], hs.
        eapply r_store_packed_success; eauto.
        by unfold types_agree; apply/eqP.
      * exists s, f, [::AI_trap], hs.
        eapply r_store_packed_failure; eauto.
        by unfold types_agree; apply/eqP.
    + (* Store None *)
      simpl in H0.
      destruct (store m (Wasm_int.N_of_uint i32m s0) off (bits v0) (t_length (typeof v0))) eqn:HStoreResult.
      * exists (upd_s_mem s (set_nth m0 s.(s_mems) n m0)), f, [::], hs.
        eapply r_store_success; eauto.
        by unfold types_agree; apply/eqP.
      * exists s, f, [::AI_trap], hs.
        eapply r_store_failure; eauto.
        by unfold types_agree; apply/eqP.

  - (* Current_memory *)
    right. invert_typeof_vcs.
    simpl in H.
    eapply mem_context_store in H; eauto.
    destruct H as [n [HMemInd HMem]].
    destruct (List.nth_error (s_mems s) n) eqn:HN => //=.
    exists s, f, [::AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size m)))))], hs.
    by eapply r_current_memory; eauto.

  - (* Grow_memory *)
    right. invert_typeof_vcs.
    simpl in H.
    eapply mem_context_store in H; eauto.
    destruct H as [n [HMemInd HMem]].
    destruct (List.nth_error (s_mems s) n) eqn:HN => //=.
    destruct v => //=.
    (* Similarly, for this proof we can just use trap and use the failure case. *)
    exists s, f, [::AI_basic (BI_const (VAL_int32 int32_minus_one))], hs.
    by eapply r_grow_memory_failure; eauto.

  - (* Composition *)
    subst.
    rewrite to_e_list_cat in HNBI_br.
    rewrite to_e_list_cat in HNRet.
    clear H.
    edestruct IHHType1; eauto.
    { by eapply nlfbr_right; eauto. }
    { by eapply nlfret_right; eauto. }
    + (* Const *)
      apply const_es_exists in H. destruct H as [cs HConst].
      apply b_e_elim in HConst. destruct HConst. subst.
      rewrite e_b_inverse in HNRet; last by apply const_list_is_basic; apply v_to_e_is_const_list.
      rewrite e_b_inverse in HNBI_br; last by apply const_list_is_basic; apply v_to_e_is_const_list.
      apply Const_list_typing in HType1. subst.
      edestruct IHHType2; eauto.
      { by eapply nlfbr_left; try apply v_to_e_is_const_list; eauto. }
      { by eapply nlfret_left; try apply v_to_e_is_const_list; eauto. }
      { by rewrite -map_cat. }
      * left. rewrite to_e_list_cat. apply const_list_concat => //.
        by rewrite e_b_inverse => //; apply v_to_e_is_const_list.
      * destruct H as [es' HReduce].
        right.
        rewrite to_e_list_cat.
        rewrite e_b_inverse; last by apply const_list_is_basic; apply v_to_e_is_const_list.
        exists es'.
        rewrite catA.
        by rewrite v_to_e_cat.
    + (* reduce *)
      destruct H as [s' [vs' [es' [hs' HReduce]]]].
      right.
      rewrite to_e_list_cat.
      exists s', vs', (es' ++ to_e_list [::e]), hs'.
      rewrite catA.
      by apply reduce_composition_right.

  - (* Weakening *)
    apply cat_split in HConstType.
    destruct HConstType.
    rewrite -map_take in H1. rewrite -map_drop in H5.
    subst.
    edestruct IHHType; eauto.
    right.
    destruct H2 as [s' [f' [es' [hs' HReduce]]]].
    replace vcs with (take (size ts) vcs ++ drop (size ts) vcs); last by apply cat_take_drop.
    rewrite -v_to_e_cat. rewrite -catA.
    exists s', f', (v_to_e_list (take (size ts) vcs) ++ es'), hs'.
    apply reduce_composition_left => //.
    by apply v_to_e_is_const_list.
Qed. 

Definition br_reduce (es: seq administrative_instruction) :=
  exists n (lh: lholed n), lfill lh [::AI_basic (BI_br n)] = es.

Definition return_reduce (es: seq administrative_instruction) :=
  exists n (lh: lholed n), lfill lh [::AI_basic BI_return] = es.

Fixpoint ai_gen_measure (e: administrative_instruction) : nat :=
  match e with
  | AI_label _ _ es => 1 + List.list_max (map ai_gen_measure es)
  | _ => 0
  end.

Definition ais_gen_measure (LI: list administrative_instruction) : nat :=
  List.list_max (map ai_gen_measure LI).

(** [br_reduce] is decidable. **)
Lemma br_reduce_decidable : forall es, decidable (br_reduce es).
Admitted.
  
(** [return_reduce] is decidable. **)
Lemma return_reduce_decidable : forall es, decidable (return_reduce es).
Admitted.

Lemma br_reduce_label_length: forall n k (lh: lholed n) es s C ts2,
    lfill lh [::AI_basic (BI_br (n + k))] = es ->
    e_typing s C es (Tf [::] ts2) ->
    length (tc_label C) > k.
Proof.
  move => n k lh.
  move: lh k.
  elim.
  - move => vs es k es' s C ts <- /=Hetype.
    rewrite -cat1s add0n in Hetype.
    invert_e_typing.
    destruct ts0, t1s => //=.
    apply et_to_bet in Ht5; auto_basic.
    simpl in *. by eapply Break_typing in Ht5 as [ts1 [ts2 [? [Hplop ?]]]]; eauto => //.
  - move => k vs n0 es lh IH es' k0 es'' s C ts <- /=Hetype.
    rewrite -cat1s in Hetype.
    invert_e_typing.
    destruct ts0, t1s => //=.
    simpl in *.
    by eapply IH in Ht4; eauto; last by (do 4 f_equal; instantiate (1 := k0.+1); lias).
Qed.

Lemma return_reduce_return_some: forall n (lh: lholed n) es s C ts2,
    lfill lh [::AI_basic BI_return] = es ->
    e_typing s C es (Tf [::] ts2) ->
    tc_return C <> None.
Proof.
  move => n.
  elim.
  - move => vs es es' s C ts <- /=Hetype.
    rewrite -cat1s in Hetype.
    invert_e_typing.
    destruct ts0, t1s => //=.
    apply et_to_bet in Ht5; auto_basic.
    simpl in *. eapply Return_typing in Ht5 as [? [? [? Hret]]]; eauto.
    by rewrite Hret.
  - move => k vs n0 es lh IH es' es'' s C ts <- /=Hetype.
    rewrite -cat1s in Hetype.
    invert_e_typing.
    by assert (tc_return (upd_label C ([::ts1] ++ tc_label C)) <> None); first by eapply IH; eauto.
Qed.

Lemma br_reduce_extract_vs: forall n k (lh: lholed n) es s C ts ts2,
    lfill lh [::AI_basic (BI_br (n + k))] = es ->
    e_typing s C es (Tf [::] ts2) ->
    List.nth_error (tc_label C) k = Some ts ->
    exists vs (lh': lholed n), const_list vs /\
      lfill lh' (vs ++ [::AI_basic (BI_br (n + k))]) = es /\
      length vs = length ts.
Proof.
  move => n k lh.
  move: lh k.
  elim.
  - move => vs es k es' s C ts rs <- /=Hetype Hnth.
    rewrite -cat1s add0n in Hetype.
    invert_e_typing.
    destruct ts0, t1s => //.
    apply et_to_bet in Ht5; auto_basic.
    eapply Break_typing in Ht5 as [ts3 [ts3' [Hsize [Hplop ?]]]]; eauto; subst.
    apply et_to_bet in Ht3; last by apply const_list_is_basic, v_to_e_is_const_list.
    apply Const_list_typing in Ht3; simpl in *.
    unfold plop2 in Hplop. move/eqP in Hplop.
    rewrite Hnth in Hplop; injection Hplop as <-.
    rewrite catA in Ht3. symmetry in Ht3.
    apply cat_split in Ht3. destruct Ht3.
    replace vs with (take (size (ts1 ++ ts3')) vs ++ drop (size (ts1 ++ ts3')) vs); last by apply cat_take_drop.
    exists (v_to_e_list (drop (size (ts1 ++ ts3')) vs)), (LH_base (take (size (ts1 ++ ts3')) vs) es).
    repeat split => /=.
    + by apply v_to_e_is_const_list.
    + rewrite -v_to_e_cat. repeat rewrite -catA.
      by rewrite cat1s.
    + subst.
      repeat rewrite length_is_size.
      by rewrite v_to_e_size size_drop size_drop size_map.
  - move => k vs n0 es lh IH es' k0 es'' s C ts rs <- /=Hetype Hnth.
    rewrite -cat1s in Hetype.
    invert_e_typing.
    destruct ts0, t1s => //.
    eapply IH in Ht4 as [es0 [lh' [HConst [Heq Hlen]]]].
    2: { instantiate (1 := k0.+1).
        (do 4 f_equal; try by lias). }
    2: { by eauto. }
    replace (k.+1+k0) with (k+k0.+1); last by lias.
    repeat eexists; eauto. 
    instantiate (1 := (LH_rec vs (length ts2) es lh' es')) => /=.
    rewrite Heq.
    by rewrite addnS.
Qed.

Lemma return_reduce_extract_vs: forall n (lh: lholed n) es s C ts ts2,
    lfill lh [::AI_basic BI_return] = es ->
    e_typing s C es (Tf [::] ts2) ->
    tc_return C = Some ts ->
    exists vs (lh': lholed n), const_list vs /\
      lfill lh' (vs ++ [::AI_basic BI_return]) = es /\
      length vs = length ts.
Proof.
  move => n.
  elim.
  - move => vs es es' s C ts rs <- /=Hetype Hret.
    rewrite -cat1s in Hetype.
    invert_e_typing.
    destruct ts0, t1s => //.
    apply et_to_bet in Ht5; auto_basic.
    simpl in *.
    eapply Return_typing in Ht5 as [ts2 [ts2' [? Hret']]]; eauto; subst.
    rewrite Hret in Hret'. inversion Hret'; subst; clear Hret'.
    apply et_to_bet in Ht3; last by apply const_list_is_basic, v_to_e_is_const_list.
    apply Const_list_typing in Ht3. simpl in Ht3.
    rewrite catA in Ht3. symmetry in Ht3.
    apply cat_split in Ht3. destruct Ht3 as [Heq ->].
    replace vs with (take (size (ts1 ++ ts2')) vs ++ drop (size (ts1 ++ ts2')) vs); last by apply cat_take_drop.
    exists (v_to_e_list (drop (size (ts1 ++ ts2')) vs)), (LH_base (take (size (ts1 ++ ts2')) vs) es).
    repeat split => /=.
    + by apply v_to_e_is_const_list.
    + rewrite -v_to_e_cat -(cat1s _ es).
      by repeat rewrite catA.
    + rewrite Heq.
      repeat rewrite length_is_size.
      by rewrite v_to_e_size -map_drop size_map cat_take_drop.
  - move => k vs n0 es lh IH es' es'' s C ts rs <- /=Hetype Hret.
    rewrite - cat1s in Hetype.
    invert_e_typing.
    destruct ts0, t1s => //.
    eapply IH in Ht4 as [es2 [lh' [Hconst [Hlf HLength]]]]; eauto.
    apply const_es_exists in Hconst as [vs' ->].
    repeat eexists; eauto; first by apply v_to_e_is_const_list.
    instantiate (1 := (LH_rec vs (length ts2) es lh' es')) => /=.
    by rewrite Hlf.
Qed.

(*
  These two guarantees that the extra conditions we put in progress_e are true -- the second
    being true only if the function doesn't return anything (so we are not in the middle of some
    Local functions).
*)
Lemma s_typing_lf_br: forall s rs f es ts,
    s_typing s rs f es ts ->
    (forall n (lh: lholed n) k, lfill lh [::AI_basic (BI_br k)] = es -> k < n).
Proof.
  move => s rs f es ts HType n lh k HLF.
  inversion HType. inversion H. subst.
  destruct (k<n) eqn: H3 => //=.
  move/ltP in H3.
  eapply br_reduce_label_length with (k := k-n) (n := n) in H1; eauto.
  - simpl in H1.
    assert (E : tc_label C1 = [::]); first by eapply inst_t_context_label_empty; eauto.
    by rewrite E in H1.
  - by replace (n + (k - n)) with k; last by lias.
Qed.

Lemma s_typing_lf_return: forall s f es ts,
    s_typing s None f es ts ->
    (forall n, not_lf_return es n).
Proof.
  unfold not_lf_return.
  move => s f es ts HType n lh HContra.
  inversion HType; subst.
  by eapply return_reduce_return_some in H1; eauto.
Qed.

Axiom host_application_exists: forall hs s tf hf vcs,
    exists hs' res, host_application hs s tf hf vcs hs' res.

Lemma t_progress_e: forall s C C' f vcs es tf ts1 ts2 lab ret hs,
    e_typing s C es tf ->
    tf = Tf ts1 ts2 ->
    C = (upd_label (upd_local_return C' (map typeof f.(f_locs)) ret) lab) ->
    inst_typing s f.(f_inst) C' ->
    map typeof vcs = ts1 ->
    store_typing s ->
    (forall n (lh: lholed n) k, lfill lh [::AI_basic (BI_br k)] = es -> k < n) ->
    (forall n, not_lf_return es n) ->
    terminal_form (v_to_e_list vcs ++ es) \/
    exists s' f' es' hs', reduce hs s f (v_to_e_list vcs ++ es) hs' s' f' es'.
Proof.
  (* e_typing *)
  move => s C C' f vcs es tf ts1 ts2 lab ret hs HType.
  move: f C' vcs ts1 ts2 lab ret hs.
  (* IP is a bit tricky here *)
  apply e_typing_ind' with (e := HType)
    (P := fun s C es tf (_ : e_typing s C es tf) => forall f C' vcs ts1 ts2 lab ret hs,
              tf = Tf ts1 ts2 ->
              C = (upd_label (upd_local_return C' (map typeof f.(f_locs)) ret) lab) ->
              inst_typing s f.(f_inst) C' ->
              map typeof vcs = ts1 ->
              store_typing s ->
              (forall n (lh: lholed n) k, lfill lh [::AI_basic (BI_br k)] = es -> k < n) ->
              (forall n, not_lf_return es n) ->
              terminal_form (v_to_e_list vcs ++ es) \/
              exists s' f' es' hs', reduce hs s f (v_to_e_list vcs ++ es) hs' s' f' es')
    (P0 := fun s rs f es ts (_ : s_typing s rs f es ts) => forall hs,
              store_typing s ->
              (forall n (lh: lholed n) k, lfill lh [::AI_basic (BI_br k)] = es -> k < n) ->
              (forall n, not_lf_return es n) ->
              (const_list es /\ length es = length ts) \/
              es = [::AI_trap] \/
              exists s' f' es' hs', reduce hs s f es hs' s' f' es'); clear HType s C es tf.
   
  - (* AI_basic *)
    move => s C bes tf HType.
    move => f C' vcs ts1 ts2 lab ret hs HTF HContext HInst HConstType HST HBI_brDepth HNRet.
    subst.
    eapply t_progress_be in HType; try instantiate (1 := vs) in HType; try by eauto.
    destruct HType as [HType | [s' [vs' [es' [hs' HType]]]]].
    + left.
      unfold terminal_form; left.
      apply const_list_concat => //. by apply v_to_e_is_const_list.
    + right.
      repeat eexists. by apply HType.
    + unfold not_lf_br. move => k lh HContra.
      by apply HBI_brDepth in HContra.
  - (* Composition *)
    move => s C es e t1s t2s t3s HType1 IHHType1 HType2 IHHType2.
    move => f C' vcs ts1 ts2 lab ret hs HTF HContext HInst HConstType HST HBI_brDepth HNRet.
    inversion HTF; subst.
    edestruct IHHType1; eauto.
    { move => n lh k HLF.
      subst es.
      eapply HBI_brDepth.
      by apply lfill_push_back_es.
    }
    { move => n.
      eapply nlfret_right. by apply HNRet. }
    + (* Terminal *)
      unfold terminal_form in H. destruct H.
      * (* Const *)
        apply const_list_split in H. destruct H as [HC1 HC2].
        apply et_to_bet in HType1; last by apply const_list_is_basic.
        apply const_es_exists in HC2.
        destruct HC2 as [esv HC2]. subst.
        apply Const_list_typing in HType1. subst.
        edestruct IHHType2; eauto.
        { by apply map_cat. }
        { move => n lh k HLF.
          eapply HBI_brDepth; eauto.
          rewrite - HLF.
          by apply lfill_push_front_vs.
        }
        { move => n.
          eapply nlfret_left.
          instantiate (1 := v_to_e_list esv); first by apply v_to_e_is_const_list.
          by apply HNRet. }
        -- (* Terminal *)
          unfold terminal_form in H. destruct H.
          ++ left. unfold terminal_form. left.
             rewrite -v_to_e_cat in H.
             by rewrite catA.
          ++ apply extract_list1 in H. destruct H.
             rewrite -v_to_e_cat in H.
             destruct vcs => //=.
             destruct esv => //=.
             left. subst. by apply terminal_trap.
        -- (* reduce *)
          rewrite -v_to_e_cat in H.
          rewrite -catA in H.
          right.
          by eapply H.
      * (* AI_trap *)
        destruct vcs => //=; destruct es => //=; destruct es => //=.
        simpl in H. inversion H. subst.
        right.
        exists s, f, [::AI_trap], hs.
        apply r_simple.
        eapply rs_trap => //.
        by instantiate (1 := (LH_base [::] [::e])).
    + (* reduce *)
      destruct H as [s' [f' [es' [hs' HReduce]]]].
      right.
      exists s', f', (es' ++ [::e]), hs'.
      eapply r_label; eauto => //.
      * instantiate (1 := LH_base nil [::e]) => /=.
        by rewrite catA.
      * done.
  - (* Weakening *)
    move => s C es ts t1s t2s HType IHHType.
    move => f C' vcs ts1 ts2 lab ret hs' HTF HContext HInst HConstType HST HBI_brDepth HNRet.
    inversion HTF; subst.
    symmetry in H0. apply cat_split in H0. destruct H0 as [HCT1 HCT2].
    rewrite - map_take in HCT1.
    rewrite - map_drop in HCT2.
    assert (Evcs : vcs = take (size ts) vcs ++ drop (size ts) vcs).
    { symmetry. by apply cat_take_drop. }
    rewrite Evcs. rewrite - v_to_e_cat.
    edestruct IHHType; eauto.
    + (* Terminal *)
      unfold terminal_form in H.
      destruct H => //=.
      * (* Const *)
        left. unfold terminal_form. left.
        rewrite -catA. apply const_list_concat => //.
        by apply v_to_e_is_const_list.
      * (* AI_trap *)
        apply v_e_trap in H; last by apply v_to_e_is_const_list.
        destruct H. subst.
        rewrite H.
        destruct (drop (size ts) vcs) eqn:HDrop => //=.
        clear H. rewrite cats0 in Evcs. rewrite -Evcs.
        rewrite cats0.
        destruct vcs => //.
        -- left. by apply terminal_trap.
        -- right.
           exists s, f, [::AI_trap], hs'.
           apply r_simple.
           apply reduce_trap_left => //.
           by apply v_to_e_is_const_list.
    + (* reduce *)
      destruct H as [s' [f' [es' [hs'' HReduce]]]].
      right.
      exists s', f', (v_to_e_list (take (size ts) vcs) ++ es'), hs''.
      rewrite -catA.
      apply reduce_composition_left => //; first by apply v_to_e_is_const_list.
      by eapply HReduce.
      
  - (* AI_trap *)
    destruct vcs => //; first by left; apply terminal_trap.
    right.
    exists s, f, [::AI_trap], hs.
    apply r_simple.
    apply reduce_trap_left => //.
    by apply v_to_e_is_const_list.
  - (* Local *)
    move => s C n f0 es ts HType IHHType HLength.
    move => f C' vcs ts1 ts2 lab ret hs HTF HContext HInst HConstType HST HBI_brDepth HNRet.
    inversion HTF; subst; clear HTF.
    symmetry in H0.
    invert_typeof_vcs.
    right.
    destruct (return_reduce_decidable es) as [HEMT | HEMF].
    { inversion HType; subst.
      unfold return_reduce in HEMT.
      destruct HEMT as [n [lh HLF]].
      eapply return_reduce_extract_vs in HLF; eauto.
      instantiate (1 := ts2) in HLF.
      destruct HLF as [cs [lh' [HConst [HLF2 HLength]]]].
      repeat eexists.
      apply r_simple.
      eapply rs_return; eauto.
      by [].
    }
    edestruct IHHType as [ | [ | ]]; eauto.
    {
      move => n lh k HLF.
      by eapply s_typing_lf_br in HLF; eauto.
    }
    { unfold return_reduce in HEMF. unfold not_lf_return.
      move => n lh HContra.
      apply HEMF. by eauto.
    }
    + (* Const *)
      destruct H.
      exists s, f, es, hs.
      apply r_simple.
      by apply rs_local_const.
    + (* AI_trap *)
      subst.
      exists s, f, [::AI_trap], hs.
      apply r_simple.
      by apply rs_local_trap.
    + (* reduce *)
      destruct H as [s' [f0' [es' [hs' HReduce]]]].
      exists s', f, [::AI_local (length ts2) f0' es'], hs'.
      by apply r_local; apply HReduce.
  - (* Invoke *)
    move => s a C cl tf HNth HType.
    move => f C' vcs ts1 ts2 lab ret hs HTF HContext HInst HConstType HST HBI_brDepth HNRet.
    inversion HType; subst.
    inversion H5; subst; clear H5.
    + (* Native *)
      right.
      exists s, f, [:: AI_local (length ts2) (Build_frame (vcs ++ n_zeros ts) i) [::AI_basic (BI_block (Tf [::] ts2) es)]], hs.
      eapply r_invoke_native; eauto.
      repeat rewrite length_is_size. by rewrite size_map.
    + (* Host *)
      right.
      assert (HApply: exists hs' res, host_application hs s (Tf (map typeof vcs) ts2) h vcs hs' res). apply host_application_exists.
      destruct HApply as [hs' [res HApply]].
      destruct res as [opres |].
      destruct opres as [p r].
      * (* Some *)
        repeat eexists.
        eapply r_invoke_host_success; eauto.
        repeat rewrite length_is_size. by apply size_map.
      * (* None *)
        repeat eexists.
        eapply r_invoke_host_diverge; eauto.
        repeat rewrite length_is_size. by apply size_map.
  - (* AI_label *)
    move => s C e0s es ts t2s n HType1 IHHType1 HType2 IHHType2 HLength.
    move => f C' vcs ts1 ts2 lab ret hs HTF HContext HInst HConstType HST HBI_brDepth HNRet.
    inversion HTF; subst.
    symmetry in H0. invert_typeof_vcs.
    rewrite upd_label_overwrite in HType2. simpl in HType2.
    destruct (br_reduce_decidable es) as [HEMT | HEMF].
    { unfold br_reduce in HEMT.
      destruct HEMT as [n [lh HLF]].
      right.
      replace (BI_br n) with (BI_br (n + 0)) in HLF; last by f_equal; lias.
      eapply br_reduce_extract_vs in HLF as [cs [lh' [HConst [<- HLength]]]]; eauto => //.
      repeat eexists.
      apply r_simple.
      by eapply rs_br; eauto; rewrite addn0.
    }
    edestruct IHHType2; eauto.
    { rewrite upd_label_overwrite. simpl. eauto. }
    { unfold br_reduce in HEMF.
      move => n lh k HLF.
      assert (Inf : k < n.+1).
      { eapply HBI_brDepth.
        instantiate (1 := LH_rec [::] (length ts) e0s lh [::]) => /=.
        by rewrite HLF.
      }
      rewrite ltnS in Inf.
      rewrite leq_eqVlt in Inf.
      remove_bools_options => //.
      subst.
      exfalso.
      apply HEMF.
      by repeat eexists.
    }
    { unfold not_lf_return.
      move => n lh HContra.
      unfold not_lf_return in HNRet.
      eapply HNRet.
      instantiate (1 := LH_rec [::] (length ts) e0s lh [::]) => /=.
      by rewrite HContra.
    }
    + (* Terminal *)
      apply terminal_form_v_e in H.
      unfold terminal_form in H. destruct H.
      * (* Const *)
        right.
        exists s, f, es, hs.
        apply r_simple.
        by apply rs_label_const.
      * (* AI_trap *)
        right. subst.
        exists s, f, [::AI_trap], hs.
        apply r_simple.
        by apply rs_label_trap.
        by apply v_to_e_is_const_list.
    + (* reduce *)
      destruct H as [s' [f' [es' [hs' HReduce]]]].
      right.
      simpl in HReduce.
      exists s', f', [::AI_label (length ts) e0s es'], hs'.
      eapply r_label; eauto.
      instantiate (1 := LH_rec nil (length ts) e0s (LH_base nil nil) nil).
      all: simpl; try by rewrite cats0.
  - (* s_typing *)
    move => s f es rs ts C C0 HFT HContext HType IHHType HRetType hs HST HBI_brDepth HNRet.
    inversion HFT.
    subst.
    edestruct IHHType; eauto.
    { (* Context *)
      assert (E : tc_local C1 = [::]).
      { by eapply inst_t_context_local_empty; eauto. }
      rewrite E. simpl.
      by fold_upd_context. }
    { by instantiate (1 := [::]). }
    + unfold terminal_form in H0. destruct H0.
      * (* Const *)
        left. split => //.
        apply et_to_bet in HType; try by apply const_list_is_basic.
        simpl in H0.
        apply const_es_exists in H0. destruct H0 as [es' H0]. subst.
        apply Const_list_typing in HType. subst.
        repeat rewrite length_is_size. simpl.
        rewrite v_to_e_size. by rewrite size_map.
      * (* AI_trap *)
        right. by left.
    + (* reduce *)
      simpl in H0. right. right. by eauto.
Qed.

Theorem t_progress: forall s f es ts hs,
    config_typing s f es ts ->
    terminal_form es \/
    exists s' f' es' hs', reduce hs s f es hs' s' f' es'.
Proof.
  move => s f es ts hs HType.
  inversion HType. inversion H0. inversion H5. subst.
  eapply t_progress_e with (vcs := [::]) (ret := None) (lab := [::]) in H7; eauto.
  - assert (E : tc_local C1 = [::]).
    { by eapply inst_t_context_local_empty; eauto. }
    rewrite E. simpl.
    fold_upd_context.
    assert (E' : tc_label (upd_local_return C1 (map typeof f.(f_locs)) None) = [::]).
    { simpl. by eapply inst_t_context_label_empty; eauto. }
    rewrite -E'.
    by destruct C1.
  - by eapply s_typing_lf_br; eauto.
  - by eapply s_typing_lf_return; eauto.
Qed.

End Host.
