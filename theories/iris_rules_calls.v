From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity iris_wp_def iris_rules_structural stdpp_aux.
Require Export datatypes host operations properties opsem.


Close Scope byte_scope.

(* basic instructions with simple(pure) reductions *)
Section iris_rules_calls.
  Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}.

  (* Placeholder until reduce_det has been updated to accomodate native invocations *)
  Import DummyHosts.
  Lemma reduce_det_temp: forall hs f ws es hs1 f1 ws1 es1 hs2 f2 ws2 es2,
      reduce (host_instance:=host_instance) hs f ws es hs1 f1 ws1 es1 ->
      reduce hs f ws es hs2 f2 ws2 es2 ->
      ( (hs1, f1, ws1, es1) = (hs2, f2, ws2, es2) \/
          first_instr es = Some (AI_basic (BI_grow_memory)) \/
          (first_instr es = Some AI_trap /\ first_instr es1 = Some AI_trap /\
             first_instr es2 = Some AI_trap /\
             (hs1, f1, ws1) = (hs2, f2, ws2))).
  Proof. Admitted.
  
  
  Lemma v_to_e_list_to_val es vs :
    iris.to_val es = Some (immV vs) ->
    v_to_e_list vs = es.
  Proof.
    revert vs. induction es.
    { intros vs Hval. destruct vs;inversion Hval. done. }
    { intros vs Hval. destruct vs;inversion Hval.
      destruct a=>//. destruct b=>//.
      destruct (to_val es)=>//.
      destruct v0=>//.
      destruct es=>//.
      destruct a=>//. destruct b=>//.
      destruct (to_val es) eqn:Hes=>//.
      destruct v1=>//. simplify_eq.
      simpl. f_equiv. rewrite IHes//.
      destruct es=>//. }
  Qed.

  (* -------------------------------------------------------------------------- *)
  (* ----------------------------- Native invocations ------------------------- *)
  (* -------------------------------------------------------------------------- *)

  Lemma wp_invoke_native (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) ves vcs t1s t2s ts a es i m f0 :
    iris.to_val ves = Some (immV vcs) ->
    length vcs = length t1s ->
    length t2s = m ->
    ↪[frame] f0 -∗
     (N.of_nat a) ↦[wf] (FC_func_native i (Tf t1s t2s) ts es) -∗
     ▷ (↪[frame] f0 ∗ (N.of_nat a) ↦[wf] (FC_func_native i (Tf t1s t2s) ts es) -∗
       WP [::AI_local m (Build_frame (vcs ++ (n_zeros ts)) i) [::AI_basic (BI_block (Tf [::] t2s) es)]] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
     WP ves ++ [AI_invoke a] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
  Proof.
    iIntros (Hparams Hlen Hret) "Hf Hi HΦ".
    iApply wp_lift_step.
    { apply to_val_cat_None2. auto. }
    iIntros ([[[? ?] ?] ?] ns κ κs nt) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (gen_heap_valid with "Hσ1 Hi") as %Hlook.
    set (σ := (s0,s1,l,i0)).
    assert (reduce (host_instance:=host_instance) s0 s1 {| f_locs := l; f_inst := i0 |}
           (ves ++ [AI_invoke a])%list s0 s1 {| f_locs := l; f_inst := i0 |}
           [AI_local m {| f_locs := vcs ++ n_zeros ts; f_inst := i |} [AI_basic (BI_block (Tf [] t2s) es)]]) as Hred.
    { eapply r_invoke_native with (ts:=ts);eauto.
      { rewrite gmap_of_list_lookup Nat2N.id in Hlook. rewrite /= nth_error_lookup //. }
      { symmetry. apply v_to_e_list_to_val. auto. } }
    iSplit.
    - iPureIntro.
      destruct s => //=.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, σ, [].
      unfold iris.prim_step => /=.
      repeat split => //.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 σ2 efs HStep).
      iMod "Hcls". iModIntro.
      destruct σ2 as [[[hs' ws'] locs'] inst'].
      destruct HStep as (H & -> & ->).
      assert (first_instr (ves ++ [AI_invoke a]) = Some (AI_invoke a)) as Hf.
      { apply first_instr_const. eapply to_val_const_list. eauto. }
      eapply reduce_det_temp in H as HH;[|apply Hred].
      destruct HH as [HH | [Hstart | (Hstart & Hstart1 & Hstart2 & Hσ) ]]; try done.
      simplify_eq. iExists f0. iFrame.
      iSplit =>//. iIntros "Hf".
      iSpecialize ("HΦ" with "[$]"). iFrame.
      rewrite Hf in Hstart. done.
  Qed.


  (* -------------------------------------------------------------------------- *)
  (* ------------------------------ Host invocations -------------------------- *)
  (* -------------------------------------------------------------------------- *)

  (* TODO: discuss what we want host invocations, in case the host invokes a wasm function *)

  
  (* In the version below, host invocations are handled with an imported host program logic, 
     as described in iris_wp_def.

     The import includes a WP definition, and two lemmas that partly unfold the WP definition.

     Note that this version fits the current setup for host import, but might need to 
     be changed in the future, if the instantiated host is able to call wasm functions
     (in which case the architecture of the setup must change, since the two opsem will 
     be mutually recursive.

   *)
  
  Lemma last_inj {A : Type} (l1 l2 : list A) (a b : A) :
    l1 = l2 -> last l1 = Some a -> last l2 = Some b -> a = b.
  Proof.
    intros Heq Hla1 Hla2.
    subst. rewrite Hla1 in Hla2. inversion Hla2. done.
  Qed.
  Lemma const_list_snoc_eq vs :
    forall ves es es' e,
    const_list ves ->
    const_list vs ->
    es ≠ [] ->
    iris.to_val es = None ->
    (vs ++ es ++ es')%SEQ = ves ++ [e] ->
    es' = [] ∧ ∃ vs2, ves = vs ++ vs2 ∧ es = vs2 ++ [e] ∧ const_list vs2.
  Proof.
    induction vs;
      intros ves es es' e Hconst1 Hconst2 Hneq Hnval Heq.
    { erewrite app_nil_l in Heq.
      apply app_eq_inv in Heq as [[k [Hk1 Hk2]] | [k [Hk1 Hk2]]].
      { destruct k.
        { rewrite app_nil_r in Hk1.
          rewrite app_nil_l in Hk2.
          simplify_eq.
          assert (is_Some (to_val (ves))) as [c Hc];[|congruence].
          apply const_list_is_val in Hconst1 as [v ->]. eauto. }
        { destruct k,es' =>//.
          rewrite app_nil_r in Hk2. simplify_eq.
          eauto. }  }
      { rewrite Hk1 in Hconst1.
        apply to_val_cat_None1 with (es2:=k) in Hnval.
        apply const_list_is_val in Hconst1 as [v Hv].
        congruence. } }
    { destruct ves.
      { destruct vs,es,es' =>//. }
      inversion Heq;subst.
      simpl in Hconst1,Hconst2.
      apply andb_true_iff in Hconst1,Hconst2.
      destruct Hconst1 as [Ha0 Hconst1].
      destruct Hconst2 as [_ Hconst2].
      apply IHvs in H1;auto.
      destruct H1 as [Heqes' [vs2 [Heq1 Heq2]]].
      subst. eauto.
    }
  Qed.
  Lemma length_to_val_immV v1 :
    forall vs1, to_val v1 = Some (immV vs1)
    -> length v1 = length vs1.
  Proof.
    induction v1;intros vs1 Hval.
    destruct vs1 =>//.
    destruct vs1.
    apply to_val_nil in Hval. done.
    simpl in *.
    destruct a;try done.
    destruct b;try done.
    destruct (to_val v1) eqn:Hv1;try done.
    destruct v2;try done.
    simplify_eq. auto.
    destruct v1;try done.
  Qed.
  Lemma const_list_app v1 v2 :
    const_list (v1 ++ v2) <-> const_list v1 ∧ const_list v2.
  Proof.
    split.
    - intros Hconst.
      apply const_list_is_val in Hconst as [v Hv].
      apply to_val_cat in Hv as [Hv1%to_val_const_list Hv2%to_val_const_list];auto.
    - intros [Hconst1 Hconst2].
      apply const_list_is_val in Hconst1 as [v1' Hv1].
      apply const_list_is_val in Hconst2 as [v2' Hv2].
      eapply to_val_const_list.
      apply to_val_cat_inv;eauto.
  Qed.      
    
  Lemma invoke_host_inv a s1 t1s t2s h s0 es1 f1 f2 hs2 ws2 es:
    reduce (host_instance:=host_instance) s0 s1
           f1 es hs2 ws2
           f2 es1 ->
    forall ves vs' vcs, iris.to_val ves = Some (immV vcs) ->
    es = vs' ++ ves ++ [AI_invoke a] -> 
    length vcs = length t1s ->
    const_list vs' ->
    const_list ves ->
    nth_error (s_funcs s1) a = Some (FC_func_host (Tf t1s t2s) h) ->
    (* (∀ hs', host_application s0 s1 (Tf t1s t2s) h vcs hs' None → False) -> *)
    (∃ r0 : result,
      f1 = f2
      ∧ es1 = vs' ++ (result_to_stack r0)
      ∧ host_application s0 s1 (Tf t1s t2s) h vcs hs2 (Some (ws2, r0)))
    ∨ (f1 = f2 ∧ es1 = es ∧ host_application s0 s1 (Tf t1s t2s) h vcs hs2 None).
  Proof.
    intros Hred.
    induction Hred using reduce_ind;
      intros ves' vs' vcs' Heq Hval Hlen Hconst Hconst' Hfunc.
    { subst. inversion H; subst; try by do 3 (try destruct vs';try destruct ves') =>//.
      all: try by do 4 (try destruct vs';try destruct ves') =>//.
      all: try by do 5 (try destruct vs';try destruct ves') =>//.
      all: rewrite app_assoc in H0.
      all: try by eapply last_inj in H0;[|apply last_snoc;eauto..].
      apply lfilled_Ind_Equivalent in H1. inversion H1;subst.
      destruct es'.
      rewrite app_assoc in H2.
      by eapply last_inj in H2;[|apply last_snoc;eauto..].
      rewrite app_assoc in H2.
      rewrite -(app_nil_r [AI_invoke a]) in H2.
      apply first_values in H2;auto;[|apply const_list_app;auto].
      destruct H2 as [_ [Hcontr _]];done.
    }
    all: subst. all: try by do 2 (try destruct vs';try destruct ves') =>//.
    all: try by do 3 (try destruct vs';try destruct ves') =>//.
    all: try by do 4 (try destruct vs';try destruct ves') =>//.
    { rewrite app_assoc in Hval. eapply last_inj in Hval;[|apply last_snoc;eauto..].
      simplify_eq. }
    { apply lfilled_Ind_Equivalent in H.
      inversion H;subst;[|].
      { rewrite app_assoc in H1.
        apply const_list_snoc_eq in H1 as HH;auto.
        destruct HH as [-> [vs2 [Hveseq [Heseq Hconst2]]]].
        apply lfilled_Ind_Equivalent in H0. inversion H0;subst.
        erewrite app_nil_r.
        apply app_eq_inv in Hveseq as [[k [Hk1 Hk2]]|[k [Hk1 Hk2]]].
        { subst. apply (IHHred ves' k vcs') in Hfunc;eauto.
          2: by rewrite app_assoc.
          destruct Hfunc as [[r0 [-> [-> Hhost]]] | [-> [ -> Hhost]]].
          left. exists r0. erewrite app_assoc. eauto.
          right. erewrite app_nil_r. erewrite !app_assoc. eauto.
          apply const_list_is_val in Hconst2 as [v Hv].
          by apply to_val_cat in Hv as [Hv1%to_val_const_list Hv2]. }
        { subst.
          apply length_to_val_immV in Heq as Hlen'.
          rewrite Hlen app_length in Hlen'.
          assert (length vs2 < length t1s -> False) as Hlt.
          eapply invoke_not_enough_arguments_no_reduce_host;eauto.
          assert (length k = 0);[lia|].
          destruct k;[|done].
          rewrite app_nil_l in Heq.
          apply (IHHred vs2 [] vcs') in Hfunc as Hsucc;auto.
          destruct Hsucc as [[r0 [-> [-> Hhost]]]|[-> [-> Hhost]]].
          left. exists r0. rewrite app_nil_r app_nil_l. auto.
          right. erewrite !app_nil_r. auto. }
        { apply const_list_app;auto. }
        { eapply reduce_not_nil. eauto. }
        { eapply val_head_stuck_reduce. eauto. } }
      { rewrite app_assoc in H1.
        rewrite -(app_nil_r [AI_invoke a]) in H1.
        apply first_values in H1;auto;[|apply const_list_app;auto].
        destruct H1 as [_ [Hcontr _]]. done. }
    }
  Qed.

  (* The following step can only work if all invariants are currently closed! *)
  (* This makes sense, since from the wasm side, only one step happens, 
     but in the host WP, multiple steps occur *)
  Lemma wp_invoke_host_success `{HWP: host_program_logic} (P : iProp Σ) (R : result -> iProp Σ)
        (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) ves vcs t1s t2s a h m f0 :
    iris.to_val ves = Some (immV vcs) ->
    length vcs = length t1s ->
    length t2s = m ->

    ↪[frame] f0 -∗
     (N.of_nat a) ↦[wf] (FC_func_host (Tf t1s t2s) h) -∗
     wp_host HWP NotStuck E h vcs R -∗
     
     ▷ (∀ r, ↪[frame] f0 ∗ (N.of_nat a) ↦[wf] (FC_func_host (Tf t1s t2s) h) ∗ R r -∗
            WP result_to_stack r @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
     WP ves ++ [AI_invoke a] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
  Proof.
    iIntros (Hparams Hlen Hret) "Hf Hi HWP HΦ".

    iLöb as "IH".
    iApply wp_unfold. rewrite /wasm_wp_pre.
    assert (to_val (ves ++ [AI_invoke a]) = None) as ->;[by apply (to_val_cat_None2 ves)|].
    iIntros ([[[? ?] ?] ?] ns κ κs nt) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iDestruct (gen_heap_valid with "Hσ1 Hi") as %Hlook.
    set (σ := (s0,s1,l,i)).
    iMod (wp_host_not_stuck HWP (s0,s1,l,i) 0 [] 0 with "[$] [$]") as "(Hσ & HWP & %Hhost)".
    { rewrite gmap_of_list_lookup Nat2N.id in Hlook. apply Hlook. }
    iApply fupd_frame_l.
    iSplit.
    - iPureIntro. unfold iris_wp_def.reducible.
      destruct s;auto.
      unfold language.reducible, language.prim_step => /=.
      destruct Hhost as [[hs' [s' [r Hhost]]]|[hs' Hhost]].
      { eexists [], _, σ, [].
        unfold iris.prim_step => /=.
        split;auto. eapply r_invoke_host_success;eauto.
        rewrite gmap_of_list_lookup Nat2N.id in Hlook. rewrite /= nth_error_lookup //.
        symmetry. apply v_to_e_list_to_val. auto. }
      { eexists [], _, σ, [].
        unfold iris.prim_step => /=.
        split;auto. eapply r_invoke_host_diverge;eauto.
        rewrite gmap_of_list_lookup Nat2N.id in Hlook. rewrite /= nth_error_lookup //.
        symmetry. apply v_to_e_list_to_val. auto. }
    - iMod (wp_host_step_red HWP (s0, s1, l, i) 0 [] [] 0 R h E vcs t1s t2s with "[$]") as "[HH HH']".
      iModIntro.
      iIntros (es1 σ2 efs HStep).
      destruct σ2 as [[[hs2 ws2] locs2] inst2].
      destruct HStep as (H & -> & ->).
      eapply invoke_host_inv with (vs':=[]) in H;eauto.
      2: { eapply to_val_const_list. eauto. }
      2: { rewrite gmap_of_list_lookup Nat2N.id in Hlook. rewrite /= nth_error_lookup //. }
      destruct H as [[r0 [Heq' [Heq Hhost']]]|[Heq' [Heq Hhost']]].
      { iSpecialize ("HH" $! (hs2,ws2,locs2,inst2) r0 Hhost').
        repeat (iMod "HH"; iModIntro; try iNext).
        iExists _. iFrame. rewrite app_nil_l in Heq. rewrite Heq.
        simplify_eq. iDestruct "HH" as "($&Hr)". iSplit =>//. }
      { iSpecialize ("HH'" $! (hs2,ws2,locs2,inst2) Hhost').
        repeat (iMod "HH'"; iModIntro; try iNext).
        iExists _. iFrame.
        simplify_eq. iDestruct "HH'" as "($&Hr)". iSplit =>//. }
      Unshelve. apply r.
  Qed.

  (* -------------------------------------------------------------------------- *)
  (* ---------------------------------- Calls --------------------------------- *)
  (* -------------------------------------------------------------------------- *)

  Lemma wp_call (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) f0 (i : nat) a :
    (inst_funcs (f_inst f0)) !! i = Some a -> 
    ↪[frame] f0 -∗
     ▷ (↪[frame] f0 -∗ WP [AI_invoke a] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
     WP [AI_basic (BI_call i)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
  Proof.
    iIntros (Hfuncs) "Hf HΦ".
    iApply wp_lift_step;[auto|].
    iIntros ([[[? ?] ?] ?] ns κ κs nt) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (ghost_map_lookup with "Hσ5 Hf") as %Hlook. simplify_map_eq.
    set (σ := (s0,s1,l,i0)).
    iSplit.
    - iPureIntro.
      destruct s => //=.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, σ, [].
      unfold iris.prim_step => /=.
      repeat split => //.
      apply r_call. rewrite /= nth_error_lookup //.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 σ2 efs HStep).
      iMod "Hcls". iModIntro.
      destruct σ2 as [[[hs' ws'] locs'] inst'].
      destruct HStep as (H & -> & ->).
      eapply reduce_det in H as HH;[|apply r_call; rewrite /= nth_error_lookup //]. 
      destruct HH as [HH | [Hstart | [[? ?] |(Hstart & Hstart1 & Hstart2 & Hσ) ]]]; try done.
      simplify_eq. iExists _. iFrame. done.
  Qed.
  

  Lemma wp_call_indirect_success (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (f0 : frame) (i : immediate) a c cl :
    (inst_types (f_inst f0)) !! i = Some (cl_type cl) ->
    (inst_tab (f_inst f0)) !! 0 = Some i -> (* current frame points to correct table? *)
    (N.of_nat i) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] (Some a) -∗
    (N.of_nat a) ↦[wf] cl -∗
    ↪[frame] f0 -∗
    ▷ ((N.of_nat i) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] (Some a)
       ∗ (N.of_nat a) ↦[wf] cl
       ∗ ↪[frame] f0 -∗ WP [AI_invoke a] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
    WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
  Proof.
    iIntros (Htype Hc) "Ha Hcl Hf Hcont".
    iApply wp_lift_step;[auto|].
    iIntros ([[[? ?] ?] ?] ns κ κs nt) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (gen_heap_valid with "Hσ2 Ha") as %Hlook.
    iDestruct (gen_heap_valid with "Hσ1 Hcl") as %Hlook2.
    iDestruct (ghost_map_lookup with "Hσ5 Hf") as %Hf. simplify_map_eq.
    simplify_lookup.
    rewrite gmap_of_list_lookup Nat2N.id in Hlook2. 
    set (σ := (s0,s1,l,i0)).
    assert (reduce (host_instance:=host_instance) s0 s1 {| f_locs := l; f_inst := i0 |}
           [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] s0 s1 {| f_locs := l; f_inst := i0 |}
           [AI_invoke a]) as Hred.
    { eapply r_call_indirect_success;eauto.
      { unfold stab_addr. destruct i0. simpl in *. destruct inst_tab;[done|]. inversion Hc.
        unfold stab_index. rewrite nth_error_lookup.
        apply list_lookup_fmap_inv in Heq as [ti [Hti Heq]].
        rewrite Heq /=. rewrite nth_error_lookup. subst.
        by rewrite Hlook /=. }
      { rewrite nth_error_lookup. eauto. }
      { simpl in *. unfold stypes.
        by rewrite nth_error_lookup Htype. } }
    iSplit.
    - iPureIntro.
      destruct s => //=.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, σ, [].
      unfold iris.prim_step => /=.
      repeat split => //.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 σ2 efs HStep).
      iMod "Hcls". iModIntro.
      destruct σ2 as [[[hs' ws'] locs'] inst'].
      destruct HStep as (H & -> & ->).
      eapply reduce_det_temp in H as HH;[|apply Hred].
      destruct HH as [HH | [Hstart | (Hstart & Hstart1 & Hstart2 & Hσ) ]]; try done.
      simplify_eq. iExists _. iFrame.
      iSplit =>//. iIntros "Hf".
      iSpecialize ("Hcont" with "[$]"). iFrame.
  Qed.
      

  Lemma wp_call_indirect_failure_types (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (f0 : frame) (i : immediate) a c cl :
    (inst_types (f_inst f0)) !! i <> Some (cl_type cl) ->
    (inst_tab (f_inst f0)) !! 0 = Some i -> (* current frame points to correct table? *)
    (N.of_nat i) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] (Some a) -∗
    (N.of_nat a) ↦[wf] cl -∗
    ↪[frame] f0 -∗
    ▷ (Φ trapV) -∗
    WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] @ s; E {{ v, Φ v ∗ ↪[frame] f0
                                                                                          ∗ (N.of_nat i) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] (Some a)
                                                                                          ∗ (N.of_nat a) ↦[wf] cl }}.
  Proof.
    iIntros (Htype Hc) "Ha Hcl Hf Hcont".
    iApply wp_lift_atomic_step;[auto|].
    iIntros ([[[? ?] ?] ?] ns κ κs nt) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (gen_heap_valid with "Hσ2 Ha") as %Hlook.
    iDestruct (gen_heap_valid with "Hσ1 Hcl") as %Hlook2.
    iDestruct (ghost_map_lookup with "Hσ5 Hf") as %Hf. simplify_map_eq.
    simplify_lookup.
    rewrite gmap_of_list_lookup Nat2N.id in Hlook2. 
    set (σ := (s0,s1,l,i0)).
    assert (reduce (host_instance:=host_instance) s0 s1 {| f_locs := l; f_inst := i0 |}
           [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] s0 s1 {| f_locs := l; f_inst := i0 |}
           [AI_trap]) as Hred.
    { eapply r_call_indirect_failure1.
      { unfold stab_addr. instantiate (1:=a). destruct i0. simpl in *. destruct inst_tab;[done|]. inversion Hc.
        unfold stab_index. rewrite nth_error_lookup.
        apply list_lookup_fmap_inv in Heq as [ti [Hti Heq]].
        rewrite Heq /=. rewrite nth_error_lookup. subst.
        by rewrite Hlook /=. }
      { rewrite nth_error_lookup. eauto. }
      { simpl in *. unfold stypes.
        rewrite nth_error_lookup. intros Hcontr%Htype. done. } }
    iSplit.
    - iPureIntro.
      destruct s => //=.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, σ, [].
      unfold iris.prim_step => /=.
      repeat split => //.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 σ2 efs HStep).
      iMod "Hcls". iModIntro.
      destruct σ2 as [[[hs' ws'] locs'] inst'].
      destruct HStep as (H & -> & ->).
      eapply reduce_det_temp in H as HH;[|apply Hred].
      destruct HH as [HH | [Hstart | (Hstart & Hstart1 & Hstart2 & Hσ) ]]; try done.
      simplify_eq. iExists _. iFrame.
      iSplit =>//. auto.
  Qed.


  Lemma wp_call_indirect_failure_notable (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (f0 : frame) (i : immediate) c :
    (inst_tab (f_inst f0)) !! 0 = None -> (* no function table *)
    ↪[frame] f0 -∗
    ▷ (Φ trapV) -∗
    WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
  Proof.
    iIntros (Hc) "Hf Hcont".
    iApply wp_lift_atomic_step;[auto|].
    iIntros ([[[? ?] ?] ?] ns κ κs nt) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (ghost_map_lookup with "Hσ5 Hf") as %Hf. simplify_map_eq.
    simplify_lookup.
    set (σ := (s0,s1,l,i0)).
    assert (reduce (host_instance:=host_instance) s0 s1 {| f_locs := l; f_inst := i0 |}
           [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] s0 s1 {| f_locs := l; f_inst := i0 |}
           [AI_trap]) as Hred.
    { eapply r_call_indirect_failure2.
      unfold stab_addr. destruct i0. simpl in *. destruct inst_tab;[done|]. inversion Hc. }
    iSplit.
    - iPureIntro.
      destruct s => //=.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, σ, [].
      unfold iris.prim_step => /=.
      repeat split => //.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 σ2 efs HStep).
      iMod "Hcls". iModIntro.
      destruct σ2 as [[[hs' ws'] locs'] inst'].
      destruct HStep as (H & -> & ->).
      eapply reduce_det_temp in H as HH;[|apply Hred].
      destruct HH as [HH | [Hstart | (Hstart & Hstart1 & Hstart2 & Hσ) ]]; try done.
      simplify_eq. iExists _. iFrame.
      iSplit =>//. auto.
  Qed.

  
  Lemma wp_call_indirect_failure_noindex (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (f0 : frame) (i : immediate) c :
    (inst_tab (f_inst f0)) !! 0 = Some i -> (* current frame points to correct table *)
    (N.of_nat i) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] None -∗ (* but no index i *)
    ↪[frame] f0 -∗
    ▷ (Φ trapV) -∗
    WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] @ s; E {{ v, Φ v ∗ ↪[frame] f0
                                                                                          ∗ (N.of_nat i) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] None }}.
  Proof.
    iIntros (Hc) "Ha Hf Hcont".
    iApply wp_lift_atomic_step;[auto|].
    iIntros ([[[? ?] ?] ?] ns κ κs nt) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (gen_heap_valid with "Hσ2 Ha") as %Hlook.
    iDestruct (ghost_map_lookup with "Hσ5 Hf") as %Hf. simplify_map_eq.
    simplify_lookup.
    set (σ := (s0,s1,l,i0)).
    assert (reduce (host_instance:=host_instance) s0 s1 {| f_locs := l; f_inst := i0 |}
           [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] s0 s1 {| f_locs := l; f_inst := i0 |}
           [AI_trap]) as Hred.
    { eapply r_call_indirect_failure2.
      { unfold stab_addr. destruct i0. simpl in *. destruct inst_tab;[done|]. inversion Hc.
        unfold stab_index. rewrite nth_error_lookup.
        apply list_lookup_fmap_inv in Heq as [ti [Hti Heq]].
        rewrite Heq /=. rewrite nth_error_lookup. subst.
        by rewrite Hlook /=. } }
    iSplit.
    - iPureIntro.
      destruct s => //=.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, σ, [].
      unfold iris.prim_step => /=.
      repeat split => //.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 σ2 efs HStep).
      iMod "Hcls". iModIntro.
      destruct σ2 as [[[hs' ws'] locs'] inst'].
      destruct HStep as (H & -> & ->).
      eapply reduce_det_temp in H as HH;[|apply Hred].
      destruct HH as [HH | [Hstart | (Hstart & Hstart1 & Hstart2 & Hσ) ]]; try done.
      simplify_eq. iExists _. iFrame.
      iSplit =>//. auto.
  Qed.

End iris_rules_calls.
