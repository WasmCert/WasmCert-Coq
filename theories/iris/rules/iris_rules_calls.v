From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity iris_wp_def iris_rules_structural stdpp_aux.
Require Export datatypes host operations properties opsem.


Close Scope byte_scope.

Section iris_rules_calls.
  
Context `{!wasmG Σ}.

  
  
  Lemma v_to_e_list_to_val es vs :
    iris.to_val es = Some (immV vs) ->
    v_to_e_list vs = es.
  Proof.
    revert vs. induction es.
    { intros vs Hval. destruct vs;inversion Hval. done. }
    { intros vs Hval.
      unfold to_val, iris.to_val in Hval.
      destruct a => // ; try destruct b => // ; simpl in Hval.
      - rewrite merge_br flatten_simplify in Hval => //.
      - rewrite merge_return flatten_simplify in Hval => //.
      - rewrite merge_prepend in Hval.
        unfold to_val, iris.to_val in IHes.
        destruct (merge_values_list _) => //.
        destruct v0 => //.
        specialize (IHes l Logic.eq_refl).
        simpl in Hval.
        inversion Hval ; subst => //=.
      - rewrite merge_trap flatten_simplify in Hval => //.
        destruct es => //.
      - destruct (merge_values_list _) => //.
        destruct v => //.
        destruct i => //.
        destruct (vh_decrease _) => //.
        rewrite merge_br flatten_simplify in Hval => //.
        rewrite merge_return flatten_simplify in Hval => //.
        rewrite merge_call_host flatten_simplify in Hval => //.
      - destruct (merge_values_list _) => //.
        destruct v => //.
        rewrite merge_call_host flatten_simplify in Hval => //.
      - rewrite merge_call_host flatten_simplify in Hval => //.
    }
  Qed.

  (* -------------------------------------------------------------------------- *)
  (* ----------------------------- Native invocations ------------------------- *)
  (* -------------------------------------------------------------------------- *)

  Lemma wp_invoke_native (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) ves vcs t1s t2s ts a es i m f :
    iris.to_val ves = Some (immV vcs) ->
    length vcs = length t1s ->
    length t2s = m ->
    ↪[frame] f -∗
     (N.of_nat a) ↦[wf] (FC_func_native i (Tf t1s t2s) ts es) -∗
     ▷ (↪[frame] f ∗ (N.of_nat a) ↦[wf] (FC_func_native i (Tf t1s t2s) ts es) -∗
       WP [::AI_local m (Build_frame (vcs ++ (n_zeros ts)) i) [::AI_basic (BI_block (Tf [::] t2s) es)]] @ s; E {{ v, Φ v }}) -∗
     WP ves ++ [AI_invoke a] @ s; E {{ v, Φ v }}.
  Proof.
    iIntros (Hparams Hlen Hret) "Hf Hi HΦ".
    iApply wp_lift_step.
    { apply to_val_const_list in Hparams. apply to_val_cat_None2; auto. }
    iIntros ([[ ? ?] ?] ns κ κs nt) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (gen_heap_valid with "Hσ1 Hi") as %Hlook.
    set (σ := (s0,l,i0)).
    assert (reduce s0 {| f_locs := l; f_inst := i0 |}
           (ves ++ [AI_invoke a])%list s0 {| f_locs := l; f_inst := i0 |}
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
      destruct σ2 as [[ ws' locs'] inst'].
      destruct HStep as (H & -> & ->).
      assert (first_instr (ves ++ [AI_invoke a]) = Some (AI_invoke a,0)) as Hf.
      { apply first_instr_const. eapply to_val_const_list. eauto. }
      eapply reduce_det in H as HH;[|apply Hred].
      destruct HH as [HH | [[? Hstart] |  (?&?&?&Hstart & Hstart1 & Hstart2 & Hσ)]]; try done.
      simplify_eq. iApply bi.sep_exist_l. iExists f. iFrame.
      iSplit => //. iIntros "Hf".
      iSpecialize ("HΦ" with "[$]"). iFrame.
      rewrite Hf in Hstart. done.
  Qed.

  (* -------------------------------------------------------------------------- *)
  (* ------------------------------ Host invocations -------------------------- *)
  (* -------------------------------------------------------------------------- *)

  
  
  Lemma wp_invoke_host s E ves vcs n t1s t2s a h f Φ :
    ves = v_to_e_list vcs ->
    length vcs = n ->
    length t1s = n ->
    (N.of_nat a) ↦[wf] (FC_func_host (Tf t1s t2s) h) -∗
    ↪[frame] f -∗
    ▷ ((N.of_nat a) ↦[wf] (FC_func_host (Tf t1s t2s) h) -∗
      ↪[frame] f -∗ 
      WP [AI_call_host (Tf t1s t2s) h vcs] @ s;E {{ Φ }}) -∗
     WP ves ++ [AI_invoke a] @ s; E {{ Φ }}.
Proof.
  iIntros (Hves Hvcs Ht1s) "Ha Hf Hwp".
  iApply wp_lift_step => //=.
  - unfold iris.to_val.
    rewrite map_app => //=.
    rewrite merge_app.
    destruct (const_list_to_val (es := ves)) as [vs Hvs].
    subst ; apply v_to_e_is_const_list.
    unfold iris.to_val in Hvs.
    destruct (merge_values_list _) => //=.
    destruct v => //=.
  - iIntros (σ ns κ κs nt) "Hσ".
    destruct σ as [[ws locs ] inst ].
    iApply fupd_mask_intro ; first by solve_ndisj.
    iIntros "Hfupd".
    iDestruct "Hσ" as "(Hσ1 & ? & ? & ? & ? & ?)".
    iDestruct (gen_heap_valid with "Hσ1 Ha") as %Hlook.
    iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => //=.
    eexists _,_,(_,_,_),_.
    repeat split => //=.
    eapply (r_invoke_host (t2s := t2s)) => //=.
    rewrite nth_error_lookup => //=.
    rewrite gmap_of_list_lookup Nat2N.id in Hlook.
    done.
  - iIntros "!>" (es σ2 efs HStep).
    iMod "Hfupd".
    iModIntro.
    destruct σ2 as [[ws' locs' ] inst' ] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H as [? | [ [??] | (?&?&?&?&?&?&?)]] ; last first.
    eapply (r_invoke_host (t2s := t2s)) => //.
    rewrite nth_error_lookup => //=.
    rewrite gmap_of_list_lookup Nat2N.id in Hlook => //.
    rewrite first_instr_const in H.
    simpl in H => //.
    by subst ; apply v_to_e_is_const_list.
    rewrite first_instr_const in H.
    simpl in H => //.
    by subst ; apply v_to_e_is_const_list.
    simplify_eq.
    iApply bi.sep_exist_l. iExists _.
    iDestruct ("Hwp" with "Ha") as "Hwp".
    iFrame.
    iSimpl. done.
Qed.


  (* -------------------------------------------------------------------------- *)
  (* ---------------------------------- Calls --------------------------------- *)
  (* -------------------------------------------------------------------------- *)

  Lemma wp_call_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) f0 (i : nat) a j lh :
    (inst_funcs (f_inst f0)) !! i = Some a -> 
    ↪[frame] f0 -∗
     ▷ (↪[frame] f0 -∗ WP [AI_invoke a] @ s; E CTX j; lh {{ v, Φ v }}) -∗
     WP [AI_basic (BI_call i)] @ s; E CTX j; lh {{ v, Φ v }}.
  Proof.
    iIntros (Hfuncs) "Hf HΦ".
    iIntros (LI Hfill).
    apply lfilled_swap with (es':=[AI_invoke a]) in Hfill as Hfill'.
    destruct Hfill' as [LI' Hfill'].
    iApply wp_lift_step.
    { apply eq_None_not_Some.
      intros Hcontr.
      eapply lfilled_to_val in Hcontr;[|eauto].
      inversion Hcontr.
      done. }
    iIntros ([[ ? ?] ?] ns κ κs nt) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (ghost_map_lookup with "Hσ5 Hf") as %Hlook. simplify_map_eq.
    set (σ := (s0,l,i0)).
    iSplit.
    - iPureIntro.
      destruct s => //=.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, σ, [].
      unfold iris.prim_step => /=.
      repeat split => //. eapply r_label.
      apply r_call. rewrite /= nth_error_lookup //. eauto. eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 σ2 efs HStep).
      iMod "Hcls". iModIntro.
      destruct σ2 as [[ ws' locs'] inst'].
      destruct HStep as (H & -> & ->).
      assert (first_instr LI = Some (AI_basic (BI_call i),0 + j)).
      { eapply starts_with_lfilled;eauto. auto. }
      eapply reduce_det in H as HH;[|eapply r_label;[|eauto..];apply r_call; rewrite /= nth_error_lookup //]. 
      destruct HH as [HH | [[? Hstart] | (?&?&? & Hstart & Hstart1 & Hstart2 & Hσ)  ]]; try done; try congruence.
      simplify_eq. iApply bi.sep_exist_l. iExists _. iFrame.
      iSplit =>//. iIntros "?". iApply ("HΦ" with "[$]"). auto.
  Qed.
  Lemma wp_call (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) f0 (i : nat) a :
    (inst_funcs (f_inst f0)) !! i = Some a -> 
    ↪[frame] f0 -∗
     ▷ (↪[frame] f0 -∗ WP [AI_invoke a] @ s; E {{ v, Φ v }}) -∗
     WP [AI_basic (BI_call i)] @ s; E {{ v, Φ v }}.
  Proof.
    iIntros (Hfuncs) "Hf HΦ".
    iApply wp_wasm_empty_ctx.
    iApply (wp_call_ctx with "[$]"). eauto.
    iNext. iIntros "?".
    iApply wp_wasm_empty_ctx.
    iApply ("HΦ" with "[$]").
  Qed. 

  Lemma wp_call_indirect_success_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (f0 : frame) (i j : immediate) a c cl d lh :
    (inst_types (f_inst f0)) !! i = Some (cl_type cl) ->
    (inst_tab (f_inst f0)) !! 0 = Some j-> 
    (N.of_nat j) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] (Some a) -∗
    (N.of_nat a) ↦[wf] cl -∗
    ↪[frame] f0 -∗
    ▷ ((N.of_nat j) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] (Some a)
       ∗ (N.of_nat a) ↦[wf] cl
       ∗ ↪[frame] f0 -∗ WP [AI_invoke a] @ s; E CTX d; lh {{ v, Φ v }}) -∗
    WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] @ s; E CTX d; lh {{ v, Φ v }}.
  Proof.
    iIntros (Htype Hc) "Ha Hcl Hf Hcont".
    iIntros (LI Hfill).
    apply lfilled_swap with (es':=[AI_invoke a]) in Hfill as Hfill'.
    destruct Hfill' as [LI' Hfill'].
    iApply wp_lift_step;[auto|].
    { apply eq_None_not_Some.
      intros Hcontr.
      eapply lfilled_to_val in Hcontr;[|eauto].
      inversion Hcontr.
      done. }
    iIntros ([[ ? ?] ?] ns κ κs nt) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (gen_heap_valid with "Hσ2 Ha") as %Hlook.
    iDestruct (gen_heap_valid with "Hσ1 Hcl") as %Hlook2.
    iDestruct (ghost_map_lookup with "Hσ5 Hf") as %Hf. simplify_map_eq.
    simplify_lookup.
    rewrite gmap_of_list_lookup Nat2N.id in Hlook2. 
    set (σ := (s0,l,i0)).
    assert (reduce s0 {| f_locs := l; f_inst := i0 |}
           [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] s0 {| f_locs := l; f_inst := i0 |}
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
      eapply r_label;eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 σ2 efs HStep).
      iMod "Hcls". iModIntro.
      destruct σ2 as [[ ws' locs'] inst'].
      destruct HStep as (H & -> & ->).
      assert (reduce s0 {| f_locs := l; f_inst := i0 |} LI s0 {| f_locs := l; f_inst := i0 |} LI') as Hred'.
      { eapply r_label;eauto. }
      eapply reduce_det in H as HH;[|apply Hred'].
      assert (first_instr LI = Some (AI_basic (BI_call_indirect i),0+d)).
      { eapply starts_with_lfilled;eauto. by cbn. }
      destruct HH as [HH | [[? Hstart] | (?&?&? & Hstart & Hstart1 & Hstart2 & Hσ)  ]]; try done; try congruence.
      simplify_eq. iApply bi.sep_exist_l. iExists _. iFrame.
      iSplit =>//. iIntros "Hf".
      iSpecialize ("Hcont" with "[$]").
      iSpecialize ("Hcont" $! _ Hfill'). iFrame.      
  Qed.
  
  Lemma wp_call_indirect_success (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (f0 : frame) (i j : immediate) a c cl :
    (inst_types (f_inst f0)) !! i = Some (cl_type cl) ->
    (inst_tab (f_inst f0)) !! 0 = Some j-> 
    (N.of_nat j) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] (Some a) -∗
    (N.of_nat a) ↦[wf] cl -∗
    ↪[frame] f0 -∗
    ▷ ((N.of_nat j) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] (Some a)
       ∗ (N.of_nat a) ↦[wf] cl
       ∗ ↪[frame] f0 -∗ WP [AI_invoke a] @ s; E {{ v, Φ v }}) -∗
    WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] @ s; E {{ v, Φ v }}.
  Proof.
    iIntros (? ?) "? ? ? H".
    iApply wp_wasm_empty_ctx.
    iApply (wp_call_indirect_success_ctx with "[$] [$] [$]");eauto.
    iNext. iIntros "?".
    iApply wp_wasm_empty_ctx.
    iApply ("H" with "[$]").
  Qed.

  Lemma wp_call_indirect_failure_types (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (f0 : frame) (i j : immediate) a c cl :
    (inst_types (f_inst f0)) !! i <> Some (cl_type cl) ->
    (inst_tab (f_inst f0)) !! 0 = Some j -> 
    (N.of_nat j) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] (Some a) -∗
    (N.of_nat a) ↦[wf] cl -∗
    ↪[frame] f0 -∗
    ▷ (Φ trapV) -∗
    WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] @ s; E {{ v, (Φ v ∗ (N.of_nat j) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] (Some a)
                                                                                          ∗ (N.of_nat a) ↦[wf] cl)
                                                                                          ∗ ↪[frame] f0 }}.
  Proof.
    iIntros (Htype Hc) "Ha Hcl Hf Hcont".
    iApply wp_lift_atomic_step;[auto|].
    iIntros ([[ ? ?] ?] ns κ κs nt) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (gen_heap_valid with "Hσ2 Ha") as %Hlook.
    iDestruct (gen_heap_valid with "Hσ1 Hcl") as %Hlook2.
    iDestruct (ghost_map_lookup with "Hσ5 Hf") as %Hf. simplify_map_eq.
    simplify_lookup.
    rewrite gmap_of_list_lookup Nat2N.id in Hlook2. 
    set (σ := (s0,l,i0)).
    assert (reduce s0 {| f_locs := l; f_inst := i0 |}
           [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] s0 {| f_locs := l; f_inst := i0 |}
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
      destruct σ2 as [[ws' locs'] inst'].
      destruct HStep as (H & -> & ->).
      eapply reduce_det in H as HH;[|apply Hred].
      destruct HH as [HH | [[? Hstart] |  (?&?&? & Hstart & Hstart1 & Hstart2 & Hσ) ]]; try done; try congruence.
      simplify_eq. iFrame. done.
  Qed.


  Lemma wp_call_indirect_failure_notable (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (f0 : frame) (i : immediate) c :
    (inst_tab (f_inst f0)) !! 0 = None -> (* no function table *)
    ↪[frame] f0 -∗
    ▷ (Φ trapV) -∗
    WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
  Proof.
    iIntros (Hc) "Hf Hcont".
    iApply wp_lift_atomic_step;[auto|].
    iIntros ([[? ?] ?] ns κ κs nt) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (ghost_map_lookup with "Hσ5 Hf") as %Hf. simplify_map_eq.
    simplify_lookup.
    set (σ := (s0,l,i0)).
    assert (reduce s0 {| f_locs := l; f_inst := i0 |}
           [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] s0 {| f_locs := l; f_inst := i0 |}
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
      destruct σ2 as [[ ws' locs'] inst'].
      destruct HStep as (H & -> & ->).
      eapply reduce_det in H as HH;[|apply Hred].
      destruct HH as [HH | [[? Hstart] | (?&?&? & Hstart & Hstart1 & Hstart2 & Hσ) ]]; try done; try congruence.
      simplify_eq. iFrame. done.
  Qed.

  Lemma wp_call_indirect_failure_noindex (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (f0 : frame) (i j : immediate) c :
    (inst_tab (f_inst f0)) !! 0 = Some j -> (* current frame points to correct table *)
    (N.of_nat j) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] None -∗ (* but no index i *)
    ↪[frame] f0 -∗
    ▷ (Φ trapV) -∗
    WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] @ s; E {{ v, (Φ v ∗ (N.of_nat j) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] None)
                                                                                          ∗ ↪[frame] f0 }}.
  Proof.
    iIntros (Hc) "Ha Hf Hcont".
    iApply wp_lift_atomic_step;[auto|].
    iIntros ([[ ? ?] ?] ns κ κs nt) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (gen_heap_valid with "Hσ2 Ha") as %Hlook.
    iDestruct (ghost_map_lookup with "Hσ5 Hf") as %Hf. simplify_map_eq.
    simplify_lookup.
    set (σ := (s0,l,i0)).
    assert (reduce s0 {| f_locs := l; f_inst := i0 |}
           [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] s0 {| f_locs := l; f_inst := i0 |}
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
      destruct σ2 as [[ ws' locs'] inst'].
      destruct HStep as (H & -> & ->).
      eapply reduce_det in H as HH;[|apply Hred].
      destruct HH as [HH | [[? Hstart] | (?&?&? & Hstart & Hstart1 & Hstart2 & Hσ) ]]; try done; try congruence.
      simplify_eq. iFrame. done.
  Qed.

  Lemma wp_call_indirect_failure_outofbounds (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (f0 : frame) (i j : immediate) c max :
    (inst_tab (f_inst f0)) !! 0 = Some j -> (* current frame points to correct table *)
    max <= (Wasm_int.nat_of_uint i32m c) ->
    (N.of_nat j) ↪[wtsize] max -∗ (* but is out of bounds *)
    ↪[frame] f0 -∗
    ▷ (Φ trapV) -∗
    WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
  Proof.
    iIntros (Hc Hge) "#Ha Hf Hcont".
    iApply wp_lift_atomic_step;[auto|].
    iIntros ([[ ? ?] ?] ns κ κs nt) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6&Hσ7&Hσ8&Hσ9)".
    iApply fupd_frame_l.
    iDestruct (gen_heap_valid with "Hσ7 Ha") as %Hlook.
    rewrite gmap_of_list_lookup Nat2N.id in Hlook.
    rewrite list_lookup_fmap in Hlook.
    iDestruct (ghost_map_lookup with "Hσ5 Hf") as %Hf. simplify_map_eq.
    apply fmap_Some_1 in Hlook as [tbli [Hlook Hsize]].
    simplify_eq.
    apply lookup_ge_None_2 in Hge.
    
    
    set (σ := (s0,l,i0)).
    assert (reduce s0 {| f_locs := l; f_inst := i0 |}
           [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] s0 {| f_locs := l; f_inst := i0 |}
           [AI_trap]) as Hred.
    { eapply r_call_indirect_failure2.
      { unfold stab_addr. destruct i0. simpl in *. destruct inst_tab;[done|]. inversion Hc.
        unfold stab_index. rewrite nth_error_lookup. simplify_eq.
        rewrite Hlook. simpl. rewrite nth_error_lookup Hge. done. } }
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
      destruct σ2 as [[ ws' locs'] inst'].
      destruct HStep as (H & -> & ->).
      eapply reduce_det in H as HH;[|apply Hred].
      destruct HH as [HH | [[? Hstart] | (?&?&? & Hstart & Hstart1 & Hstart2 & Hσ) ]]; try done; try congruence.
      simplify_eq. iFrame. done.
  Qed.

End iris_rules_calls.
