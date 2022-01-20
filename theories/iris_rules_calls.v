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

  (* The contextual and local version of these rules are strictly speaking not necessary, 
     since calls will always be independent of ambient context *)
  Lemma wp_invoke_native_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) j lh ves vcs t1s t2s ts a es i m f0 :
    iris.to_val ves = Some (immV vcs) ->
    length vcs = length t1s ->
    length t2s = m ->
    ↪[frame] f0 -∗
     (N.of_nat a) ↦[wf] (FC_func_native i (Tf t1s t2s) ts es) -∗
     (↪[frame] f0 ∗ (N.of_nat a) ↦[wf] (FC_func_native i (Tf t1s t2s) ts es) -∗
       WP [::AI_local m (Build_frame (vcs ++ (n_zeros ts)) i) [::AI_basic (BI_block (Tf [::] t2s) es)]] @ s; E CTX j; lh {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
     WP ves ++ [AI_invoke a] @ s; E CTX j; lh {{ v, Φ v ∗ ↪[frame] f0 }}.
  Proof.
    iIntros (Hparams Hlen Hret) "Hf Hi HΦ".
    iIntros (LI Hfill).
    destruct (iris.to_val LI) eqn:Hcontr.
    { apply lfilled_to_val in Hfill as [v' Hv];eauto.
      assert (iris.to_val [AI_invoke a] = None) as Hnone;auto.
      apply (to_val_cat_None2 ves) in Hnone.
      rewrite Hv in Hnone. done. }
    iApply wp_lift_step;[auto|].
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
    apply lfilled_swap with (es':=[::AI_local m (Build_frame (vcs ++ (n_zeros ts)) i) [::AI_basic (BI_block (Tf [::] t2s) es)]]) in Hfill as Hfill'.
    destruct Hfill' as [LI' Hfill'].  
    iSplit.
    - iPureIntro.
      destruct s => //=.
      unfold language.reducible, language.prim_step => /=.
      eexists [], LI', σ, [].
      unfold iris.prim_step => /=.
      repeat split => //. eapply r_label;eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 σ2 efs HStep).
      iMod "Hcls". iModIntro.
      destruct σ2 as [[[hs' ws'] locs'] inst'].
      destruct HStep as (H & -> & ->).
      assert (first_instr LI = Some (AI_invoke a)) as Hf.
      { eapply starts_with_lfilled;[|apply Hfill]. apply first_instr_const. eapply to_val_const_list. eauto. }
      eapply reduce_det_temp in H as HH;[|eapply r_label;[apply Hred|eauto..]].
      destruct HH as [HH | [Hstart | (Hstart & Hstart1 & Hstart2 & Hσ) ]]; try congruence.
      simplify_eq. iExists f0. iFrame.
      iSplit =>//. iIntros "Hf".
      iSpecialize ("HΦ" with "[$]").
      iSpecialize ("HΦ" $! _ Hfill'). iFrame.
  Qed.
  Lemma wp_invoke_native_local_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) j lh ves vcs t1s t2s ts a es i m f0 n f :
    iris.to_val ves = Some (immV vcs) ->
    length vcs = length t1s ->
    length t2s = m ->
    ↪[frame] f0 -∗
     (N.of_nat a) ↦[wf] (FC_func_native i (Tf t1s t2s) ts es) -∗
     (↪[frame] f0 ∗ (N.of_nat a) ↦[wf] (FC_func_native i (Tf t1s t2s) ts es) -∗
       WP [::AI_local m (Build_frame (vcs ++ (n_zeros ts)) i) [::AI_basic (BI_block (Tf [::] t2s) es)]] @ s; E FRAME n; f CTX j; lh {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
     WP ves ++ [AI_invoke a] @ s; E FRAME n; f CTX j; lh {{ v, Φ v ∗ ↪[frame] f0 }}.
  Proof.
    iIntros (Hparams Hlen Hret) "Hf Hi HΦ".
    iIntros (LI Hfill).
    destruct (iris.to_val LI) eqn:Hcontr.
    { apply lfilled_to_val in Hfill as [v' Hv];eauto.
      assert (iris.to_val [AI_invoke a] = None) as Hnone;auto.
      apply (to_val_cat_None2 ves) in Hnone.
      rewrite Hv in Hnone. done. }
    iApply wp_lift_step;[auto|].
    iIntros ([[[? ?] ?] ?] ns κ κs nt) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (gen_heap_valid with "Hσ1 Hi") as %Hlook.
    set (σ := (s0,s1,l,i0)).
    assert (reduce (host_instance:=host_instance) s0 s1 f
           (ves ++ [AI_invoke a])%list s0 s1 f
           [AI_local m {| f_locs := vcs ++ n_zeros ts; f_inst := i |} [AI_basic (BI_block (Tf [] t2s) es)]]) as Hred.
    { eapply r_invoke_native with (ts:=ts);eauto.
      { rewrite gmap_of_list_lookup Nat2N.id in Hlook. rewrite /= nth_error_lookup //. }
      { symmetry. apply v_to_e_list_to_val. auto. } }
    apply lfilled_swap with (es':=[::AI_local m (Build_frame (vcs ++ (n_zeros ts)) i) [::AI_basic (BI_block (Tf [::] t2s) es)]]) in Hfill as Hfill'.
    destruct Hfill' as [LI' Hfill'].  
    iSplit.
    - iPureIntro.
      destruct s => //=.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, σ, [].
      unfold iris.prim_step => /=.
      repeat split => //. eapply r_local. eapply r_label;eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 σ2 efs HStep).
      iMod "Hcls". iModIntro.
      destruct σ2 as [[[hs' ws'] locs'] inst'].
      destruct HStep as (H & -> & ->).
      assert (first_instr [AI_local n f LI] = Some (AI_invoke a)) as Hf.
      { apply first_instr_local. eapply starts_with_lfilled;[|apply Hfill]. apply first_instr_const. eapply to_val_const_list. eauto. }
      eapply reduce_det_temp in H as HH;[|eapply r_local;eapply r_label;[apply Hred|eauto..]].
      destruct HH as [HH | [Hstart | (Hstart & Hstart1 & Hstart2 & Hσ) ]]; try congruence.
      simplify_eq. iExists f0. iFrame.
      iSplit =>//. iIntros "Hf".
      iSpecialize ("HΦ" with "[$]").
      iSpecialize ("HΦ" $! _ Hfill'). iFrame.
  Qed.
  Lemma wp_invoke_native (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) ves vcs t1s t2s ts a es i m f0 :
    iris.to_val ves = Some (immV vcs) ->
    length vcs = length t1s ->
    length t2s = m ->
    ↪[frame] f0 -∗
     (N.of_nat a) ↦[wf] (FC_func_native i (Tf t1s t2s) ts es) -∗
     (↪[frame] f0 ∗ (N.of_nat a) ↦[wf] (FC_func_native i (Tf t1s t2s) ts es) -∗
       WP [::AI_local m (Build_frame (vcs ++ (n_zeros ts)) i) [::AI_basic (BI_block (Tf [::] t2s) es)]] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
     WP ves ++ [AI_invoke a] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
  Proof.
    iIntros (Hparams Hlen Hret) "Hf Hi HΦ".
    iApply wp_wasm_empty_ctx.
    iApply (wp_invoke_native_ctx with "[$] [$]");eauto.
    iIntros "Hf". iSpecialize ("HΦ" with "Hf").
    iApply wp_wasm_empty_ctx. iFrame.
  Qed.


  (* -------------------------------------------------------------------------- *)
  (* ------------------------------ Host invocations -------------------------- *)
  (* -------------------------------------------------------------------------- *)

  (* TODO: discuss what we want host invocations to look like: black box or new mode in wasm opsem? *)

  
  (* suggestion for version with host mode:
     
     update opsem as follows: 
     - [invoke a] -> host(h)
     - if h -h> h' then host(h) -> host(h')
     - if r is a host value then host(r) -> result_to_stack(r)

     where -h> are host steps, that will be part of the program logic instantiation
     then we can define a spec that looks as follows: 

     iris.to_val ves = Some (immV vcs) ->
     length vcs = length t1s ->
     length t2s = m ->
     ↪[frame] f0 -∗
     (↪[frame] f0 -∗ WP host(h) {{ Psi ∗ frame f0 }}) -∗
     forall w, Psi w ∗ frame f0 -∗ WP result_to_stack w {{ Phi ∗ frame f0 }}.

     This would also mean that the invoke step first copies over the host function, in a deterministic way.


     Alternatively, instantiation could require some more information about the 
     behaviour of a host function, such as its footprint, and its expected behaviour? see below. Quite ugly.


     forall a cl h t1s t2s ves vcs m n s s' r f hs hs',
        List.nth_error s.(s_funcs) a = Some cl ->
        cl = FC_func_host (Tf t1s t2s) h ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length t1s = n ->
        length t2s = m ->
        host_application hs s (Tf t1s t2s) h vcs hs' (Some (s', r)) ->
        reduce hs s f (ves ++ [::AI_invoke a]) hs' s' f (result_to_stack r)

   *)

  Lemma wp_invoke_host_success (P : iProp Σ) (Q : iProp Σ) (R : result -> iProp Σ) (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) ves vcs t1s t2s a h m f0 :
    iris.to_val ves = Some (immV vcs) ->
    length vcs = length t1s ->
    length t2s = m ->

    P -∗
    ↪[frame] f0 -∗
     (N.of_nat a) ↦[wf] (FC_func_host (Tf t1s t2s) h) -∗

     □ (∀ hs s locs inst ns κ κs nt,
           state_interp (hs,s,locs,inst) ns (κ ++ κs) nt ∗ P -∗
                        (⌜exists hs' s' r, host_application hs s (Tf t1s t2s) h vcs hs' (Some (s',r))⌝)
                        ∗ (⌜forall hs', host_application hs s (Tf t1s t2s) h vcs hs' None -> False⌝)) -∗
     □ (∀ hs s locs inst ns κ κs nt hs' s' r ns' κ' κs' nt',
           state_interp (hs,s,locs,inst) ns (κ ++ κs) nt ∗ P ∗ ⌜host_application hs s (Tf t1s t2s) h vcs hs' (Some (s',r))⌝ ==∗
           state_interp (hs',s',locs,inst) ns' (κ' ++ κs') nt' ∗ Q ∗ R r) -∗
     
     
     (∀ r, ↪[frame] f0 ∗ (N.of_nat a) ↦[wf] (FC_func_host (Tf t1s t2s) h) ∗ Q ∗ R r -∗
            WP result_to_stack r @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
     WP ves ++ [AI_invoke a] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
  Proof.
    iIntros (Hparams Hlen Hret) "HP Hf Hi #Hsuccess #Hspec HΦ".
    iApply wp_lift_step;[by apply (to_val_cat_None2 ves)|].
    iIntros ([[[? ?] ?] ?] ns κ κs nt) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iDestruct (gen_heap_valid with "Hσ1 Hi") as %Hlook.
    set (σ := (s0,s1,l,i)).
    iDestruct ("Hsuccess" $! s0 with "[$]") as %Hhost.
    destruct Hhost as [[hs' [s' [r Hhost]]] Hfalse].
    assert (reduce (host_instance:=host_instance) s0 s1 (Build_frame l i)
           (ves ++ [AI_invoke a])%list s0 s1 (Build_frame l i)
           (result_to_stack r)) as Hred.
    { eapply r_invoke_host_success;eauto.
      rewrite gmap_of_list_lookup Nat2N.id in Hlook. rewrite /= nth_error_lookup //.
      symmetry. apply v_to_e_list_to_val. auto. }
    iApply fupd_frame_l.
    iSplit.
    - iPureIntro. unfold iris_wp_def.reducible.
      destruct s;auto.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, σ, [].
      unfold iris.prim_step => /=.
      split;auto. apply Hred.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 σ2 efs HStep).
      
      destruct σ2 as [[[hs2 ws2] locs2] inst2].
      destruct HStep as (H & -> & ->).
      assert (∃ r, locs2 = l ∧ inst2 = i ∧ es1 = result_to_stack r ∧ host_application s0 s1 (Tf t1s t2s) h vcs hs2 (Some (ws2, r))) as [r' [-> [-> [-> Hr']]]].
      { admit. (* use the assumption that the host application never fails to prove this *) }
      iMod ("Hspec" with "[Hσ1 Hσ2 Hσ3 Hσ4 Hσ5 Hσ6 $HP]") as "(Hσ2 & Q & R)".
      { iFrame. iPureIntro. apply Hr'. }
      iMod "Hcls". iModIntro.
      iExists f0. iFrame.
      iSplit =>//. Unshelve. all: try apply 0. all: apply [].
  Admitted.
    

  (* -------------------------------------------------------------------------- *)
  (* ---------------------------------- Calls --------------------------------- *)
  (* -------------------------------------------------------------------------- *)

  (* Note that the contextual versions are unnecessary, a fresh call needs 
     no knowledge of the ambient context *)
  Lemma wp_call_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) f0 (i : nat) a j lh :
    (inst_funcs (f_inst f0)) !! i = Some a -> 
    ↪[frame] f0 -∗
     ▷ (↪[frame] f0 -∗ WP [AI_invoke a] @ s; E CTX j; lh {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
     WP [AI_basic (BI_call i)] @ s; E CTX j; lh {{ v, Φ v ∗ ↪[frame] f0 }}.
  Proof.
    iIntros (Hfuncs) "Hf HΦ".
    iIntros (LI Hfill).
    destruct (iris.to_val LI) eqn:Hcontr.
    { apply lfilled_to_val in Hfill as [v' Hv];eauto.
      assert (iris.to_val [AI_basic (BI_call i)] = None) as Hnone;auto.
      rewrite Hv in Hnone. done. }
    iApply wp_lift_step;[auto|].
    iIntros ([[[? ?] ?] ?] ns κ κs nt) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (ghost_map_lookup with "Hσ5 Hf") as %Hlook. simplify_map_eq.
    set (σ := (s0,s1,l,i0)).
    apply lfilled_swap with (es':=[AI_invoke a]) in Hfill as Hfill'.
    destruct Hfill' as [LI' Hfill'].  
    iSplit.
    - iPureIntro.
      destruct s => //=.
      unfold language.reducible, language.prim_step => /=.
      eexists [], LI', σ, [].
      unfold iris.prim_step => /=.
      repeat split => //. eapply r_label;eauto.
      apply r_call. rewrite /= nth_error_lookup //.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 σ2 efs HStep).
      iMod "Hcls". iModIntro.
      destruct σ2 as [[[hs' ws'] locs'] inst'].
      destruct HStep as (H & -> & ->).
      assert (first_instr LI = Some (AI_basic (BI_call i))) as Hf.
      { eapply starts_with_lfilled;[|apply Hfill]. auto. }
      eapply reduce_det in H as HH;[|eapply r_label;[|eauto..];apply r_call; rewrite /= nth_error_lookup //]. 
      destruct HH as [HH | [Hstart | [[? ?] |(Hstart & Hstart1 & Hstart2 & Hσ) ]]]; try congruence.
      simplify_eq. iExists _. iFrame.
      iSplit =>//. iIntros "Hf".
      iSpecialize ("HΦ" with "[$]").
      iSpecialize ("HΦ" $! _ Hfill'). iFrame.
  Qed.
  Lemma wp_call (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) f0 (i : nat) a :
    (inst_funcs (f_inst f0)) !! i = Some a -> 
    ↪[frame] f0 -∗
     ▷ (↪[frame] f0 -∗ WP [AI_invoke a] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
     WP [AI_basic (BI_call i)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
  Proof.
    iIntros (Hfuncs) "Hf HΦ".
    iApply wp_wasm_empty_ctx.
    iApply (wp_call_ctx with "[$]");eauto.
    iNext.
    iIntros "Hf". iSpecialize ("HΦ" with "Hf").
    iApply wp_wasm_empty_ctx. iFrame.
  Qed.

  Lemma wp_call_indirect_success_ctx : False.
  Proof.
  Admitted.




(*



  | r_call :
      forall s f i a hs,
        List.nth_error f.(f_inst).(inst_funcs) i = Some a ->
        reduce hs s f [::AI_basic (BI_call i)] hs s f [::AI_invoke a]
  | r_call_indirect_success :
      forall s f i a cl c hs,
        (*        stab s f.(f_inst) (Wasm_int.nat_of_uint i32m c) = Some cl ->*)
        stab_addr s f (Wasm_int.nat_of_uint i32m c) = Some a ->
        List.nth_error s.(s_funcs) a = Some cl ->
        stypes s f.(f_inst) i = Some (cl_type cl) ->
        reduce hs s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] hs s f [::AI_invoke a]
  | r_call_indirect_failure1 :
      forall s f i a cl c hs,
(*        stab s f.(f_inst) (Wasm_int.nat_of_uint i32m c) = Some cl ->*)
        stab_addr s f (Wasm_int.nat_of_uint i32m c) = Some a ->
        List.nth_error s.(s_funcs) a = Some cl ->
        stypes s f.(f_inst) i <> Some (cl_type cl) ->
        reduce hs s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] hs s f [::AI_trap]
  | r_call_indirect_failure2 :
      forall s f i c hs,
(*        stab s f.(f_inst) (Wasm_int.nat_of_uint i32m c) = None ->*)
        stab_addr s f (Wasm_int.nat_of_uint i32m c) = None ->
        reduce hs s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] hs s f [::AI_trap]

*)  
End iris_rules_calls.
