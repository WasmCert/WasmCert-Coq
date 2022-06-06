From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris_properties iris_wp_def stdpp_aux.
Require Export datatypes host operations properties opsem.



(* empty lists, frame and context rules *)

Close Scope byte_scope.

Section structural_rules.
Context `{!wasmG Σ}.

Lemma wp_wasm_empty_ctx (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) e :
  ⊢ WP e @ s ; E {{ Φ }} ∗-∗ WP e @ s ; E CTX_EMPTY {{ Φ }}.
Proof.
  iSplit.
  { iIntros "HWP". iIntros (LI Hfill%lfilled_Ind_Equivalent).
    inversion Hfill. subst. erewrite app_nil_l; erewrite app_nil_r. done. }
  { iIntros "HWP".
    iDestruct ("HWP" $! e with "[]") as "$".
    iPureIntro. cbn. rewrite app_nil_r eqseqE. apply eq_refl. }
Qed.

Lemma wp_wasm_empty_ctx_frame (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) e n f :
  ⊢ WP e @ s ; E FRAME n; f {{ Φ }} ∗-∗ WP e @ s ; E FRAME n; f CTX_EMPTY {{ v, Φ v }}.
Proof.
  iSplit.
  { iIntros "HWP". iIntros (LI Hfill%lfilled_Ind_Equivalent).
    inversion Hfill. subst. erewrite app_nil_l; erewrite app_nil_r. done. }
  { iIntros "HWP".
    iDestruct ("HWP" $! e with "[]") as "$".
    iPureIntro. cbn. rewrite app_nil_r eqseqE. apply eq_refl. }
Qed.

Lemma wp_nil (s : stuckness) (E : coPset) (Φ : iProp Σ) f :
  ↪[frame] f ∗ Φ ⊢ WP [] @ s ; E CTX_EMPTY {{ fun v => Φ }}%I.
Proof.
  iIntros "(Hframe & H)". iApply wp_wasm_empty_ctx.
  rewrite wp_unfold /wp_pre /=. iFrame. eauto.
Qed.
  
(* Sequencing rule which is guaranteed not to trap *)
Lemma wp_seq_ctx (s : stuckness) (E : coPset) (Φ Ψ : iris.val -> iProp Σ) (es1 es2 : language.expr wasm_lang) (i : nat) (lh : lholed) :
  ((¬ (Ψ trapV)) ∗
  WP es1 @ NotStuck; E {{ w, Ψ w }} ∗
  ∀ w, Ψ w -∗ WP (iris.of_val w ++ es2) @ s; E CTX i; lh {{ v, Φ v }})%I
  ⊢ WP (es1 ++ es2) @ s; E CTX i; lh {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ i lh).
{ iIntros "[Hntrap [Hes1 Hes2]]".
  (* iDestruct (wp_wasm_empty_ctx with "Hes1") as "Hes1". *)
  iIntros (LI Hfilled).
  iApply wp_unfold. rewrite /wp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val LI) as [vs|] eqn:Hetov.
  { iDestruct (wp_unfold with "Hes1") as "Hes1".
    rewrite /wp_pre /=.
    eapply lfilled_to_val_app in Hfilled as Hv;eauto.
    destruct Hv as [vs' [Hvs' Hfilled']].
    unfold iris_wp_def.to_val in Hvs'.
    rewrite Hvs'.
    iSpecialize ("Hes2" with "Hes1").
    iMod "Hes2".
    iSpecialize ("Hes2" $! _ Hfilled').
    iDestruct (wp_unfold with "Hes2") as "Hes2". rewrite /wp_pre /= Hetov.
    done.
  }
  {
  repeat rewrite wp_unfold. rewrite /wp_pre /=.
  (* Ind *)
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod "Hes1".
    iSpecialize ("Hes2" with "Hes1").
    iSpecialize ("Hes2" $! _ Hfilled).
    iDestruct (wp_unfold with "Hes2") as "Hes2"; rewrite /wp_pre /=.
    rewrite Hetov.
    iSpecialize ("Hes2" $! σ ns κ κs nt with "[$]").
    iMod "Hes2" as "[%H1 H2]".
    iIntros "!>".
    iSplit.
    - iPureIntro. by apply H1. 
    - by iApply "H2".
  }
  {
    iSpecialize ("Hes1" $! σ ns κ κs nt with "[$]").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct s => //.
      apply append_reducible with (es2:=es2) in H1;auto.
      eapply lfilled_reducible. apply Hfilled. auto.
    - iIntros (e2 σ2 efs HStep').
      eapply lfilled_prim_step_split_reduce_r in HStep' as Heq;[|apply Hfilled|apply H1].
      apply prim_step_obs_efs_empty in HStep' as Hemp. inversion Hemp;subst;clear Hemp.
      destruct Heq as [[e' [HStep'' Hlfilled']] | [[lh' Hlf] <-]].
      + apply prim_step_obs_efs_empty in HStep'' as Hemp. inversion Hemp;subst;clear Hemp.
        iSpecialize ("H2" $! e' σ2 [] HStep'').
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        iModIntro.
        iDestruct "H2" as "(Hσ & Hes)".
        iDestruct "Hes" as (f1) "(Hf & Hes'' & Hefs)".
        iFrame. iExists _. iFrame.
        iSplit =>//.
        iIntros "?"; iSpecialize ("Hes''" with "[$]").
        iDestruct ("IH" with "[$Hntrap $Hes'' $Hes2]") as "Hcont"; by iApply "Hcont".
      + assert (iris.prim_step es1 σ [] [AI_trap] σ []) as HStep2.
        { unfold iris.prim_step.
          destruct σ as [[??]?].
          repeat split => //.
          apply r_simple; eapply rs_trap => //.
          move => HContra; subst.
          by simpl in Hes.
        }
        iSpecialize ("H2" $! [AI_trap] σ [] HStep2).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        destruct σ as [[? ?]?].
        iDestruct "H2" as "[Hσ H]".
        iDestruct "H" as (f) "(Hf1 & Hes'' & Hefs)".
        iModIntro => /=.
        iFrame. iExists _. iFrame.
        iIntros "?"; iSpecialize ("Hes''" with "[$]").
        replace [AI_trap] with (iris.of_val trapV) => //=.
        iDestruct (wp_unfold with "Hes''") as "Hes''";rewrite /wp_pre /=.
        destruct (iris.to_val e2) eqn:Hx.
        * iMod "Hes''". 
          by iSpecialize ("Hntrap" with "Hes''").
        * iApply wp_unfold. rewrite /wp_pre /= Hx /=.
          iIntros (?????) "?".
          iMod "Hes''".
          by iSpecialize ("Hntrap" with "Hes''").
  } } }
Qed.


(* Contextual rules for Local computation *)

Lemma wp_frame_rewrite (s: stuckness) (E: coPset) (Φ: val -> iProp Σ) es n f:
  WP es @ s; E FRAME n; f {{ v, Φ v }} ⊣⊢
  WP [AI_local n f es] @ s; E {{ v, Φ v }}.
Proof.
  trivial.
Qed.

Lemma wp_frame_value (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es n f f0 vs :
  iris.to_val es = Some (immV vs) ->
  length es = n ->
  ↪[frame] f0 -∗
  ▷ (Φ (immV vs)) -∗
  WP es @ s; E FRAME n; f {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hv Hlen) "Hframe H".
  rewrite wp_frame_rewrite.
  apply to_val_const_list in Hv as Hconst.
  iApply (wp_lift_atomic_step with "[H Hframe]"); simpl ; trivial;eauto.
  unfold iris.to_val => /=.
  apply const_list_to_val in Hconst as [??].
  unfold iris.to_val in H.
  destruct (merge_values_list _) => //.
  by inversion H.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], es, σ, [].
    destruct σ as [[ ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //. apply r_simple. apply rs_local_const; auto.
  - destruct σ as [[ws locs] inst].
    iIntros "!>" (es2 σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'].
    destruct HStep as (H & -> & ->). iFrame.
    (* iDestruct ("H" with "Hframe") as "[H Hframe]". iFrame. *)
    only_one_reduction H. all:simplify_eq;iFrame. rewrite Hv. iFrame.
    1,2:rewrite find_first_const// in Hstart.
Qed.

Lemma wp_seq_ctx_frame (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) (i : nat) (lh : lholed) (n : nat) (f : frame) (f0 : frame) (f1 : frame) :
  (forall LI, lfilled i lh (es1 ++ es2) LI -> iris.to_val [AI_local n f LI] = None) ->
  ((¬ (Ψ trapV)) ∗ ↪[frame] f0 ∗
   (↪[frame] f -∗ WP es1 @ NotStuck; E {{ w, Ψ w ∗ ↪[frame] f1 }}) ∗
  ∀ w, Ψ w ∗ ↪[frame] f0 -∗ WP (iris.of_val w ++ es2) @ s; E FRAME n ; f1 CTX i; lh {{ v, Φ v }})%I
  ⊢ WP (es1 ++ es2) @ s; E FRAME n ; f CTX i; lh {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ i lh n f f0 f1).
{ iIntros (Hnone) "[Htrap [Hf0 [Hes1 Hes2]]]".
  (* iDestruct (wp_wasm_empty_ctx with "Hes1") as "Hes1". *)
  iIntros (LI Hfilled).
  iApply wp_unfold.
  (* Base case, when both es1 and es2 are values *)

  destruct (iris.to_val [AI_local n f LI]) as [vs|] eqn:Hetov.
  { assert (iris.to_val [AI_local n f LI] = Some vs) as Hetov' => //.
    unfold iris.to_val in Hetov ; simpl in Hetov.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v => //.
    (* destruct l0 => //. *) 
    eapply lfilled_to_val_app in Hfilled as Heq;[|eauto] ; last first.
    unfold iris.to_val ; rewrite Hmerge => //. 
    destruct Heq as [vs' [Heq Hfilled']].
    repeat rewrite wp_unfold /wp_pre /=.
    rewrite Heq. apply Hnone in Hfilled. congruence.
    
  }
  { repeat rewrite wp_unfold /wp_pre /=. rewrite Hetov.
    unfold iris.to_val in Hetov.
    destruct (merge_values_list _) eqn:Hmerge => //.
    apply Hnone in Hfilled as Hnone'.
    apply lfilled_to_sfill in Hfilled as Hsfill.
    destruct Hsfill as [sh Hsh].
    rewrite Hsh in Hnone'. rewrite sfill_to_llfill in Hnone'.
    apply to_val_local_none in Hnone' as Hnone2.

    iIntros (σ ns κ κs nt) "Hσ".
    destruct σ as [[s1 locs] inst].
    iDestruct "Hσ" as "(Hfuncs&Htables&Hmems&Hglobals&Hframe&Hlen)".
    iDestruct (ghost_map_lookup with "Hframe Hf0") as %Hlook;rewrite lookup_insert in Hlook;inversion Hlook.
    iMod (ghost_map_update f with "Hframe Hf0") as "[Hframe Hf]"; rewrite insert_insert.
    iDestruct ("Hes1" with "Hf") as "Hes1".
    destruct f.

    
    destruct (iris.to_val es1) eqn:Hetov'.
    { (* apply to_val_local_no_local_none in Hnone2. *)
      (* rewrite Hetov' in Hnone2. *)
      iMod "Hes1" as "[HPsi Hf]".
      iDestruct (ghost_map_lookup with "Hframe Hf") as %Hlook';rewrite lookup_insert in Hlook';inversion Hlook'.
      subst f1 f0.
      iMod (ghost_map_update {| f_locs := locs; f_inst := inst |}
             with "Hframe Hf") as "[Hframe Hf]"; rewrite insert_insert.
      iDestruct ("Hes2" with "[$]") as "Hes2".
      erewrite of_to_val;[|eauto].
      iDestruct ("Hes2" with "[]") as "Hes2".
      { iPureIntro. eauto. }
      iDestruct (wp_frame_rewrite with "Hes2") as "Hes2".
      iDestruct (wp_unfold with "Hes2") as "Hes2".
      rewrite /wp_pre /= Hsh sfill_to_llfill Hnone'.
      iSpecialize ("Hes2" $! (s1,locs,inst) ns κ κs nt with "[$]").
      iFrame. }

    

    iSpecialize ("Hes1" $! (s1,f_locs,f_inst) ns κ κs nt with "[$]").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    { iPureIntro.
      destruct s => //.
      apply append_reducible with (es2:=es2) in H1;auto.
      eapply local_frame_lfilled_reducible. apply Hfilled. auto. }
    iIntros (e2 σ2 efs HStep').
    destruct σ2 as [[s3 locs2] inst2].
    eapply local_frame_lfilled_prim_step_split_reduce_r in HStep' as Heq;[|apply Hfilled|apply H1].
    destruct Heq as [[e' [v'' [i'' [LI' [HStep'' [-> [-> [-> Hfill]]]]]]]]|[lh' [Hlh HH]]].
    { apply prim_step_obs_efs_empty in HStep'' as Hemp. inversion Hemp;subst;clear Hemp.
      (* apply prim_step_obs_efs_empty in HStep' as Hemp. inversion Hemp;subst;clear Hemp. *)
      iSpecialize ("H2" $! e' (s3,v'',i'') [] HStep'').
      iMod "H2".
      repeat iModIntro.
      repeat iMod "H2".
      iDestruct "H2" as "(Hσ & H)".
      iDestruct "H" as (f) "(Hf1 & Hes'' & Hefs)".
      (* iExists f. *)
      iDestruct "Hσ" as "(Hfuncs&Htables&Hmems&Hglobals&Hframe&Hlen)".
      iDestruct (ghost_map_lookup with "Hframe Hf1") as %Hlook';rewrite lookup_insert in Hlook';inversion Hlook'.
      subst f.
      apply lfilled_to_sfill in Hfill as Hsh.
      destruct Hsh as [sh' Hsh'].
      destruct (iris.to_val [AI_local n {| f_locs := v''; f_inst := i'' |} e']) eqn:Hetov2.
      { apply to_val_local_inv in Hetov2 as Heq.
        destruct Heq as [tf [h [w [vh Heq]]]]. subst v.
        
        apply to_val_call_host_rec_local in Hetov2 as HH.
        destruct HH as [LI2 [HeqLI HLI]].
        rewrite app_nil_l app_nil_r in HeqLI. simplify_eq.
        
        iDestruct ("Hes''" with "[$]") as "Hes''".
        iDestruct (wp_unfold with "Hes''") as "Hes''".
        rewrite /wp_pre /= HLI.
        iMod "Hes''" as "[HPsi Hf]".
        iDestruct (ghost_map_lookup with "Hframe Hf") as %Hlook';rewrite lookup_insert in Hlook';inversion Hlook'.
        subst f1.
        iMod (ghost_map_update (Build_frame locs2 inst2) with "Hframe Hf") as "[Hframe Hf]"; rewrite insert_insert.
        iModIntro. iFrame.
        iExists _. iFrame. iIntros "Hf".
        iDestruct ("Hes2" with "[$]") as "Hes2".
        iDestruct ("Hes2" with "[]") as "Hes2".
        { iPureIntro. apply of_to_val in HLI. rewrite HLI. eauto. }
        iFrame.
      }

      destruct (iris.to_val e') eqn:Hetov3.
      { iDestruct ("Hes''" with "[$]") as "Hes''".
        iDestruct (wp_unfold with "Hes''") as "Hes''".
        rewrite /wp_pre /= Hetov3.
        iMod "Hes''" as "[HPsi Hf]".
        iDestruct (ghost_map_lookup with "Hframe Hf") as %Hlook'';rewrite lookup_insert in Hlook'';inversion Hlook''.
        subst f1.
        iMod (ghost_map_update (Build_frame locs2 inst2) with "Hframe Hf") as "[Hframe Hf]"; rewrite insert_insert.
        iModIntro. iFrame.
        iExists _. iFrame. iIntros "Hf".
        iDestruct ("Hes2" with "[$]") as "Hes2".
        iDestruct ("Hes2" with "[]") as "Hes2".
        { iPureIntro. erewrite of_to_val;eauto. }
        iFrame.
      }
      
      assert (e' ++ es2 = sfill (SH_base [] es2) e') as Hsh'';[auto|].
      pose proof (sfill_nested sh' (SH_base [] es2) e') as [vh' Hvh'].
      
      apply to_val_local_none_inv with (vh:=ll_of_sh vh') in Hetov2 as Hetov4;[|auto].
      rewrite - sfill_to_llfill in Hetov4.
      rewrite -Hvh' -Hsh'' - Hsh' in Hetov4.

      iFrame.
      iMod (ghost_map_update (Build_frame locs2 inst2) with "Hframe Hf1") as "[Hframe Hf]"; rewrite insert_insert.
      iModIntro. iFrame.
      
      iExists _. iFrame.
      iSplit => //. iIntros "Hf".
      iApply ("IH" with "[] [$] []");auto.
      iPureIntro. intros LI HLI.
      eapply lfilled_inj in Hfill;eauto.
      subst LI. auto.
    }

    (* trap case *)
    simplify_eq.
    set (σ:=(s3, f_locs, f_inst)).
    assert (iris.prim_step es1 σ [] [AI_trap] σ []) as HStep2.
    { unfold iris.prim_step.
      destruct σ as [[??]?].
      repeat split => //.
      apply r_simple; eapply rs_trap => //.
      move => HContra; subst. done.
    }
    (* apply prim_step_obs_efs_empty in HStep' as Heq. *)
    destruct HStep' as [HStep' [-> ->]].
    simplify_eq.
    iSpecialize ("H2" $! [AI_trap] σ [] HStep2).
    iMod "H2".
    repeat iModIntro.
    repeat iMod "H2".
    iDestruct "H2" as "(Hσ & H )".
    iDestruct "H" as (f2) "(Hf1 & Hes'' & Hefs)".
    iDestruct "Hσ" as "(Hfuncs&Htables&Hmems&Hglobals&Hframe&Hlen)".
    iDestruct (ghost_map_lookup with "Hframe Hf1") as %Hlook';rewrite lookup_insert in Hlook';inversion Hlook'.
    iSpecialize ("Hes''" with "[$]").
    replace [AI_trap] with (iris.of_val trapV) => //=.
    
    destruct (iris.to_val e2) eqn:Hx.
    * rewrite wp_unfold /wp_pre /=. iMod "Hes''" as "[Hes'' _]".
      by iSpecialize ("Htrap" with "Hes''").
    * rewrite wp_unfold /wp_pre /=. iMod "Hes''" as "[Hes'' _]".
      by iSpecialize ("Htrap" with "Hes''").
      Unshelve. all: try apply 0. all: apply [].
  } }
Qed.

Lemma wp_seq (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) :
  (¬ Ψ trapV ∗ 
  WP es1 @ s; E {{ w, Ψ w }} ∗
  ∀ w, Ψ w -∗ WP (iris.of_val w ++ es2) @ s; E {{ v, Φ v }})
  ⊢ WP (es1 ++ es2) @ s; E {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ).
  iIntros "(Hntrap & Hes1 & Hes2)".
  (* Base case, when both es1 and es2 are values *)
  iApply wp_unfold. repeat rewrite wp_unfold /wp_pre /=.
  destruct (iris.to_val (es1 ++ es2)) as [vs|] eqn:Hetov.
  { assert (lfilled 0 (LH_base [] []) (es1 ++ es2) (es1 ++ es2)) as Hfilled.
    { cbn. erewrite app_nil_r. by apply/eqP. }
    eapply lfilled_to_val_app in Hfilled as Hv;eauto.
    destruct Hv as [vs' [Hvs' Hfilled']].
    unfold iris_wp_def.to_val in Hvs'.
    rewrite Hvs'.
    iSpecialize ("Hes2" with "Hes1").
    iMod "Hes2".
    apply lfilled_Ind_Equivalent in Hfilled';inversion Hfilled';simplify_eq.
    erewrite app_nil_r in H1.
    assert (iris.of_val vs' ++ es2 = es1 ++ es2) as ->;auto.
    iDestruct (wp_unfold with "Hes2") as "Hes2". rewrite /wp_pre /= Hetov.
    done.
  }
  (* Ind *)
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod "Hes1".
    iSpecialize ("Hes2" with "Hes1").
    iDestruct (wp_unfold with "Hes2") as "Hes2"; rewrite /wp_pre /=.
    rewrite Hetov.
    iSpecialize ("Hes2" $! σ ns κ κs nt with "[$]").
    iMod "Hes2" as "[%H1 H2]".
    iIntros "!>".
    iSplit.
    - iPureIntro. by apply H1. 
    - by iApply "H2".
  }
  {
    iSpecialize ("Hes1" $! σ ns κ κs nt with "[$]").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct s => //.
      by apply append_reducible.
    - iIntros (e2 σ2 efs HStep).
      assert (κ = [] /\ efs = []) as [-> ->]; first by apply prim_step_obs_efs_empty in HStep; inversion HStep.
      apply prim_step_split_reduce_r in HStep; last by [].
      destruct HStep as [[es'' [-> HStep]] | [n [m [lh [Hlf1 [Hlf2 ->]]]]]].
      + iSpecialize ("H2" $! es'' σ2 [] HStep).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        iModIntro.
        destruct σ2 as [[??]?].
        iDestruct "H2" as "[Hσ H]".
        iDestruct "H" as (f1) "(Hf1 & Hes'' & Hefs)".
        iFrame. iExists _. iFrame.
        iIntros "?"; iSpecialize ("Hes''" with "[$]").
        iApply "IH".
        by iFrame. 
      + move/lfilledP in Hlf1.
        inversion Hlf1; subst; clear Hlf1.
        assert (iris.prim_step es1 σ [] [AI_trap] σ []) as HStep2.
        { unfold iris.prim_step.
          destruct σ as [[??]?].
          repeat split => //.
          apply r_simple; eapply rs_trap => //.
          move => HContra; subst.
          by destruct n.
        }
        iSpecialize ("H2" $! [AI_trap] σ [] HStep2).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        destruct σ as [[??]?].
        iDestruct "H2" as "[Hσ H]".
        iDestruct "H" as (f1) "(Hf1 & Hes'' & Hefs)".
        iFrame. iExists _. iFrame.
        iModIntro.
        iFrame.
        iIntros "?"; iSpecialize ("Hes''" with "[$]").
        replace [AI_trap] with (iris.of_val trapV) => //.
        repeat rewrite wp_unfold /wp_pre /=.
        destruct (iris.to_val (take n es1 ++ AI_trap :: drop m (es1 ++ es2))%SEQ) eqn:Hx.
        * iMod "Hes''".
          by iSpecialize ("Hntrap" with "Hes''").
        * iIntros (?????) "?".
          iMod "Hes''".
          by iSpecialize ("Hntrap" with "Hes''").
  }
Qed.

Lemma wp_val (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v0 : value) (es : language.expr wasm_lang) :
  (* Like for wp_seq, this lemma is true without the trap condition, but would
     be problematic to prove without it. *)
  ((¬ Φ trapV) ∗
  WP es @ NotStuck ; E {{ v, (Φ (val_combine (immV [v0]) v))  }}
  ⊢ WP ((AI_basic (BI_const v0)) :: es) @ s ; E {{ v, Φ v }})%I.
Proof.
  (* This also needs an iLob. *)
  iLöb as "IH" forall (v0 es Φ).
  iIntros "(Hntrap & H)".
  iApply wp_unfold.               
  repeat rewrite wp_unfold /wp_pre /=.
  destruct (iris.to_val es) as [vs|] eqn:Hes.
  { destruct vs.
    { apply of_to_val in Hes as <-. rewrite to_val_cons_immV. auto. }
    apply to_val_trap_is_singleton in Hes as ->. simpl.
    iIntros (?????) "?".
    iMod "H".
    by iSpecialize ("Hntrap" with "H").
    erewrite to_val_cons_brV;eauto.
    erewrite to_val_cons_retV;eauto.
    erewrite to_val_cons_callHostV;eauto.
  }
  { rewrite to_val_cons_None.
    iIntros (σ ns κ κs nt) "Hσ".
    iSpecialize ("H" $! σ ns κ κs nt with "[$]").
    iMod "H".
    iModIntro.
    iDestruct "H" as "(%H1 & H)".
    iSplit.
    - iPureIntro.
      destruct s => //=.
      rewrite - cat1s.
      by eapply prepend_reducible; eauto.
    - iIntros (es2 σ2 efs HStep).
      rewrite -cat1s in HStep.
      eapply reduce_ves in H1; last by apply HStep.
      assert (κ = [] /\ efs = []) as [-> ->]; first by apply prim_step_obs_efs_empty in HStep; inversion HStep.
      destruct H1 as [[-> HStep2] | [lh1 [lh2 [Hlf1 [Hlf2 ->]]]]].
      + iSpecialize ("H" $! (drop 1 es2) σ2 [] HStep2).
        iMod "H".
        repeat iModIntro.
        repeat iMod "H".
        iModIntro.
        iDestruct "H" as "[Hσ H]".
        iDestruct "H" as  (f1) "(Hf1 & Hes & Hefs)".
        iSimpl.
        iFrame. iExists _. iFrame.
        iSplit => //.
        iIntros "?"; iSpecialize ("Hes" with "[$]").
        iApply "IH".
        by iFrame.
      + move/lfilledP in Hlf1.
        inversion Hlf1; subst; clear Hlf1.
        move/lfilledP in Hlf2.
        inversion Hlf2; subst; clear Hlf2.
        assert (iris.prim_step (vs0 ++ [AI_trap] ++ es'0) σ2 [] [AI_trap] σ2 []) as HStep2.
        { unfold iris.prim_step.
          destruct σ2 as [[??]?].
          repeat split => //.
          apply r_simple; eapply rs_trap => //.
          - move => HContra.
            by replace (vs0 ++ [AI_trap] ++ es'0)%SEQ with [AI_trap] in Hes.
          - apply/lfilledP.
            by apply LfilledBase.
        }
        iSpecialize ("H" $! [AI_trap] σ2 [] HStep2).
        iMod "H".
        repeat iModIntro.
        repeat iMod "H".
        iDestruct "H" as "[Hσ H]".
        iDestruct "H" as (f1) "(Hf1 & Hes & Hefs)".
        iFrame.
        iModIntro. iExists _. iFrame.
        iSplit => //.
        iIntros "?"; iSpecialize ("Hes" with "[$]").
        repeat rewrite wp_unfold /wp_pre /=.
        destruct (iris.to_val (vs ++ AI_trap :: es')%SEQ) eqn:Hx.
        * iMod "Hes".
          by iSpecialize ("Hntrap" with "Hes").
        * iIntros (?????) "?".
          iMod "Hes".
          by iSpecialize ("Hntrap" with "Hes").
          auto.
  }
Qed.
  
Lemma wp_val_app' (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs (es : language.expr wasm_lang) :
  (* □ is required here -- this knowledge needs to be persistent instead of 
     one-off. *)
  (□ (¬ Φ trapV )) ∗
  WP es @ NotStuck ; E {{ v, (Φ (val_combine (immV vs) v)) }}%I
  ⊢ WP ((v_to_e_list vs) ++ es) @ s ; E {{ v, Φ v }}%I.

Proof.
  iInduction vs as [|c vs] "IH" forall (Φ s E es).
  { simpl.
    iIntros "(#Hntrap & HWP)".
    destruct s.
    2: iApply wp_stuck_weaken.
    all: iApply (wp_wand with "HWP").
    all: iIntros (v).
    all: destruct v => /=.
    all: iIntros "HΦ" => //.
    all: by rewrite vh_push_const_nil + rewrite sh_push_const_nil + rewrite llh_push_const_nil.
  }
  { iIntros "(#Hntrap & HWP)".
    iSimpl.
    iApply wp_val.
    iSplitR => //.
    iApply "IH" => //=.
    iSplit => //.
    iApply (wp_mono with "HWP").
    iIntros (vs') "HΦ".
    iSimpl. destruct vs';auto.
    by rewrite -vh_push_const_app.
    by rewrite -sh_push_const_app.
    by rewrite -llh_push_const_app.
  }
Qed.
  
Lemma wp_val_app (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs v' (es : language.expr wasm_lang) :
  iris.to_val vs = Some (immV v') ->
  (□ (¬ Φ trapV )) ∗
  WP es @ NotStuck ; E {{ v, (Φ (val_combine (immV v') v)) }}%I
  ⊢ WP (vs ++ es) @ s ; E {{ v, Φ v }}%I.
Proof.
  iIntros "%Hves [#Hntrap Hwp]".
  apply iris.of_to_val in Hves; subst.
  iApply wp_val_app'.
  by iFrame.
Qed.


(* Trying to resolve the problem by naively not allowing any consumption of ↪ in
   the WP premises.

   However, we then cannot connect the resulting frame after executing es1 to 
   that at the start of es2: the only way to achieve that is to have a 
   ↪[frame] in the post condition of es1; but to prove any WP with that post
   condition, we need to provide a ↪[frame] to its precondition as well; 
   so we will need two copies of the same ↪ to prove any WP, rendering the 
   spec useless.

   What we need in the post condition is some predicate like ↪ which gives
   us the knowledge of the new frame, but does not actually assert any 
   ownership -- in some sense, we need to be able to assert 0 ownership of 
   something while still asserting the knowledge of that value. This seems to
   be a weird feature to ask for, however.
 *)
(* Upd: THIS IS DONE!!!!
        Note how the post condition successfully prevents the leakage of any
        frame resources from the inner to the outer frame via Ψ -- the outer 
        frame predicate remains unchanged despite that it could undergo 
        arbitrary changes inside the frames. *)

Lemma wp_frame_seq es1 es2 n (f0 f f': frame) E s Ψ Φ :
  (iris.to_val [AI_local n f (es1 ++ es2)] = None) ->
  ¬ Ψ trapV -∗ ↪[frame] f0 -∗
  ((↪[frame] f) -∗ WP es1 @ NotStuck; E {{ v, Ψ v ∗ ↪[frame] f'}}) -∗
  (∀ w, ↪[frame] f0 -∗ (Ψ w) -∗ WP (iris.of_val w ++ es2) @ s; E FRAME n; f' {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
  (WP (es1 ++ es2) @ s; E FRAME n ; f {{ v, Φ v ∗ ↪[frame]f0 }}).
Proof.
  iIntros (Hnone) "Htrap Hf Hes1 Hcont".
  iApply wp_wasm_empty_ctx_frame.
  iApply (wp_seq_ctx_frame with "[$Htrap $Hf $Hes1 Hcont]").
  { intros LI HLI%lfilled_Ind_Equivalent. inversion HLI. erewrite app_nil_l, app_nil_r. auto. } 
  iIntros (w) "[H1 H2]".
  iApply wp_wasm_empty_ctx_frame.
  iApply ("Hcont" with "[$] [$]").
Qed.

  
End structural_rules.
