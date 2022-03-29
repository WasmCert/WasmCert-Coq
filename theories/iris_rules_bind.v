From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export datatypes host operations properties opsem iris_rules_control iris_properties.
Require Export iris_wp_def stdpp_aux.

(* empty lists, frame and context rules *)

Close Scope byte_scope.

Section bind_rules.
  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}.

  Lemma lfilled_to_sfill i lh es LI :
    lfilled i lh es LI ->
    ∃ sh, LI = sfill sh es.
  Proof.
    revert i es LI.
    induction lh;intros i es LI Hfill%lfilled_Ind_Equivalent.
    { inversion Hfill;simplify_eq.
      apply const_es_exists in H4 as [vs Hvs].
      exists (SH_base vs l0);rewrite Hvs;simpl;auto. }
    { inversion Hfill;simplify_eq.
      apply lfilled_Ind_Equivalent in H8.
      apply IHlh in H8 as [sh Hsh]. simplify_eq.
      apply const_es_exists in H7 as [vs Hvs].
      exists (SH_rec vs n l0 sh l1).
      rewrite Hvs;simpl;auto. }
  Qed.

  Lemma to_val_app_retV v :
  ∀ (s : simple_valid_holed) (es : iris.expr),
    iris.to_val es = Some (retV s)
    → iris.to_val (v_to_e_list v ++ es)%SEQ =
        Some (retV (sh_push_const s v)).
  Proof.
    induction v;intros s es Hes.
    simpl. rewrite sh_push_const_nil;auto.
    simpl.
    apply IHv in Hes.
    rewrite (separate1 a).
    erewrite sh_push_const_app.
    apply to_val_cons_retV with (v:=a) in Hes.
    rewrite Hes. auto.
  Qed.

  Fixpoint sh_pull_const_r sh vs :=
  match sh with
  | SH_base bef aft  => SH_base (bef ++ vs) aft 
  | SH_rec bef n es sh aft => SH_rec bef n es (sh_pull_const_r sh vs) aft
  end.
  
  Lemma sfill_sh_pull_const_r sh :
    ∀ e x, sfill (sh_pull_const_r sh x) e = sfill sh (v_to_e_list x ++ e).
  Proof.
    induction sh;intros e x.
    { cbn. rewrite -to_e_list_fmap. rewrite !fmap_app. repeat rewrite app_assoc. repeat f_equiv. }
    { cbn. rewrite IHsh. auto. }
  Qed.

  Fixpoint lh_pull_const_r lh vs :=
  match lh with
  | LH_base bef aft  => LH_base (bef ++ vs) aft 
  | LH_rec bef n es sh aft => LH_rec bef n es (lh_pull_const_r sh vs) aft
  end.

  Lemma lh_pull_const_r_app i lh x es es1 :
    lfilled i lh (v_to_e_list x ++ es) es1 ->
    ∃ lh', lfilled i lh' es es1.
  Proof.
    revert i es1.
    induction lh;intros i es1 Hfill%lfilled_Ind_Equivalent.
    { inversion Hfill;simplify_eq.
      exists (LH_base (l ++ (v_to_e_list) x) l0).
      apply lfilled_Ind_Equivalent. repeat erewrite app_assoc.
      erewrite <- (app_assoc _ _ l0). constructor.
      apply const_list_app. split;auto. apply v_to_e_is_const_list. }
    { inversion Hfill;simplify_eq. apply lfilled_Ind_Equivalent in H8.
      apply IHlh in H8 as [lh' Hlh'%lfilled_Ind_Equivalent].
      eexists. apply lfilled_Ind_Equivalent.
      constructor;eauto. }
  Qed.
    
  Lemma reduce_det_local hs ws f hs' ws' f' es1 es2 n f0 :
    iris.to_val es1 = None ->
    opsem.reduce (host_instance:=DummyHosts.host_instance) hs ws f [AI_local n f0 es1] hs' ws' f' es2 ->
    ∃ es2' f1, es2 = [AI_local n f1 es2'] ∧ f = f' ∧
                 opsem.reduce (host_instance:=DummyHosts.host_instance) hs ws f0 es1 hs' ws' f1 es2'.
  Proof.
    intros Hes1.
    remember [AI_local n f0 es1] as es.
    revert es2. induction 1;simplify_eq.
    all: try destruct vcs =>//.
    { remember [AI_local n f0 es1] as es.
      revert e' H;induction 1;simplify_eq.
      all: try do 2 destruct vs =>//.
      { apply const_list_to_val in H as [? ?]. congruence. }
      { apply const_es_exists in H as [? ?]. simplify_eq. 
        apply lfilled_to_sfill in H1 as [sh Hsh].
        rewrite -sfill_sh_pull_const_r in Hsh.
        rewrite Hsh in Hes1.
        assert (iris.of_val (retV (sh_pull_const_r sh x)) = es1);[rewrite Hsh;auto|].
        rewrite Hsh in H. rewrite -H in Hes1.
        rewrite to_of_val in Hes1. done. }
      { apply lfilled_Ind_Equivalent in H0. inversion H0. do 2 destruct vs =>//. }
    }
    { apply lfilled_Ind_Equivalent in H0.
      inversion H0;simplify_eq.
      rewrite -(app_nil_l [AI_local n f0 es1]) in H2.
      apply val_head_stuck_reduce in H as Hstuck.
      apply const_list_snoc_eq3 in H2;auto.
      2,4: intros ->;done.
      2: intros [? ?]%const_list_to_val;congruence.
      destruct H2 as [? [? [? [? [? ?]]]]].
      simplify_eq. destruct vs,x,x0,es'0 =>//.
      apply lfilled_Ind_Equivalent in H1.
      inversion H1;simplify_eq. erewrite app_nil_l, app_nil_r.
      apply IHreduce. auto.
      rewrite -(app_nil_l [AI_local n f0 es1]) in H2.
      apply first_values in H2 as [?[? ?]];auto. done. }
    { eauto. }
  Qed.

  Lemma reduce_det_label hs ws f hs' ws' f' es1 es2 n es :
    iris.to_val es1 = None ->
    opsem.reduce (host_instance:=DummyHosts.host_instance) hs ws f [AI_label n es es1] hs' ws' f' es2 ->
    ∃ es2', es2 = [AI_label n es es2'] ∧
              opsem.reduce (host_instance:=DummyHosts.host_instance) hs ws f es1 hs' ws' f' es2'.
  Proof.
    intros Hes1.
    remember [AI_label n es es1] as es''.
    revert es2. induction 1;simplify_eq.
    all: try destruct vcs =>//.
    { remember [AI_label n es es1] as es''.
      revert e' H;induction 1;simplify_eq.
      all: try do 2 destruct vs =>//.
      { apply const_list_to_val in H as [? ?]. congruence. }
      { apply const_es_exists in H as [? ?]. simplify_eq.
        apply lh_pull_const_r_app in H1 as [lh' Hlh'].        
        apply lfilled_to_vfill with (i:=i) in Hlh';[|lia].
        destruct Hlh' as [vh [Heq Hvh]].
        assert (iris.of_val (brV vh) = es1);[auto|].
        rewrite -H in Hes1.
        rewrite to_of_val in Hes1. done. }
      { apply lfilled_Ind_Equivalent in H0. inversion H0. do 2 destruct vs =>//. }
    }
    { apply lfilled_Ind_Equivalent in H0.
      inversion H0;simplify_eq.
      { apply val_head_stuck_reduce in H as Hstuck.
        destruct es0 =>//.
        destruct vs =>//;[|destruct vs =>//].
        destruct es0 =>//.
        destruct es'0 =>//.
        erewrite app_nil_l, app_nil_r in H2. simplify_eq.
        apply lfilled_Ind_Equivalent in H1. inversion H1. simplify_eq.
        erewrite app_nil_l, app_nil_r. eauto. }
      { destruct vs =>//;[|destruct vs =>//].
        destruct es'' =>//.
        erewrite app_nil_l in H2. simplify_eq.
        apply lfilled_Ind_Equivalent in H1. inversion H1. simplify_eq.
        erewrite app_nil_l, app_nil_r.
        exists LI. split;auto.
        apply lfilled_Ind_Equivalent in H7.
        apply lfilled_Ind_Equivalent in H13.
        eapply r_label;eauto. 
      }
    }
  Qed.

  Lemma wp_frame_bind (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) n f f0 LI :
    ↪[frame] f0 -∗
     (↪[frame] f -∗ WP LI @ s; E {{ w, ∃ f, (↪[frame] f0 -∗ WP of_val w @ s; E FRAME n; f {{ w, Φ w }}) ∗ ↪[frame] f }}) -∗
     WP LI @ s; E FRAME n; f {{ w, Φ w }}.
  Proof.
    iIntros "Hframe H".
    rewrite wp_frame_rewrite.
    iLöb as "IH" forall (s E LI f f0).
    (* iApply wp_unfold. *)
    repeat rewrite wp_unfold /wp_pre /=.
    destruct (iris.to_val (LI)) as [vs|] eqn:Hetov.
    { iApply wp_unfold.
      iIntros (σ ns κ κs nt) "Hσ".
      destruct σ as [[[? ?] ?] ?].
      iDestruct "Hσ" as "(H1&H2&H3&H4&Hff&H5&H6)".
      iDestruct (ghost_map_lookup with "Hff Hframe") as %Hlook.
      iMod (ghost_map_update f with "Hff Hframe") as "[Hff Hframe]".
      iMod ("H" with "Hframe") as "Hf".
      iDestruct "Hf" as (f') "[H Hf]".
      rewrite wp_frame_rewrite.
      iDestruct (ghost_map_lookup with "Hff Hf") as %Hlook'.
      iMod (ghost_map_update f0 with "Hff Hf") as "[Hff Hf]".
      rewrite !insert_insert. rewrite lookup_insert in Hlook'. inversion Hlook'.
      iDestruct ("H" with "Hf") as "H".
      iDestruct (wp_unfold with "H") as "H".
      rewrite /wp_pre /=. rewrite lookup_insert in Hlook;inversion Hlook.
      iSpecialize ("H" $! (s0,_,_,_) 0 κ [] 0 with "[$H1 $H2 $H3 $H4 $H5 $H6 $Hff]").
      erewrite of_to_val;[|apply Hetov].
      iMod "H" as "[? H]". iModIntro. iFrame. }
    { iApply wp_unfold.
      iIntros (σ ns κ κs nt) "Hσ".
      destruct σ as [[[? ?] ?] ?].
      iDestruct "Hσ" as "(H1&H2&H3&H4&Hff&H5&H6)".
      iDestruct (ghost_map_lookup with "Hff Hframe") as %Hlook.
      iMod (ghost_map_update f with "Hff Hframe") as "[Hff Hframe]".
      rewrite insert_insert.
      iDestruct ("H" with "Hframe") as "H". destruct f.
      iSpecialize ("H" $! (s0,_,_,_) 0 κ [] 0). 
      iDestruct ("H" with "[$H1 $H2 $H3 $H4 $H5 $H6 $Hff]") as "H".
      rewrite lookup_insert in Hlook;inversion Hlook.

      iMod "H" as "[%Hred H]".
      iModIntro. iSplit.
      { iPureIntro. destruct s =>//.
        destruct Hred as [x [e' [σ' [efs Hstep]]]].
        destruct σ' as [[[? ?] ?] ?].
        eexists x,[AI_local n {| f_locs := l0; f_inst := i0 |} e'],(s,s2,l,i),efs.
        simpl. destruct Hstep as [Hstep [-> ->]]. split;auto.
        apply r_local. eauto. }

      iIntros (e2 σ2 efs Hstep).
      destruct σ2 as [[[? ?] ?] ?].
      destruct Hstep as [Hstep [-> ->]].
      apply reduce_det_local in Hstep as Hstep';[|auto].
      destruct Hstep' as [es2' [f1 [Heq1 [Heq2 Hstep']]]].
      simplify_eq. destruct f1.
      iSpecialize ("H" $! _ (_,_,_,_) _ with "[]").
      { iPureIntro. split;eauto. }

      repeat iMod "H". iModIntro. iNext.
      repeat iMod "H". simpl.
      iDestruct "H" as "[H Hf]".
      iDestruct "Hf" as (f1) "[Hf Hcont]".
      iDestruct "H" as "(H1&H2&H3&H4&Hff&H5&H6)".
      iDestruct (ghost_map_lookup with "Hff Hf") as %Hlook'.
      rewrite lookup_insert in Hlook'. inversion Hlook'.
      iMod (ghost_map_update {| f_locs := l0; f_inst := i0 |} with "Hff Hf") as "[Hff Hframe]".
      rewrite insert_insert.
      simpl. iApply fupd_mask_intro_subseteq;[solve_ndisj|]. iFrame.
      iExists _. iFrame. iSplit =>//. iIntros "Hf".
      iDestruct "Hcont" as "[Hcont _]".
      iApply ("IH" with "Hf Hcont").
    }
  Qed.

  Lemma wp_label_bind (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) e n es :
    WP e @ s; E {{ w, WP of_val w @ s; E CTX 1; LH_rec [] n es (LH_base [] []) [] {{ w, Φ w }} }} -∗
    WP e @ s; E CTX 1; LH_rec [] n es (LH_base [] []) [] {{ w, Φ w }}.
  Proof.
    iIntros "H". iIntros (LI HLI).
    iLöb as "IH" forall (s E e LI HLI).
    (* iApply wp_unfold. *)
    repeat rewrite wp_unfold /wp_pre /=.
    destruct (iris.to_val (LI)) as [vs|] eqn:Hetov.
    { iApply wp_unfold.
      assert (is_Some (iris.to_val LI)) as Hsome;[eauto|].
      eapply lfilled_to_val in Hsome as [v Hv];[|eauto].
      rewrite /wp_pre /= Hetov Hv. erewrite of_to_val;eauto.
      iMod "H". iDestruct ("H" $! _ HLI) as "H".
      iDestruct (wp_unfold with "H") as "H".
      rewrite /wp_pre /= Hetov. done. }
    { iApply wp_unfold. rewrite /wp_pre /= Hetov.
      destruct (iris.to_val e) eqn:Hetov'.
      { erewrite of_to_val;[|eauto].
        iDestruct ("H" $! _ HLI) as "H".
        iIntros (σ ns κ κs nt) "Hσ".
        destruct σ as [[[? ?] ?] ?].
        iMod "H".
        iDestruct (wp_unfold with "H") as "H".
        rewrite /wp_pre /= Hetov.
        iDestruct ("H" $! (s0,_,_,_) 0 _ [] 0 with "Hσ") as "H".
        iFrame. }
      { iIntros (σ ns κ κs nt) "Hσ".
        destruct σ as [[[? ?] ?] ?].
        iDestruct ("H" $! (s0,_,_,_) 0 [] [] 0 with "Hσ") as "H".
        iMod "H" as "[%Hred H]". iModIntro.
        iSplit.
        { iPureIntro.
          destruct s =>//.
          eapply lfilled_reducible;eauto. }
        apply lfilled_Ind_Equivalent in HLI.
        inversion HLI;simplify_eq. inversion H8;simplify_eq.
        repeat erewrite app_nil_l, app_nil_r.
        iIntros (e2 σ2 efs Hprim).
        destruct σ2 as [[[? ?] ?] ?].
        destruct Hprim as [Hprim [-> ->]].
        apply reduce_det_label in Hprim as Hprim';[|auto]. destruct Hprim' as [es2' [-> Hstep]].
        iDestruct ("H" $! _ (_,_,_,_) with "[]") as "H".
        { iPureIntro. split;eauto. }
        iMod "H". iModIntro. iNext.
        repeat iMod "H". iApply fupd_mask_intro_subseteq;[solve_ndisj|].
        iDestruct "H" as "[Hσ H]".
        iFrame. iDestruct "H" as (f) "[Hf [H _]]".
        iExists _. iFrame.
        iSplit =>//. iIntros "Hf".
        iDestruct ("H" with "Hf") as "H".
        iDestruct ("IH" with "[] H") as "H".
        { iPureIntro. apply lfilled_Ind_Equivalent. constructor;auto. constructor;auto. }
        repeat erewrite app_nil_l, app_nil_r.
        iFrame.
      }
    }
  Qed.
  
  
End bind_rules.
