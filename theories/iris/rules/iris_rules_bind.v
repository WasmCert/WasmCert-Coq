From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export iris_rules_control.


Section bind_rules.
  
Context `{!wasmG Σ}.

  Lemma wp_frame_bind (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) n f f0 LI :
    iris.to_val [AI_local n f LI] = None ->
    ↪[frame] f0 -∗
     (↪[frame] f -∗ WP LI @ s; E {{ w, ∃ f', (↪[frame] f0 -∗ WP of_val w @ s; E FRAME n; f' {{ w, Φ w }}) ∗ ↪[frame] f' }})-∗
     WP LI @ s; E FRAME n; f {{ w, Φ w }}.
  Proof.
    iIntros (Hetov') "Hframe H".
    rewrite wp_frame_rewrite.
    iLöb as "IH" forall (s E LI f f0 Hetov').
    destruct (iris.to_val (LI)) as [vs|] eqn:Hetov.
    { iApply wp_unfold.
      unfold wp_pre. simpl language.to_val. rewrite Hetov'; simpl.
      iIntros (σ ns κ κs nt) "Hσ".
      destruct σ as [[ ? ?] ?].
      iDestruct "Hσ" as "(H1&H2&H3&H4&Hff&H5&H6)".
      iDestruct (ghost_map_lookup with "Hff Hframe") as %Hlook.
      iMod (ghost_map_update f with "Hff Hframe") as "[Hff Hframe]".
      iDestruct ("H" with "Hframe") as "H".
      iDestruct (wp_unfold with "H") as "H".
      rewrite /wp_pre /= Hetov.
      iMod ("H") as "Hf".
      iDestruct "Hf" as (f') "[H Hf]".
      rewrite wp_frame_rewrite.
      iDestruct (ghost_map_lookup with "Hff Hf") as %Hlook'.
      iMod (ghost_map_update f0 with "Hff Hf") as "[Hff Hf]".
      rewrite !insert_insert. rewrite lookup_insert in Hlook'. inversion Hlook'.
      iDestruct ("H" with "Hf") as "H".
      iDestruct (wp_unfold with "H") as "H".
      rewrite /wp_pre /=.
      apply of_to_val in Hetov as Heq. rewrite Heq.
      subst f. rewrite Hetov'.
      rewrite lookup_insert in Hlook;inversion Hlook.
      iSpecialize ("H" $! (_,_,_) 0 κ [] 0 with "[$H1 $H2 $H3 $H4 $H5 $H6 $Hff]").
      iMod "H" as "[? H]". iModIntro. iFrame. }
    { iApply wp_unfold. unfold wp_pre. simpl. rewrite Hetov'.
      iIntros (σ ns κ κs nt) "Hσ".
      destruct σ as [[ ? ?] ?].
      iDestruct "Hσ" as "(H1&H2&H3&H4&Hff&H5&H6)".
      iDestruct (ghost_map_lookup with "Hff Hframe") as %Hlook.
      rewrite lookup_insert in Hlook;inversion Hlook.
      
      iMod (ghost_map_update f with "Hff Hframe") as "[Hff Hframe]".
      rewrite insert_insert.
      iDestruct ("H" with "Hframe") as "H". destruct f.
      iDestruct (wp_unfold with "H") as "H". rewrite /wp_pre /= Hetov.
      iSpecialize ("H" $! (_,_,_) 0 κ [] 0). 
      iDestruct ("H" with "[$H1 $H2 $H3 $H4 $H5 $H6 $Hff]") as "H".

      iMod "H" as "[%Hred H]".
      iModIntro. iSplit.
      { iPureIntro. destruct s =>//.
        destruct Hred as [x [e' [σ' [efs Hstep]]]].
        destruct σ' as [[ ? ?] ?].
        eexists x,[AI_local n {| f_locs := l0; f_inst := i0 |} e'],(_,l,i),efs.
        simpl. destruct Hstep as [Hstep [-> ->]]. split;auto.
        apply r_local. eauto. }

      iIntros (e2 σ2 efs Hstep).
      destruct σ2 as [[ ? ?] ?].
      destruct Hstep as [Hstep [-> ->]].
      apply reduce_det_local in Hstep as Hstep';[|auto].
      destruct Hstep' as [es2' [f1 [Heq1 [Heq2 Hstep']]]].
      simplify_eq. destruct f1.
      iSpecialize ("H" $! _ (_,_,_) _ with "[]").
      { iPureIntro. split;eauto. }

      repeat iMod "H". iModIntro. iNext.
      repeat iMod "H". simpl.
      iDestruct "H" as "[H Hf]".
      iDestruct "Hf" as (f1) "[Hf Hcont]".
      iDestruct "H" as "(H1&H2&H3&H4&Hff&H5&H6)".
      iDestruct (ghost_map_lookup with "Hff Hf") as %Hlook'.
      rewrite lookup_insert in Hlook'. inversion Hlook'.
      iDestruct "Hcont" as "[Hcont _]".
      subst f1.

      destruct (iris.to_val [AI_local n {| f_locs := f_locs0; f_inst := f_inst0 |} es2']) eqn:Hsome.
      { apply to_val_local_inv in Hsome as Hsome'.
        destruct Hsome' as [tf [h [w [vh Heq]]]]. subst v.
        apply to_val_call_host_rec_local in Hsome as Heq.
        destruct Heq as [LI' [Heq HLI]].
        erewrite app_nil_l, app_nil_r in Heq. inversion Heq;subst.
        iDestruct ("Hcont" with "Hf") as "Hcont".
        iDestruct (wp_unfold with "Hcont") as "Hcont".
        rewrite /wp_pre /= HLI.
        iMod "Hcont" as "Hf".
        iDestruct "Hf" as (f) "[Hcont Hf]".
        iFrame.
        iDestruct (ghost_map_lookup with "Hff Hf") as %Hlook2.
        rewrite lookup_insert in Hlook2. inversion Hlook2. simplify_eq.
        iMod (ghost_map_update {| f_locs := l0; f_inst := i0 |} with "Hff Hf") as "[Hff Hframe]".
        rewrite insert_insert. iFrame.

        iApply fupd_mask_intro_subseteq;[solve_ndisj|].
        iExists _. iFrame. iSplit =>//. iIntros "Hf". iApply wp_fupd.
        iApply wp_value;[unfold IntoVal;eapply of_to_val;eauto|].
        iDestruct ("Hcont" with "Hf") as "Hcont".
        iDestruct (wp_unfold with "Hcont") as "Hcont".
        eassert (iris.to_val [AI_local n {| f_locs := f_locs0; f_inst := f_inst0 |}
                                       (iris.of_val (callHostV tf h w vh))]
                = Some (callHostV tf h w (LL_local [] n {| f_locs := f_locs0; f_inst := f_inst0 |} vh []))) as Hetov2.
        { erewrite of_to_val;[|eauto].
          apply to_val_local_add_frame. auto. }
        rewrite /wp_pre /= Hetov2. iFrame. }
      
      iMod (ghost_map_update {| f_locs := l0; f_inst := i0 |} with "Hff Hf") as "[Hff Hframe]".
      rewrite insert_insert.
      simpl. iApply fupd_mask_intro_subseteq;[solve_ndisj|]. iFrame.
      iExists _. iFrame. iSplit =>//. iIntros "Hf".
      iApply ("IH" with "[] Hf Hcont");[auto|..].
    }
  Qed.

  Lemma wp_label_bind (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) e n es l1 l2 :
    WP e @ s; E {{ w, WP of_val w @ s; E CTX 1; LH_rec l1 n es (LH_base [] []) l2 {{ w, Φ w }} }} -∗
    WP e @ s; E CTX 1; LH_rec l1 n es (LH_base [] []) l2 {{ w, Φ w }}.
  Proof.
    iIntros "H". iIntros (LI HLI).
    iLöb as "IH" forall (s E e LI HLI).
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
        destruct σ as [[ ? ?] ?].
        iMod "H".
        iDestruct (wp_unfold with "H") as "H".
        rewrite /wp_pre /= Hetov.
        iDestruct ("H" $! (_,_,_) 0 _ [] 0 with "Hσ") as "H".
        iFrame. }
      { iIntros (σ ns κ κs nt) "Hσ".
        destruct σ as [[ ? ?] ?].
        iDestruct ("H" $! (_,_,_) 0 [] [] 0 with "Hσ") as "H".
        iMod "H" as "[%Hred H]". iModIntro.
        iSplit.
        { iPureIntro.
          destruct s => //.
          eapply lfilled_reducible;eauto. }
        apply lfilled_Ind_Equivalent in HLI.
        inversion HLI;simplify_eq. inversion H8;simplify_eq.
        repeat erewrite app_nil_l, app_nil_r.
        iIntros (e2 σ2 efs Hprim).
        destruct σ2 as [[ ? ?] ?].
        destruct Hprim as [Hprim [-> ->]].
        eapply reduce_det_label in Hprim as Hprim';[|auto..]. destruct Hprim' as [es2' [-> Hstep]].
        iDestruct ("H" $! _ (_,_,_) with "[]") as "H".
        { iPureIntro. split;eauto. }
        iMod "H". iModIntro. iNext.
        repeat iMod "H". iApply fupd_mask_intro_subseteq;[solve_ndisj|].
        iDestruct "H" as "[Hσ H]".
        iFrame. iDestruct "H" as (f) "[Hf [H _]]".
        iExists _. iFrame.
        iSplit => //. iIntros "Hf".
        iDestruct ("H" with "Hf") as "H".
        iDestruct ("IH" with "[] H") as "H".
        { iPureIntro. apply lfilled_Ind_Equivalent. constructor;auto. constructor;auto. }
        repeat erewrite app_nil_l, app_nil_r.
        iFrame.
      }
    }
  Qed.

  Lemma wp_label_bind_inv (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) e n es l1 l2 :
    const_list l1 ->
    WP e @ s; E CTX 1; LH_rec l1 n es (LH_base [] []) l2 {{ w, Φ w }} -∗
    WP e @ s; E {{ w, WP of_val w @ s; E CTX 1; LH_rec l1 n es (LH_base [] []) l2 {{ w, Φ w }} }}.
  Proof.
    iIntros (Hconst) "H".
    iLöb as "IH" forall (s E e).
    eassert (lfilled 1 (LH_rec l1 n es (LH_base [] []) l2) e _) as Hfill.
    { apply lfilled_Ind_Equivalent. constructor;eauto. constructor;eauto. }
    repeat rewrite wp_unfold /wp_pre /=.
    destruct (iris.to_val e) eqn:Hetov.
    { iDestruct ("H" with "[]") as "H".
      { iPureIntro. eauto. }
      iModIntro.
      iIntros (LI HLI%lfilled_Ind_Equivalent).
      inversion HLI;simplify_eq.
      inversion H8;simplify_eq.
      repeat erewrite app_nil_l, app_nil_r.
      erewrite of_to_val;eauto. }
    { iDestruct ("H" with "[]") as "H".
      { iPureIntro. eauto. }
      repeat erewrite app_nil_l, app_nil_r.
      erewrite app_nil_l, app_nil_r in Hfill.
      assert (iris.to_val (l1 ++ [AI_label n es e] ++ l2) = None).
      { eapply to_val_None_lfilled with (k:=1);eauto. }
      iDestruct (wp_unfold with "H") as "H".
      rewrite /wp_pre/= H.
      iIntros (σ ns κ κs nt) "Hσ".
      destruct σ as [[ ? ?] ?].
      iDestruct ("H" $! (_,_,_) 0 [] [] 0 with "Hσ") as "H".
      iMod "H" as "[%Hred H]". iModIntro.
      erewrite (separate1 (AI_label _ _ _)) in Hred.
      iSplit.
      { iPureIntro. destruct s =>//.
        destruct Hred as (?&?&?&?&?).
        destruct x1 as [[ ??]?].
        destruct H0 as [Hred [-> ->]].
        eapply reduce_det_label in Hred as Hred';eauto.
        destruct Hred' as [es2 [Heq Hred']].
        eexists _,_,(_,_,_),_. split;eauto. }
      iIntros (e2 σ2 efs Hprim).
      destruct σ2 as [[ ??]?].
      destruct Hprim as [Hprim [-> ->]].
      iDestruct ("H" $! _ (_,_,_) with "[]") as "H".
      { iPureIntro. split;eauto.
        eapply r_label;eauto.
        apply lfilled_Ind_Equivalent.
        constructor;auto. apply lfilled_Ind_Equivalent.
        cbn. apply/eqP. done. }
      iMod "H". iModIntro. iNext.
      repeat iMod "H". iApply fupd_mask_intro_subseteq;[solve_ndisj|].
      iDestruct "H" as "[Hσ H]". iFrame.
      iDestruct "H" as (a) "[Hf [Ha _]]".
      iExists _. iFrame. iSplit =>//.
      iIntros "H". iDestruct ("Ha" with "H") as "H".
      rewrite app_nil_r.
      iApply "IH".
      iIntros (LI HLI%lfilled_Ind_Equivalent).
      inversion HLI;simplify_eq.
      inversion H9;simplify_eq.
      erewrite app_nil_l, app_nil_r. done.      
    }
  Qed.

  Lemma wp_label_bind_next (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) e n es l1 l2 i lh :
    base_is_empty lh ->
    WP e @ s; E {{ w, WP of_val w @ s; E CTX (S i); LH_rec l1 n es lh l2 {{ w, Φ w }} }} -∗
    WP e @ s; E CTX (S i); LH_rec l1 n es lh l2 {{ w, Φ w }}.
  Proof.
    iInduction (lh) as [|l1' m es' lh l2'] "IH" forall (i Φ e l1 l2 n es).
    { iIntros (Hbase) "He".
      inversion Hbase;subst.
      destruct i;[|iIntros (LI HLI%lfilled_Ind_Equivalent);inversion HLI;inversion H8].
      iApply wp_label_bind. eauto. }
    { iIntros (Hbase) "He". iIntros (LI HLI).
      apply lfilled_flatten in HLI as HLI'.
      destruct HLI' as [LI' [Hfill1 Hfill2]].
      iApply (wp_label_bind with "[He]");eauto.
      apply lfilled_Ind_Equivalent in Hfill2.
      inversion Hfill2;simplify_eq.
      inversion H8;simplify_eq.
      apply lfilled_Ind_Equivalent in Hfill1.
      inversion Hfill1;simplify_eq.
      iApply ("IH" with "[] [He]");auto;cycle 1.
      { iPureIntro. apply lfilled_Ind_Equivalent.
        constructor;eauto. }
      iApply (wp_wand with "He").
      iIntros (v) "He".
      iIntros (LI0 HLI0%lfilled_Ind_Equivalent).
      inversion HLI0;simplify_eq.
      iDestruct ("He" with "[]") as "He".
      { iPureIntro. apply lfilled_Ind_Equivalent. constructor;eauto. }
      iApply wp_label_bind_inv;auto.
      iIntros (LI' HLI'%lfilled_Ind_Equivalent).
      inversion HLI';simplify_eq.
      inversion H15;simplify_eq.
      erewrite app_nil_l,app_nil_r. eauto. }
  Qed.
  
  Lemma wp_ctx_bind (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) e i lh :
    base_is_empty lh ->
    WP e @ s; E {{ w, WP of_val w @ s; E CTX i; lh {{ w, Φ w }} }} -∗
    WP e @ s; E CTX i; lh {{ w, Φ w }}.
  Proof.
    iIntros (Hbase) "He".
    iInduction (lh) as [] "IH" forall (i Φ).
    { iIntros (LI Hfill%lfilled_Ind_Equivalent).
      inversion Hfill;simplify_eq.
      inversion Hbase;simplify_eq.
      erewrite app_nil_r, app_nil_l.
      iApply wp_fupd.
      iApply (wp_wand with "He").
      iIntros (v) "Hv".
      iSpecialize ("Hv" $! (of_val v) with "[]");[iPureIntro;cbn;apply/eqP;by rewrite app_nil_r|].
      iDestruct (wp_unfold with "Hv") as "Hv".
      rewrite /wp_pre/=. rewrite to_of_val. done. }
    { simpl in Hbase.
      iSpecialize ("IH" $! Hbase).
      destruct i.
      { iIntros (LI HLI%lfilled_Ind_Equivalent);inversion HLI;inversion H8. }
      iApply wp_label_bind_next;eauto. }
  Qed.


    
End bind_rules.
