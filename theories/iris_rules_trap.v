From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export datatypes host operations properties opsem.
Require Export iris_wp_def stdpp_aux.



(* empty lists, frame and context rules *)

Close Scope byte_scope.

Section trap_rules.
  Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}.

  Let val := iris.val.
  Let expr := iris.expr.
  Let to_val := iris.to_val.

  Lemma wp_trap (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (vs1 es2 : expr) f :
    const_list vs1 ->
    Φ trapV -∗
    ↪[frame] f -∗
    WP vs1 ++ [AI_trap] ++ es2 @ s; E {{ v, Φ v ∗ ↪[frame] f }}.
  Proof.
    iLöb as "IH" forall (s E vs1 es2 f). 
    iIntros (Hconst) "HΦ Hf".
    destruct (iris.to_val (vs1 ++ [AI_trap] ++ es2)) eqn:Hsome.
    { destruct vs1,es2 =>//;[|by erewrite to_val_not_trap_interweave in Hsome;auto..].
      rewrite app_nil_l app_nil_r.
      iApply wp_value;[|iFrame]. done. }
    iApply wp_unfold.
    repeat rewrite /wp_pre /=.
    rewrite Hsome.
    iIntros (σ ns κ κs nt) "Hσ".
    iApply fupd_frame_l.
    iSplit.
    { iPureIntro.
      destruct s =>//.
      unfold iris_wp_def.reducible, reducible.
      eexists _,[AI_trap],σ,_.
      destruct σ as [[[? ?]?]?]. simpl.
      repeat split;eauto.
      eapply r_simple,rs_trap.
      2: instantiate (1 := LH_base vs1 es2);apply lfilled_Ind_Equivalent;by constructor.
      destruct vs1,es2 =>//; destruct vs1 =>//. }
    { iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls".
      iIntros (e2 σ2 efs Hstep).
      iModIntro. iNext. iModIntro.
      iMod "Hcls". iModIntro.
      assert (lfilled 0 (LH_base vs1 es2) [AI_trap] (vs1 ++ (AI_trap :: es2))) as Hfill.
      { apply lfilled_Ind_Equivalent. constructor. done. }
      destruct σ as [[[? ?]?]?].
      destruct σ2 as [[[? ?]?]?].
      simpl in *. destruct Hstep as [Hstep [-> ->]].
      eapply trap_reduce in Hstep as Hred;[|apply Hfill].
      destruct Hred as [lh' [Hfill' Heq]]. simplify_eq.
      iApply bi.sep_exist_l. iExists _. iFrame. iSplit =>//.
      iIntros "Hf".
      apply lfilled_Ind_Equivalent in Hfill';inversion Hfill';subst.
      iApply ("IH" with "[] HΦ Hf"). auto.
    }
  Qed.
  

  Lemma wp_seq_trap (s : stuckness) (E : coPset) (es1 es2 : language.expr wasm_lang) f f' :
    ↪[frame] f ∗
     (↪[frame] f -∗ WP es1 @ s; E {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }})
     ⊢ WP (es1 ++ es2) @ s; E {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }}.
  Proof.
    iIntros "[Hf Hes1]".
    iLöb as "IH" forall (s E es1 es2 f f').
    iApply wp_unfold.
    repeat rewrite wp_unfold /wp_pre /=.
    destruct (iris.to_val (es1 ++ es2)) as [vs|] eqn:Hetov.
    {
      destruct vs.
      {
        apply to_val_cat in Hetov as [-> Hev2].
        apply iris.of_to_val in Hev2 as <-.
        iMod ("Hes1" with "Hf") as "[%Hcontr _]". done.
      }
      {
        apply to_val_trap_is_singleton in Hetov.
        apply app_eq_singleton in Hetov as [[-> ->]|[-> ->]].
        all:iMod ("Hes1" with "Hf") as "[%Hcontr Hf]"; try done. auto.
      }
    }
    (* Ind *)
    iIntros (σ ns κ κs nt) "Hσ".
    destruct (iris.to_val es1) as [vs|] eqn:Hes.
    { apply of_to_val in Hes as <-.
    iMod ("Hes1" with "Hf") as "[%Heq Hf]". subst.
    iApply fupd_frame_l.
    iSplit.
    { iPureIntro.
      destruct s =>//.
      unfold iris_wp_def.reducible, reducible.
      eexists _,[AI_trap],σ,_.
      destruct σ as [[[? ?]?]?]. simpl.
      repeat split;eauto.
      eapply r_simple,rs_trap.
      2: instantiate (1 := LH_base [] es2);apply lfilled_Ind_Equivalent;by constructor.
      destruct es2 =>//. }
    { iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls".
      iIntros (e2 σ2 efs Hstep).
      iModIntro. iNext. iModIntro.
      iMod "Hcls". iModIntro.
      assert (lfilled 0 (LH_base [] es2) [AI_trap] (of_val trapV ++ es2)) as Hfill.
      { apply lfilled_Ind_Equivalent. constructor. done. }
      destruct σ as [[[? ?]?]?].
      destruct σ2 as [[[? ?]?]?].
      simpl in *. destruct Hstep as [Hstep [-> ->]].
      eapply trap_reduce in Hstep as Hred;[|apply Hfill].
      destruct Hred as [lh' [Hfill' Heq]]. simplify_eq.
      apply lfilled_Ind_Equivalent in Hfill'. inversion Hfill';subst.
      iApply bi.sep_exist_l. iExists _. iFrame. iSplit =>//.
      iIntros "Hf". erewrite app_assoc.
      iApply ("IH" with "[$Hf]").
      iIntros "Hf".
      iApply wp_trap;eauto. }
  }
  { destruct σ as [[[? ?]?]?].
    set (σ:=(s0,s1,l,i)).
    iDestruct "Hσ" as "(?&?&?&?&Hfr&?)".
    iDestruct (ghost_map_lookup with "Hfr Hf") as %Heq1.
    iSpecialize ("Hes1" with "[$]").
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
        destruct σ2 as [[[??] ?]?].
        iDestruct "H2" as "[Hσ H]".
        iDestruct "H" as (f1) "(Hf1 & Hes'' & Hefs)".
        iExists f1.
        iFrame. (* iSplit =>//. *)
        iIntros "?".
        iSpecialize ("IH" with "[$]").
        iApply "IH". eauto.
      + move/lfilledP in Hlf1.
        inversion Hlf1; subst; clear Hlf1.
        assert (iris.prim_step es1 σ [] [AI_trap] σ []) as HStep2.
        { unfold iris.prim_step.
          destruct σ as [[[??]?]?].
          repeat split => //.
          apply r_simple; eapply rs_trap => //.
          move => HContra; subst.
          by destruct n.
        }
        iSpecialize ("H2" $! [AI_trap] σ [] HStep2).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        destruct σ as [[[??] ?]?].
        iDestruct "H2" as "[Hσ H]".
        iDestruct "H" as (f1) "(Hf1 & Hes'' & Hefs)".
        iApply bi.sep_exist_l.  iExists f1.
        iDestruct "Hσ" as "(?&?&?&?&Hfr&?)".
        iDestruct (ghost_map_lookup with "Hfr Hf1") as %Heq.
        iDestruct ("Hes''" with "Hf1") as "Hes''".
        rewrite wp_unfold /wp_pre /=.
        iMod "Hes''" as "[_ Hf1]".
        iDestruct (ghost_map_lookup with "Hfr Hf1") as %Heq'.
        simplify_map_eq.
        (* iModIntro. *)
        iFrame. (* iApply fupd_frame_r. iSplit =>//. *)
        iModIntro. iIntros "Hf".
        erewrite cons_middle.
        erewrite app_assoc.
        iApply ("IH" with "[$Hf]").
        iIntros "Hf".
        iApply wp_trap;auto. }
  Qed.

  
End trap_rules.
