From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris_wp_def iris_properties iris_rules_trap iris_rules_structural iris_rules_control stdpp_aux.
Require Export datatypes host operations properties opsem.



(* empty lists, frame and context rules *)

Close Scope byte_scope.

Section structural_rules.
Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}.

(* Sequencing rule which is always allowed to trap *)
(* This rule is useful in particular for semantic type soundness, which allows traps *)

Lemma wp_seq_can_trap_ctx (s : stuckness) (E : coPset) (Φ Ψ : iris.val -> iProp Σ) (es1 es2 : language.expr wasm_lang) (i : nat) (lh : lholed) f :
  ((¬ (Ψ trapV)) ∗ (Φ trapV) ∗ ↪[frame] f ∗
  (↪[frame] f -∗ WP es1 @ NotStuck; E {{ w, (⌜w = trapV⌝ ∨ Ψ w) ∗ ∃ f, ↪[frame] f }}) ∗
  ∀ w f, Ψ w ∗ ↪[frame] f -∗ WP (iris.of_val w ++ es2) @ s; E CTX i; lh {{ v, Φ v ∗ ∃ f, ↪[frame] f }})%I
  ⊢ WP (es1 ++ es2) @ s; E CTX i; lh {{ v, Φ v ∗ ∃ f, ↪[frame] f }}.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ i lh f).
{ iIntros "[Hntrap [Ht [Hf [Hes1 Hes2]]]]".
  (* iDestruct (wp_wasm_empty_ctx with "Hes1") as "Hes1". *)
  iIntros (LI Hfilled).
  repeat rewrite wp_unfold /wp_pre /=.
  (* iApply wp_unfold. rewrite /wp_pre /=. *)
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val LI) as [vs|] eqn:Hetov.
  { iApply wp_unfold. rewrite /wp_pre /= Hetov.
    destruct vs.
    { pose proof (filled_is_val_imm _ _ _ _ _ Hetov Hfilled) as
        [vs [es' [-> [-> [Hconst1 Hconst2]]]]].
      apply const_list_is_val in Hconst1 as [v1 Hv1].
      apply const_list_is_val in Hconst2 as [v2 Hv2].
      edestruct fill_val as [vs12 [Hvs12 Heql]];eauto.
      assert (Hvs12':=Hvs12).
      apply to_val_cat in Hvs12' as [-> Hev2].
      apply iris.of_to_val in Hev2 as <-.
      iMod ("Hes1" with "Hf") as "[Hes1 Hf]".
      iDestruct "Hf" as (f') "Hf".
      iSpecialize ("Hes2" with "[Hf Hes1]").
      { iDestruct "Hes1" as "[%Hcontr | Hes1]"; [done|eauto]. iFrame. }
      
      (* iDestruct (wp_unfold with "Hes2") as "Hes2". *)
      (* iMod "Hes2". *)
      unfold iris.of_val.
      rewrite - fmap_app take_drop.
      rewrite of_val_imm.
      pose proof (lfilled_swap (iris.of_val (immV vs12)) Hfilled) as [LI' Hfilled'].
      iSpecialize ("Hes2" $! _ Hfilled').
      iDestruct (wp_unfold with "Hes2") as "Hes2". rewrite /wp_pre /=.
      assert (iris.to_val LI' = Some (immV l)) as ->;[|iFrame].
      apply lfilled_Ind_Equivalent in Hfilled'. inversion Hfilled';subst.
      apply to_val_cat_inv;auto. apply to_val_cat_inv;auto. apply iris.to_of_val.
    }
    { apply to_val_trap_is_singleton in Hetov. subst.
      apply lfilled_Ind_Equivalent in Hfilled.
      inversion Hfilled;subst.
      2: { exfalso. do 2 destruct vs =>//=. }
      apply app_eq_singleton in H as [[HH HH']|[HH HH']];subst.
      { exfalso. destruct es1,es2,es' =>//=. }
      apply app_eq_singleton in HH' as [[HH HH']|[HH HH']];subst.
      { apply app_eq_singleton in HH as [[-> ->]|[-> ->]].
        simpl.
        all: iMod ("Hes1" with "Hf") as "[_ Hf]";iDestruct "Hf" as (f') "Hf".
        all: by iFrame; iExists _; iFrame. }
      { destruct es1,es2 =>//=.
        all: iMod ("Hes1" with "Hf") as "[_ Hf]";iDestruct "Hf" as (f') "Hf".
        all: by iFrame; iExists _; iFrame. }
    }
  }
  {
  (* Ind *)
  (* iIntros (σ ns κ κs nt) "Hσ". *)
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod ("Hes1" with "Hf") as "[Hes1 Hf]".
    iDestruct "Hf" as (f') "Hf".
    iDestruct "Hes1" as "[-> | Hes1]".
    { iPoseProof (wp_trap_ctx s E f' i lh [] es2 with "Hf") as "HH";auto.
      iSpecialize ("HH" $! LI with "[]");auto.
      iApply (wp_wand with "HH").
      iIntros (v) "[-> Hf]". iFrame. iExists _. iFrame. 
    }
    { iApply wp_unfold. rewrite /wp_pre /= Hetov.
      iIntros (σ ns κ κs nt) "Hσ".
      iSpecialize ("Hes2" with "[$]").
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
  }
  { iApply wp_unfold. rewrite /wp_pre /= Hetov.
    iIntros (σ ns κ κs nt) "Hσ".
    iSpecialize ("Hes1" with "[$]").
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
        iIntros "Hf". (* iSpecialize ("Hes''" with "[$]"). *)
        iDestruct ("IH" with "[Hf Ht $Hntrap $Hes'' $Hes2 ]") as "Hcont". iFrame. by iApply "Hcont".
        
      + assert (iris.prim_step es1 σ [] [AI_trap] σ []) as HStep2.
        { unfold iris.prim_step.
          destruct σ as [[[??]?]?].
          repeat split => //.
          apply r_simple; eapply rs_trap => //.
          move => HContra; subst.
          by simpl in Hes.
        }
        iSpecialize ("H2" $! [AI_trap] σ [] HStep2).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        destruct σ as [[[??] ?]?].
        iDestruct "H2" as "[Hσ H]".
        iDestruct "H" as (f') "(Hf1 & Hes'' & Hefs)".
        iModIntro => /=.
        iFrame. iExists _. iFrame.
        iIntros "?"; iSpecialize ("Hes''" with "[$]").
        replace [AI_trap] with (iris.of_val trapV) => //=.
        iDestruct (wp_unfold with "Hes''") as "Hes''".
        rewrite /wp_pre /=. iMod "Hes''" as "[[_ | Hcontr] Hf]".
        2: by iDestruct ("Hntrap" with "Hcontr") as "?".
        iDestruct "Hf" as (f0) "Hf".
        apply lfilled_Ind_Equivalent in Hlf;inversion Hlf;subst.
        assert ((vs ++ [AI_trap] ++ es')%SEQ ++ es2 =
                  (vs ++ [AI_trap] ++ (es' ++ es2)))%list as Hassoc;[repeat erewrite app_assoc;auto|].
        rewrite Hassoc in Hfilled.
        apply lfilled_Ind_Equivalent in Hfilled.
        eapply lfilledInd_frame in Hfilled;auto.
        apply lfilled_Ind_Equivalent in Hfilled.
        destruct HStep' as [HStep' _].
        eapply trap_reduce_lfilled in HStep';eauto.
        destruct HStep' as [lh2 [j [Hlh' Hle]]].
        iPoseProof (wp_trap_ctx s E f0 j _ [] [] with "Hf") as "HH";auto.
        iSpecialize ("HH" $! _ Hlh').
        iApply (wp_wand with "HH").
        iIntros (v) "[-> Hf]". iFrame. iExists _. iFrame. 
  } } }
Qed.
  
End structural_rules.
