From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_rules.
Require Export datatypes host operations properties opsem typing.
Require Export iris_logrel iris_fundamental_helpers.
Import uPred.

Section fundamental.
  Import DummyHosts. (* placeholder *)

  Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* ------------------------------------------ BR ----------------------------------------- *)
  
  Lemma typing_br C i t1s ts t2s : ssrnat.leq (S i) (length (tc_label C)) ->
                                   plop2 C i ts ->
                                   ⊢ semantic_typing (HWP:=HWP) C (to_e_list [BI_br i]) (Tf (t1s ++ ts) t2s).
  Proof.
    iIntros (Hleq Hlookup) "".
    iIntros (j lh).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hc]]]" (f vs) "[Hf Hfv] #Hv".
    unfold interp_expression.
    apply lholed_lengths_length_depth in Hlh_len as Hleneq.
    
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [Hf]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.

    iSimpl.
    rewrite /plop2 nth_error_lookup in Hlookup.
    assert (tc_label C !! i = Some ts) as Hlook;[|clear Hlookup].
    { revert Hlookup. by move/eqP. }
    iApply iRewrite_nil_r. erewrite <- app_assoc.
    pose proof (to_val_br_eq ws i []) as Hval.
    apply of_to_val in Hval.
    iApply wp_value;[done|].
    iSplitR;[|iExists _;iFrame].
    iRight. iApply fixpoint_interp_br_eq. iExists _,_,_. iSplit;[eauto|].
    iDestruct (big_sepL_lookup with "Hc") as (vs n es lh' es' lh'' Hlayer Hdep Hmin) "Hbr";[apply Hlook|].
    rewrite app_length in Hlen.
    apply list_app_split in Hlen as [ws1 [ws2 [-> [Hlen1 Hlen2]]]].
    apply get_layer_lh_depth in Hlayer as Heq;cycle 1.
    { rewrite -(lholed_lengths_length_depth (rev (tc_label C)))//.
      rewrite rev_length. apply lookup_lt_is_Some_1. eauto. }
    eapply get_layer_lookup_lh_lengths in Hlayer as Hn;[|eauto..].
    iExists ts, vs, n, es, lh', es', lh'',t1s.
    repeat (iSplitR;[auto|]).
    { iRight. iExists _. iFrame "Hv". eauto. }
    iIntros (f0) "[Hf0 Hf0v]".
    rewrite Heq.
    iApply (iris_rules_control.wp_br_ctx with "Hf0").
    { apply v_to_e_is_const_list. }
    { rewrite fmap_length. rewrite -Hlen1 drop_app. simplify_eq;auto. }
    iNext. iIntros "Hf". rewrite -Hlen1 drop_app.

    unfold interp_expression.
    iDestruct (big_sepL2_app_inv with "Hv") as "[Hv1 Hv2]";[auto|].
    iDestruct ("Hbr" with "[] [Hf Hf0v]") as (τs2) "Hcont".
    { iRight. iExists _. iFrame "Hv2". auto. }
    { iFrame. }
    rewrite !app_assoc. iFrame.
    iApply (wp_wand with "Hcont").
    { iIntros (v) "[[H|H] $]";[auto|].
      iRight. iNext. iFrame. }
  Qed.

End fundamental.
