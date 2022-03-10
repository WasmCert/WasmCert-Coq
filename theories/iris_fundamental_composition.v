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

  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* -------------------------------------- COMPOSITION ------------------------------------ *)

  Lemma typing_composition C es t1s t2s t3s e : (⊢ semantic_typing (HWP:=HWP) C (to_e_list es) (Tf t1s t2s)) ->
                               (⊢ semantic_typing (HWP:=HWP) C (to_e_list [e]) (Tf t2s t3s)) ->
                               ⊢ semantic_typing (HWP:=HWP) C (to_e_list (es ++ [e])%list) (Tf t1s t3s).
  Proof.
    iIntros (Ht1 Ht2).
    unfold semantic_typing, interp_expression.
    iIntros (i lh).
    iIntros "#Hi #Hc" (f vs) "[Hf Hfv] #Hv". 
    
    iAssert (↪[frame] f -∗
             WP of_val vs ++ to_e_list es
             {{ vs1, (⌜vs1 = trapV⌝ ∨ interp_values t2s vs1 ∨ interp_br (tc_local C) i vs1 lh (tc_label C)) ∗
                     (∃ f1,  ↪[frame]f1 ∗ interp_frame (tc_local C) i f1) }})%I with "[Hfv]" as "H1".
    { iIntros "Hf".
      iDestruct (Ht1 with "Hi Hc [$] Hv") as "H1".
      iApply (wp_wand with "H1").
      unfold interp_val. iIntros (v). rewrite -or_assoc. auto. }

    iApply wp_wasm_empty_ctx.
    rewrite to_e_list_cat app_assoc.
    iApply (wp_seq_can_trap_ctx).
    iFrame "∗ #".
    iSplitR.
    { rewrite fixpoint_interp_br_eq.
      iIntros "[Hcontr|Hcontr]";[iDestruct "Hcontr" as (? ?) "?"|
                                  iDestruct "Hcontr" as (? ? ? ?) "?"];try done. }
    iSplitR.
    { iLeft. by iLeft. }

    iIntros (w f') "[Hw [Hf Hfv]]".
    iDestruct "Hw" as "[#Hw|Hbr]".
    { iIntros (LI Hfill%lfilled_Ind_Equivalent);inversion Hfill;simplify_eq.
      erewrite app_nil_l, app_nil_r.
      iApply (Ht2 with "[] [] [$]");iFrame "#". }

    iIntros (LI Hfill%lfilled_Ind_Equivalent);inversion Hfill;simplify_eq.
    erewrite app_nil_l, app_nil_r.
    rewrite fixpoint_interp_br_eq.
    iDestruct "Hbr" as (j vs' es' ->) "Hbr".
    assert (of_val (brV j vs' es') ++ to_e_list [e] =
              of_val (brV j vs' (es' ++ to_e_list [e]))) as ->.
    { simpl. repeat erewrite <- app_assoc. f_equiv. auto. }
    iApply wp_value;[done|].
    iSplitR "Hf Hfv";[|iExists _;iFrame].
    iRight.
    iApply fixpoint_interp_br_eq.
    iExists _,_,_. iSplit;[eauto|].
    iFrame.
  Qed.

End fundamental.
