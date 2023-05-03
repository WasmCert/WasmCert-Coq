From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

Require Export iris_logrel iris_fundamental_helpers.
Import uPred.

Section fundamental.


  Context `{!wasmG Σ, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)
  
  (* ----------------------------------------- GET_GLOBAL ---------------------------------- *)

  Lemma typing_get_global C i t : option_map tg_t (nth_error (tc_global C) i) = Some t ->
                                  ⊢ semantic_typing C (to_e_list [BI_get_global i]) (Tf [] [t]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Hnth j lh hl).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws;[|done].
    rewrite app_nil_l.

    iDestruct (interp_instance_lookup_global with "Hi") as (gt mut n Hnth' Hn Htg) "Hg";[eauto|].

    iAssert (∃ P, □ (∀ w, P t w -∗ interp_value t w)
                    ∗ na_inv logrel_nais (wgN (N.of_nat n))
                    (∃ (w : leibnizO value), (N.of_nat n)↦[wg] (Build_global mut w) ∗ P t w))%I as (P) "[#Hcond #Hginv]".
    { unfold interp_global.
      simplify_eq. iSimpl in "Hg".
      destruct mut.
      { iDestruct "Hg" as (P) "[Hcond Hinv]". iExists P. iFrame "#". }
      { iExists (interp_value). iFrame "Hg".
        iModIntro. auto. } }

    iDestruct "Hfv" as (locs Hlocs) "[#Hlocs Hown]".
    iApply fupd_wp.
    iMod (na_inv_acc with "Hginv Hown") as "(Hn & Hown & Hcls)";[solve_ndisj..|].
    iModIntro.
    iDestruct "Hn" as (w) "[>Hn HP]".

    iApply wp_fupd.
    iApply (wp_wand _ _ _ (λ vs, (⌜vs = immV ([w])⌝
                                   ∗ P t w)
                                   ∗ N.of_nat n↦[wg] Build_global mut w ∗ ↪[frame] f)%I with "[Hf Hn HP]").
    { iApply (wp_get_global with "[HP] Hf Hn");eauto;by rewrite -nth_error_lookup Hlocs /=. }
    iIntros (v) "[[-> HP] [Hn Hf]]".
    iDestruct ("Hcond" with "HP") as "#Hg_val".
    iMod ("Hcls" with "[$Hown Hn HP]") as "Hown".
    { iNext. iExists _. iFrame. }
    iModIntro. iSplitR;[|iExists _;iFrame].
    { iLeft. iRight. iExists _. iSplit =>//.
      iSplit =>//. }
    iExists _. eauto.
  Qed.

End fundamental.
