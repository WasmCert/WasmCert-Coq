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

  (* ----------------------------------------- GET_LOCAL ----------------------------------- *)

  Lemma typing_get_local C i t : nth_error (tc_local C) i = Some t ->
                                 ⊢ semantic_typing C (to_e_list [BI_get_local i]) (Tf [] [t]).
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
    simpl of_val. rewrite app_nil_l.

    iDestruct "Hfv" as (locs Heq) "[#Hlocs Hown]".
    iDestruct "Hlocs" as "[%Hcontr | Hlocs]";[done|].
    iDestruct "Hlocs" as (wlocs Heqw) "Hlocs". inversion Heqw.
    rewrite nth_error_lookup in Hnth.
    apply lookup_lt_Some in Hnth as Hlt.
    iDestruct (big_sepL2_length with "Hlocs") as %Hlen'.
    rewrite -Hlen' in Hlt.
    apply lookup_lt_is_Some_2 in Hlt as [w Hw].
    iDestruct (big_sepL2_lookup with "Hlocs") as "Hw";[eauto..|].
    
    iApply (wp_wand _ _ _ (λ vs, ⌜vs = immV ([w])⌝ ∗ ↪[frame] f)%I with "[Hf]").
    { iApply (wp_get_local with "[] [$Hf]");[subst;eauto|].
      simpl. done. }
    iIntros (v) "[-> Hf]".
    iSplitR;[|iExists _;iFrame].
    { iLeft. iRight. iExists _. iSplit;eauto.
      iSplit;[|done]. eauto. }
    iExists locs. iSplit =>//.
    iRight. iExists _. eauto.
  Qed.

    
End fundamental.
