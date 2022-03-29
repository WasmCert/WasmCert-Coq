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

  (* ----------------------------------------- SET_LOCAL ----------------------------------- *)

  Lemma typing_set_local C i t : nth_error (tc_local C) i = Some t ->
                                 ⊢ semantic_typing (HWP:=HWP) C (to_e_list [BI_set_local i]) (Tf [t] []).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Hnth j lh).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".

    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws as [|w ws];[done|destruct ws;[|done]].
    iSimpl in "Hv". iDestruct "Hv" as "[Hv _]".
    simpl of_val.

    iDestruct "Hfv" as (locs Heq) "[#Hlocs Hown]".
    iDestruct "Hlocs" as "[%Hcontr | Hlocs]";[done|].
    iDestruct "Hlocs" as (wlocs Heqw) "Hlocs". inversion Heqw.
    rewrite nth_error_lookup in Hnth.
    apply lookup_lt_Some in Hnth as Hlt.
    iDestruct (big_sepL2_length with "Hlocs") as %Hlen'.
    rewrite -Hlen' in Hlt.

    iApply (wp_wand _ _ _ (λ vs, ⌜vs = immV ([])⌝ ∗ ↪[frame] _)%I with "[Hf]").
    { iSimpl. iApply (wp_set_local with "Hf");[subst;eauto|].
      simpl. done. }
    iIntros (v) "[-> Hf]".
    iSplitR;[|iExists _;iFrame].
    { iLeft. iRight. iExists _. iSplit;eauto. }
    iExists _. rewrite Heq //. iSplit =>//. 
    iRight. subst locs. rewrite -fmap_insert_set_nth;[|auto].
    iSimpl. iExists _. iSplit =>//.
    rewrite -(list_insert_id (tc_local C) i t);[|auto].
    iApply big_sepL2_insert;iFrame "#".
    rewrite list_insert_id;auto.
  Qed.
    
End fundamental.
