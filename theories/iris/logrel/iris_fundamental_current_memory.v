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

  Context `{!wasmG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* --------------------------------- CURRENT_MEMORY -------------------------------------- *)

  Lemma typing_current_memory C : tc_memory C ≠ [] ->
                                  ⊢ semantic_typing (HWP:=HWP) C (to_e_list [BI_current_memory]) (Tf [] [T_i32]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Hnil i lh).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".

    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws;[|done]. rewrite app_nil_l.

    iDestruct (interp_instance_get_mem with "Hi") as (τm mem Hlook1 Hlook2) "[_ #Hm]";auto.
    rewrite nth_error_lookup in Hlook1.
    rewrite nth_error_lookup in Hlook2.
    iApply fupd_wp.
    iDestruct "Hfv" as (locs Hlocs) "[#Hlocs Hown]".
    iMod (na_inv_acc with "Hm Hown") as "(Hms & Hown & Hcls)";[solve_ndisj..|].
    iDestruct "Hms" as (ms) ">Hmemblock".
    iDestruct "Hmemblock" as "[Hmem Hsize]".
    iModIntro.

    iApply wp_fupd.
    iApply (wp_wand _ _ _ (λ vs, (⌜vs = immV _⌝ ∗ _) ∗ _)%I with "[Hsize Hf]").
    { iApply (wp_current_memory with "[$Hf $Hsize]");auto. by rewrite Hlocs /=. }
    iIntros (v) "[[-> Hsize] Hf]".
    iMod ("Hcls" with "[Hsize Hmem $Hown]") as "Hown".
    { iNext. iExists _; iFrame. }
    iModIntro.
    iSplitR;[|iExists _;iFrame;iExists _;eauto].
    iLeft. iRight. iExists _. iSplit;eauto.
    iSimpl. iSplit =>//. iExists _;eauto.
  Qed.

End fundamental.
