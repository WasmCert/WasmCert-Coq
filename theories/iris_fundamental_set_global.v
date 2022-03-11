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

  (* ----------------------------------------- SET_GLOBAL ---------------------------------- *)

  Lemma typing_set_global C i g t : nth_error (tc_global C) i = Some g ->
                              tg_t g = t ->
                              is_mut g ->
                              ⊢ semantic_typing (HWP:=HWP) C (to_e_list [BI_set_global i]) (Tf [t] []).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Hnth Hg Hmut j lh).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws as [|w ws];[done|destruct ws;[|done]].

    iDestruct (interp_instance_lookup_global _ _ i with "Hi") as (gt mut n Hnth' Hn Htg) "Hg".
    { rewrite Hnth. simpl. rewrite Hg. eauto. }
    destruct g.
    simplify_eq. rewrite /is_mut /= in Hmut. revert Hmut. move/eqP =>Hmut.
    subst tg_mut.
    iSimpl in "Hg".

    iApply fupd_wp.
    iDestruct "Hfv" as (locs Hlocs) "[#Hlocs Hown]".
    iMod (na_inv_acc with "Hg Hown") as "(Hn & Hown & Hcls)";[solve_ndisj..|].
    iModIntro.
    iDestruct "Hn" as (g) "[>Hn _]".
    iSimpl.
    
    iApply wp_fupd.
    iApply (wp_wand _ _ _ (λ vs, (⌜vs = immV ([])⌝
                                   ∗ N.of_nat n↦[wg] Build_global (g_mut g) w) ∗ ↪[frame] f)%I with "[Hf Hn]").
    { iApply (wp_set_global with "[] Hf Hn");eauto;by rewrite -nth_error_lookup Hlocs /=. }
    iIntros (v) "[[-> Hn] Hf]".
    iMod ("Hcls" with "[$Hown Hn]") as "Hown".
    { iNext. iExists _. iFrame. iSimpl.
      iSimpl in "Hv". iDestruct "Hv" as "[$ _]". }
    iModIntro. iSplitR;[|iExists _;iFrame].
    { iLeft;iRight. iExists _. iSplit;done. }
    iExists _. eauto.
  Qed.
    
End fundamental.
