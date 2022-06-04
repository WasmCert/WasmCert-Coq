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


  Context `{!wasmG Σ, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* ----------------------------------------- CONST --------------------------------------- *)
  
  Lemma typing_const C v : ⊢ semantic_typing C (to_e_list [BI_const v]) (Tf [] [typeof v]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (i lh hl).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]".
    iIntros (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    { iDestruct "Hv" as (ws ->) "Hv".
      iDestruct (big_sepL2_nil_inv_r with "Hv") as %->.
      rewrite app_nil_l. iSimpl.
      assert ([AI_basic (BI_const v)] = of_val (immV [v])) as ->;auto.
      iApply wp_value;[done|].
      iSplitR;cycle 1.
      { iExists _. iFrame. }
      iLeft. iRight.
      iExists _. iSplit;eauto.
      iSimpl. iSplit =>//. iApply interp_value_type_of. }
  Qed.

End fundamental.
