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

  (* ----------------------------------------- TESTOP -------------------------------------- *)

  Lemma typing_testop C t op : is_int_t t -> ⊢ semantic_typing C (to_e_list [BI_testop t op]) (Tf [t] [T_i32]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Hisint i lh hl).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws as [|w1 ws];[done|destruct ws;[|done]].
    iSimpl in "Hv".
    iDestruct "Hv" as "[Hv1 _]".
    iSimpl.

    destruct t;try done.

    { iDestruct "Hv1" as (z) "->".
      iApply (wp_wand _ _ _ (λne v, interp_val [T_i32] v ∗ ↪[frame] f)%I with "[Hf]").
      { iApply (wp_testop_i32 with "Hf []");eauto.
        iSimpl. iRight. iExists _. iSplit;eauto.
        iNext. iSplit;[|done].
        iExists _. eauto. }
      iIntros (v) "[H Hf]".
      iFrame. iExists _;iFrame. }
    
    { iDestruct "Hv1" as (z) "->".
      iApply (wp_wand _ _ _ (λne v, interp_val [T_i32] v ∗ ↪[frame] f)%I with "[Hf]").
      { iApply (wp_testop_i64 with "Hf []");eauto.
        iSimpl. iRight. iExists _. iSplit;eauto. iNext.
        iSplit;[|done].
        iExists _. eauto. }
      iIntros (v) "[H Hf]".
      iFrame. iExists _;iFrame. }
  Qed.

End fundamental.
