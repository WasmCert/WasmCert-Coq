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


  Context `{!wasmG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* ----------------------------------------- RETURN -------------------------------------- *)

  Lemma typing_return C ts t1s t2s : tc_return C = Some ts ->
                                     ⊢ semantic_typing (*HWP:=HWP*) C (to_e_list [BI_return]) (Tf (t1s ++ ts) t2s).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Hsome).
    iIntros (i lh).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".

    assert (of_val (immV ws) = v_to_e_list ws) as ->;[auto|].
    iApply iRewrite_nil_r.
    iApply wp_value.
    { unfold IntoVal.
      simpl language.of_val. erewrite of_to_val. 2: apply to_val_ret_eq.
      rewrite app_assoc. auto. }

    iSplitR;[|iExists _;iFrame;iExists _;eauto].
    iRight. iRight.
    unfold interp_return_option.
    iSimpl.
    iExists _,ws. iSplit;[eauto|]. iSplit;[eauto|].
    rewrite Hsome.
    iExists t1s. iSplit.
    { iRight. iExists _. iSplit;eauto. }
    iIntros (f0 f1) "[Hf Hfv]".

    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    rewrite app_length in Hlen.
    rewrite -(take_drop (length t1s) ws).
    iDestruct (big_sepL2_app_inv with "Hv") as "[Hws1 Hws2]".
    { right. rewrite drop_length. lia. }
    iDestruct (big_sepL2_length with "Hws2") as %Hlen'.

    iApply (wp_wand _ _ _ (λ vs, ⌜vs = immV (drop (length t1s) ws)⌝ ∗ _)%I with "[Hf]").
    { iApply (wp_return with "[Hf]");[..|iFrame];cycle 3.
      { iApply wp_value. 2:eauto. done. }
      { simpl. apply to_val_fmap. }
      { simpl. rewrite fmap_length. auto. }
      { simpl. rewrite - v_to_e_cat. rewrite <- app_assoc.
        instantiate (2:=0). instantiate (1:= LH_base ((λ x : value, AI_basic (BI_const x)) <$> take (length t1s) ws) []).
        unfold lfilled. simpl. rewrite const_list_of_val.
        apply/eqP. simpl. rewrite app_nil_r. auto. }
    }
    iIntros (v) "[-> Hf]".
    iSplitR;[|iExists _;iFrame;iExists _;eauto].
    iRight. iExists _. iSplit;eauto.
  Qed.

End fundamental.
