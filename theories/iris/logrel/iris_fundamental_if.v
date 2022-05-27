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
Require Export iris_logrel iris_fundamental_helpers iris_fundamental_block.
Import uPred.

Section fundamental.


  Context `{!wasmG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* ----------------------------------------- IF ------------------------------------------ *)

  Lemma typing_if C tn tm es1 es2 : (⊢ semantic_typing (*HWP:=HWP*) (upd_label C ([tm] ++ tc_label C)%list) (to_e_list es1) (Tf tn tm)) ->
                                    (⊢ semantic_typing (*HWP:=HWP*) (upd_label C ([tm] ++ tc_label C)%list) (to_e_list es2) (Tf tn tm)) ->
                                    ⊢ semantic_typing (*HWP:=HWP*) C (to_e_list [BI_if (Tf tn tm) es1 es2]) (Tf (tn ++ [T_i32]) tm).
  Proof.
    intros IHbe_typing1 IHbe_typing2.
    unfold semantic_typing, interp_expression.
    iIntros (i lh).
    iIntros "#Hi #Hc". iIntros (f vs) "[Hf Hfv] #Hv".
    
    iDestruct "Hv" as "[-> | Hv]".
    {  take_drop_app_rewrite_twice 0 1.
       iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
       { iApply (wp_trap with "[] [Hf]");auto. }
       iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    assert (exists w ws', ws = ws' ++ [w]) as [w [ws' ->]].
    { induction ws using rev_ind;eauto. destruct tn =>//. }
    iDestruct (big_sepL2_app_inv with "Hv") as "[Hws' Hw]";[by right|].
    simpl of_val. rewrite - v_to_e_cat. rewrite -app_assoc.
    iApply iRewrite_nil_r. rewrite -app_assoc.
    iApply wp_wasm_empty_ctx.
    iApply wp_base_push.
    { apply const_list_of_val. }
    iSimpl.
    iSimpl in "Hw". iDestruct "Hw" as "[Hw _]".
    iDestruct "Hw" as (n) "->".
    
    destruct (Wasm_int.Int32.eq_eqP n (Wasm_int.int_zero i32m)).

    { iApply (wp_if_false_ctx with "Hf");[auto|].
      iNext. iIntros "Hf".

      apply typing_block in IHbe_typing2.
      iDestruct (IHbe_typing2 $! i lh with "[]") as "HH2"; [by (destruct C,i;eauto)|].
      iIntros (LI HLI%lfilled_Ind_Equivalent).
      inversion HLI;simplify_eq. erewrite app_nil_r.
      rewrite -/(iris.of_val (immV ws')).
      unfold interp_expression. simpl to_e_list.
      iApply ("HH2" with "[] [Hf Hfv]");iFrame "∗ #".
      iRight. iExists _. iSplit;eauto.
    }
    { iApply (wp_if_true_ctx with "Hf");[auto|].
      iNext. iIntros "Hf".

      apply typing_block in IHbe_typing1.
      iDestruct (IHbe_typing1 $! i lh with "[]") as "HH2"; [by (destruct C,i;eauto)|].
      iIntros (LI HLI%lfilled_Ind_Equivalent).
      inversion HLI;simplify_eq. erewrite app_nil_r.
      rewrite -/(iris.of_val (immV ws')).
      unfold interp_expression. simpl to_e_list.
      iApply ("HH2" with "[] [Hf Hfv]");iFrame "∗ #".
      iRight. iExists _. iSplit;eauto.
    }
  Qed.
    

End fundamental.
