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
Require Import iris_fundamental_br.
Import uPred.

Section fundamental.


  Context `{!wasmG Σ, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* ----------------------------------------- BR_TABLE ------------------------------------ *)

  Lemma typing_br_table C i t1s ts t2s ins :
    all (λ i : nat, ssrnat.leq (S i) (length (tc_label C)) && plop2 C i ts) (ins ++ [i])%list ->
    ⊢ semantic_typing C (to_e_list [BI_br_table ins i]) (Tf (t1s ++ ts ++ [T_i32]) t2s).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Hall j lh hl).
    iIntros "#Hi #Hc" (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".

    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    assert (∃ w ws', ws = ws' ++ [w]) as [w [ws' Heq]].
    { induction ws using rev_ind;eauto. destruct t1s, ts =>//. } subst ws.
    rewrite (app_assoc t1s ts).
    iDestruct (big_sepL2_app_inv with "Hv") as "[Hv' Hw]";[auto|].
    iDestruct (big_sepL2_app_inv_r with "Hv'") as (ws1 ws2 Heqw) "[Hv1 Hv2]".
    iSimpl. rewrite -v_to_e_cat -app_assoc -app_assoc. iSimpl.
    iSimpl in "Hw". iDestruct "Hw" as "[Hw _]".
    iDestruct "Hw" as (z) "->" .

    (* first we reduce the br_if either to nil, or to a br instruction *)
    iApply wp_wasm_empty_ctx.
    iApply iRewrite_nil_r_ctx. rewrite -app_assoc.
    iApply wp_base_push;[apply v_to_e_is_const_list|].
    iApply iRewrite_nil_r_ctx.
    
    iApply (wp_seq_ctx _ _ _ (λne (vs : leibnizO val), ⌜(∃ i', nth_error ins (Wasm_int.nat_of_uint i32m z) = Some i' ∧ vs = brV (VH_base i' [] [])) ∨ (nth_error (ins ++ [i]) (length ins) = Some i ∧ vs = brV (VH_base i [] []))⌝ ∗ ↪[frame] f)%I).
    iSplitR;[iIntros "[[%Hcontr|%Hcontr] _]"|].
    { destruct Hcontr as (?&?&?). done. }
    { destruct Hcontr as (?&?);done. }
    iSplitL "Hf".
    { destruct (ssrnat.leq (length ins) (Wasm_int.nat_of_uint i32m z)) eqn:Hle.
      { iApply (wp_br_table_length with "Hf");auto.
        iNext. iIntros "Hf".
        iApply wp_value.
        { instantiate (1:=brV (VH_base i [] [])). done. }
        iFrame. iRight. iPureIntro;split; auto.
        rewrite nth_error_app2;[|lia].
        rewrite PeanoNat.Nat.sub_diag. auto. }
      { revert Hle. move/ssrnat.leP=>Hle.
        assert (Wasm_int.nat_of_uint i32m z < length ins) as Hi';[lia|].
        apply lookup_lt_is_Some_2 in Hi' as [i' Hi'].
        rewrite -nth_error_lookup in Hi'.
        iApply (wp_br_table with "Hf");eauto.
        { apply/ssrnat.leP. apply Nat.lt_nge in Hle. apply lt_le_S. auto. }
        iNext. iIntros "Hf".
        iApply wp_value.
        { instantiate (1:=brV (VH_base i' [] [])). done. }
        iFrame. iLeft. iExists i'. eauto. }
    }

    iIntros (w) "[[%Hi' | [%Hi ->]] Hf]".
    { (* the br targets i' *)
      destruct Hi' as [i' [Hi' ->]].
      eapply all_projection in Hall;cycle 1.
      { rewrite nth_error_app1;eauto.
        rewrite nth_error_lookup in Hi'.
        apply lookup_lt_is_Some_1;eauto. }
      revert Hall. move/andP=>[Hle Hplop].

      iDestruct (typing_br _ _ t1s _ t2s with "Hi Hc [$] []") as "Hbr";[eauto..|].
      { iRight. iExists _;eauto. }
      unfold interp_expression.
      iIntros (LI Hfill%lfilled_Ind_Equivalent);inversion Hfill;simplify_eq.
      repeat erewrite app_nil_r. iSimpl.
      rewrite of_val_imm.
      iApply "Hbr". }

    { (* the br targets i *)
      eapply all_projection in Hall;eauto.
      revert Hall. move/andP=>[Hle Hplop].
      
      iDestruct (typing_br _ _ t1s _ t2s with "Hi Hc [$] []") as "Hbr";[eauto..|].
      { iRight. iExists _;eauto. }
      unfold interp_expression.
      iIntros (LI Hfill%lfilled_Ind_Equivalent);inversion Hfill;simplify_eq.
      repeat erewrite app_nil_r. iSimpl.
      rewrite of_val_imm.
      iApply "Hbr". }
  Qed.
    

End fundamental.
