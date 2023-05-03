From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

Require Import iris_fundamental_br.
Import uPred.

Section fundamental.


  Context `{!wasmG Σ, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* ----------------------------------------- BR_IF --------------------------------------- *)
  
  Lemma typing_br_if C i ts : ssrnat.leq (S i) (length (tc_label C)) ->
                              plop2 C i ts ->
                              ⊢ semantic_typing C (to_e_list [BI_br_if i]) (Tf (ts ++ [T_i32]) ts).
  Proof.
    iIntros (Hleq Hlookup) "".
    iIntros (j lh hl).
    iIntros "#Hi #Hc" (f vs) "[Hf Hfv] #Hv".
    unfold interp_expression.
    
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [Hf]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    assert (∃ w ws', ws = ws' ++ [w]) as [w [ws' Heq]].
    { induction ws using rev_ind;eauto. destruct ts =>//. } subst ws.
    iDestruct (big_sepL2_app_inv with "Hv") as "[Hv' Hw]";[auto|].
    iSimpl. rewrite -v_to_e_cat -app_assoc. iSimpl.
    iSimpl in "Hw". iDestruct "Hw" as "[Hw _]".
    iDestruct "Hw" as (z) "->" .

    (* first we reduce the br_if either to nil, or to a br instruction *)
    iApply wp_wasm_empty_ctx.
    iApply iRewrite_nil_r_ctx. rewrite -app_assoc.
    iApply wp_base_push;[apply v_to_e_is_const_list|].
    iApply iRewrite_nil_r_ctx.
    iApply (wp_seq_ctx _ _ _ (λne (vs : leibnizO val), ⌜vs = immV [] ∨ vs = brV (VH_base i [] [] : valid_holed i)⌝ ∗ ↪[frame] f)%I).
    iSplitR;[iIntros "[[%Hcontr|%Hcontr] _]"; done|].
    iSplitL "Hf".
    { destruct (Wasm_int.Int32.eq_eqP z (Wasm_int.int_zero i32m)).
      { iApply (wp_br_if_false with "Hf");auto. }
      { iApply (wp_br_if_true with "Hf");auto. iNext. iIntros "Hf".
        iApply wp_value.
        { instantiate (1:=brV (VH_base i [] [])). done. }
        iFrame. iRight. auto. }
    }

    iIntros (w) "[[-> | ->] Hf]".
    { (* if the br does not happen, we return and get the result of type ts *)
      iSimpl. iIntros (LI Hfill%lfilled_Ind_Equivalent);inversion Hfill;simplify_eq.
      repeat erewrite app_nil_r.
      iApply wp_value.
      { instantiate (1:=immV ws'). done. }
      iSplitR;[|iExists _;iFrame].
      iLeft. iRight. iExists _. iSplit;eauto. }

    (* otherwise, we continue as reason about the br as in typing_br *)
    iDestruct (typing_br _ _ [] _ ts with "Hi Hc [$] []") as "Hbr";[eauto..|].
    { rewrite app_nil_l. iRight. iExists _;eauto. }
    unfold interp_expression.
    iIntros (LI Hfill%lfilled_Ind_Equivalent);inversion Hfill;simplify_eq.
    repeat erewrite app_nil_r.
    iApply "Hbr".
  Qed.

End fundamental.
