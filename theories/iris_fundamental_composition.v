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

  Lemma get_base_l_append {i : nat} (lh : valid_holed i) e :
    get_base_l (vh_append lh e) = get_base_l lh.
  Proof.
    induction lh;simpl;auto.
  Qed.

  Lemma append_lh_depth {i : nat} (lh : valid_holed i) e :
    lh_depth (lh_of_vh lh) = lh_depth (lh_of_vh (vh_append lh e)).
  Proof.
    induction lh;simpl;auto.
  Qed.

  Lemma simple_get_base_l_append (lh : simple_valid_holed) e :
    simple_get_base_l (sh_append lh e) = simple_get_base_l lh.
  Proof.
    induction lh;simpl;auto.
  Qed.
  
  (* -------------------------------------- COMPOSITION ------------------------------------ *)

  Lemma typing_composition C es t1s t2s t3s e : (⊢ semantic_typing (HWP:=HWP) C (to_e_list es) (Tf t1s t2s)) ->
                               (⊢ semantic_typing (HWP:=HWP) C (to_e_list [e]) (Tf t2s t3s)) ->
                               ⊢ semantic_typing (HWP:=HWP) C (to_e_list (es ++ [e])%list) (Tf t1s t3s).
  Proof.
    iIntros (Ht1 Ht2).
    unfold semantic_typing, interp_expression.
    iIntros (i lh).
    iIntros "#Hi #Hc" (f vs) "[Hf Hfv] #Hv". 
    
    iAssert (↪[frame] f -∗
             WP of_val vs ++ to_e_list es
             {{ vs1, (⌜vs1 = trapV⌝ ∨ interp_values t2s vs1 ∨ interp_br (tc_local C) i (tc_return C) vs1 lh (tc_label C)
                      ∨ interp_return_option (tc_return C) (tc_local C) i vs1) ∗
                     (∃ f1,  ↪[frame]f1 ∗ interp_frame (tc_local C) i f1) }})%I with "[Hfv]" as "H1".
    { iIntros "Hf".
      iDestruct (Ht1 with "Hi Hc [$] Hv") as "H1".
      iApply (wp_wand with "H1").
      unfold interp_val. iIntros (v). rewrite -or_assoc. auto. }

    iApply wp_wasm_empty_ctx.
    rewrite to_e_list_cat app_assoc.
    iApply (wp_seq_can_trap_ctx).
    iFrame "∗ #".
    iSplitR.
    { rewrite fixpoint_interp_br_eq.
      iIntros "[Hcontr|[Hcontr|Hcontr]]";[iDestruct "Hcontr" as (? ?) "?"|
                                  iDestruct "Hcontr" as (? ? ? ? ?) "?"|iDestruct "Hcontr" as (? ? ?) "?"];try done. }
    iSplitR.
    { iLeft. by iLeft. }

    iIntros (w f') "[Hw [Hf Hfv]]".
    iDestruct "Hw" as "[#Hw|[Hbr|Hret]]".
    { iIntros (LI Hfill%lfilled_Ind_Equivalent);inversion Hfill;simplify_eq.
      erewrite app_nil_l, app_nil_r.
      iApply (Ht2 with "[] [] [$]");iFrame "#". }

    { iIntros (LI Hfill%lfilled_Ind_Equivalent);inversion Hfill;simplify_eq.
      erewrite app_nil_l, app_nil_r.
      rewrite fixpoint_interp_br_eq.
      iDestruct "Hbr" as (j lh' vs' p -> Hbase Hdepth) "Hbr".
      rewrite of_val_br_app_r.
      iApply wp_value;[done|].
      iSplitR "Hf Hfv";[|iExists _;iFrame].
      iRight. iLeft.
      iApply fixpoint_interp_br_eq.
      iExists _,_,_,_. iSplit;[eauto|].
      iFrame. rewrite get_base_l_append -append_lh_depth. auto. }
    { iIntros (LI Hfill%lfilled_Ind_Equivalent);inversion Hfill;simplify_eq.
      erewrite app_nil_l, app_nil_r.
      iDestruct "Hret" as (sh vs' -> Hbase) "Hret".
      destruct (tc_return C);[|done].
      rewrite of_val_ret_app_r.
      iApply wp_value;[done|].
      iSplitR "Hf Hfv";[|iExists _;iFrame].
      iRight. iRight.
      iExists _,_. iSplit;[eauto|].
      rewrite simple_get_base_l_append.
      iSplit;eauto.

      pose proof (sfill_to_lfilled (sh_append sh (to_e_list [e])) ([AI_basic BI_return])) as [j Hj].
      pose proof (sfill_to_lfilled sh ([AI_basic BI_return])) as [j' Hj'].

      iDestruct "Hret" as (?) "[#Hw Hret]".
      iDestruct "Hw" as "[%Hcontr|Hw]";[done|iDestruct "Hw" as (? Heq) "Hw"].
      inversion Heq; subst vs'.
      
      eapply (lfilled_simple_get_base_pull _ _ _ _ (take (length τs'') ws) (drop (length τs'') ws)) in Hj as Hj2.
      2: rewrite simple_get_base_l_append;rewrite take_drop;eauto.
      eapply (lfilled_simple_get_base_pull _ _ _ _ (take (length τs'') ws) (drop (length τs'') ws)) in Hj' as Hj3.
      2: rewrite take_drop;eauto.
      destruct Hj2 as [lh' Hlh'].
      destruct Hj3 as [lh'' Hlh''].

      
      iDestruct (big_sepL2_length with "Hw") as %Hlen.
      iExists _. iSplitR;[iRight;iExists _;iSplit;eauto;rewrite H0;eauto|].
      iIntros (f0 f1) "[Hf Hfv]". iSpecialize ("Hret" $! f0 with "[$]").
      iApply (wp_ret_shift with "Hret");[| |apply Hlh''|apply Hlh'].
      { apply const_list_of_val. }
      { rewrite fmap_length. rewrite drop_length.
        rewrite app_length in Hlen. apply Nat.add_sub_eq_r. rewrite Hlen. lia. }
    }
  Qed.

End fundamental.
