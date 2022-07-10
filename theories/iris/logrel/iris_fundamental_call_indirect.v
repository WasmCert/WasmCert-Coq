From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_rules.
Require Export datatypes operations properties opsem typing.
Require Export iris_logrel iris_fundamental_helpers.
Import uPred.

Section fundamental.


  Context `{!wasmG Σ, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  Lemma interp_instance_get_table C hl j :
    tc_table C ≠ [] ->
    ⊢ interp_instance C hl j -∗
      ∃ τt a, ⌜(tc_table C) !! 0 = Some τt⌝
            ∗ ⌜(inst_tab j) !! 0 = Some a⌝
            ∗ ∃ table_size, (N.of_nat a) ↪[wtsize] table_size
                          ∗ (interp_table table_size (λ _, interp_closure hl)) (N.of_nat a).
  Proof.
    iIntros (Hnil) "#Hi".
    destruct C,j.
    iDestruct "Hi" as "[_ [_ [Hi _]]]". simpl in Hnil.
    destruct (nth_error tc_table 0) eqn:Ht0;cycle 1.
    { exfalso. rewrite nth_error_lookup in Ht0.
      apply lookup_ge_None_1 in Ht0. apply Hnil.
      destruct tc_table;auto. simpl in Ht0. lia. }
    destruct tc_table, inst_tab;try done.
    iDestruct "Hi" as (table_size table_lim) "[#Hsize [#Hlim Hi]]".
    iExists t, t1. iSimpl.
    iFrame "% #". iSplit;auto.
  Qed.    
  
  Lemma interp_instance_type_lookup C hl i tf j :
    nth_error (tc_types_t C) i = Some tf ->
    ⊢ interp_instance C hl j -∗
      ⌜nth_error (inst_types j) i = Some tf⌝.
  Proof.
    iIntros (Hnth) "#Hi".
    destruct C,j.
    iDestruct "Hi" as "[%Heq _]".
    rewrite Heq. auto.
  Qed.

  (* ------------------------------------ CALL_INDIRECT ------------------------------------ *)

  Lemma typing_call_indirect C i t1s t2s :
    ssrnat.leq (S i) (length (tc_types_t C)) ->
    nth_error (tc_types_t C) i = Some (Tf t1s t2s) ->
    tc_table C ≠ [] ->
    ⊢ semantic_typing C (to_e_list [BI_call_indirect i]) (Tf (t1s ++ [T_i32]) t2s).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Hleq Hnth Htable j lh hl).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".

    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    assert (∃ w ws', ws = ws' ++ [w]) as [w [ws' Heq]].
    { induction ws using rev_ind;eauto. destruct t1s =>//. } subst ws.
    iDestruct (big_sepL2_app_inv with "Hv") as "[Hv' Hw]";[auto|].
    iSimpl. rewrite -v_to_e_cat -app_assoc. iSimpl.
    iSimpl in "Hw". iDestruct "Hw" as "[Hw _]".
    iDestruct "Hw" as (z) "->" .

    iDestruct (interp_instance_get_table with "Hi") as (τt a Hlook1 Hlook2 table_size)
                                                         "[Htsize Ht]";[auto|].
    iDestruct (interp_instance_type_lookup with "Hi") as %Htlook;[apply Hnth|].
    iDestruct "Hfv" as (locs Heq) "[#Hlocs Hown]".

    (* the index may still be out of bounds *)
    destruct (decide (table_size <= (Wasm_int.nat_of_uint i32m z))).
    { iApply (wp_wand with "[-]");cycle 1.
      { iIntros (v) "H". rewrite -or_assoc. iExact "H". }
      iApply wp_val_can_trap_app'. iFrame.
      iSplitR.
      { iModIntro. rewrite fixpoint_interp_br_eq fixpoint_interp_call_host_eq.
        iIntros "[H|[H|[H|H]]]";[iDestruct "H" as (? ?) "_"
                                |iDestruct "H" as (? ? ? ? ?) "_"
                                |iDestruct "H" as (? ? ?) "_"
                                |iDestruct "H" as (? ? ? ? ? ? ?) "[% _]"];try done. }
      iIntros "Hf".
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_call_indirect_failure_outofbounds with "[$] [$]");auto.
        rewrite Heq /= //. }
      iIntros (v) "[-> Hf]". iSplitR;[|iExists _;eauto].
      by iLeft.
    }

    (* otherwise the indirect call is a success, and we must find its function entry in the table interpretation *)
    assert (Wasm_int.nat_of_uint i32m z < table_size) as Hlt;[lia|].
    apply repeat_lookup with 0 _ _ in Hlt.
    iDestruct (big_sepL_lookup with "Ht") as (τf fe) "[Hz Hfe]";[apply Hlt|].

    iApply fupd_wp.
    iMod (na_inv_acc with "[$Hz] [$Hown]") as "(>Ha & Hown & Hcls)";[solve_ndisj..|].
    iModIntro.


    (* if the entry is empty the indirect call traps *)
    destruct (fe);cycle 1.
    { iApply (wp_wand with "[-]");cycle 1.
      { iIntros (v) "H". rewrite -or_assoc. iExact "H". }
      iApply wp_val_can_trap_app'. iFrame.
      iSplitR.
      { iModIntro. rewrite fixpoint_interp_br_eq fixpoint_interp_call_host_eq.
        iIntros "[H|[H|[H|H]]]";[iDestruct "H" as (? ?) "_"
                                |iDestruct "H" as (? ? ? ? ?) "_"
                                |iDestruct "H" as (? ? ?) "_"
                                |iDestruct "H" as (? ? ? ? ? ? ? ?) "_"];try done.
      }
      iIntros "Hf".
      iApply wp_fupd.
      iApply (wp_wand _ _ _ (λ vs, (⌜vs = trapV⌝ ∗ _) ∗  ↪[frame]f)%I with "[Hf Ha]").
      { iApply (wp_call_indirect_failure_noindex with "[$] [$] [-]");auto.
        rewrite Heq /= //. }
      iIntros (v) "[[-> Ha] Hf]".
      iMod ("Hcls" with "[$Hown $Ha]") as "$". iModIntro.
      iSplitR;[|iExists _;eauto].
      by iLeft.
    }

    iDestruct "Hfe" as (cl) "[Hn0 Hcl]".
    iApply fupd_wp.
    iMod (na_inv_acc with "Hn0 Hown") as "(>Hn & Hown & Hcls')";[solve_ndisj| | ].
    { unfold wfN, wtN, wf, wt. solve_ndisj. }
    iModIntro.
    
    (* if the types fail the indirect call traps *)    
    destruct (function_type_eq_dec (cl_type cl) (Tf t1s t2s));cycle 1.
    { iApply (wp_wand with "[-]");cycle 1.
      { iIntros (v) "H". rewrite -or_assoc. iExact "H". }
      iApply wp_val_can_trap_app'. iFrame.
      iSplitR.
      { iModIntro. rewrite fixpoint_interp_br_eq fixpoint_interp_call_host_eq.
        iIntros "[H|[H|[H|H]]]";[iDestruct "H" as (? ?) "_"
                                |iDestruct "H" as (? ? ? ? ?) "_"
                                |iDestruct "H" as (? ? ?) "_"
                                |iDestruct "H" as (? ? ? ? ? ? ? ?) "_"];try done.
      }
      iIntros "Hf".
      iApply wp_fupd.
      iApply (wp_wand _ _ _ (λ vs, (⌜vs = trapV⌝ ∗ _) ∗  ↪[frame]f)%I with "[Hf Ha Hn]").
      { iApply (wp_call_indirect_failure_types with "[$Ha] [$Hn] [-]");auto.
        2: rewrite Heq /= //. rewrite Heq /=.
        rewrite nth_error_lookup in Htlook. rewrite Htlook.
        intros Hcontr;inversion Hcontr. done. }
      iIntros (v) "[[-> [Ha Hn]] Hf]".
      iMod ("Hcls'" with "[$Hown $Hn]") as "Hown".
      iMod ("Hcls" with "[$Hown $Ha]") as "Hown".
      iModIntro.
      iSplitR;[|iExists _;iFrame;eauto].
      by iLeft.
    }
    
    (* otherwise, we reduce the call indirect to the appropriate function invocation *)
    iApply wp_wasm_empty_ctx.
    iApply iRewrite_nil_r_ctx. rewrite -app_assoc.
    iApply wp_base_push;[apply v_to_e_is_const_list|].
    
    iApply iRewrite_nil_r_ctx.
    iApply (wp_wand_ctx _ _ _ (λne (v : leibnizO val), ((interp_val t2s v ∨ interp_call_host (tc_local C) j (tc_return C) hl v lh (tc_label C) t2s) ∗ na_own logrel_nais ⊤) ∗ ↪[frame]f)%I with "[-]").
    { iApply (wp_call_indirect_success_ctx with "[$] [$] [$] [-]");[rewrite Heq /= //..|].
      { rewrite nth_error_lookup in Htlook. rewrite Htlook//. f_equiv. auto. }
      iNext. iIntros "[Ha [Hn Hf]]".
      iIntros (LI Hfill%lfilled_Ind_Equivalent);inversion Hfill;simplify_eq.
      iApply fupd_wp.
      iMod ("Hcls'" with "[$Hown $Hn]") as "Hown".
      iMod ("Hcls" with "[$Hown $Ha]") as "Hown".
      iModIntro.
      erewrite app_nil_r.

      iApply fupd_wp.
      iMod (na_inv_acc _ ⊤ with "Hn0 Hown") as "(>Ha & Hown & Hcls)";[solve_ndisj..|].
      iModIntro.
      
      destruct cl.
      { (* native function *)
        destruct f.
        iDestruct "Hcl" as (Heq) "Hcl". destruct τf;simplify_eq. inversion e;subst r r0.
        iDestruct (big_sepL2_length with "Hv'") as %Hlen'.
        iApply (wp_invoke_native with "[$] [$]");eauto.
        { apply to_val_fmap. }
        iNext. iIntros "[Hf Ha]".
        iApply fupd_wp.
        iMod ("Hcls" with "[$]") as "Hown".
        iModIntro.
        iApply (wp_wand with "[Hf Hown]").
        { iApply wp_wasm_empty_ctx_frame.
          take_drop_app_rewrite 0.
          iApply (wp_block_local_ctx with "Hf");eauto.
          iNext. iIntros "Hf".
          iApply wp_label_push_nil_local. simpl push_base.
          unfold interp_closure_native.
          erewrite app_nil_l.
          iApply ("Hcl" with "[] Hown Hf").
          iRight. iExists _. eauto. }
        iIntros (v) "[[Hw | Hw] [$ $]]".
        { by iLeft. }
        { iRight. iClear "#". iLöb as "IH" forall (v).
          rewrite fixpoint_interp_call_host_cls_eq.
          rewrite fixpoint_interp_call_host_eq.
          iDestruct "Hw" as (? ? ? ? ? ? ? ? ? ?) "[#? #H]".
          iExists _,_,_,_,_,_. repeat (iSplit;[eauto|]).
          iModIntro. iIntros (v2 f) "? [? Hfrv]".
          iDestruct "Hfrv" as (?) "[Hv1 [Hv2 ?]]".
          iDestruct ("H" with "[$] [$] [$]") as "H'".
          iApply (wp_wand with "H'").
          iIntros (w) "[[#Hw | Hw] [? ?]]".
          { iSplitR;[by iLeft|].
            iExists _. iFrame. iExists _. iFrame. }
          { iSplitL "Hw".
            { repeat iRight. iNext.
              iApply "IH". iFrame. }
            iExists _. iFrame. iExists _. iFrame. }          
        }
      }
      { (* host function *)
        destruct f.
        iDestruct "Hcl" as %[Heq HH]. destruct τf;simplify_eq. inversion e;subst r r0.
        iDestruct (big_sepL2_length with "Hv'") as %Hlen'.
        iApply (wp_invoke_host with "[$] [$]");eauto.
        iModIntro.
        iIntros "Ha Hf".
        iApply fupd_wp.
        iMod ("Hcls" with "[$]") as "Hown".
        iModIntro.
        iApply wp_value.
        { instantiate (1:=callHostV _ _ _ _). eapply of_to_val. eauto. }
        iFrame. iRight. iApply fixpoint_interp_call_host_eq.
        iExists _,_,_,_,_,_. do 3 (iSplit;[eauto|]).
        iSplit;[auto|].
        iSplit.
        { iRight. iExists _. eauto. }
        iModIntro. iIntros (v2 f) "#Hv2 [Hf Hfv]".
        simpl llfill. rewrite app_nil_r. iApply wp_value;[done|].
        iSplitR;[|iExists _;iFrame].
        iLeft. done.
      }
    }

    iIntros (v) "[[Hw Hown] Hf]".
    iFrame. iSplitR "Hf".
    { iDestruct "Hw" as "[Hw | Hw]";[by iLeft|by iRight;iRight;iRight]. }
    iExists _. iFrame. eauto.
  Qed.
    
End fundamental.
