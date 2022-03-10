From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_rules iris_wp.
Require Export datatypes host operations properties opsem typing.
Require Export iris_logrel iris_fundamental_helpers.
Import uPred.

Section fundamental.
  Import DummyHosts. (* placeholder *)

  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* ------------------------------------------ CALL --------------------------------------- *)

  Lemma typing_call C i tf : ssrnat.leq (S i) (length (tc_func_t C)) ->
                             nth_error (tc_func_t C) i = Some tf ->
                             ⊢ semantic_typing (HWP:=HWP) C (to_e_list [BI_call i]) tf.
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Hleq Hlookup). destruct tf as [tf1 tf2].
    iIntros (j lh) "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]".
    iIntros (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".

    iDestruct (interp_instance_function_lookup with "Hi") as (func Hfunc) "Hfunc";[eauto..|].
    unfold interp_function.
    iDestruct "Hfunc" as (cl) "[Hfunc Hcl]".
    iDestruct "Hfv" as (locs Hlocs) "[#Hlocs Hown]".

    (* we open the invariant containing the function reference *)
    iApply fupd_wp.
    iMod (na_inv_acc _ ⊤ with "Hfunc Hown") as "(>Ha & Hown & Hcls)";[solve_ndisj..|].
    iModIntro. (* TODO: fix tactic instance for wp mod *)

    iApply wp_wasm_empty_ctx.
    iApply iRewrite_nil_r_ctx;rewrite -app_assoc.
    iApply wp_base_push;[apply const_list_of_val|].
    iApply (wp_wand_ctx _ _ _ (λne (v : leibnizO val), (interp_val tf2 v ∗ na_own logrel_nais ⊤) ∗ ↪[frame]f)%I with "[-]").
    { iApply (wp_call_ctx with "Hf").
      { rewrite Hlocs /= -nth_error_lookup. eauto. }
      iNext. iIntros "Hf".
      iIntros (LI Hfill%lfilled_Ind_Equivalent);inversion Hfill;simplify_eq.
      erewrite app_nil_r.

      destruct cl.
      { (* native function *)
        destruct f.
        iDestruct "Hcl" as (Heq) "Hcl". inversion Heq;subst r r0.
        iDestruct (big_sepL2_length with "Hv") as %Hlen.
        iApply (wp_invoke_native with "[$] [$]");eauto.
        { apply to_val_fmap. }
        iNext. iIntros "[Hf Ha]".
        iApply fupd_wp.
        iMod ("Hcls" with "[$]") as "Hown".
        iModIntro.
        rewrite -wp_frame_rewrite.
        iApply wp_wasm_empty_ctx_frame.
        take_drop_app_rewrite 0.
        iApply (wp_block_local_ctx with "Hf");eauto.
        iNext. iIntros "Hf".
        iApply wp_label_push_nil_local. simpl push_base.
        unfold interp_closure_native.
        erewrite app_nil_l.
        iApply ("Hcl" with "[] Hown Hf").
        iRight. iExists _. eauto.
      }
      { (* host function *)
        destruct f.
        iDestruct "Hcl" as (Heq) "Hcl". inversion Heq;subst r r0.
        iDestruct (big_sepL2_length with "Hv") as %Hlen.
        iApply (wp_invoke_host_success with "[$] [$]");eauto.
        { apply to_val_fmap. }
        { iApply "Hcl". iRight. iExists _. eauto. }
        iNext. iIntros (r) "[Hf [Ha Hpost]]".
        iApply fupd_wp.
        iMod ("Hcls" with "[$]") as "Hown".
        iModIntro.
        destruct (to_val (result_to_stack r)) eqn:Hval;[|done].
        iApply wp_value;[instantiate (1:=v);rewrite /IntoVal /=;erewrite of_to_val;eauto|].
        iFrame.
      }
    }

    iIntros (v) "[[Hw Hown] Hf]".
    iFrame.
    iExists _. iFrame. eauto.
  Qed.
            

End fundamental.
