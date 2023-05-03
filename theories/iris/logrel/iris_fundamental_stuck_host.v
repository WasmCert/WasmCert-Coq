From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

Require Export iris_logrel iris_fundamental_helpers.

Import uPred.

Section fundamental.
  Context `{!wasmG Σ, !logrel_na_invs Σ}.

    
  Lemma typing_local_stuck_host C es τ1 τ2 τs hl :
    (∀ C es τ, be_typing C es τ -> ⊢ semantic_typing C (to_e_list es) τ) ->
    (tc_label C) = [] ∧ (tc_return C) = None ->
    be_typing (upd_local_label_return C (τ1 ++ τs) [τ2] (Some τ2)) es (Tf [] τ2) ->
    ⊢ semantic_typing_local_stuck_host hl C es τs (Tf τ1 τ2).
  Proof.
    intros be_fundamental Hnil Htyping.
    iSplit;[auto|].
    iIntros (i) "#Hi". iIntros (f vs) "Hf Hown #Hv".
    apply be_fundamental in Htyping.
    iDestruct (Htyping) as "Ht".
    iDestruct (interp_instance_change_label [τ2] with "Hi") as "Hi'".
    iDestruct (interp_instance_change_return (Some τ2) with "Hi'") as "Hi''".
    iDestruct (interp_instance_change_local τ1 with "Hi''") as "Hi_final".
    iSpecialize ("Ht" $! _ (LH_rec [] (length τ2) [] (LH_base [] []) []) with "[$Hi_final] []").
    { unfold interp_ctx. iSimpl. repeat (iSplit;[by auto|]).
      iSplit =>//. unfold interp_ctx_continuation.
      iSimpl. iExists _,_,_,_,_,(LH_base [] []). iSplit;[eauto|].
      repeat (iSplit;[by auto|]). iModIntro.
      iIntros (v f') "#Hv' [Hf' Hfv']".
      iExists τ2. rewrite app_nil_l !app_nil_r.
      iApply wp_value;[done|].
      iSplitR;[|iExists _;iFrame].
      iLeft. iFrame "Hv'". }

    destruct (iris.to_val [AI_local (length τ2) {| f_locs := vs; f_inst := i |}
                                    [AI_label (length τ2) [] (to_e_list es)]]) eqn:Hetov.
    { apply to_val_local_inv in Hetov as Heq.
      destruct Heq as [tf [h [w [vh Heq]]]]. subst v.
      apply to_val_call_host_rec_local in Hetov as Heq.
      destruct Heq as [LI [Heq HLI]].
      simpl in Heq. inversion Heq. subst.
      apply to_val_call_host_label_inv in HLI as Heq'.
      destruct Heq' as [vh' [Heq' Hvh']]. subst.
      apply to_es_list_llfill_contr in Hvh'. done.
    }

    unfold interp_expression_closure.
    iApply (wp_wand _ _ _ ((λ vs0,
               (interp_val τ2 vs0
                ∨ interp_call_host_cls hl τ2 vs0) ∗
               ↪[frame]f ∗ na_own logrel_nais ⊤)%I) with "[-]").
    { iApply (wp_frame_bind with "Hf");[auto|].
      iIntros "Hf".
      iApply wp_wasm_empty_ctx.
      iApply wp_label_push_nil.
      iApply wp_label_bind.
      iDestruct ("Ht" $! _ (immV []) with "[$Hf Hown] []") as "Hcont".
      { iExists _. iFrame. iSplit;eauto. }
      { iRight. iExists _. iSplit;eauto. }
      iSimpl in "Hcont". unfold interp_expression.
      iApply (wp_wand with "Hcont").
      iClear "Ht".
      iIntros (v) "[Hv' Hf0]".
      iDestruct "Hf0" as (f0) "[Hf0 Hf0v]".
      iDestruct "Hv'" as "[[-> | Hv'] | [Hbr | [Hret | Hch] ]]";simpl language.of_val.
      { iApply (local_host_trap with "[$] [$]"). }
      { iApply (local_host_val with "[$] [$] [$]"). }
      { iApply (local_host_br with "[$] [$] [$]"). }
      { iApply (local_host_ret with "[$] [$] [$]"). }
      { iApply (local_host_call with "[$] [$] [$]"). }
    }
    iIntros (v) "[$ [$ $]]".
  Qed.
  
End fundamental.
