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
Require Export iris_logrel.
Import uPred.

Section fundamental.
  Import DummyHosts. (* placeholder *)

  Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* ------------------------------ HELPER TACTICS AND LEMMAS ------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)
  
  Ltac take_drop_app_rewrite n :=
    match goal with
    | |- context [ WP ?e @ _; _ CTX _; _ {{ _ }} %I ] =>
        rewrite -(list.take_drop n e);simpl take; simpl drop
    | |- context [ WP ?e @ _; _ {{ _ }} %I ] =>
        rewrite -(list.take_drop n e);simpl take; simpl drop
    | |- context [ WP ?e @ _; _ FRAME _; _ CTX _; _  {{ _, _ }} %I ] =>
        rewrite -(list.take_drop n e);simpl take; simpl drop
    | |- context [ WP ?e @ _; _ FRAME _; _ {{ _ }} %I ] =>
        rewrite -(list.take_drop n e);simpl take; simpl drop
    end.
  
  Ltac take_drop_app_rewrite_twice n m :=
    take_drop_app_rewrite n;
    match goal with
    | |- context [ WP _ ++ ?e @ _; _ CTX _; _ {{ _ }} %I ] =>
        rewrite -(list.take_drop (length e - m) e);simpl take; simpl drop
    | |- context [ WP _ ++ ?e @ _; _ {{ _ }} %I ] =>
        rewrite -(list.take_drop (length e - m) e);simpl take; simpl drop
    end.
  (* Helper lemmas and tactics for necessary list manipulations for expressions *)
  Lemma iRewrite_nil_l (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (e : iris.expr) :
    (WP [] ++ e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Φ }}).
  Proof. rewrite app_nil_l. auto. Qed.
  Lemma iRewrite_nil_r (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (e : iris.expr) :
    (WP e ++ [] @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Φ }}).
  Proof. rewrite app_nil_r. auto. Qed.
  Lemma iRewrite_nil_l_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (e : iris.expr) i lh :
    (WP [] ++ e @ s; E CTX i; lh {{ Φ }} ⊢ WP e @ s; E CTX i; lh {{ Φ }}).
  Proof. rewrite app_nil_l. auto. Qed.
  Lemma iRewrite_nil_r_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (e : iris.expr) i lh :
    (WP e ++ [] @ s; E CTX i; lh {{ Φ }} ⊢ WP e @ s; E CTX i; lh {{ Φ }}).
  Proof. rewrite app_nil_r. auto. Qed.

  Lemma wp_wand_ctx s E e Φ Ψ i lh :
    WP e @ s; E CTX i; lh {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E CTX i; lh {{ Ψ }}.
  Proof.
    iIntros "Hwp H". iIntros (LI HLI).
    iSpecialize ("Hwp" $! LI HLI).
    iApply (wp_wand with "Hwp"). auto.
  Qed.

  Lemma interp_value_type_of v : (⊢ interp_value (Σ:=Σ) (typeof v) v)%I.
  Proof.
    unfold interp_value.
    destruct v;simpl;eauto.
  Qed.

  Lemma const_list_of_val vs :
    const_list (of_val (immV vs)).
  Proof.
    induction vs;auto. Qed.




  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  Lemma typing_const C v : ⊢ semantic_typing (HWP:=HWP) C (to_e_list [BI_const v]) (Tf [] [typeof v]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (i lh f vs).
    iIntros "#Hi [%Hlh_base [%Hlh_len #Hcont]] #Hv".
    iExists (LH_base [] []). iSplit;auto.
    iIntros "Hf".
    iApply wp_wasm_empty_ctx.
    iDestruct "Hf" as (locs Heq) "[#Hlocs Hf]".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand_r _ _ _ (λ vs, interp_val [typeof v] vs ∗  ↪[frame]f)%I). iSplitL.
      { iApply (wp_trap with "[] [$]");auto. by iLeft. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame. }
    { iDestruct "Hv" as (ws ->) "Hv".
      iDestruct (big_sepL2_nil_inv_r with "Hv") as %->.
      iApply (wp_wand_r _ _ _ (λ vs, interp_val [typeof v] vs ∗  ↪[frame]f)%I). iSplitL.
      { rewrite app_nil_l.
        iApply wp_value;[by instantiate (1:= immV [_])|].
        iFrame. iRight. iExists _. iSplit;eauto.
        iSimpl; iSplit =>//. iApply interp_value_type_of. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame. 
    }
  Qed.

  Lemma lh_depth_push_base lh n es es1 vs2 :
    lh_depth (push_base lh n es es1 vs2) = S (lh_depth lh).
  Proof.
    induction lh;simpl;auto.
  Qed.

  Lemma get_layer_push_base lh k vs j es0 lh' es' vs' es es1 es0' :
    get_layer lh k = Some (vs, j, es0, lh', es') ->
    get_layer (push_base lh vs' es es1 es0') k = Some (vs, j, es0, (push_base lh' vs' es es1 es0'), es').
  Proof.
    revert lh. induction k;intros lh Hlayer.
    { destruct lh;[done|]. simpl in Hlayer. simplify_eq. auto. }
    { destruct lh;[done|]. simpl in Hlayer. apply IHk in Hlayer.
      simpl. auto. }
  Qed.

  Lemma interp_ctx_push_label C tm i lh tn ws es :
    interp_ctx (tc_label C) tm (tc_local C) i lh -∗
    interp_ctx (tc_label (upd_label C ([tn] ++ tc_label C)%list)) tm
      (tc_local (upd_label C ([tn] ++ tc_label C)%list)) i
      (push_base lh (length (of_val (immV ws))) [AI_basic (BI_loop (Tf tn tm) es)] [] []).
  Proof.
    iIntros "[%Hlh_base [%Hlh_len #Hc]]".
    iSplit;[|iSplit].
    { admit. }
    { admit. }
    { iSplitR.
      { admit. }
      iApply (big_sepL_mono with "Hc").
      iIntros (k y Hk). iSimpl.
      iIntros "#Hcont".
      iDestruct "Hcont" as (vs j es0 lh' es' Hlayer) "Hcont".
      iExists vs,j,es0,_,es'.
      rewrite lh_depth_push_base PeanoNat.Nat.sub_succ.
      iSplit.
      { iPureIntro. apply get_layer_push_base;eauto. }
      iModIntro. iIntros (v f lh'' [Hdep Hmin]) "#Hv Hf".
      iDestruct "Hf" as (locs Heq) "[#Hlocs Hf]".
      rewrite PeanoNat.Nat.sub_succ in Hdep.
      iApply ("Hcont" with "[] Hv [Hf]").
      { iPureIntro. split;auto. admit. }
      iExists _. iFrame. eauto.
    }
  Admitted.

      
    
  Lemma typing_loop C es tn tm : (⊢ semantic_typing (HWP:=HWP) (upd_label C ([tn] ++ tc_label C)%list) (to_e_list es) (Tf tn tm)) ->
                                 ⊢ semantic_typing (HWP:=HWP) C (to_e_list [BI_loop (Tf tn tm) es]) (Tf tn tm).
  Proof.
    intros IHbe_typing.
    unfold semantic_typing, interp_expression.
    iIntros (i lh f vs).
    iIntros "#Hi #Hc #Hv".
    
    iDestruct "Hv" as "[-> | Hv]".
    { iExists (LH_base [] []). iSplit;auto.
      iIntros "Hf".
      iApply wp_wasm_empty_ctx.
      iDestruct "Hf" as (locs Heq) "[#Hlocs Hf]". 
      take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand_r _ _ _ (λ vs, interp_val tm vs ∗  ↪[frame]f)%I). iSplitL.
      { iApply (wp_trap with "[] [$]");auto. by iLeft. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame. }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    
    iDestruct (IHbe_typing with "[] [] []") as (lh') "[%Hlh' HH]";try by (destruct C,i;eauto).
    { instantiate (1:=push_base lh (length (of_val (immV ws))) [AI_basic (BI_loop (Tf tn tm) es)] [] []).
      iApply interp_ctx_push_label. iFrame "Hc".}
    { instantiate (1:=immV ws). iRight. eauto. }

    destruct Hlh' as [-> | ->].

    { iExists lh. iSplit;auto.
      iIntros "Hf".
      iDestruct "Hf" as (locs Heq) "[#Hlocs Hf]".
      iAssert (↪[frame]f -∗ WP of_val (immV ws) ++ to_e_list es CTX S (lh_depth lh);
               push_base lh (length (of_val (immV ws))) [AI_basic (BI_loop (Tf tn tm) es)] [] []
                {{ vs, interp_val tm vs ∗ (∃ f0 : leibnizO frame,  ↪[frame]f0) }})%I as "Hcontlh'".
      { iIntros "Hf". unfold interp_expression. rewrite lh_depth_push_base. iApply ("HH"). iFrame. iExists _. eauto. }
      iApply (wp_loop_ctx with "Hf");eauto.
      { apply v_to_e_is_const_list. }
      { rewrite fmap_length //. }
      iNext. iIntros "Hf".
      iApply wp_label_push_nil. iApply "Hcontlh'". iFrame. }

    { iExists (LH_base [] []). iSplit;auto.
      iIntros "Hf".
      iDestruct "Hf" as (locs Heq) "[#Hlocs Hf]".
      iAssert (↪[frame]f -∗ WP of_val (immV ws) ++ to_e_list es
                {{ vs, interp_val tm vs ∗ (∃ f0 : leibnizO frame,  ↪[frame]f0) }})%I as "Hcontlh'".
      { iIntros "Hf". unfold interp_expression. iApply wp_wasm_empty_ctx. iApply "HH". iFrame. iExists _. eauto. }
      iSimpl.
      iApply wp_wasm_empty_ctx.
      iApply (wp_loop with "Hf");eauto.
      { apply v_to_e_is_const_list. }
      { rewrite fmap_length //. }
      iNext. iIntros "Hf".
      iApply wp_wasm_empty_ctx.
      iApply wp_label_push_nil.
      iApply iRewrite_nil_r_ctx.
      iApply wp_seq_can_trap_ctx. iFrame "∗ #". 
      iSplitR.
      { iIntros "Hcontr". simpl.
        iDestruct "Hcontr" as (ws0 Hcontr) "_". done. }
      iSplitR.
      { iLeft. auto. }
      iIntros (w f0) "Hres".
      iDestruct "Hres" as "[Hw Hf]".
      iDestruct "Hw" as (vs ->) "Hvs".
      rewrite app_nil_r. simpl push_base.
      iApply (wp_wand_ctx with "[-]").
      { iApply (wp_val_return with "Hf").
        { apply const_list_of_val. }
        iIntros "Hf". iFrame.
        instantiate (1:=interp_val tm).
        iApply wp_value;[by rewrite app_nil_l app_nil_r|iRight;eauto]. }
      { iIntros (v) "[Hw Hf]". iFrame. eauto. } }
  Qed.
    
  (* --------------------------------------------------------------------------------------- *)
  (* ------------------------------- FTLR: simple typing ----------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)
  
  Theorem be_fundamental C es τ : be_typing C es τ -> ⊢ semantic_typing (HWP:=HWP) C (to_e_list es) τ.
  Proof.
    induction 1.
    { apply typing_const. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { by apply typing_loop. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
  Admitted.

End fundamental.
