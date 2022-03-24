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

  Lemma interp_ctx_continuations_push_label_block lh C i tm :
    base_is_empty lh ->
    lholed_lengths (rev (tc_label C)) lh ->
    interp_ctx_continuations (tc_label C) (tc_local C) i lh -∗
    interp_ctx_continuation (tc_label (upd_label C ([tm] ++ tc_label C))) (push_base lh (length tm) [] [] [])
                              0 tm (tc_local C) i.
  Proof.
    iIntros (Hlh_base Hlh_len) "#Hc". unfold interp_ctx_continuation.
    iSimpl. rewrite lh_depth_push_base.
    assert (S (lh_depth lh) - 1 = lh_depth lh) as ->;[lia|].
    rewrite get_layer_push_base_0;[|auto].
    apply lh_minus_push_base_Some with (n:=length tm) (es:=[]) (vs1:=[]) (es2:=[]) in Hlh_base as Hmin.
    iExists _,_,_,_,_,_. repeat (iSplit;[simpl;eauto|]).
    iModIntro. iIntros (v f).
    iIntros "#Hw [Hf Hfv]".
    unfold interp_expression.
    rewrite app_nil_l app_nil_r.

    iDestruct "Hw" as "[-> | Hv]".
    { iExists [].
      take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [Hf]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }

    iDestruct "Hv" as (ws' ->) "Hv". iExists tm.
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    repeat rewrite -!/(interp_frame _ _ _).
    rewrite app_nil_r.
    iApply wp_value;[done|].
    iSplitR;[|iExists _;iFrame;iExists _;eauto].
    iLeft. iRight. iExists _. eauto.
  Qed.

  Lemma interp_ctx_push_label_block C tm i lh :
    interp_ctx (tc_label C) (tc_local C) i lh -∗
    interp_ctx (tc_label (upd_label C ([tm] ++ tc_label C)%list))
      (tc_local (upd_label C ([tm] ++ tc_label C)%list)) i
      (push_base lh (length tm) [] [] []).
  Proof.
    iIntros "[%Hlh_base [%Hlh_len [%Hlh_valid #Hc]]]".
    iSplit;[|iSplit;[|iSplit]].
    { iPureIntro. apply base_is_empty_push_base. }
    { iPureIntro. apply lholed_lengths_push_base. auto. }
    { iPureIntro. apply lholed_valid_push_base. auto. }
    { iSplitR.
      { iSimpl. iSplitR;[|done].
        iApply (interp_ctx_continuations_push_label_block with "[]");auto. }
      iApply (big_sepL_mono with "Hc").
      iIntros (k y Hk). iSimpl.
      iIntros "#Hcont".
      iDestruct "Hcont" as (vs j es0 lh' es' lh'' Hlayer Hdep Hmin) "Hcont".
      iExists vs,j,es0,_,es',lh''.
      rewrite lh_depth_push_base PeanoNat.Nat.sub_succ.
      iSplit.
      { iPureIntro. apply get_layer_push_base;eauto. }
      iSplit;[auto|]. iSplit.
      { iPureIntro. apply push_base_lh_minus_is_Some. auto. }
      iModIntro. iIntros (v f) "#Hv [Hf Hvf]".
      iDestruct ("Hcont" with "Hv [$Hf $Hvf]") as "Hcont'".
      iFrame.
    }
  Qed.

  Lemma interp_br_step C (j : nat) (vh: valid_holed j) m vs p i tm lh f' :
    m = length tm ->
    get_base_l vh = vs ->
    lh_depth (lh_of_vh vh) = p ->
    j = p ->
    interp_br_body (tc_label (upd_label C ([tm] ++ tc_label C)))
                   (push_base lh (length tm) [] [] [])
                   j p vs (tc_local C) i -∗
    ↪[frame]f' -∗
    interp_frame (tc_local C) i f' -∗
    WP [AI_label m [] (vfill vh [AI_basic (BI_br j)])]
      {{ v, (interp_val tm v ∨ interp_br (tc_local C) i v lh (tc_label C)) ∗
           (∃ f0,  ↪[frame]f0 ∗ interp_frame (tc_local C) i f0) }}.
  Proof.
    iIntros (Hlen Hbase Hsize e) "Hbr Hf Hfv".
    unfold interp_br_body.
    destruct (pull_base_l_drop_len vh (length vs - length tm)) eqn:Hpb.
    erewrite vfill_pull_base_l_take_len;[|eauto].
    pose proof (vfill_to_lfilled v (((λ x : value, AI_basic (BI_const x)) <$> l) ++ [AI_basic (BI_br j)])) as [k [Hle Hfill]].
    apply lfilled_depth in Hfill as Hdepth.
    erewrite <-lh_depth_pull_base_l_take_len in Hdepth;[|eauto]. subst k.
    rewrite Hsize -e in Hfill.
    assert (j - p = 0) as ->;[lia|].
    iDestruct "Hbr" as (? ? ? ? ? ? ? ? Hlook Hlayer) "Hbr".
    simpl in Hlook. inversion Hlook;subst τs'.
    iDestruct "Hbr" as (Hdepth Hmin) "[#Hvalvs Hbr]".
    iDestruct "Hvalvs" as "[%|Hvalvs]";[done|].
    iDestruct "Hvalvs" as (ws' Heq') "Hvalvs". inversion Heq';subst ws'.
    iDestruct (big_sepL2_length with "Hvalvs") as %Hlen2.
    rewrite app_length in Hlen2.
        
    iApply (wp_br_alt with "Hf");[..|eauto|].
    { apply const_list_of_val. }
    { rewrite fmap_length. eapply length_pull_base_l_take_len in Hpb;[|eauto]. rewrite Hpb.
      rewrite Hlen.
      assert (length vs >= length tm);[|lia]. rewrite Hlen2. lia. }
    iNext. iIntros "Hf".
    rewrite app_nil_r.
    rewrite of_val_imm.
    iApply wp_value;[done|].
    iSplitR "Hfv Hf";[|iExists _;iFrame;iExists _;eauto].
    iLeft. iRight. iExists _. iSplit;eauto.
    eapply take_drop_pull_base_l_take_len in Hpb as Happ;[|eauto..];[|lia].
    rewrite Happ.
    iDestruct (big_sepL2_app_inv with "Hvalvs") as "[? ?]".
    { right. eapply length_pull_base_l_take_len in Hpb;[|eauto]. rewrite Hpb.
      assert (length vs >= length tm);[|lia]. rewrite Hlen2. lia. }
    iFrame "#".
  Qed.

  (* ----------------------------------------- BLOCK --------------------------------------- *)

  Lemma typing_block C tn tm es : (⊢ semantic_typing (HWP:=HWP) (upd_label C ([tm] ++ tc_label C)%list) (to_e_list es) (Tf tn tm)) ->
                                  ⊢ semantic_typing (HWP:=HWP) C (to_e_list [BI_block (Tf tn tm) es]) (Tf tn tm).
  Proof.
    intros IHbe_typing.
    unfold semantic_typing, interp_expression.
    iIntros (i lh).
    iIntros "#Hi".
    
    iDestruct (IHbe_typing $! i (push_base lh (length tm) [] [] []) with "[]") as "HH"; [by (destruct C,i;eauto)|].

    iIntros "#Hc". iIntros (f vs) "[Hf Hfv] #Hv".
    
    iDestruct "Hv" as "[-> | Hv]".
    {  take_drop_app_rewrite_twice 0 1.
       iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
       { iApply (wp_trap with "[] [Hf]");auto. }
       iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.

    iApply (wp_block with "Hf");eauto.
    { apply v_to_e_is_const_list. }
    { rewrite fmap_length //. }
    iNext. iIntros "Hf".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.

    iAssert (∀ f, interp_frame (tc_local C) i f -∗ ↪[frame] f -∗ WP of_val (immV ws) ++ to_e_list es
              {{ v, (⌜v = trapV⌝ ∨
                       interp_values tm v ∨
                       interp_br (tc_local C) i v _ _)
                      ∗ ∃ f, ↪[frame] f ∗ interp_frame (tc_local C) i f }})%I as "Hcont".
    { iIntros (f') "Hfv Hf".
      iDestruct ("HH" with "[] [Hf Hfv] []") as "Hcont".
      { iApply (interp_ctx_push_label_block with "[$]"). }
      { iFrame "∗ #". }
      { iRight. iExists _. eauto. }
      iApply (wp_wand with "Hcont").
      iIntros (v) "H". rewrite -or_assoc. iFrame. }
    
    iDestruct ("Hcont" $! f with "[$]") as "Hcontf". simpl push_base.
    iApply iRewrite_nil_r_ctx.

    iApply (wp_seq_can_trap_ctx). iFrame.
    iSplitR.
    { iIntros "[Hcontr | Hcontr]";[iDestruct "Hcontr" as (? ?) "_";done|
                                    rewrite fixpoint_interp_br_eq; iDestruct "Hcontr" as (? ? ? ? ?) "_";done]. }
    iSplitR;[by iLeft;iLeft|].

    iIntros (w f') "[Hred [Hf Hfv]]".
    rewrite app_nil_r.
    iDestruct "Hred" as "[#Hval | Hbr]".
    
    { iDestruct "Hval" as (vs ->) "Hval".
      iDestruct (big_sepL2_length with "Hval") as %Hlen'.
      iApply (wp_wand_ctx _ _ _ (λ vs, ⌜vs = immV _⌝ ∗ _)%I with "[Hf]").
      { iApply (wp_val_return with "Hf");[apply const_list_of_val|].
        iIntros "Hf". rewrite app_nil_l app_nil_r.
        iApply wp_value;[done|]. iFrame. eauto. }
      iIntros (v) "[-> Hf]".
      iSplitR;[|iExists _;iFrame;iExists _;eauto].
      iLeft. iRight. iExists _. iSplit;eauto. }

    { rewrite fixpoint_interp_br_eq.
      iDestruct "Hbr" as (j vh vs p -> Hbase Hsize) "Hbr".
      simpl of_val.
      
      assert (LH_rec [] (length tm) [] (LH_base [] []) [] =
                push_base (LH_base [] []) (length tm) [] [] []) as Heq;[auto|].
      rewrite Heq.
      iApply wp_label_push_nil_inv. iApply wp_wasm_empty_ctx.

      destruct (decide (j = p)).
      { iApply (interp_br_step with "Hbr Hf Hfv");eauto. }

      { iAssert (⌜lholed_lengths (rev (tc_label C)) lh⌝ ∧ ⌜lholed_valid lh⌝ ∧ ⌜base_is_empty lh⌝)%I as %[Hlh_length [Hlh_valid Hlh_empty]].
        { iDestruct "Hc" as "[% [% [% _]]]". auto. }
        iApply (interp_br_stuck_push with "Hbr Hf Hfv");eauto. }
    }
  Qed.

End fundamental.
