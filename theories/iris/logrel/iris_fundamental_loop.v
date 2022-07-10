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

  (* ----------------------------------------- LOOP ---------------------------------------- *)

  Lemma interp_ctx_continuations_push_label_loop lh C i tm tn es tr hl :
    base_is_empty lh ->
    lholed_lengths (rev (tc_label C)) lh ->
    □ (∀ (a : leibnizO frame) (a0 : seq.seq (leibnizO value)),
           ⌜length a0 = length tn⌝
           →  ↪[frame]a -∗
               interp_frame (tc_local C) i a -∗
             □ ([∗ list] w;τ ∈ a0;tn, interp_value τ w) -∗
             WP of_val (immV a0) ++ to_e_list [BI_loop (Tf tn tm) es]
             {{ vs,
                (interp_val tm vs
                 ∨ interp_br (tc_local C) i tr hl vs lh (tc_label C)
                 ∨ interp_return_option tr (tc_local C) i vs
                 ∨ interp_call_host (tc_local C) i tr hl vs lh (tc_label C) tm) ∗
                (∃ f0 : leibnizO frame,  ↪[frame]f0 ∗
                   interp_frame (tc_local C) i f0) }}) -∗
      interp_ctx_continuations (tc_label C) tr hl (tc_local C) i lh -∗
      interp_ctx_continuation (tc_label (upd_label C ([tn] ++ tc_label C))) tr hl (push_base lh (length tn) [AI_basic (BI_loop (Tf tn tm) es)] [] [])
                              0 tn (tc_local C) i.
  Proof.
    iIntros (Hlh_base Hlh_len) "#HIH #Hc". unfold interp_ctx_continuation.
    iSimpl. rewrite lh_depth_push_base.
    assert (S (lh_depth lh) - 1 = lh_depth lh) as ->;[lia|].
    rewrite get_layer_push_base_0;[|auto].
    apply lh_minus_push_base_Some with (n:=length tn) (es:=[AI_basic (BI_loop (Tf tn tm) es)]) (vs1:=[]) (es2:=[]) in Hlh_base as Hmin.
    iExists _,_,_,_,_,_. repeat (iSplit;[eauto|]).
    iModIntro. iIntros (v f).
    iIntros "#Hw [Hf Hfv]".
    unfold interp_expression.
    rewrite app_nil_l app_nil_r.

    iDestruct "Hw" as "[-> | Hv]".
    { iClear "HIH". iExists [].
      take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [Hf]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }

    iDestruct "Hv" as (ws' ->) "Hv". iExists tm.
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    repeat rewrite -!/(interp_frame _ _ _).
    iApply ("HIH" with "[] Hf Hfv Hv");eauto. 
  Qed.

  Lemma interp_ctx_push_label_loop C tm i lh tn es tr hl :
    □ (∀ (a : leibnizO frame) (a0 : seq.seq (leibnizO value)),
           ⌜length a0 = length tn⌝
           →  ↪[frame]a -∗
               interp_frame (tc_local C) i a -∗
             □ ([∗ list] w;τ ∈ a0;tn, interp_value τ w) -∗
             WP of_val (immV a0) ++ to_e_list [BI_loop (Tf tn tm) es]
             {{ vs,
                (interp_val tm vs
                 ∨ interp_br (tc_local C) i tr hl vs lh (tc_label C)
                 ∨ interp_return_option tr (tc_local C) i vs
                 ∨ interp_call_host (tc_local C) i tr hl vs lh (tc_label C) tm) ∗
                (∃ f0 : leibnizO frame,  ↪[frame]f0 ∗
                   interp_frame (tc_local C) i f0) }}) -∗
    interp_ctx (tc_label C) tr hl (tc_local C) i lh -∗
    interp_ctx (tc_label (upd_label C ([tn] ++ tc_label C)%list))
      tr hl (tc_local (upd_label C ([tn] ++ tc_label C)%list)) i
      (push_base lh (length tn) [AI_basic (BI_loop (Tf tn tm) es)] [] []).
  Proof.
    iIntros "#HIH [%Hlh_base [%Hlh_len [%Hlh_valid #Hc]]]".
    iSplit;[|iSplit;[|iSplit]].
    { iPureIntro. apply base_is_empty_push_base. }
    { iPureIntro. apply lholed_lengths_push_base. auto. }
    { iPureIntro. apply lholed_valid_push_base. auto. }
    { iSplitR.
      { iSimpl. iSplitR;[|done].
        iApply (interp_ctx_continuations_push_label_loop with "[] []");auto. }
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

  Lemma interp_br_step C (j : nat) (vh: valid_holed j) m vs tn p i es tm lh f' tr hl :
    m = length tn ->
    get_base_l vh = vs ->
    lh_depth (lh_of_vh vh) = p ->
    j = p ->
    □ (∀ a a0, ⌜length a0 = length tn⌝ →
               ↪[frame]a -∗ interp_frame (tc_local C) i a -∗
             □ ([∗ list] w;τ ∈ a0;tn, interp_value τ w) -∗
             WP ((λ v : value, AI_basic (BI_const v)) <$> a0) ++
                to_e_list [BI_loop (Tf tn tm) es]
             {{ vs0,
                (interp_val tm vs0
                 ∨ interp_br (tc_local C) i tr hl vs0 lh (tc_label C)
                 ∨ interp_return_option tr (tc_local C) i vs0
                 ∨ interp_call_host (tc_local C) i tr hl vs0 lh (tc_label C) tm) ∗
                (∃ f0 : leibnizO frame,  ↪[frame]f0 ∗
                                          interp_frame (tc_local C) i f0) }}) -∗
      ▷ interp_br_body (tc_label (upd_label C ([tn] ++ tc_label C)))
                     (push_base lh (length tn) [AI_basic (BI_loop (Tf tn tm) es)] [] [])
                     j p vs (tc_local C) i tr hl -∗
      ↪[frame]f' -∗
      interp_frame (tc_local C) i f' -∗
      WP [AI_label m [AI_basic (BI_loop (Tf tn tm) es)]
        (vfill vh [AI_basic (BI_br j)])]
      {{ v, (interp_val tm v
             ∨ interp_br (tc_local C) i tr hl v lh (tc_label C)
             ∨ interp_return_option tr (tc_local C) i v
             ∨ interp_call_host (tc_local C) i tr hl v lh (tc_label C) tm) ∗
           (∃ f0,  ↪[frame]f0 ∗ interp_frame (tc_local C) i f0) }}.
  Proof.
    iIntros (Hlen Hbase Hsize e) "#IH Hbr Hf Hfv".
    unfold interp_br_body.
    destruct (pull_base_l_drop_len vh (length vs - length tn)) eqn:Hpb.
    erewrite vfill_pull_base_l_take_len;[|eauto].
    pose proof (vfill_to_lfilled v (((λ x : value, AI_basic (BI_const x)) <$> l) ++ [AI_basic (BI_br j)])) as [Hle Hfill]. 
    erewrite <-lh_depth_pull_base_l_take_len in Hfill;[|eauto]. 
    rewrite Hsize -e in Hfill.
    assert (j - p = 0) as ->;[lia|].
    iDestruct "Hbr" as (? ? ? ? ? ? ? ?) "[>%Hlook [>%Hlayer Hbr]]".
    simpl in Hlook. inversion Hlook;subst τs'.
    iDestruct "Hbr" as "[>%Hdepth [>%Hmin [#>Hvalvs Hbr]]]".
    iDestruct "Hvalvs" as "[%|Hvalvs]";[done|].
    iDestruct "Hvalvs" as (ws' Heq') "Hvalvs". inversion Heq';subst ws'.
    iDestruct (big_sepL2_length with "Hvalvs") as %Hlen2.
    rewrite app_length in Hlen2.
        
    iApply (wp_br with "Hf");[..|eauto|].
    { apply const_list_of_val. }
    { rewrite fmap_length. eapply length_pull_base_l_take_len in Hpb;[|eauto]. rewrite Hpb.
      rewrite Hlen.
      assert (length vs >= length tn);[|lia]. rewrite Hlen2. lia. }
    iNext. iIntros "Hf".
    iApply ("IH" with "[] Hf Hfv");auto.
    { iPureIntro. erewrite length_pull_base_l_take_len;eauto.
      assert (length vs >= length tn);[|lia]. rewrite Hlen2. lia. }
    { eapply take_drop_pull_base_l_take_len in Hpb as Happ;[|eauto..];[|lia].
      rewrite Happ.
      iDestruct (big_sepL2_app_inv with "Hvalvs") as "[? ?]".
      { right. eapply length_pull_base_l_take_len in Hpb;[|eauto]. rewrite Hpb.
        assert (length vs >= length tn);[|lia]. rewrite Hlen2. lia. }
      iModIntro. iFrame "#".
    }
  Qed.

  Lemma interp_call_host_label C i w f' tn tm es lh hl :
    □ (∀ a a0, ⌜length a0 = length tn⌝ →
               ↪[frame]a -∗ interp_frame (tc_local C) i a -∗
             □ ([∗ list] w;τ ∈ a0;tn, interp_value τ w) -∗
             WP ((λ v : value, AI_basic (BI_const v)) <$> a0) ++
                to_e_list [BI_loop (Tf tn tm) es]
             {{ vs0,
                (interp_val tm vs0
                 ∨ interp_br (tc_local C) i (tc_return C) hl vs0 lh (tc_label C)
                 ∨ interp_return_option (tc_return C) (tc_local C) i vs0
                 ∨ interp_call_host (tc_local C) i (tc_return C) hl vs0 lh (tc_label C) tm) ∗
                (∃ f0 : leibnizO frame,  ↪[frame]f0 ∗
                                          interp_frame (tc_local C) i f0) }}) -∗
    interp_ctx (tc_label C) (tc_return C) hl (tc_local C) i lh -∗
    interp_call_host (tc_local C) i (tc_return C) hl w (push_base lh (length tn) [AI_basic (BI_loop (Tf tn tm) es)] [] []) (tc_label (upd_label C ([tn] ++ tc_label C))) tm -∗
    ↪[frame]f' -∗
    interp_frame (tc_local C) i f' -∗
    WP of_val w CTX 1; LH_rec [] (length tn) [AI_basic (BI_loop (Tf tn tm) es)] (LH_base [] []) []
    {{ v, (interp_val tm v
           ∨ interp_br (tc_local C) i (tc_return C) hl v lh (tc_label C)
           ∨ interp_return_option (tc_return C) (tc_local C) i v
           ∨ interp_call_host (tc_local C) i (tc_return C) hl v lh (tc_label C) tm) ∗
           (∃ f0 : frame,  ↪[frame]f0 ∗ interp_frame (tc_local C) i f0) }}.
  Proof.
    iIntros "#HIH #Hc Hch Hf Hfv".
    
    iDestruct (fixpoint_interp_call_host_eq with "Hch") as "Hch".
    iDestruct "Hch" as (? ? ? ? ? ? Heqw Htf Hin Hb) "[#Hv #Hch]".
    rewrite Heqw.

    eassert (LH_rec [] (length tn) [AI_basic (BI_loop (Tf tn tm) es)] (LH_base [] []) [] =
              push_base (LH_base [] []) (length tn) [AI_basic (BI_loop (Tf tn tm) es)] [] []) as Heq';[simpl;auto|].
    rewrite Heq'.
    iApply wp_label_push_nil_inv. iApply wp_wasm_empty_ctx.

    rewrite llfill_label.
    eassert (llfill (LL_label [] (length tn) [AI_basic (BI_loop (Tf tn tm) es)] vh []) [AI_call_host tf h v] = of_val (callHostV _ _ _ _)) as Hval.
    { simpl of_val. f_equiv; eauto. }
    iApply wp_value;[done|].
    iSplitR "Hf Hfv";[|iExists _;iFrame;iExists _;eauto].
    iRight. iRight. iRight. clear Hval. iRevert "Hv Hch".
    iLöb as "IH"
  forall (tf h v w vh τs1 τs2 Heqw Htf Hin Hb);iIntros "#Hv #Hch".
    match goal with
    | |- context [ (▷ ?IH0)%I ] =>
        set (IH:=IH0)
    end.

    iApply fixpoint_interp_call_host_eq.
    iExists _,_,_,_,_,_. do 5 (iSplitR;[eauto|]).
    iModIntro. iIntros (v2 f) "#Hw [Hf Hfv]".

    simpl sfill.
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.
    iApply wp_ctx_bind;[simpl;auto|].
    iDestruct ("Hch" with "Hw [$]") as "Hch'".
    iApply (wp_wand with "Hch'").
    
    iIntros (v') "[[Hv' | [Hv' | [Hv' | Hv']]] Hf]";iDestruct "Hf" as (f0) "[Hf Hfv]".
    { iApply wp_label_push_nil_inv. iApply wp_wasm_empty_ctx.
      iDestruct "Hv'" as "[-> | Hv']".
      { iApply (wp_wand with "[Hf]").
        { iApply (wp_label_trap with "Hf");[auto|].
          by instantiate (1:=(λ v, ⌜v = trapV⌝)%I). }
        iIntros (v0) "[-> Hf]".
        iSplitR "Hf Hfv";[|iExists _;iFrame].
        iLeft. iLeft. done. }
      iDestruct "Hv'" as (ws ->) "Hv'".
      iApply (wp_wand with "[Hf]").
      { iApply (wp_label_value with "Hf");[eapply to_of_val|].
        by instantiate (1:=(λ v, ⌜v = immV _⌝)%I). }
      iIntros (v0) "[-> Hf]".
      iSplitR "Hf Hfv";[|iExists _;iFrame].
      iLeft. iRight. iExists _. iSplit;eauto.
    }
    { rewrite fixpoint_interp_br_eq.
      iDestruct "Hv'" as (j vh' vs p) "[>%Heqbr [>%Hbase [>%Hsize Hbr]]]".
      rewrite -/(wp_wasm_ctx _ _ _ _ _ _).
      rewrite Heqbr.

      iApply wp_label_push_nil_inv. iApply wp_wasm_empty_ctx.
      
      destruct (decide (j = p)).
      { iApply (wp_wand with "[-]").
        { iApply (interp_br_step with "HIH Hbr Hf Hfv");[eauto|apply Hbase|apply Hsize|apply e]. }
        iIntros (v0) "[[H|[H|[H|H]]] $]".
        { iLeft. iFrame. }
        { iRight. iLeft. iNext. iFrame. }
        { iRight. iRight. iLeft. iFrame. }
        { repeat iRight. iNext. iFrame. } }
        
      { iAssert (⌜lholed_lengths (rev (tc_label C)) lh⌝ ∧ ⌜lholed_valid lh⌝ ∧ ⌜base_is_empty lh⌝)%I as %[Hlh_length [Hlh_valid Hlh_empty]].
        { iDestruct "Hc" as "[% [% [% _]]]". auto. }
        iApply (wp_wand with "[-]").
        { iApply (interp_br_stuck_push_later with "Hbr Hf Hfv");eauto. }
        iIntros (v0) "[[H|[H|[H|H]]] $]".
        { iLeft. iFrame. }
        { iRight. iLeft. iNext. iFrame. }
        { iRight. iRight. iLeft. iFrame. }
        { repeat iRight. iNext. iFrame. } }
    }
    { iDestruct (interp_return_label with "Hv' Hf Hfv") as "Hv'".
      iApply (wp_wand_ctx with "Hv'").
      iIntros (v0) "[[H|[H|[H|H]]] $]".
        { iLeft. iFrame. }
        { iRight. iLeft. iNext. iFrame. }
        { iRight. iRight. iLeft. iFrame. }
        { repeat iRight. iNext. iFrame. } Unshelve. apply [].
    }
    { rewrite fixpoint_interp_call_host_eq.
      iDestruct "Hv'" as (? ? ? ? ? ?) "[>%Heq [>%Htf0 [>%Hin' [>%Hb' [#Hv' #Hch']]]]]".
      rewrite -/(wp_wasm_ctx _ _ _ _ _ _). rewrite Heq.

      iApply wp_label_push_nil_inv. iApply wp_wasm_empty_ctx.
      rewrite llfill_label.
      eassert (llfill (LL_label [] (length tn) [AI_basic (BI_loop (Tf tn tm) es)] vh0 []) [AI_call_host tf0 h0 v0] = of_val (callHostV _ _ _ _)) as Hval'.
      { simpl of_val. f_equiv; eauto. }
      iApply wp_value;[done|].
      iSplitR "Hf Hfv";[|iExists _;iFrame].
      repeat iRight. iNext.
      unfold IH. iApply "IH";auto.
    }    
  Qed.

  Lemma typing_loop C es tn tm : (⊢ semantic_typing (upd_label C ([tn] ++ tc_label C)%list) (to_e_list es) (Tf tn tm)) ->
                                 ⊢ semantic_typing C (to_e_list [BI_loop (Tf tn tm) es]) (Tf tn tm).
  Proof.
    intros IHbe_typing.
    unfold semantic_typing, interp_expression.
    iIntros (i lh hl).
    iIntros "#Hi".
    
    iDestruct (IHbe_typing $! i (push_base lh (length tn) [AI_basic (BI_loop (Tf tn tm) es)]
                                           [] []) with "[]") as "HH"; [by (destruct C,i;eauto)|].

    iIntros "#Hc". iIntros (f vs) "[Hf Hfv] #Hv".
    
    iDestruct "Hv" as "[-> | Hv]".
    {  take_drop_app_rewrite_twice 0 1.
       iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
       { iApply (wp_trap with "[] [Hf]");auto. }
       iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.

    iRevert "Hfv Hv". iLöb as "IH"
  forall (f ws Hlen).
    iIntros "Hlocs #Hv".
    iApply (wp_loop with "Hf");eauto.
    { apply v_to_e_is_const_list. }
    { rewrite fmap_length //. }
    iNext. iIntros "Hf".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.

    iAssert (∀ f, interp_frame (tc_local C) i f -∗ ↪[frame] f -∗ WP of_val (immV ws) ++ to_e_list es
              {{ v, (⌜v = trapV⌝ ∨
                       interp_values tm v ∨
                       interp_br (tc_local C) i (tc_return C) hl v _ _ ∨ _)
                      ∗ ∃ f, ↪[frame] f ∗ interp_frame (tc_local C) i f }})%I as "Hcont".
    { iIntros (f') "Hfv Hf".
      iDestruct ("HH" with "[] [Hf Hfv] []") as "Hcont".
      { iApply (interp_ctx_push_label_loop with "[$] [$]"). }
      { iFrame "∗ #". }
      { iRight. iExists _. eauto. }
      iApply (wp_wand with "Hcont").
      iIntros (v) "H". rewrite -or_assoc. iFrame. }
    
    iDestruct ("Hcont" $! f with "[$]") as "Hcontf". simpl push_base.
    iApply iRewrite_nil_r_ctx.
    
    iApply (wp_seq_can_trap_ctx). iFrame.
    iSplitR.
    { iIntros "[Hcontr | [Hcontr | [Hcontr | Hcontr] ] ]";[by iDestruct "Hcontr" as (? ?) "_"|..].
      { rewrite fixpoint_interp_br_eq. iDestruct "Hcontr" as (? ? ? ? ?) "_". done. }
      { iDestruct "Hcontr" as (? ? ?) "_";done. }
      { rewrite fixpoint_interp_call_host_eq. iDestruct "Hcontr" as (? ? ? ? ?  ? ? ?) "_";done. } }
    iSplitR;[iIntros (?) "?"; iSplitR;[by iLeft;iLeft|eauto]|].

    iIntros (w f') "[Hred [Hf Hfv]]".
    rewrite app_nil_r.
    iDestruct "Hred" as "[#Hval | [Hbr | [Hret | Hch]]]".
    
    { iDestruct "Hval" as (vs ->) "Hval".
      rewrite fmap_length Hlen. iDestruct (big_sepL2_length with "Hval") as %Hlen'.
      iApply (wp_wand_ctx _ _ _ (λ vs, ⌜vs = immV _⌝ ∗ ↪[frame] _)%I with "[Hf]").
      { iApply (wp_val_return with "Hf");[apply const_list_of_val|].
        iIntros "Hf". rewrite app_nil_l app_nil_r.
        iApply wp_value;[done|]. iFrame. eauto. }
      iIntros (v) "[-> Hf]".
      iSplitR;[|iExists _;iFrame;iExists _;eauto].
      iLeft. iRight. iExists _. iSplit;eauto. }

    { rewrite fixpoint_interp_br_eq.
      iDestruct "Hbr" as (j vh vs p -> Hbase Hsize) "Hbr".
      simpl of_val.

      rewrite fmap_length.
      assert (LH_rec [] (length ws) [AI_basic (BI_loop (Tf tn tm) es)] (LH_base [] []) [] =
                push_base (LH_base [] []) (length ws) [AI_basic (BI_loop (Tf tn tm) es)] [] []) as Heq;[auto|].
      rewrite Heq.
      iApply wp_label_push_nil_inv. iApply wp_wasm_empty_ctx.

      destruct (decide (j = p)).
      { iApply (interp_br_step with "[] Hbr Hf Hfv");eauto. }

      { iAssert (⌜lholed_lengths (rev (tc_label C)) lh⌝ ∧ ⌜lholed_valid lh⌝ ∧ ⌜base_is_empty lh⌝)%I as %[Hlh_length [Hlh_valid Hlh_empty]].
        { iDestruct "Hc" as "[% [% [% _]]]". auto. }
        iApply (interp_br_stuck_push with "Hbr Hf Hfv");eauto. }
    }

    { iApply (interp_return_label  with "Hret Hf Hfv"). }
    { rewrite fmap_length Hlen. iApply (interp_call_host_label with "IH Hc Hch Hf Hfv"). }
  Qed.

End fundamental.
