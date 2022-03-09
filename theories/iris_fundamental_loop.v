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

  Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* ----------------------------------------- LOOP ---------------------------------------- *)

  Lemma interp_ctx_continuations_push_label_loop lh C i tm tn es :
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
                 ∨ interp_br (tc_local C) i vs lh (tc_label C)) ∗
                (∃ f0 : leibnizO frame,  ↪[frame]f0 ∗
                   interp_frame (tc_local C) i f0) }}) -∗
      interp_ctx_continuations (tc_label C) (tc_local C) i lh -∗
      interp_ctx_continuation (tc_label (upd_label C ([tn] ++ tc_label C))) (push_base lh (length tn) [AI_basic (BI_loop (Tf tn tm) es)] [] [])
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

  Lemma interp_ctx_push_label_loop C tm i lh tn es :
    □ (∀ (a : leibnizO frame) (a0 : seq.seq (leibnizO value)),
           ⌜length a0 = length tn⌝
           →  ↪[frame]a -∗
               interp_frame (tc_local C) i a -∗
             □ ([∗ list] w;τ ∈ a0;tn, interp_value τ w) -∗
             WP of_val (immV a0) ++ to_e_list [BI_loop (Tf tn tm) es]
             {{ vs,
                (interp_val tm vs
                 ∨ interp_br (tc_local C) i vs lh (tc_label C)) ∗
                (∃ f0 : leibnizO frame,  ↪[frame]f0 ∗
                   interp_frame (tc_local C) i f0) }}) -∗
    interp_ctx (tc_label C) (tc_local C) i lh -∗
    interp_ctx (tc_label (upd_label C ([tn] ++ tc_label C)%list))
      (tc_local (upd_label C ([tn] ++ tc_label C)%list)) i
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

  (* Lemma push_ctx_interp_br es vs n es' es1 tm C lh i : *)
  (*   WP es {{ vs, (interp_val tm vs ∨ interp_br (tc_label C) tm lh (tc_local C) i vs) ∗ (∃ f, ↪[frame]f ∗ interp_frame (tc_local C) i f) }} *)
  (*   WP es CTX 1; LH_rec vs n es' (LH_base [] []) es1 *)
  (*         {{ vs, (interp_val tm vs ∨ interp_br (tc_label C) tm lh (tc_local C) i vs) ∗ (∃ f, ↪[frame]f ∗ interp_frame (tc_local C) i f) }}. *)

  Lemma typing_loop C es tn tm : (⊢ semantic_typing (HWP:=HWP) (upd_label C ([tn] ++ tc_label C)%list) (to_e_list es) (Tf tn tm)) ->
                                 ⊢ semantic_typing (HWP:=HWP) C (to_e_list [BI_loop (Tf tn tm) es]) (Tf tn tm).
  Proof.
    intros IHbe_typing.
    unfold semantic_typing, interp_expression.
    iIntros (i lh).
    iIntros "#Hi".
    
    iDestruct (IHbe_typing $! i (push_base lh (length tn) [AI_basic (BI_loop (Tf tn tm) es)]
                                           [] []) with "[]") as "HH"; [by (destruct C,i;eauto)|].

    iIntros "#Hc". iIntros (f vs) "[Hf Hfv] #Hv".
    (* iDestruct "Hfv" as (locs Heq) "#Hlocs". *)
    
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
                       interp_br (tc_local C) i v _ _)
                      ∗ ∃ f, ↪[frame] f ∗ interp_frame (tc_local C) i f }})%I as "Hcont".
    { iIntros (f') "Hfv Hf".
      iDestruct ("HH" with "[] [Hf Hfv] []") as "Hcont".
      { iApply (interp_ctx_push_label_loop with "[$] [$]"). }
      { iFrame "∗ #". }
      { iRight. iExists _. eauto. }
      iApply (wp_wand with "Hcont").
      iIntros (v) "H". rewrite -or_assoc. iFrame. }
    
    iDestruct ("Hcont" $! f with "[$]") as "Hcontf". simpl push_base.
    (* Difficulty: 
       There is a mismatch with the way we apply bind and return,
       and the way values are currently defined: 

       with the current expression relation, we need to bind over 
       each context one by one, which means we need to return one
       by one as well. However, we can neither return, nor continue
       an expression with a br inside a context that is too shallow

       we therefore get stuck at this point.

       In essence, since we never know when we need to actually bind (i.e. we 
       don't know if the hole reduces to a br or not), so we need to be
       able to return one by one, even in case of a break.

       Solution: make a stuck br (a br in a too shallow ctx) a value, 
       and we return one by one until we find the right level.

       Until then, the lemma is admitted.
     *)
  Admitted.

End fundamental.
