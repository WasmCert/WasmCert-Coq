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


  Context `{!wasmG Σ, !logrel_na_invs Σ}.
  
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

  Lemma composition_br t1s t3s vs C i hl w lh f' e :
  interp_val t1s vs -∗
  interp_br (tc_local C) i (tc_return C) hl w lh (tc_label C) -∗
  ↪[frame]f' -∗
  interp_frame (tc_local C) i f' -∗
  WP iris.of_val w ++ [e]
  CTX
  0; LH_base [] []
  {{ v,
     (interp_val t3s v
      ∨ interp_br (tc_local C) i (tc_return C) hl v lh (tc_label C)
        ∨ interp_return_option (tc_return C) (tc_local C) i v
          ∨ interp_call_host (tc_local C) i (tc_return C) hl v lh
              (tc_label C) t3s) ∗
     (∃ f0 : frame,  ↪[frame]f0 ∗ interp_frame (tc_local C) i f0) }}.
  Proof.
    iIntros "#Hv Hbr Hf Hfv".
    iIntros (LI Hfill%lfilled_Ind_Equivalent);inversion Hfill;simplify_eq.
    erewrite app_nil_l, app_nil_r.
    rewrite fixpoint_interp_br_eq.
    iDestruct "Hbr" as (j lh' vs' p) "[%Heq [%base [%Hdepth Hbr]]]".
    rewrite Heq. rewrite of_val_br_app_r.
    iApply wp_value;[done|].
    iSplitR "Hf Hfv";[|iExists _;iFrame].
    iRight. iLeft.
    iApply fixpoint_interp_br_eq.
    iExists _,_,_,_. iSplit;[eauto|].
    iFrame. rewrite get_base_l_append -append_lh_depth. auto.
  Qed.

  Lemma composition_return t1s t3s vs C i w f' e hl lh :
  interp_val t1s vs -∗
  interp_return_option (tc_return C) (tc_local C) i w -∗
  ↪[frame]f' -∗
  interp_frame (tc_local C) i f' -∗
  WP iris.of_val w ++ [e]
  CTX
  0; LH_base [] []
  {{ v,
     (interp_val t3s v
      ∨ interp_br (tc_local C) i (tc_return C) hl v lh (tc_label C)
        ∨ interp_return_option (tc_return C) (tc_local C) i v
          ∨ interp_call_host (tc_local C) i (tc_return C) hl v lh
              (tc_label C) t3s) ∗
     (∃ f0 : frame,  ↪[frame]f0 ∗ interp_frame (tc_local C) i f0) }}.
  Proof.
    iIntros "Hv Hret Hf Hfv".
    iIntros (LI Hfill%lfilled_Ind_Equivalent);inversion Hfill;simplify_eq.
    erewrite app_nil_l, app_nil_r.
    iDestruct "Hret" as (sh vs' -> Hbase) "Hret".
    destruct (tc_return C);[|done].
    rewrite of_val_ret_app_r.
    iApply wp_value;[done|].
    iSplitR "Hf Hfv";[|iExists _;iFrame].
    iRight. iRight. iLeft.
    iExists _,_. iSplit;[eauto|].
    rewrite simple_get_base_l_append.
    iSplit;eauto.

    pose proof (sfill_to_lfilled (sh_append sh ([e])) ([AI_basic BI_return])) as Hj.
    pose proof (sfill_to_lfilled sh ([AI_basic BI_return])) as Hj'.

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
    iIntros (f0 f1) "Hf". iSpecialize ("Hret" $! f0 with "[$]").
    iApply (wp_ret_shift with "Hret");[| |apply Hlh''|apply Hlh'].
    { apply const_list_of_val. }
    { rewrite fmap_length. rewrite drop_length.
      rewrite app_length in Hlen. apply Nat.add_sub_eq_r. rewrite Hlen. lia. }
  Qed.

  Lemma llfill_sh_append vh es es' :
    llfill (llh_append vh es) es' = llfill (LL_base [] es) (llfill vh es').
  Proof.
    induction vh;simpl.
    { rewrite !app_assoc. auto. }
    { rewrite app_comm_cons app_assoc. auto. }
    { rewrite app_comm_cons app_assoc. auto. }
  Qed.

  Lemma is_basic_app l1 l2 :
    is_basic_expr l1 ->
    is_basic_expr l2 ->
    is_basic_expr (l1 ++ l2).
  Proof.
    revert l2. induction l1;intros l2;auto.
    simpl. intros [? ?]. intros.
    split;auto.
  Qed.
  
  Lemma llholed_basic_sh_append vh e :
    is_basic e ->
    llholed_basic vh ->
    llholed_basic (llh_append vh [e]).
  Proof.
    induction vh;simpl;intros;auto.
    { apply is_basic_app;auto. simpl. split;auto. }
    { destruct H0 as [? ?]. split;auto.
      apply is_basic_app;auto. simpl. split;auto. }
    { destruct H0 as [? ?]. split;auto.
      apply is_basic_app;auto. simpl. split;auto. }
  Qed.
  
  Lemma composition_call_host t2s t3s C i hl w lh f' e :
    is_basic e ->
    (⊢ semantic_typing C [e] (Tf t2s t3s)) ->
    interp_instance C hl i -∗
    interp_ctx (tc_label C) (tc_return C) hl (tc_local C) i lh -∗
    (* interp_val t1s vs -∗ *)
    interp_call_host (tc_local C) i (tc_return C) hl w lh (tc_label C) t2s -∗
    ↪[frame]f' -∗
    interp_frame (tc_local C) i f' -∗
    WP iris.of_val w ++ [e]
    CTX
    0; LH_base [] []
    {{ v,
        (interp_val t3s v
         ∨ interp_br (tc_local C) i (tc_return C) hl v lh (tc_label C)
         ∨ interp_return_option (tc_return C) (tc_local C) i v
         ∨ interp_call_host (tc_local C) i (tc_return C) hl v lh (tc_label C) t3s) ∗
     (∃ f0 : frame,  ↪[frame]f0 ∗ interp_frame (tc_local C) i f0) }}.
  Proof.
    iIntros (He Ht2) "#Hi #Hc Hch Hf Hfv".
    rewrite fixpoint_interp_call_host_eq.
    iDestruct "Hch" as (? ? ? ? ? ? Heqv Heqt Hin Hb) "[#Hw #HK]".
    rewrite Heqv.

    assert (forall tf h v lh es,
                 iris.of_val (callHostV tf h v lh) ++ es =
                   iris.of_val (callHostV tf h v (llh_append lh es))) as Heq.
    { intros. simpl. destruct lh0;simpl.
      all: by rewrite app_comm_cons app_assoc. }
    
    rewrite Heq.
    iApply wp_wasm_empty_ctx.
    iApply wp_value;[done|].
    iSplitR;[|iExists _;iFrame].
    repeat iRight.
    iApply fixpoint_interp_call_host_eq.
    iExists _,_,tf,h,τs1,τs2. rewrite Heqv.
    do 4 (iSplit;[eauto|]).
    { iPureIntro. apply llholed_basic_sh_append;auto. }
    iFrame "Hw". iModIntro.
    iIntros (v2 f) "#Hv2 [Hf Hfv]".
    rewrite llfill_sh_append. simpl llfill.

    iRevert "Hv2 HK". clear Heqv Heqt. iLöb as "IH"
  forall (f vh v2 τs2 Hb);iIntros "#Hv2 #HK".

    iAssert (↪[frame] f -∗
             WP llfill vh (iris.of_val v2)
             {{ vs1, (⌜vs1 = trapV⌝ ∨ interp_values t2s vs1
                      ∨ ▷ interp_br (tc_local C) i (tc_return C) hl vs1 lh (tc_label C)
                      ∨ interp_return_option (tc_return C) (tc_local C) i vs1
                      ∨ ▷ interp_call_host (tc_local C) i (tc_return C) hl vs1 lh (tc_label C) t2s) ∗
                     (∃ f1,  ↪[frame]f1 ∗ interp_frame (tc_local C) i f1) }})%I with "[Hfv]" as "H1".
    { iIntros "Hf".
      iDestruct ("HK" with "Hv2 [$]") as "Hcont".
      iApply (wp_wand with "Hcont").
      unfold interp_val. iIntros (v0). rewrite -or_assoc. auto. }

    iApply wp_wasm_empty_ctx.
    iApply (wp_seq_can_trap_ctx).
    iFrame "∗ #".
    iSplitR.
    { iIntros "[Hcontr | [Hcontr | [Hcontr | Hcontr] ] ]";[by iDestruct "Hcontr" as (? ?) "_"|..].
      { rewrite fixpoint_interp_br_eq. iDestruct "Hcontr" as (? ? ? ?) "[>%H _]". done. }
      { iDestruct "Hcontr" as (? ? ?) "_";done. }
      { rewrite fixpoint_interp_call_host_eq. iDestruct "Hcontr" as (? ? ? ? ? ?) "[>%H _]";done. } }
    iSplitR;[iIntros (?) "?"; iSplitR;[by iLeft;iLeft|eauto]|].
    iIntros (w0 f0) "[Hw0 [Hf Hfv]]".
    iDestruct "Hw0" as "[#H|[H|[H|H]]]".
    { iApply wp_wasm_empty_ctx.
      iDestruct (Ht2 with "Hi Hc [$] []") as "Ht2".
      { iRight. iFrame "H". }
      iApply (wp_wand with "Ht2").
      iIntros (v1) "H'".
      iDestruct "H'" as "[[H'|[H'|[H'|H']]] $]".
      { by iLeft. }
      { iRight. by iLeft. }
      { iRight. iRight. by iLeft. }
      { by repeat iRight. }
    }
    { rewrite fixpoint_interp_br_eq.
      iDestruct "H" as (j lh' vs' p) "[>%Heqbr [>%Hbase [>%Hdepth Hbr]]]".
      rewrite -/(wp_wasm_ctx _ _ _ _ _ _). rewrite Heqbr.
      rewrite of_val_br_app_r. iApply wp_wasm_empty_ctx.
      iApply wp_value;[done|].
      iSplitR "Hf Hfv";[|iExists _;iFrame].
      iRight. iLeft.
      iNext. rewrite fixpoint_interp_br_eq.
      iExists _,_,_,_. iSplit;[eauto|].
      iFrame. rewrite get_base_l_append -append_lh_depth. auto. }
    { iDestruct (composition_return with "Hv2 H Hf Hfv") as "H".
      iApply (wp_wand_ctx with "H").
      iIntros (v1) "H'".
      iDestruct "H'" as "[[H'|[H'|[H'|H']]] $]".
      { by iLeft. }
      { iRight. by iLeft. }
      { iRight. iRight. by iLeft. }
      { by repeat iRight. }
    }
    { rewrite fixpoint_interp_call_host_eq.
      iDestruct "H" as (? ? ? ? ? ?) "[>%Heqch [>%Htf [>%Hin' [>%Hb' [>#Hval #H]]]]]".
      rewrite -/(wp_wasm_ctx _ _ _ _ _ _).

      rewrite Heqch.
      simpl iris.of_val.
      eassert (llfill (LL_base [] [e]) (llfill vh0 [_]) = llfill vh0 [AI_call_host tf0 h0 v0] ++ [e]) as <-.
      { simpl. eauto. }
      iApply wp_wasm_empty_ctx.
      eassert (llfill _ _ = iris.of_val (callHostV _ _ _ (llh_append vh0 [e]))) as ->.
      { simpl. rewrite llfill_sh_append. eauto. }
      iApply wp_value;[done|].
      iSplitR "Hf Hfv";[|iExists _;iFrame].
      repeat iRight.
      iNext.
      rewrite fixpoint_interp_call_host_eq.
      iExists _,_,_,_,_,_. do 4 (iSplitR;[eauto|]).
      { iPureIntro. apply llholed_basic_sh_append;auto. }
      iFrame "Hval". iModIntro.
      iIntros (v1 f1) "#Hv1 [Hf Hfv]".
      rewrite llfill_sh_append. simpl sfill.
      iApply ("IH" with "[] Hf Hfv Hv1 H"). auto.
    }
  Qed.
    
  (* -------------------------------------- COMPOSITION ------------------------------------ *)

  Lemma typing_composition C es t1s t2s t3s e : is_basic e -> (⊢ semantic_typing C es (Tf t1s t2s)) ->
                               (⊢ semantic_typing C [e] (Tf t2s t3s)) ->
                               ⊢ semantic_typing C (es ++ [e]) (Tf t1s t3s).
  Proof.
    iIntros (Hbasic Ht1 Ht2).
    unfold semantic_typing, interp_expression.
    iIntros (i lh hl).
    iIntros "#Hi #Hc" (f vs) "[Hf Hfv] #Hv".
    
    iAssert (↪[frame] f -∗
             WP of_val vs ++ es
             {{ vs1, (⌜vs1 = trapV⌝ ∨ interp_values t2s vs1
                      ∨ interp_br (tc_local C) i (tc_return C) hl vs1 lh (tc_label C)
                      ∨ interp_return_option (tc_return C) (tc_local C) i vs1
                      ∨ interp_call_host (tc_local C) i (tc_return C) hl vs1 lh (tc_label C) t2s) ∗
                     (∃ f1,  ↪[frame]f1 ∗ interp_frame (tc_local C) i f1) }})%I with "[Hfv]" as "H1".
    { iIntros "Hf".
      iDestruct (Ht1 with "Hi Hc [$] Hv") as "H1".
      iApply (wp_wand with "H1").
      unfold interp_val. iIntros (v). rewrite -or_assoc. auto. }

    iApply wp_wasm_empty_ctx.
    rewrite app_assoc.
    iApply (wp_seq_can_trap_ctx).
    iFrame "∗ #".
    iSplitR.
    { iIntros "[Hcontr | [Hcontr | [Hcontr | Hcontr] ] ]";[by iDestruct "Hcontr" as (? ?) "_"|..].
      { rewrite fixpoint_interp_br_eq. iDestruct "Hcontr" as (? ? ? ?) "[%H _]". done. }
      { iDestruct "Hcontr" as (? ? ?) "_";done. }
      { rewrite fixpoint_interp_call_host_eq. iDestruct "Hcontr" as (? ? ? ? ?  ?) "[%H _]";done. } }
    iSplitR;[iIntros (?) "?"; iSplitR;[by iLeft;iLeft|eauto]|].

    iIntros (w f') "[Hw [Hf Hfv]]".
    iDestruct "Hw" as "[#Hw|[Hbr|[Hret|Hch]]]".
    { iIntros (LI Hfill%lfilled_Ind_Equivalent);inversion Hfill;simplify_eq.
      erewrite app_nil_l, app_nil_r.
      iApply (Ht2 with "[] [] [$]");iFrame "#". }

    { iApply (composition_br with "Hv Hbr Hf Hfv"). }
    { iApply (composition_return with "Hv Hret Hf Hfv"). }
    { iApply (composition_call_host with "Hi Hc Hch Hf Hfv"); auto. }
  Qed.

End fundamental.
