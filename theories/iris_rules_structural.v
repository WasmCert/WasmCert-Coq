From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris_wp_def stdpp_aux.
Require Export datatypes host operations properties opsem.



(* empty lists, frame and context rules *)

Close Scope byte_scope.

Section structural_rules.
Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}.

Lemma wp_wasm_empty_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) e :
  ⊢ WP e @ s ; E {{ Φ }} ∗-∗ WP e @ s ; E CTX_EMPTY {{ Φ }}.
Proof.
  iSplit.
  { iIntros "HWP". iIntros (LI Hfill%lfilled_Ind_Equivalent).
    inversion Hfill. subst. erewrite app_nil_l; erewrite app_nil_r. done. }
  { iIntros "HWP".
    iDestruct ("HWP" $! e with "[]") as "$".
    iPureIntro. cbn. rewrite app_nil_r eqseqE. apply eq_refl. }
Qed.

Lemma wp_wasm_empty_ctx_frame (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) e n f :
  ⊢ WP e @ s ; E FRAME n; f {{ Φ }} ∗-∗ WP e @ s ; E FRAME n; f CTX_EMPTY {{ v, Φ v }}.
Proof.
  iSplit.
  { iIntros "HWP". iIntros (LI Hfill%lfilled_Ind_Equivalent).
    inversion Hfill. subst. erewrite app_nil_l; erewrite app_nil_r. done. }
  { iIntros "HWP".
    iDestruct ("HWP" $! e with "[]") as "$".
    iPureIntro. cbn. rewrite app_nil_r eqseqE. apply eq_refl. }
Qed.

Lemma wp_nil (s : stuckness) (E : coPset) (Φ : iProp Σ) f :
  ↪[frame] f ∗ Φ ⊢ WP [] @ s ; E CTX_EMPTY {{ fun v => Φ }}%I.
Proof.
  iIntros "(Hframe & H)". iApply wp_wasm_empty_ctx.
  by rewrite wp_unfold /wasm_wp_pre.
Qed.

Lemma wp_seq_ctx (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) (i : nat) (lh : lholed) :
  (WP es1 @ NotStuck; E {{ w, Ψ w }} ∗
  ∀ w, Ψ w -∗ WP (iris.of_val w ++ es2) @ s; E CTX i; lh {{ v, Φ v }})%I
  ⊢ WP (es1 ++ es2) @ s; E CTX i; lh {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ i lh).
{ iIntros "[Hes1 Hes2]".
  (* iDestruct (wp_wasm_empty_ctx with "Hes1") as "Hes1". *)
  iIntros (LI Hfilled).
  repeat rewrite wp_unfold /wasm_wp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val LI) as [vs|] eqn:Hetov.
  { destruct vs.
    { pose proof (filled_is_val_imm _ _ _ _ _ Hetov Hfilled) as
        [vs [es' [-> [-> [Hconst1 Hconst2]]]]].
      apply const_list_is_val in Hconst1 as [v1 Hv1].
      apply const_list_is_val in Hconst2 as [v2 Hv2].
      edestruct fill_val as [vs12 [Hvs12 Heql]];eauto.
      assert (Hvs12':=Hvs12).
      apply to_val_cat in Hvs12' as [-> Hev2].
      apply iris.of_to_val in Hev2 as <-.
      iMod "Hes1".
      iSpecialize ("Hes2" with "Hes1").
      unfold iris.of_val.
      rewrite - fmap_app take_drop.
      rewrite of_val_imm.
      pose proof (lfilled_swap (iris.of_val (immV vs12)) Hfilled) as [LI' Hfilled'].
      iSpecialize ("Hes2" $! _ Hfilled').
      rewrite wp_unfold /wasm_wp_pre /=.
      assert (iris.to_val LI' = Some (immV l)) as ->;[|iFrame].
      apply lfilled_Ind_Equivalent in Hfilled'. inversion Hfilled';subst.
      apply to_val_cat_inv;auto. apply to_val_cat_inv;auto. apply iris.to_of_val.
    }
    { apply to_val_trap_is_singleton in Hetov. subst.
      apply lfilled_Ind_Equivalent in Hfilled.
      inversion Hfilled;subst.
      2: { exfalso. do 2 destruct vs =>//=. }
      apply app_eq_singleton in H as [[HH HH']|[HH HH']];subst.
      { exfalso. destruct es1,es2,es' =>//=. }
      apply app_eq_singleton in HH' as [[HH HH']|[HH HH']];subst.
      { apply app_eq_singleton in HH as [[-> ->]|[-> ->]].
        simpl.
        all:iMod "Hes1".
        all: iSpecialize ("Hes2" with "Hes1").
        all:rewrite /=.
        all: iDestruct (wp_wasm_empty_ctx with "Hes2") as "Hes2".
        all:by rewrite wp_unfold /wasm_wp_pre /=. }
      { destruct es1,es2 =>//=.
        iMod "Hes1".
        iSpecialize ("Hes2" with "Hes1").
        rewrite /=.
        iSpecialize ("Hes2" $! [AI_trap] with "[]").
        { iPureIntro. constructor. }
        by rewrite wp_unfold /wasm_wp_pre /=.  }
    }
  }
  {
  (* Ind *)
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod "Hes1".
    iSpecialize ("Hes2" with "Hes1").
    iSpecialize ("Hes2" $! _ Hfilled).
    rewrite wp_unfold /wasm_wp_pre /=.
    rewrite Hetov.
    iSpecialize ("Hes2" $! σ ns κ κs nt with "[$]").
    iMod "Hes2" as "[%H1 H2]".
    iIntros "!>".
    iSplit.
    - iPureIntro. by apply H1. 
    - by iApply "H2".
  }
  {
    iSpecialize ("Hes1" $! σ ns κ κs nt with "[$]").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct s => //.
      apply append_reducible with (es2:=es2) in H1;auto.
      eapply lfilled_reducible. apply Hfilled. auto.
    - iIntros (e2 σ2 efs HStep').
      eapply lfilled_prim_step_split_reduce_r in HStep' as Heq;[|apply Hfilled|apply H1].
      destruct Heq as [e' [HStep'' Hlfilled']].
      apply prim_step_obs_efs_empty in HStep'' as Hemp. inversion Hemp;subst;clear Hemp.
      apply prim_step_obs_efs_empty in HStep' as Hemp. inversion Hemp;subst;clear Hemp.
      iSpecialize ("H2" $! e' σ2 [] HStep'').
      iMod "H2".
      repeat iModIntro.
      repeat iMod "H2".
      iModIntro.
      iDestruct "H2" as (f1) "(Hσ & Hf1 & Hes'' & Hefs)".
      iExists f1.
      iFrame.
      iSplit => //.
      iIntros "?"; iSpecialize ("Hes''" with "[$]").
      iDestruct ("IH" with "[$Hes'' $Hes2]") as "Hcont".
      by iApply "Hcont".
  } } }
Qed.

(* Contextual rules for Local computation *)

Lemma wp_frame_rewrite (s: stuckness) (E: coPset) (Φ: val -> iProp Σ) es n f:
  WP es @ s; E FRAME n; f {{ v, Φ v }} ⊣⊢
  WP [AI_local n f es] @ s; E {{ v, Φ v }}.
Proof.
  trivial.
Qed.

Lemma wp_frame_value (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es n f f0 vs :
  iris.to_val es = Some (immV vs) ->
  length es = n ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ Φ (immV vs)) -∗
  WP es @ s; E FRAME n; f {{ Φ }}.
Proof.
  iIntros (Hv Hlen) "Hframe H".
  rewrite wp_frame_rewrite.
  apply to_val_const_list in Hv as Hconst.
  iApply wp_lift_atomic_step. simpl ; trivial.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], es, σ, [].
    destruct σ as [[[ hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //. apply r_simple. apply rs_local_const; auto.
  - destruct σ as [[[hs ws] locs] inst].
    iIntros "!>" (es2 σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'].
    destruct HStep as (H & -> & ->).
    iExists _.
    iFrame. rewrite PeanoNat.Nat.add_0_l.
    erewrite app_nil_l.
    only_one_reduction H. all:simplify_eq;iFrame. rewrite Hv. iFrame.
    1,2,3:rewrite find_first_const// in Hstart.
Qed.

Lemma wp_return (s: stuckness) (E: coPset) (Φ: val -> iProp Σ) es vs vs0 n f0 f i lh:
  iris.to_val vs = Some (immV vs0) ->
  length vs = n ->
  lfilled i lh (vs ++ [AI_basic BI_return]) es ->
  WP vs @ s; E {{ v, Φ v ∗ ↪[frame] f0 }} -∗
  WP [AI_local n f es] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}%I.
Proof.
  iIntros (Hval Hlen Hlf) "HΦ".
  iApply wp_lift_atomic_step => //=.
  rewrite wp_unfold /wasm_wp_pre /=.
  rewrite Hval.
  iIntros (σ ns κ κs nt) "Hσ !>".
  assert (const_list vs) as Hcvs; first by apply to_val_const_list in Hval.
  iSplit.
  - iPureIntro. destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], vs, σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    constructor. econstructor =>//.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iModIntro.
    iIntros (es1 σ2 efs HStep).
    iMod "HΦ" as "(HΦ & Hf0)".
    iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H.
    + iExists f0.
      rewrite Hval.
      iFrame.
      by iIntros "?".
    all: assert (lfilled 0 (LH_base vs []) [AI_basic (BI_return)]
                    (vs ++ [AI_basic (BI_return)]));
      first (by unfold lfilled, lfill ; rewrite Hcvs ; rewrite app_nil_r);
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hlf) as [lh' Hfill'] ;
    eapply lfilled_implies_starts in Hfill' => //= ;
    unfold first_instr in Hstart ; simpl in Hstart ;
    unfold first_instr in Hfill' ; rewrite Hfill' in Hstart ;
    inversion Hstart.
Qed.

Lemma wp_frame_return (s: stuckness) (E: coPset) (Φ: val -> iProp Σ) vs vs0 n f0 f i lh LI:
  iris.to_val vs = Some (immV vs0) ->
  length vs = n ->
  lfilled i lh (vs ++ [AI_basic BI_return]) LI ->
  ( WP vs @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}
  ⊢ WP LI @ s; E FRAME n ; f {{ v, Φ v ∗ ↪[frame] f0 }}).
Proof.
  iIntros (Hval Hlen Hlf) "HΦ".
  by iApply wp_return.
Qed.

Lemma wp_seq_ctx_frame (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) (i : nat) (lh : lholed) (n : nat) (f : frame) (f0 : frame) (f1 : frame) :
  (↪[frame] f0 ∗
  (↪[frame] f -∗ WP es1 @ NotStuck; E {{ w, Ψ w ∗ ↪[frame] f1 }}) ∗
  ∀ w, Ψ w ∗ ↪[frame] f0 -∗ WP (iris.of_val w ++ es2) @ s; E FRAME n ; f1 CTX i; lh {{ v, Φ v }})%I
  ⊢ WP (es1 ++ es2) @ s; E FRAME n ; f CTX i; lh {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ i lh n f f0 f1).
{ iIntros "[Hf0 [Hes1 Hes2]]".
  (* iDestruct (wp_wasm_empty_ctx with "Hes1") as "Hes1". *)
  iIntros (LI Hfilled).
  repeat rewrite wp_unfold /wasm_wp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val LI) as [vs|] eqn:Hetov.
  { destruct vs.
    { pose proof (filled_is_val_imm _ _ _ _ _ Hetov Hfilled) as
        [vs [es' [-> [-> [Hconst1 Hconst2]]]]].
      apply const_list_is_val in Hconst1 as [v1 Hv1].
      apply const_list_is_val in Hconst2 as [v2 Hv2].
      edestruct fill_val as [vs12 [Hvs12 Heql]];eauto.
      assert (Hvs12':=Hvs12).
      apply to_val_cat in Hvs12' as [-> Hev2].
      apply iris.of_to_val in Hev2 as <-.
      iIntros (? ? ? ? ?) "Hσ".
      destruct σ1 as [[[s0 s1] locs] inst].
      iDestruct "Hσ" as "(Hfuncs&Htables&Hmems&Hglobals&Hframe&Hlen)".
      (* We remember the current state now so we can reconstruct it upon return *)
      iDestruct (ghost_map_lookup with "Hframe Hf0") as %Hlook. rewrite lookup_insert in Hlook. inversion Hlook. subst f0. clear Hlook.
      (* update the local state to the local state of the inner frame *)
      iMod (ghost_map_update f with "Hframe Hf0") as "[Hframe Hf0]". rewrite insert_insert.
      iMod ("Hes1" with "Hf0") as "[HPsi Hf]".
      (* reconstruct it to its original state for the continuation *)
      iDestruct (ghost_map_lookup with "Hframe Hf") as %Hlook. rewrite lookup_insert in Hlook. inversion Hlook.
      iMod (ghost_map_update (Build_frame locs inst) with "Hframe Hf") as "[Hframe Hf0]". rewrite insert_insert.
      iSpecialize ("Hes2" with "[$HPsi $Hf0]").
      unfold iris.of_val.
      rewrite - fmap_app take_drop.
      rewrite of_val_imm.
      pose proof (lfilled_swap (iris.of_val (immV vs12)) Hfilled) as [LI' Hfilled'].
      iSpecialize ("Hes2" $! _ Hfilled').
      rewrite wp_unfold /wasm_wp_pre /=.
      iSpecialize ("Hes2" $! (s0,s1,locs,inst) _ _ _ _ with "[$Hfuncs $Htables $Hmems $Hglobals $Hlen $Hframe]").
      assert (iris.to_val LI' = Some (immV l)) as HLI';[|iFrame].
      apply lfilled_Ind_Equivalent in Hfilled'. inversion Hfilled';subst.
      apply to_val_cat_inv;auto. apply to_val_cat_inv;auto. apply iris.to_of_val.
      apply to_val_immV_inj with (es':=LI') in Hetov as Heq;auto. subst LI.
      iFrame.
    }
    { apply to_val_trap_is_singleton in Hetov. subst.
      apply lfilled_Ind_Equivalent in Hfilled.
      inversion Hfilled;subst.
      2: { exfalso. do 2 destruct vs =>//=. }
      apply app_eq_singleton in H as [[HH HH']|[HH HH']];subst.
      { exfalso. destruct es1,es2,es' =>//=. }
      apply app_eq_singleton in HH' as [[HH HH']|[HH HH']];subst.
      { apply app_eq_singleton in HH as [[-> ->]|[-> ->]].
        simpl.
        all: iIntros (? ? ? ? ?) "Hσ".
        all: destruct σ1 as [[[s0 s1] locs] inst].
        all: iDestruct "Hσ" as "(Hfuncs&Htables&Hmems&Hglobals&Hframe&Hlen)".
        all: iDestruct (ghost_map_lookup with "Hframe Hf0") as %Hlook;rewrite lookup_insert in Hlook;inversion Hlook; clear Hlook.
        all: iMod (ghost_map_update f with "Hframe Hf0") as "[Hframe Hf0]"; rewrite insert_insert.
        all: iMod ("Hes1" with "Hf0") as "[HPsi Hf]".
        all: iDestruct (ghost_map_lookup with "Hframe Hf") as %Hlook; rewrite lookup_insert in Hlook; inversion Hlook.
        all: iMod (ghost_map_update (Build_frame locs inst) with "Hframe Hf") as "[Hframe Hf0]"; rewrite insert_insert.
        all: iSpecialize ("Hes2" with "[$HPsi $Hf0]").
        all: rewrite /=.
        all: iDestruct (wp_wasm_empty_ctx_frame with "Hes2") as "Hes2".
        all: rewrite wp_frame_rewrite.
        all: rewrite wp_unfold /wasm_wp_pre /=.
        all: by iSpecialize ("Hes2" $! (s0,s1,locs,inst) _ _ _ _ with "[$Hfuncs $Htables $Hmems $Hglobals $Hlen $Hframe]").
      }
      { destruct es1,es2 =>//=.
        iIntros (? ? ? ? ?) "Hσ".
        destruct σ1 as [[[s0 s1] locs] inst].
        iDestruct "Hσ" as "(Hfuncs&Htables&Hmems&Hglobals&Hframe&Hlen)".
        iDestruct (ghost_map_lookup with "Hframe Hf0") as %Hlook;rewrite lookup_insert in Hlook;inversion Hlook;clear Hlook.
        iMod (ghost_map_update f with "Hframe Hf0") as "[Hframe Hf0]"; rewrite insert_insert.
        iMod ("Hes1" with "Hf0") as "[HPsi Hf]".
        iDestruct (ghost_map_lookup with "Hframe Hf") as %Hlook. rewrite lookup_insert in Hlook. inversion Hlook.
        iMod (ghost_map_update (Build_frame locs inst) with "Hframe Hf") as "[Hframe Hf0]"; rewrite insert_insert.
        iSpecialize ("Hes2" with "[$HPsi $Hf0]").
        rewrite /=.
        iSpecialize ("Hes2" $! [AI_trap] with "[]").
        { iPureIntro. constructor. }
        rewrite wp_unfold /wasm_wp_pre /=.
        by iSpecialize ("Hes2" $! (s0,s1,locs,inst) _ _ _ _ with "[$Hfuncs $Htables $Hmems $Hglobals $Hlen $Hframe]").
      }
    }
  }
  {
  (* Ind *)
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    destruct σ as [[[s0 s1] locs] inst].
    iDestruct "Hσ" as "(Hfuncs&Htables&Hmems&Hglobals&Hframe&Hlen)".
    iDestruct (ghost_map_lookup with "Hframe Hf0") as %Hlook;rewrite lookup_insert in Hlook;inversion Hlook. clear Hlook.
    iMod (ghost_map_update f with "Hframe Hf0") as "[Hframe Hf0]"; rewrite insert_insert.
    iMod ("Hes1" with "Hf0") as "[HPsi Hf]".
    iDestruct (ghost_map_lookup with "Hframe Hf") as %Hlook. rewrite lookup_insert in Hlook. inversion Hlook.
    iMod (ghost_map_update (Build_frame locs inst) with "Hframe Hf") as "[Hframe Hf0]"; rewrite insert_insert.
    iSpecialize ("Hes2" with "[$HPsi $Hf0]").
    iSpecialize ("Hes2" $! _ Hfilled).
    rewrite wp_unfold /wasm_wp_pre /=.
    (* rewrite Hetov. *)
    iSpecialize ("Hes2" $! (s0,s1,locs,inst) ns κ κs nt with "[$]"). subst f.
    iMod "Hes2" as "[%H1 H2]".
    iIntros "!>".
    iSplit.
    - iPureIntro. by apply H1. 
    - by iApply "H2".
  }
  {
    destruct σ as [[[s0 s1] locs] inst].
    iDestruct "Hσ" as "(Hfuncs&Htables&Hmems&Hglobals&Hframe&Hlen)".
    iDestruct (ghost_map_lookup with "Hframe Hf0") as %Hlook;rewrite lookup_insert in Hlook;inversion Hlook.
    iMod (ghost_map_update f with "Hframe Hf0") as "[Hframe Hf]"; rewrite insert_insert.
    iDestruct ("Hes1" with "Hf") as "Hes1".
    destruct f.
    iSpecialize ("Hes1" $! (s0,s1,f_locs,f_inst) ns κ κs nt with "[$]").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct s => //.
      apply append_reducible with (es2:=es2) in H1;auto.
      eapply local_frame_lfilled_reducible. apply Hfilled. auto.
    - iIntros (e2 σ2 efs HStep').
      destruct σ2 as [[[s2 s3] locs2] inst2].
      eapply local_frame_lfilled_prim_step_split_reduce_r in HStep' as Heq;[|apply Hfilled|apply H1].
      destruct Heq as [e' [v'' [i'' [LI' [HStep'' [-> [-> [-> Hfill]]]]]]]].
      
      (* eapply lfilled_prim_step_split_reduce_r in HStep' as Heq;[|apply Hfilled|apply H1]. *)
      (* destruct Heq as [e' [HStep'' Hlfilled']]. *)
      apply prim_step_obs_efs_empty in HStep'' as Hemp. inversion Hemp;subst;clear Hemp.
      apply prim_step_obs_efs_empty in HStep' as Hemp. inversion Hemp;subst;clear Hemp.
      iSpecialize ("H2" $! e' (s2,s3,v'',i'') [] HStep'').
      iMod "H2".
      repeat iModIntro.
      repeat iMod "H2".
      iDestruct "H2" as (f) "(Hσ & Hf1 & Hes'' & Hefs)".
      (* iExists f. *)
      iDestruct "Hσ" as "(Hfuncs&Htables&Hmems&Hglobals&Hframe&Hlen)".
      iDestruct (ghost_map_lookup with "Hframe Hf1") as %Hlook';rewrite lookup_insert in Hlook';inversion Hlook'.
      iMod (ghost_map_update (Build_frame locs2 inst2) with "Hframe Hf1") as "[Hframe Hf]"; rewrite insert_insert.
      iExists _. iFrame.
      iModIntro.
      iSplit => //.
      iIntros "Hf". (* iSpecialize ("Hes''" with "[$]"). *)
      rewrite -wp_frame_rewrite. iApply ("IH" with "[-]");[|iPureIntro;apply Hfill].
      iFrame "Hes''". iFrame. Unshelve. all: try apply 0. all: apply [].
  } } }
Qed.

(* behaviour of seq might be a bit unusual due to how reductions work. *)
(* Note that the sequence wp is also true without the premise that Ψ doesn't trap, but it is very tricky to prove that version. The following is the fault-avoiding version.*)
Lemma wp_seq (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) :
  (¬ Ψ trapV ∗ 
  WP es1 @ s; E {{ w, Ψ w }} ∗
  ∀ w, Ψ w -∗ WP (iris.of_val w ++ es2) @ s; E {{ v, Φ v }})
  ⊢ WP (es1 ++ es2) @ s; E {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ).
  iIntros "(Hntrap & Hes1 & Hes2)".
  repeat rewrite wp_unfold /wasm_wp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val (es1 ++ es2)) as [vs|] eqn:Hetov.
  {
    destruct vs.
    {
      apply to_val_cat in Hetov as [-> Hev2].
      apply iris.of_to_val in Hev2 as <-.
      iMod "Hes1".
      iSpecialize ("Hes2" with "Hes1").
      unfold iris.of_val.
      rewrite - fmap_app take_drop.
      rewrite of_val_imm.
      rewrite wp_unfold /wasm_wp_pre /=.
      rewrite of_val_imm iris.to_of_val.
      by iAssumption.
    }
    {
      apply to_val_trap_is_singleton in Hetov.
      apply app_eq_singleton in Hetov as [[-> ->]|[-> ->]].
      all:iMod "Hes1".
      all: iSpecialize ("Hes2" with "Hes1").
      all:rewrite /=.
      all:by rewrite wp_unfold /wasm_wp_pre /=. 
    }
  }
  (* Ind *)
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod "Hes1".
    iSpecialize ("Hes2" with "Hes1").
    rewrite wp_unfold /wasm_wp_pre /=.
    rewrite Hetov.
    iSpecialize ("Hes2" $! σ ns κ κs nt with "[$]").
    iMod "Hes2" as "[%H1 H2]".
    iIntros "!>".
    iSplit.
    - iPureIntro. by apply H1. 
    - by iApply "H2".
  }
  {
    iSpecialize ("Hes1" $! σ ns κ κs nt with "[$]").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct s => //.
      by apply append_reducible.
    - iIntros (e2 σ2 efs HStep).
      assert (κ = [] /\ efs = []) as [-> ->]; first by apply prim_step_obs_efs_empty in HStep; inversion HStep.
      apply prim_step_split_reduce_r in HStep; last by [].
      destruct HStep as [[es'' [-> HStep]] | [n [m [lh [Hlf1 [Hlf2 ->]]]]]].
      + iSpecialize ("H2" $! es'' σ2 [] HStep).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        iModIntro.
        destruct σ2 as [[[??] ?]?].
        iDestruct "H2" as (f1) "(Hσ & Hf1 & Hes'' & Hefs)".
        iExists f1.
        iFrame.
        iIntros "?"; iSpecialize ("Hes''" with "[$]").
        iApply "IH".
        by iFrame. 
      + move/lfilledP in Hlf1.
        inversion Hlf1; subst; clear Hlf1.
        assert (iris.prim_step es1 σ [] [AI_trap] σ []) as HStep2.
        { unfold iris.prim_step.
          destruct σ as [[[??]?]?].
          repeat split => //.
          apply r_simple; eapply rs_trap => //.
          move => HContra; subst.
          by destruct n.
        }
        iSpecialize ("H2" $! [AI_trap] σ [] HStep2).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        destruct σ as [[[??] ?]?].
        iDestruct "H2" as (f1) "(Hσ & Hf1 & Hes'' & Hefs)".
        iExists f1.
        iModIntro.
        iFrame.
        iIntros "?"; iSpecialize ("Hes''" with "[$]").
        replace [AI_trap] with (iris.of_val trapV) => //.
        repeat rewrite wp_unfold /wasm_wp_pre /=.
        destruct (iris.to_val (take n es1 ++ AI_trap :: drop m (es1 ++ es2))%SEQ) eqn:Hx.
        * iMod "Hes''".
          by iSpecialize ("Hntrap" with "Hes''").
        * iIntros (?????) "?".
          iMod "Hes''".
          by iSpecialize ("Hntrap" with "Hes''").
  }
Qed.

Lemma wp_val (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v0 : value) (es : language.expr wasm_lang) :
  (* Like for wp_seq, this lemma is true without the trap condition, but would
     be problematic to prove without it. *)
  ((¬ Φ trapV) ∗
  WP es @ NotStuck ; E {{ v, (Φ (val_combine (immV [v0]) v))  }}
  ⊢ WP ((AI_basic (BI_const v0)) :: es) @ s ; E {{ v, Φ v }})%I.
Proof.
  (* This also needs an iLob. *)
  iLöb as "IH" forall (v0 es Φ).
  iIntros "(Hntrap & H)".
  repeat rewrite wp_unfold /wasm_wp_pre /=.
  destruct (iris.to_val es) as [vs|] eqn:Hes.
  {
    destruct vs; first by apply of_to_val in Hes as <-.
    iIntros (?????) "?".
    iMod "H".
    by iSpecialize ("Hntrap" with "H").
  }
  {
    iIntros (σ ns κ κs nt) "Hσ".
    iSpecialize ("H" $! σ ns κ κs nt with "[$]").
    iMod "H".
    iModIntro.
    iDestruct "H" as "(%H1 & H)".
    iSplit.
    - iPureIntro.
      destruct s => //=.
      rewrite - cat1s.
      by eapply prepend_reducible; eauto.
    - iIntros (es2 σ2 efs HStep).
      rewrite -cat1s in HStep.
      eapply reduce_ves in H1; last by apply HStep.
      assert (κ = [] /\ efs = []) as [-> ->]; first by apply prim_step_obs_efs_empty in HStep; inversion HStep.
      destruct H1 as [[-> HStep2] | [lh1 [lh2 [Hlf1 [Hlf2 ->]]]]].
      + iSpecialize ("H" $! (drop 1 es2) σ2 [] HStep2).
        iMod "H".
        repeat iModIntro.
        repeat iMod "H".
        iModIntro.
        iDestruct "H" as (f1) "(Hσ & Hf1 & Hes & Hefs)".
        iSimpl.
        iExists f1.
        iFrame.
        iSplit => //.
        iIntros "?"; iSpecialize ("Hes" with "[$]").
        iApply "IH".
        by iFrame.
      + move/lfilledP in Hlf1.
        inversion Hlf1; subst; clear Hlf1.
        move/lfilledP in Hlf2.
        inversion Hlf2; subst; clear Hlf2.
        assert (iris.prim_step (vs0 ++ [AI_trap] ++ es'0) σ2 [] [AI_trap] σ2 []) as HStep2.
        { unfold iris.prim_step.
          destruct σ2 as [[[??]?]?].
          repeat split => //.
          apply r_simple; eapply rs_trap => //.
          - move => HContra.
            by replace (vs0 ++ [AI_trap] ++ es'0)%SEQ with [AI_trap] in Hes.
          - apply/lfilledP.
            by apply LfilledBase.
        }
        iSpecialize ("H" $! [AI_trap] σ2 [] HStep2).
        iMod "H".
        repeat iModIntro.
        repeat iMod "H".
        iDestruct "H" as (f1) "(Hσ & Hf1 & Hes & Hefs)".
        iExists f1.
        iFrame.
        iModIntro.
        iSplit => //.
        iIntros "?"; iSpecialize ("Hes" with "[$]").
        repeat rewrite wp_unfold /wasm_wp_pre /=.
        destruct (iris.to_val (vs ++ AI_trap :: es')%SEQ) eqn:Hx.
        * iMod "Hes".
          by iSpecialize ("Hntrap" with "Hes").
        * iIntros (?????) "?".
          iMod "Hes".
          by iSpecialize ("Hntrap" with "Hes").
  }
Qed.
  
Lemma wp_val_app' (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs (es : language.expr wasm_lang) :
  (* □ is required here -- this knowledge needs to be persistent instead of 
     one-off. *)
  (□ (¬ Φ trapV )) ∗
  WP es @ NotStuck ; E {{ v, (Φ (val_combine (immV vs) v)) }}%I
  ⊢ WP ((v_to_e_list vs) ++ es) @ s ; E {{ v, Φ v }}%I.

Proof.
  iInduction vs as [|c vs] "IH" forall (Φ s E es).
  { simpl.
    iIntros "(#Hntrap & HWP)".
    destruct s.
    2: iApply wp_stuck_weaken.
    all: iApply (wp_wand with "HWP").
    all: iIntros (v).
    all: destruct v => /=.
    all: iIntros "HΦ" => //.
  }
  { iIntros "(#Hntrap & HWP)".
    iSimpl.
    iApply wp_val.
    iSplitR => //.
    iApply "IH" => //=.
    iSplit => //.
    iApply (wp_mono with "HWP").
    iIntros (vs') "HΦ".
    iSimpl. destruct vs';auto.
  }
Qed.
  
Lemma wp_val_app (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs v' (es : language.expr wasm_lang) :
  iris.to_val vs = Some (immV v') ->
  (□ (¬ Φ trapV )) ∗
  WP es @ NotStuck ; E {{ v, (Φ (val_combine (immV v') v)) }}%I
  ⊢ WP (vs ++ es) @ s ; E {{ v, Φ v }}%I.
Proof.
  iIntros "%Hves [#Hntrap Hwp]".
  apply iris.of_to_val in Hves; subst.
  iApply wp_val_app'.
  by iFrame.
Qed.

Import DummyHosts.
Let reduce := @reduce host_function host_instance.

Canonical Structure wasm_lang := Language wasm_mixin.
 
Let reducible := @reducible wasm_lang.

(* TODO: uncomment if prim_step_reduce lemma for local frames does not hold

Lemma AI_local_reduce hs ws f0 hs' ws' f0' n f es es0':
  reduce hs ws f0 [AI_local n f es] hs' ws' f0' es0' ->
  exists f' es', f0 = f0' /\ es0' = [AI_local n f' es'] /\ reduce hs ws f es hs' ws' f' es'.
Proof.
Admitted.


Lemma reduce_tmp es1 es2 es' hs ws f hs' ws' f':
  iris.to_val es1 = None ->
  reduce hs ws f (es1 ++ es2) hs' ws' f' es' ->
  exists es1', reduce hs ws f es1 hs' ws' f' es1' /\ es' = (es1' ++ es2).
Proof.
Admitted.*)





(* Trying to resolve the problem by naively not allowing any consumption of ↪ in
   the WP premises.

   However, we then cannot connect the resulting frame after executing es1 to 
   that at the start of es2: the only way to achieve that is to have a 
   ↪[frame] in the post condition of es1; but to prove any WP with that post
   condition, we need to provide a ↪[frame] to its precondition as well; 
   so we will need two copies of the same ↪ to prove any WP, rendering the 
   spec useless.

   What we need in the post condition is some predicate like ↪ which gives
   us the knowledge of the new frame, but does not actually assert any 
   ownership -- in some sense, we need to be able to assert 0 ownership of 
   something while still asserting the knowledge of that value. This seems to
   be a weird feature to ask for, however.
 *)
(* Upd: THIS IS DONE!!!!
        Note how the post condition successfully prevents the leakage of any
        frame resources from the inner to the outer frame via Ψ -- the outer 
        frame predicate remains unchanged despite that it could undergo 
        arbitrary changes inside the frames. *)

Lemma wp_frame_seq es1 es2 n (f0 f f': frame) E s Ψ Φ:
  ( ↪[frame] f0) -∗
  ((↪[frame] f) -∗ WP es1 @ NotStuck; E {{ v, Ψ v ∗ ↪[frame] f'}}) -∗
  (∀ w, ↪[frame] f0 -∗ (Ψ w) -∗ WP (iris.of_val w ++ es2) @ s; E FRAME n; f' {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
  (WP (es1 ++ es2) @ s; E FRAME n ; f {{ v, Φ v ∗ ↪[frame]f0 }}).
Proof.
  iIntros "Hf Hes1 Hcont".
  iApply wp_wasm_empty_ctx_frame.
  iApply (wp_seq_ctx_frame with "[$Hf $Hes1 Hcont]").
  iIntros (w) "[H1 H2]".
  iApply wp_wasm_empty_ctx_frame.
  iApply ("Hcont" with "[$] [$]").
Qed.

  
(*
Lemma wp_frame_seq es1 es2 n (f0 f f': frame) E Ψ Φ:
  ( ↪[frame] f0) -∗
  (¬ (Ψ trapV)) -∗
  ((↪[frame] f) -∗ WP es1 @ NotStuck; E {{ v, ↪[frame] f' ∗ Ψ v }}) -∗
  (∀ w, ↪[frame] f0 -∗ (Ψ w) -∗ WP (iris.of_val w ++ es2) @ NotStuck; E FRAME n; f' {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
  (WP (es1 ++ es2) @ NotStuck; E FRAME n ; f {{ v, Φ v ∗ ↪[frame]f0 }}).
(* WP [AI_local n f (es1 ++ es2)] @ NotStuck; E {{ v, Φ v }} *)
Proof.
  iLöb as "IH" forall (f0 f f' E es1 es2 Ψ Φ n).
  iIntros "Hf0 Hntrap Hwp1 Hwp2".
  unfold wp_wasm_frame.
  repeat rewrite wp_unfold /wasm_wp_pre /=.
  destruct (iris.to_val es1) as [vs|] eqn:Hetov.
  
  { (* when es1 is a value, the post condition of the first wp needs to
       provide enough information for the second wp to work. *)
    iIntros (σ ns κ κs nt) "Hσ".
    destruct σ as [[[hs ws] locs] inst].
    iDestruct "Hσ" as "(Hfunc&Ht&Hm&Hg& Hframe & Hmemlen)".
    (* We must always remember to link the frame predicate to the state interp:
       else we lose their relationship when we update the state later. *)
    iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf".
    rewrite lookup_insert in Hf.
    inversion Hf; subst; clear Hf.
    iMod (ghost_map_update with "Hframe Hf0") as "(Hframe & Hf0)".
    instantiate (1 := f).
    iSpecialize ("Hwp1" with "[$]").
    iMod "Hwp1" as "(Hf' & HΨ)".
    (* Again, must remember to link f' to the state interp here *)
    iDestruct (ghost_map_lookup with "Hframe Hf'") as "%Hf'".
    rewrite lookup_insert in Hf'.
    inversion Hf'; subst; clear Hf'.
    iMod (ghost_map_update with "Hframe Hf'") as "(Hframe & Hf')".
    instantiate (1 := (Build_frame locs inst)).
    iSpecialize ("Hwp2" $! vs with "[$] [$]").
    rewrite wp_unfold /wasm_wp_pre /=.
    repeat rewrite insert_insert.
    iSpecialize ("Hwp2" $! (hs, ws, locs, inst) ns κ κs nt
                   with "[$Hfunc $Ht $Hm $Hg Hframe $Hmemlen]"); first by destruct f'.
    iMod "Hwp2" as "(%Hreducible & Hwp2)".
    iModIntro.
    apply of_to_val in Hetov as <-.
    by iSplit.
  }
  { 
    iIntros (σ ns κ κs nt) "Hσ".
    destruct σ as [[[hs ws] locs] inst].
    iDestruct "Hσ" as "(Hf & Ht & Hm & Hg & Hframe & Hmemlen)".
    iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
    rewrite lookup_insert in Hf0.
    inversion Hf0; subst; clear Hf0.
    iMod (ghost_map_update with "Hframe Hf0") as "(Hframe & Hfx)".
    instantiate (1 := f).
    iSpecialize ("Hwp1" with "Hfx").
    iSpecialize ("Hwp1" $! (hs, ws, f.(f_locs), f.(f_inst)) ns [] κs nt).
    rewrite insert_insert.
    iSpecialize ("Hwp1" with "[$Hf $Ht $Hm $Hg $Hmemlen Hframe]"); first by destruct f => /=.
    iMod "Hwp1" as "(%Hreducible & Hwp1)".
    iModIntro.
    iSplit.
    { (* reducibility of seq within AI_local. *)
      iPureIntro.
      unfold reducible, language.reducible, language.prim_step in *.
      destruct Hreducible as [κ' [es'[σ'[efs HStep]]]].
      destruct σ' as [[[hs' ws'] locs'] inst'].
      exists κ', [AI_local n (Build_frame locs' inst') (es' ++ es2)], (hs', ws', locs, inst), [].
      simpl in *.
      destruct HStep as [Hreduce [-> ->]].
      repeat split => //.
      apply r_local.
      destruct f.
      by apply r_elimr.
    }
    iIntros (es' σ' efs HStep).
    destruct σ' as [[[hs' ws'] locs'] inst'].

    inversion HStep as [Hreduce [-> ->]].
    apply AI_local_reduce in Hreduce as [f'' [es'' [Hf0 [-> Hreduce]]]].
    inversion Hf0; subst; clear Hf0.
    apply reduce_tmp in Hreduce as [es1' [Hreduce' ->]] => //.
    iSpecialize ("Hwp1" $! es1' (hs', ws', f''.(f_locs), f''.(f_inst)) [] with "[%]"); first ((repeat split); by destruct f, f'') => //=.
  
    (* We can't eliminate all the modalities -- one fupd needs to remain for us
       to update the frame back. But the masks in Hwp1 can be stripped *)
    iMod "Hwp1".
    do 2 iModIntro.
    iMod "Hwp1".
    iModIntro.
    iMod "Hwp1".

    iDestruct "Hwp1" as (f1) "((?&?&?&?& Hframe &?) & Hf1 & Hwp1 & ?)".

    (* Establish the relationship between f1 and f'' the cell gets consumed. This
       is also the reason that we can have an arbitrary existential in the 
       definition of the weakest precondition fixpoint. *)
    iDestruct (ghost_map_lookup with "Hframe Hf1") as "%Hf".
    rewrite lookup_insert in Hf.
    inversion Hf; subst; clear Hf.
    
    
    (* Now we do have the ↪; modify the ghost_map back to f0 *)
    iMod (ghost_map_update with "Hframe Hf1") as "(Hframe & Hf1)".
    instantiate (1 := Build_frame locs' inst').
    rewrite insert_insert.
    iExists (Build_frame locs' inst').
  
    iModIntro.
    iFrame => /=.

    iIntros "Hf1".
    
    iApply ("IH" with "[Hf1] [Hntrap] [Hwp1]") => //.
    destruct f''.
    iIntros "?"; iSpecialize ("Hwp1" with "[$]").
    by iAssumption.
  }
(*
   The key that enables the above to be proved is the modification of wp: instead
   of only knowing that a frame predicate exists at the end, we now know that
   it exists at each step. Note that this could not have worked without changing
   the wp: the statement that there is always a frame ownership is not an
   universal property of Iris, but a property of the Wasm semantics instead.
   As a result, we need this specific version of wp to prove this result.
   Also, we need to prove that every reduction respects this preservation of 
   the existence of a frame ownership.
 *)
Qed.*)



End structural_rules.
