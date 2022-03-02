From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export datatypes host operations properties opsem.
Require Export iris_rules_structural.
Require Import Coq.Program.Equality.
Require Export iris_wp_def stdpp_aux iris_properties.

Close Scope byte_scope.
Section control_rules.
Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}.

Lemma wp_br (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n vs es i LI lh f0 f:
  const_list vs ->
  length vs = n ->
  lfilled i lh (vs ++ [::AI_basic (BI_br i)]) LI ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP (vs ++ es) @ s; E {{ v, Φ v ∗ ↪[frame] f }})
  -∗ WP [AI_label n es LI] @ s; E {{ v, Φ v ∗ ↪[frame] f }}.
Proof.
  iIntros (Hvs Hlen Hfill) "Hf0 HΦ".
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  - iPureIntro. destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], (vs ++ es), σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    constructor. econstructor =>//.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    iApply bi.sep_exist_l.
    only_one_reduction H;
    try by assert (lfilled 0 (LH_base vs []) [AI_basic (BI_br i)]
                    (vs ++ [AI_basic (BI_br i)])) ;
      first (by unfold lfilled, lfill ; rewrite Hvs ; rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfill'] ;
    eapply lfilled_implies_starts in Hfill' => //= ;
    unfold first_instr in Hstart ; simpl in Hstart ;
    unfold first_instr in Hfill' ; rewrite Hfill' in Hstart ;
                                              inversion Hstart.    
Qed.

Lemma wp_block (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs es n m t1s t2s  f0 f:
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_label m [::] (vs ++ to_e_list es)] @ s; E {{ v, Φ v ∗ ↪[frame] f }})
  -∗ WP (vs ++ [::AI_basic (BI_block (Tf t1s t2s) es)]) @ s; E {{ v, Φ v ∗ ↪[frame] f }}.
Proof.
  iIntros (Hvs Hlen1 Hlen2 Hlen3) "Hf0 HΦ".
  iApply wp_lift_step => //=.
  apply to_val_cat_None2;auto.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  - iPureIntro. destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], _, σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    constructor. econstructor =>//.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    iApply bi.sep_exist_l.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H as [H | [[i0 Hstart] | [ (a & cl & tf & h & i0 & Hstart & Hstart1 & Hstart2) |
                                               (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
      last (by eapply r_simple, rs_block) ;
      first (inversion H; subst; clear H ; by iExists f0; iFrame) ;
      rewrite first_instr_const in Hstart => //=.
Qed.

Lemma wp_label_value (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es m ctx v f0 :
  iris.to_val es = Some (immV v) -> 
  ↪[frame] f0 -∗
  Φ (immV v) -∗ WP [::AI_label m ctx es] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hval) "Hf0 HP".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], es, σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.  apply rs_label_const.
    eapply to_val_const_list. apply Hval.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es1 σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H as [H | [[i0 Hstart] | [ (a & cl & tf & h & i0 & Hstart & Hstart1 & Hstart2) |
                                               (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
      (try by apply r_simple ; apply rs_label_const ;
       eapply to_val_const_list ; apply Hval) .
    + (* The only possible case. *)
      inversion H; subst; clear H.
      rewrite Hval.
      iFrame. done. 
    (* All of the rest are impossible reductions since es is a value. *)
    all: try by unfold first_instr in Hstart ; simpl in Hstart ;
      remember (find_first_some (map first_instr_instr es)) as fes ;
      destruct fes => //= ;
                     apply to_val_const_list in Hval ;
                     eapply starts_implies_not_constant in Hval ; first (by exfalso) ;
                     unfold first_instr ; rewrite <- Heqfes.
Qed.
(* This lemma turned out not being used in wp_label_trap ; leaving it here for possible
   future usage *)
(*
Lemma lfilled_trap_to_val k lh LI :
  lfilled k lh [AI_trap] LI ->
  (LI = [AI_trap] \/ to_val LI = None).
Proof.
  intro Hfill. destruct k ; unfold lfilled, lfill in Hfill.
  { destruct lh ; last by false_assumption.
    destruct (const_list l) ; last by false_assumption.
    apply b2p in Hfill. subst.
    induction l.
    { destruct l0. { left ; by rewrite app_nil_r. }
      right. unfold to_val, iris.to_val => //=. } 
    right. destruct IHl as [Htrap | HNone].
    apply app_eq_unit in Htrap as [[ -> Htrap ] | [ _ Habs]].
    apply app_eq_unit in Htrap as [[ Habs _ ] | [ _ ->  ]] => //=.
    destruct a => //=. destruct b => //=.
    apply app_eq_nil in Habs as [? ?] => //=.
    replace ((a :: l)%SEQ ++ [AI_trap] ++ l0) with ([a] ++ (l ++ [AI_trap] ++ l0)).
    by apply to_val_cat_None2. done. }
  fold lfill in Hfill. destruct lh ; first by false_assumption.
  destruct (const_list l) ; last by false_assumption.
  destruct (lfill _ _ _ ) ; last by false_assumption.
  apply b2p in Hfill. right.
  subst ; induction l ; first unfold to_val, iris.to_val => //=.
  replace ((a :: l)%SEQ ++ (AI_label n l0 l2 :: l1)%SEQ) with
    ([a] ++ (l ++ AI_label n l0 l2 :: l1)) ; last done.
  by apply to_val_cat_None2.
Qed.
  *)
    

Lemma wp_label_trap (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es m ctx f0 :
  iris.to_val es = Some trapV -> 
  ↪[frame] f0 -∗
  Φ trapV -∗ WP [::AI_label m ctx es] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hval) "Hf0 HP".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [AI_trap], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply to_val_trap_is_singleton in Hval as ->.
    apply r_simple.  apply rs_label_trap.
  - apply to_val_trap_is_singleton in Hval as ->.
    destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es1 σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    (* Here, the conclusion of reduce_det is not strong enough, so we re-do the proof
       of this subcase by hand, since in this particular case, we can get a 
       stronger result *)
    remember [AI_label m ctx [AI_trap]] as es0.
    remember {| f_locs := locs ; f_inst := inst |} as f.
    remember {| f_locs := locs' ; f_inst := inst' |} as f'.
    rewrite <- app_nil_l in Heqes0.
    induction H ; (try by inversion Heqes0) ;
      try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
    { destruct H ; (try by inversion Heqes0) ;
        try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
      - inversion Heqes0 ; subst. inversion H.
      - inversion Heqes0 ; subst. inversion Heqf' ; subst.
        iFrame. done.
      - inversion Heqes0 ; subst. simple_filled H1 i lh bef aft n l l'.
        found_intruse (AI_basic (BI_br 0)) H1 Hxl1.
        apply in_or_app. right. apply in_or_app. left.
        apply in_or_app. right => //=. by left.
      - rewrite Heqes0 in H0. filled_trap H0 Hxl1. }
    rewrite Heqes0 in H0.
    unfold lfilled, lfill in H0 ; destruct k.
    { destruct lh ; last by false_assumption.
      destruct (const_list l) ; last by false_assumption.
      move/eqP in H0; apply Logic.eq_sym in H0 ; simpl in H0.
      apply app_eq_unit in H0 as [[ -> H0 ] | [_ Habs]].
      apply app_eq_unit in H0 as [[ -> _] | [-> ->]] => //=.
      apply empty_no_reduce in H. by exfalso.
      unfold lfilled, lfill in H1 ; simpl in H1. move/eqP in H1.
      rewrite app_nil_r in H1 ; subst.
      apply IHreduce => //=.
      apply app_eq_nil in Habs as [-> _].
      by apply empty_no_reduce in H. }
    fold lfill in H0. destruct lh ; first by false_assumption.
    destruct (const_list l) ; last by false_assumption.
    remember (lfill _ _ _) as fill ; destruct fill ; last by false_assumption.
    move/eqP in H0; apply Logic.eq_sym in H0. simpl in H0.
    apply app_eq_unit in H0 as [[ _ H0 ] | [ _ Habs]].
    inversion H0 ; subst.
    unfold lfill in Heqfill ; destruct k.
    { destruct lh ; last by inversion Heqfill.
      destruct (const_list l0) ; inversion Heqfill.
      apply Logic.eq_sym, app_eq_unit in H3 as [[ _ H3 ]|[ _ Habs]].
      apply app_eq_unit in H3 as [[ -> _ ]|[ -> _]].
      by apply empty_no_reduce in H.
      by apply test_no_reduce_trap in H.
      apply app_eq_nil in Habs as [-> _] ; by apply empty_no_reduce in H. }
    fold lfill in Heqfill.
    destruct lh ; first by inversion Heqfill.
    destruct (const_list l0) ; last by inversion Heqfill.
    destruct (lfill k lh es) ; inversion Heqfill.
    found_intruse (AI_label n l1 l3) H3 Hxl1.
    inversion Habs.
Qed.

Lemma wp_val_return (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs vs' es' es'' n f0 f:
  const_list vs ->
  ↪[frame] f0 -∗
  (↪[frame] f0 -∗ WP vs' ++ vs ++ es'' @ s; E {{ v, Φ v ∗ ↪[frame] f }})
  -∗ WP vs @ s; E CTX 1; LH_rec vs' n es' (LH_base [] []) es'' {{ v, Φ v ∗ ↪[frame] f }}.
Proof.
  iIntros (Hconst) "Hf0 HWP".
  iLöb as "IH".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  inversion Hfill;subst.
  inversion H8;subst.
  assert (vs' ++ [AI_label n es' ([] ++ vs ++ [])] ++ es''
          = ((vs' ++ [AI_label n es' ([] ++ vs ++ [])]) ++ es''))%SEQ as ->.
  { erewrite app_assoc. auto. }
  apply const_list_is_val in Hconst as [v1 Hv1].
  apply const_list_is_val in H7 as [v2 Hv2].
  eapply to_val_cat_inv in Hv1 as Hvv;[|apply Hv2].
  iApply (wp_seq _ _ _ (λ v, (⌜v = immV (v2 ++ v1)⌝ ∗ ↪[frame] f0))%I).
  iSplitR; first by iIntros "(%H & ?)".
  iSplitR "HWP".
  - iApply wp_val_app; first by apply Hv2.
    iSplit; first by iIntros "!> (%H & ?)".
    iApply (wp_label_value with "[$]") => //=; first by erewrite app_nil_r; apply Hv1 .
  - iIntros (w) "(-> & Hf0)".
    erewrite iris.of_to_val => //.
    rewrite app_assoc.
    by iApply "HWP".
Qed.

Lemma wp_base (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs vs' es'' :
  WP vs' ++ vs ++ es'' @ s; E {{ Φ }}
  ⊢ WP vs @ s; E CTX 0; LH_base vs' es'' {{ Φ }}.
Proof.
  iIntros "HWP".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  inversion Hfill;subst. iFrame.
Qed.

Fixpoint push_base (lh : lholed) n es' vs_pre es_post :=
  match lh with
  | LH_base vs_pre' es_post' => LH_rec vs_pre' n es' (LH_base vs_pre es_post) es_post'
  | LH_rec vs m es'' lh' es => LH_rec vs m es'' (push_base lh' n es' vs_pre es_post) es
  end.

Fixpoint frame_base (lh : lholed) l1 l2 :=
  match lh with
  | LH_base vs es => LH_base (vs ++ l1) (l2 ++ es)
  | LH_rec vs m es' lh' es => LH_rec vs m es' (frame_base lh' l1 l2) es
  end.

Fixpoint pull_base (lh : lholed) :=
  match lh with
  | LH_base vs es => (LH_base [] [], vs, es)
  | LH_rec vs m es' lh' es => let '(lh'',l1,l2) := pull_base lh' in
                             (LH_rec vs m es' lh'' es,l1,l2)
  end.

Lemma lfilledInd_push i : ∀ lh n es' es LI l1 l2,
  const_list l1 ->
  lfilledInd i lh ([::AI_label n es' (l1 ++ es ++ l2)]) LI ->
  lfilledInd (S i) (push_base lh n es' l1 l2) es LI.
Proof.
  induction i.
  all: intros lh n es' es LI l1 l2 Hconst Hfill.
  { inversion Hfill;subst.
    constructor. auto. constructor. auto.
    (* apply lfilled_Ind_Equivalent. cbn. rewrite eqseqE app_nil_r. done.  *)}
  { inversion Hfill;subst. simpl. constructor. auto.
    apply IHi. auto. auto. }
Qed.
Lemma lfilledInd_frame i : ∀ lh l1 es l2 LI,
    const_list l1 ->
    lfilledInd i lh (l1 ++ es ++ l2) LI ->
    lfilledInd i (frame_base lh l1 l2) (es) LI.
Proof.
  induction i.
  all: intros lh l1 es l2 LI Hconst Hfill.
  { inversion Hfill;subst.
    assert (vs ++ (l1 ++ es ++ l2) ++ es'
            = (vs ++ l1) ++ es ++ (l2 ++ es'))%SEQ as ->.
    { repeat erewrite app_assoc. auto. }
    constructor. apply const_list_concat;auto. }
  { inversion Hfill;subst. simpl. constructor. auto.
    apply IHi. auto. auto. }
Qed.
Lemma lfilledInd_pull i : ∀ lh es LI,
    lfilledInd i lh (es) LI ->
    let '(lh',l1,l2) := pull_base lh in lfilledInd i lh' (l1++es++l2) LI.
Proof.
  induction i.
  all: intros lh es LI Hfill.
  { inversion Hfill;subst.
    simpl. apply lfilled_Ind_Equivalent. cbn.
    rewrite app_nil_r. rewrite eqseqE. apply eq_refl. }
  { inversion Hfill;subst. simpl.
    apply IHi in H1.
    destruct (pull_base lh') as [[lh'' l1] l2].
    constructor;auto. }
Qed.
      
(* Structural lemmas for contexts *)

Lemma wp_base_push (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es l1 l2 i lh :
  const_list l1 ->
  WP es @ s; E CTX i; frame_base lh l1 l2 {{ Φ }}
  ⊢ WP l1 ++ es ++ l2 @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hconst) "HWP".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  apply lfilledInd_frame in Hfill.
  iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
  iPureIntro. by apply lfilled_Ind_Equivalent. auto.
Qed.
Lemma wp_base_pull (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es i lh :
  (let '(lh',l1,l2) := pull_base lh in WP l1 ++ es ++ l2 @ s; E CTX i; lh' {{ Φ }})
  ⊢ WP es @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros "HWP".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  apply lfilledInd_pull in Hfill.
  destruct (pull_base lh) as [[lh' l1] l2].
  iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
  iPureIntro. by apply lfilled_Ind_Equivalent.
Qed.
Lemma wp_label_push (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es i lh n es' l1 l2 :
  const_list l1 ->
  WP es @ s; E CTX S i; push_base lh n es' l1 l2 {{ Φ }}
  ⊢ WP [::AI_label n es' (l1 ++ es ++ l2)] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hconst) "HWP".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  apply lfilledInd_push in Hfill.
  iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
  iPureIntro. by apply lfilled_Ind_Equivalent. auto.
Qed.
Lemma wp_label_push_nil (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es i lh n es' :
  WP es @ s; E CTX S i; push_base lh n es' [] [] {{ Φ }}
  ⊢ WP [::AI_label n es' es] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros "HWP".
  iDestruct (wp_label_push with "HWP") as "HWP". auto.
  erewrite app_nil_l. erewrite app_nil_r. done.
Qed.

(* Structural lemmas for contexts within a local scope *)

Lemma wp_base_push_local (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es l1 l2 i lh n f :
  const_list l1 ->
  WP es @ s; E FRAME n; f CTX i; frame_base lh l1 l2 {{ v, Φ v }}
  ⊢ WP l1 ++ es ++ l2 @ s; E FRAME n; f CTX i; lh {{ v, Φ v }}.
Proof.
  iIntros (Hconst) "HWP".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  apply lfilledInd_frame in Hfill.
  iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
  iPureIntro. by apply lfilled_Ind_Equivalent. auto.
Qed.
Lemma wp_label_push_local (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es i lh n es' l1 l2 m f :
  const_list l1 ->
  WP es @ s; E FRAME m; f CTX S i; push_base lh n es' l1 l2 {{ v, Φ v }}
  ⊢ WP [::AI_label n es' (l1 ++ es ++ l2)] @ s; E FRAME m; f CTX i; lh {{ v, Φ v }}.
Proof.
  iIntros (Hconst) "HWP".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  apply lfilledInd_push in Hfill.
  iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
  iPureIntro. by apply lfilled_Ind_Equivalent. auto.
Qed.
Lemma wp_label_push_nil_local (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es i lh n es' m f :
  WP es @ s; E FRAME m; f CTX S i; push_base lh n es' [] [] {{ v, Φ v }}
  ⊢ WP [::AI_label n es' es] @ s; E FRAME m; f CTX i; lh {{ v, Φ v }}.
Proof.
  iIntros "HWP".
  iDestruct (wp_label_push_local with "HWP") as "HWP". auto.
  erewrite app_nil_l. erewrite app_nil_r. done.
Qed.

Lemma wp_block_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (i : nat) (lh : lholed) vs t1s t2s es n m f0:
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_label m [::] (vs ++ to_e_list es)] @ s; E CTX i; lh {{ Φ }})
  -∗ WP (vs ++ [::AI_basic (BI_block (Tf t1s t2s) es)]) @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hconst Hn Hn' Hm) "Hf0 HWP".
  iIntros (LI Hfill).
  destruct (iris.to_val LI) eqn:Hcontr.
  { apply lfilled_to_val in Hfill as [v' Hv];eauto.
    assert (iris.to_val [AI_basic (BI_block (Tf t1s t2s) es)] = None) as Hnone;auto.
    apply (to_val_cat_None2 vs) in Hnone;auto.
    rewrite Hv in Hnone. done. }
  unfold wp_wasm_ctx.
  iApply wp_unfold.
  repeat rewrite /wp_pre/=.
  rewrite Hcontr.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  { iPureIntro. destruct s;auto.
    apply lfilled_swap with (es':=[::AI_label m [::] (vs ++ to_e_list es)]) in Hfill as Hfill'.
    destruct Hfill' as [LI' Hfill'].
    eexists [],_,σ,[]. simpl.
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple. eapply rs_block.
    apply Hconst. apply Hn. apply Hn'. apply Hm. eauto. eauto. }
  destruct σ as [[[hs ws] locs] inst] => //=.
  iApply fupd_mask_intro;[solve_ndisj|].
  iIntros "Hcls" (es1 σ2 efs HStep) "!>!>!>".
  iMod "Hcls". iModIntro.
  destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
  apply lfilled_swap with (es':=[::AI_label m [::] (vs ++ to_e_list es)]) in Hfill as Hfill'.
  destruct Hfill' as [LI' Hfill'].
  destruct HStep as [H [-> ->]].
  iApply bi.sep_exist_l.
  eapply reduce_det in H as [H | [[i0 Hstart] | [ (a & cl & tf & h & i0 & Hstart & Hstart1 & Hstart2) |
                                               (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
    try by assert (lfilled 0 (LH_base vs []) [AI_basic (BI_block (Tf t1s t2s) es)]
                  (vs ++ [AI_basic (BI_block (Tf t1s t2s) es)])) ;
    first (unfold lfilled, lfill ; rewrite Hconst ; by rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfill''] ;
    eapply lfilled_implies_starts in Hfill'' ; (try done) ;
    rewrite Hfill'' in Hstart ; inversion Hstart => //=.
  2: { eapply r_label. apply r_simple. eapply rs_block;eauto. all: eauto. }
  inversion H; subst; clear H.
  iExists f0.
  iFrame. iSplit => //.
  iIntros "Hf0".
  iSpecialize ("HWP" with "[$]").
  by iSpecialize ("HWP" with "[%]").
Qed.
  
Lemma wp_block_local_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (i : nat) (lh : lholed) vs t1s t2s es n m n1 f1 f0 :
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_label m [::] (vs ++ to_e_list es)] @ s; E FRAME n1; f1 CTX i; lh {{ v, Φ v }})
  -∗ WP (vs ++ [::AI_basic (BI_block (Tf t1s t2s) es)]) @ s; E FRAME n1; f1 CTX i; lh {{ v, Φ v }}.
Proof.
  iIntros (Hconst Hn Hn' Hm) "Hf0 HWP".
  iIntros (LI Hfill).
  destruct (iris.to_val LI) eqn:Hcontr.
  { apply lfilled_to_val in Hfill as [v' Hv];eauto.
    assert (iris.to_val [AI_basic (BI_block (Tf t1s t2s) es)] = None) as Hnone;auto.
    apply (to_val_cat_None2 vs) in Hnone;auto.
    rewrite Hv in Hnone. done. }
  unfold wp_wasm_ctx.
  iApply wp_unfold.
  repeat rewrite /wp_pre/=.
  (* rewrite Hcontr. *)
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  { iPureIntro. destruct s;auto.
    apply lfilled_swap with (es':=[::AI_label m [::] (vs ++ to_e_list es)]) in Hfill as Hfill'.
    destruct Hfill' as [LI' Hfill'].
    eexists [],_,σ,[]. simpl.
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //. eapply r_local.
    eapply r_label. apply r_simple. eapply rs_block.
    apply Hconst. apply Hn. apply Hn'. apply Hm. eauto. eauto. }
  destruct σ as [[[hs ws] locs] inst] => //=.
  iApply fupd_mask_intro;[solve_ndisj|].
  iIntros "Hcls" (es1 σ2 efs HStep) "!>!>!>".
  iMod "Hcls". iModIntro.
  destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
  apply lfilled_swap with (es':=[::AI_label m [::] (vs ++ to_e_list es)]) in Hfill as Hfill'.
  destruct Hfill' as [LI' Hfill'].
  destruct HStep as [H [-> ->]].
  assert (first_instr [AI_local n1 f1 LI] = Some (AI_basic (BI_block (Tf t1s t2s) es),S (0 + i))) as HH.
  { apply first_instr_local. eapply starts_with_lfilled;[|apply Hfill].
    apply first_instr_const;auto. }
  iApply bi.sep_exist_l.
  eapply reduce_det in H as [H | [[i0 Hstart] | [ (a & cl & tf & h & i0 & Hstart & Hstart1 & Hstart2) |
                                               (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
    try congruence;
    try by assert (lfilled 0 (LH_base vs []) [AI_basic (BI_block (Tf t1s t2s) es)]
                  (vs ++ [AI_basic (BI_block (Tf t1s t2s) es)])) ;
    first (unfold lfilled, lfill ; rewrite Hconst ; by rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfill''] ;
    eapply lfilled_implies_starts in Hfill'' ; (try done) ;
    rewrite Hfill'' in Hstart ; inversion Hstart => //=.
  2: { eapply r_local. eapply r_label. apply r_simple. eapply rs_block;eauto. all: eauto. }
  inversion H; subst; clear H.
  all: iExists f0.
  all: iFrame. iSplit => //.
  iIntros "Hf0".
  iSpecialize ("HWP" with "[$]").
  by iSpecialize ("HWP" with "[%]").
Qed.

Lemma wp_br_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n vs es i lh vs' es' f0:
  const_list vs ->
  length vs = n ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP (vs' ++ vs ++ es ++ es') @ s; E {{ Φ }})
  -∗ WP vs ++ [::AI_basic (BI_br i)] @ s; E CTX S i; LH_rec vs' n es lh es' {{ Φ }}.
Proof.
  iIntros (Hvs Hlen) "Hf0 HΦ".
  iIntros (LI Hfill).
  destruct (iris.to_val LI) eqn:Hcontr.
  { exfalso. eapply lfilled_to_val_0 in Hfill;eauto. lia. }
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  { apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;subst.
    iPureIntro. destruct s;auto.
    apply lfilled_Ind_Equivalent in H8 as Hfill'.
    apply lfilled_swap with (es':=vs ++ es) in Hfill' as Hfill''.
    destruct Hfill'' as [LI' Hfill''].    
    eexists [],_,σ,[].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.   
    eapply r_label with (lh:=(LH_base vs' es')).
    2: { erewrite cons_middle. apply lfilled_Ind_Equivalent.
         econstructor;auto. }
    2: { apply lfilled_Ind_Equivalent. econstructor;auto. }
    apply r_simple. eapply rs_br.
    apply Hvs. auto. eauto. }
  destruct σ as [[[hs ws] locs] inst] => //=.
  iApply fupd_mask_intro;[solve_ndisj|].
  iIntros "Hcls !>" (es1 σ2 efs HStep).
  iMod "Hcls". iModIntro.
  destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
  apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;subst.
  apply lfilled_Ind_Equivalent in H8 as Hfill'.
  apply lfilled_swap with (es':=vs ++ es) in Hfill' as Hfill''.
  destruct Hfill'' as [LI' Hfill''].    
  destruct HStep as [H [-> ->]].
  iApply bi.sep_exist_l.
  eapply reduce_det in H as [H | [[i0 Hstart] | [ (a & cl & tf & h & i0 & Hstart & Hstart1 & Hstart2) |
                                               (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
    try by apply lfilled_Ind_Equivalent in Hfill ;
    assert (lfilled 0 (LH_base vs []) [AI_basic (BI_br i)]
                    (vs ++ [AI_basic (BI_br i)])) ;
    first (unfold lfilled, lfill ; rewrite Hvs ; by rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
    eapply lfilled_implies_starts in Hfilln ; (try done) ;
    rewrite Hfilln in Hstart ; inversion Hstart => //=. 
  2: { eapply r_label with (lh:=(LH_base vs' es')).
       2: { apply lfilled_Ind_Equivalent.
            econstructor;auto. }
       2: { apply lfilled_Ind_Equivalent. econstructor;auto. }
       apply r_simple. eapply rs_br. apply Hvs. all:eauto. }
  inversion H; subst; clear H.
  iExists f0.
  iFrame. iSplit => //.
  iIntros "Hf0".
  iSpecialize ("HΦ" with "[$]").
  by erewrite !app_assoc.
Qed.

Lemma wp_br_local_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n vs es i lh vs' es' f0 n1 f1 :
  const_list vs ->
  length vs = n ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP (vs' ++ vs ++ es ++ es') @ s; E FRAME n1; f1 {{ v, Φ v }})
  -∗ WP vs ++ [::AI_basic (BI_br i)] @ s; E FRAME n1; f1 CTX S i; LH_rec vs' n es lh es' {{ v, Φ v }}.
Proof.
  iIntros (Hvs Hlen) "Hf0 HΦ".
  iIntros (LI Hfill).
  destruct (iris.to_val LI) eqn:Hcontr.
  { exfalso. eapply lfilled_to_val_0 in Hfill;eauto. lia. }
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  { apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;subst.
    iPureIntro. destruct s;auto.
    apply lfilled_Ind_Equivalent in H8 as Hfill'.
    apply lfilled_swap with (es':=vs ++ es) in Hfill' as Hfill''.
    destruct Hfill'' as [LI' Hfill''].    
    eexists [],_,σ,[].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //. eapply r_local.
    eapply r_label with (lh:=(LH_base vs' es')).
    2: { erewrite cons_middle. apply lfilled_Ind_Equivalent.
         econstructor;auto. }
    2: { apply lfilled_Ind_Equivalent. econstructor;auto. }
    apply r_simple. eapply rs_br.
    apply Hvs. auto. eauto. }
  destruct σ as [[[hs ws] locs] inst] => //=.
  iApply fupd_mask_intro;[solve_ndisj|].
  iIntros "Hcls !>" (es1 σ2 efs HStep).
  iMod "Hcls". iModIntro.
  destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
  apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;subst.
  apply lfilled_Ind_Equivalent in H8 as Hfill'.
  apply lfilled_swap with (es':=vs ++ es) in Hfill' as Hfill''.
  destruct Hfill'' as [LI' Hfill''].    
  destruct HStep as [H [-> ->]].
  assert (first_instr [AI_local n1 f1 (vs' ++ [AI_label (length vs) es LI0] ++ es')] 
     = Some (AI_basic (BI_br i),S (0 + S i))) as HH.
  { apply lfilled_Ind_Equivalent in Hfill.
    apply first_instr_local. eapply starts_with_lfilled;[|apply Hfill].
    apply first_instr_const;auto. }
  iApply bi.sep_exist_l.
  eapply reduce_det in H as [H | [[i0 Hstart] | [ (a & cl & tf & h & i0 & Hstart & Hstart1 & Hstart2) |
                                               (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
    try congruence;
    try by apply lfilled_Ind_Equivalent in Hfill ;
    assert (lfilled 0 (LH_base vs []) [AI_basic (BI_br i)]
                    (vs ++ [AI_basic (BI_br i)])) ;
    first (unfold lfilled, lfill ; rewrite Hvs ; by rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
    eapply lfilled_implies_starts in Hfilln ; (try done) ;
    rewrite Hfilln in Hstart ; inversion Hstart => //=. 
  2: { eapply r_local.
       eapply r_label with (lh:=(LH_base vs' es')).
       2: { apply lfilled_Ind_Equivalent.
            econstructor;auto. }
       2: { apply lfilled_Ind_Equivalent. econstructor;auto. }
       apply r_simple. eapply rs_br. apply Hvs. all:eauto. }
  inversion H; subst; clear H.
  iExists f0.
  iFrame. iSplit => //.
  iIntros "Hf0".
  iSpecialize ("HΦ" with "[$]").
  by erewrite !app_assoc.
Qed.

Lemma wp_loop_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs es n m t1s t2s i lh f0:
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_label n [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)] @ s; E CTX i; lh {{ Φ }})
  -∗ WP vs ++ [::AI_basic (BI_loop (Tf t1s t2s) es)] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hvs Hn Hn' Hm) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill].
    assert (iris.to_val [AI_basic (BI_loop (Tf t1s t2s) es)] = None) as HH;auto.
    apply (to_val_cat_None2 vs) in HH;auto. rewrite Hfill in HH. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. eapply rs_loop;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    iApply bi.sep_exist_l.
    eapply reduce_det in H as [H | [[i0 Hstart] | [ (a & cl & tf & h & i0 & Hstart & Hstart1 & Hstart2) |
                                               (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
    try by assert (lfilled 0 (LH_base vs []) [AI_basic (BI_loop (Tf t1s t2s) es)]
                  (vs ++ [AI_basic (BI_loop (Tf t1s t2s) es)])) ;
    first (unfold lfilled, lfill ; rewrite Hvs ; by rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfill''] ;
    eapply lfilled_implies_starts in Hfill'' ; (try done) ;
    rewrite Hfill'' in Hstart ; inversion Hstart => //=.
    2: { eapply r_label. apply r_simple;eauto. eapply rs_loop;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
  iExists f0.
  iFrame. iSplit => //.
  iIntros "Hf0".
  iSpecialize ("HP" with "[$]").
  by iSpecialize ("HP" with "[%]").
Qed.

Lemma wp_loop_local_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs es n m t1s t2s i lh f0 n1 f1 :
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_label n [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)] @ s; E FRAME n1; f1 CTX i; lh {{ v, Φ v }})
  -∗ WP vs ++ [::AI_basic (BI_loop (Tf t1s t2s) es)] @ s; E FRAME n1; f1 CTX i; lh {{ v, Φ v }}.
Proof.
  iIntros (Hvs Hn Hn' Hm) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  (* { destruct (iris.to_val LI) eqn:Hcontr;auto. *)
  (*   apply lfilled_to_val in Hfill;eauto. *)
  (*   destruct Hfill as [? Hfill]. *)
  (*   assert (iris.to_val [AI_basic (BI_loop (Tf t1s t2s) es)] = None) as HH;auto. *)
  (*   apply (to_val_cat_None2 vs) in HH. rewrite Hfill in HH. done. } *)
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], _, σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //. eapply r_local.
    eapply r_label. apply r_simple;eauto. eapply rs_loop;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    iApply bi.sep_exist_l.
    assert (first_instr [AI_local n1 f1 LI] = Some (AI_basic (BI_loop (Tf t1s t2s) es),S (0 + i))) as HH.
    { apply first_instr_local. eapply starts_with_lfilled;[|apply Hfill].
      apply first_instr_const. auto. }
    eapply reduce_det in H as [H | [[i0 Hstart] | [ (a & cl & tf & h & i0 & Hstart & Hstart1 & Hstart2) |
                                               (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
      try congruence;
      try by assert (lfilled 0 (LH_base vs []) [AI_basic (BI_loop (Tf t1s t2s) es)]
                  (vs ++ [AI_basic (BI_loop (Tf t1s t2s) es)])) ;
    first (unfold lfilled, lfill ; rewrite Hvs ; by rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfill''] ;
    eapply lfilled_implies_starts in Hfill'' ; (try done) ;
    rewrite Hfill'' in Hstart ; inversion Hstart => //=.
    2: { eapply r_local. eapply r_label. apply r_simple;eauto. eapply rs_loop;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
  iExists f0.
  iFrame. iSplit => //.
  iIntros "Hf0".
  iSpecialize ("HP" with "[$]").
  by iSpecialize ("HP" with "[%]").
Qed.

Lemma wp_loop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs es n m t1s t2s f0:
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_label n [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)] @ s; E {{ Φ }})
  -∗ WP vs ++ [::AI_basic (BI_loop (Tf t1s t2s) es)] @ s; E {{ Φ }}.
Proof.
  iIntros (Hvs Hn Hn' Hm) "Hf0 HP".
  iApply wp_wasm_empty_ctx. iApply (wp_loop_ctx with "[$]") => //.
  iNext.
  iIntros "?"; iSpecialize ("HP" with "[$]").
  by iApply wp_wasm_empty_ctx. 
Qed.

Lemma wp_if_true_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s i lh f0:
  n ≠ Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_block tf e1s)] @ s; E CTX i; lh {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hn) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. eapply rs_if_true;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    rename tf into tf'.
    iApply bi.sep_exist_l.
    only_one_reduction H.
    + iExists f0.
      iFrame.
      iIntros "?"; iSpecialize ("HP" with "[$]").
      by iApply "HP".
    all: by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 n))] [])
                    [AI_basic (BI_if tf' e1s e2s)]
                    [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf' e1s e2s)]) ;
      first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
    eapply lfilled_implies_starts in Hfilln => //= ;
    rewrite Hfilln in Hstart ; inversion Hstart.
Qed.

Lemma wp_if_true_local_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s i lh f0 n1 f1 :
  n ≠ Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_block tf e1s)] @ s; E FRAME n1; f1 CTX i; lh {{ v, Φ v }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E FRAME n1; f1 CTX i; lh {{ v, Φ v }}.
Proof.
  iIntros (Hn) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], _, σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //. eapply r_local.
    eapply r_label. apply r_simple;eauto. eapply rs_if_true;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    iApply bi.sep_exist_l.
    assert (first_instr [AI_local n1 f1 LI] = Some (AI_basic (BI_if tf e1s e2s),S (0 + i))) as HH.
    { apply first_instr_local. eapply starts_with_lfilled;[|apply Hfill]. auto. }
    eapply reduce_det in H as [H | [[i0 Hstart] | [ (a & cl & tf' & h & i0 & Hstart & Hstart1 & Hstart2) |
                                               (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
      try congruence;
      try by assert (lfilled 0 (LH_base vs []) [AI_basic (BI_loop (Tf t1s t2s) es)]
                             (vs ++ [AI_basic (BI_loop (Tf t1s t2s) es)])) ;
      first (unfold lfilled, lfill ; rewrite Hvs ; by rewrite app_nil_r) ;
      destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfill''] ;
      eapply lfilled_implies_starts in Hfill'' ; (try done) ;
      rewrite Hfill'' in Hstart ; inversion Hstart => //=.
    2: { eapply r_local. eapply r_label. apply r_simple;eauto. eapply rs_if_true;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    iExists f0.
    iFrame. iSplit => //.
    iIntros "Hf0".
    iSpecialize ("HP" with "[$]").
    by iSpecialize ("HP" with "[%]").
Qed.

Lemma wp_if_true (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s f0:
  n ≠ Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_block tf e1s)] @ s; E {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E {{ Φ }}.
Proof.
  iIntros (?) "Hf0 HP".
  iApply wp_wasm_empty_ctx. iApply (wp_if_true_ctx with "[$]");eauto.
  iNext. iIntros "?"; iSpecialize ("HP" with "[$]").
  by iApply wp_wasm_empty_ctx.
Qed.
  
Lemma wp_if_false_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s i lh f0:
  n = Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_block tf e2s)] @ s; E CTX i; lh {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hn) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. eapply rs_if_false;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    iApply bi.sep_exist_l.
    eapply reduce_det in H as [H | [[i0 Hstart] | [ (a & cl & tf' & h & i0 & Hstart & Hstart1 & Hstart2) |
                                               (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
    try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 n))] [])
                    [AI_basic (BI_if tf e1s e2s)]
                    [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf e1s e2s)]) ;
      first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
    eapply lfilled_implies_starts in Hfilln => //= ;
    rewrite Hfilln in Hstart ; inversion Hstart.
    2: { eapply r_label. apply r_simple;eauto. eapply rs_if_false;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    iExists f0.
    iFrame.
    iSplit => //.
    iIntros "?"; iSpecialize ("HP" with "[$]").
    by iApply "HP".
Qed.

Lemma wp_if_false_local_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s i lh f0 n1 f1 :
  n = Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_block tf e2s)] @ s; E FRAME n1; f1 CTX i; lh {{ v, Φ v }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E FRAME n1; f1 CTX i; lh {{ v, Φ v }}.
Proof.
  iIntros (Hn) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], _, σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //. eapply r_local.
    eapply r_label. apply r_simple;eauto. eapply rs_if_false;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    assert (first_instr [AI_local n1 f1 LI] = Some (AI_basic (BI_if tf e1s e2s),S (0 + i))) as HH.
    { apply first_instr_local. eapply starts_with_lfilled;[|apply Hfill];auto. }
    iApply bi.sep_exist_l.
    eapply reduce_det in H as [H | [[i0 Hstart] | [ (a & cl & tf' & h & i0 & Hstart & Hstart1 & Hstart2) |
                                               (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
      try congruence;
      try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 n))] [])
                    [AI_basic (BI_if tf e1s e2s)]
                    [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf e1s e2s)]) ;
      first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
    eapply lfilled_implies_starts in Hfilln => //= ;
    rewrite Hfilln in Hstart ; inversion Hstart.
    2: { eapply r_local. eapply r_label. apply r_simple;eauto. eapply rs_if_false;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    iExists f0.
    iFrame.
    iSplit => //.
    iIntros "?"; iSpecialize ("HP" with "[$]").
    by iApply "HP".
Qed.

Lemma wp_if_false (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s f0:
  n = Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_block tf e2s)] @ s; E {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E {{ Φ }}.
Proof.
  iIntros (?) "Hf0 HP".
  iApply wp_wasm_empty_ctx. iApply (wp_if_false_ctx with "[$]");eauto.
  iNext. iIntros "?". iApply wp_wasm_empty_ctx.
  by iApply "HP".
Qed.

Lemma wp_br_if_true_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n i j lh f0:
  n ≠ Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_br i)] @ s; E CTX j; lh {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] @ s; E CTX j; lh {{ Φ }}.
Proof.
  iIntros (Hn) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. eapply rs_br_if_true;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    iApply bi.sep_exist_l.
    only_one_reduction H ;
    try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 n))] [])
                    [AI_basic (BI_br_if i)]
                    [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_br_if i)]) ;
      first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
    eapply lfilled_implies_starts in Hfilln => //= ;
    rewrite Hfilln in Hstart ; inversion Hstart.
    iExists f0; iFrame.
    iIntros "?". by iApply ("HP" with "[$]").
Qed.

Lemma wp_br_if_true_local_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n i j lh f0 n1 f1 :
  n ≠ Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_br i)] @ s; E FRAME n1; f1 CTX j; lh {{ v, Φ v }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] @ s; E FRAME n1; f1 CTX j; lh {{ v, Φ v }}.
Proof.
  iIntros (Hn) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], _, σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //. eapply r_local.
    eapply r_label. apply r_simple;eauto. eapply rs_br_if_true;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    assert (first_instr [AI_local n1 f1 LI] = Some (AI_basic (BI_br_if i),S (0 + j))) as HH.
    { apply first_instr_local. eapply starts_with_lfilled;[|apply Hfill];auto. }
    iApply bi.sep_exist_l.
    eapply reduce_det in H as [H | [[i0 Hstart] | [ (a & cl & tf' & h & i0 & Hstart & Hstart1 & Hstart2) |
                                               (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
      try congruence;
      try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 n))] [])
                    [AI_basic (BI_if tf e1s e2s)]
                    [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf e1s e2s)]) ;
      first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
    eapply lfilled_implies_starts in Hfilln => //= ;
    rewrite Hfilln in Hstart ; inversion Hstart.
    2: { eapply r_local. eapply r_label. apply r_simple;eauto. eapply rs_br_if_true;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    iExists f0.
    iFrame.
    iSplit => //.
    iIntros "?"; iSpecialize ("HP" with "[$]").
    by iApply "HP".
Qed.

Lemma wp_br_if_true (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n i f0:
  n ≠ Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_br i)] @ s; E {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] @ s; E {{ Φ }}.
Proof.
  iIntros (?) "Hf0 HP".
  iApply wp_wasm_empty_ctx. iApply (wp_br_if_true_ctx with "[$]");eauto.
  iNext. iIntros "?". iApply wp_wasm_empty_ctx. by iApply ("HP" with "[$]").
Qed.

(* The following expression reduces to a value reguardless of context, 
   and thus does not need a context aware version *)
Lemma wp_br_if_false (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n i f0:
  n = Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷ Φ (immV [])
  -∗ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hn) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_br_if_false.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H. iFrame.
Qed.


Lemma wp_br_table_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i j k lh f0:
  ssrnat.leq (S (Wasm_int.nat_of_uint i32m c)) (length iss) ->
  List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_br j)] @ s; E CTX k; lh {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E CTX k; lh {{ Φ }}.
Proof.
  iIntros (Hiss Hj) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. apply rs_br_table;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    iApply bi.sep_exist_l.
    only_one_reduction H ;
     try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 c))] [])
                    [AI_basic (BI_br_table iss i)]
                    [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_br_table iss i)]) ;
      first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
    eapply lfilled_implies_starts in Hfilln => //= ;
    rewrite Hfilln in Hstart ; inversion Hstart.
    iExists f0; iFrame.
    iIntros "?"; by iApply ("HP" with "[$]").
Qed.
Lemma wp_br_table_local_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i j k lh f0 n1 f1 :
  ssrnat.leq (S (Wasm_int.nat_of_uint i32m c)) (length iss) ->
  List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_br j)] @ s; E FRAME n1; f1 CTX k; lh {{ v, Φ v }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E FRAME n1; f1 CTX k; lh {{ v, Φ v }}.
Proof.
  iIntros (Hiss Hj) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], _, σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //. eapply r_local.
    eapply r_label. apply r_simple;eauto. apply rs_br_table;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    assert (first_instr [AI_local n1 f1 LI] = Some (AI_basic (BI_br_table iss i),S (0 + k))) as HH.
    { apply first_instr_local. eapply starts_with_lfilled;[|apply Hfill];auto. }
    iApply bi.sep_exist_l.
    eapply reduce_det in H as [H | [[i0 Hstart] | [ (a & cl & tf' & h & i0 & Hstart & Hstart1 & Hstart2) |
                                               (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
      try congruence;
      try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 n))] [])
                    [AI_basic (BI_if tf e1s e2s)]
                    [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf e1s e2s)]) ;
      first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
    eapply lfilled_implies_starts in Hfilln => //= ;
    rewrite Hfilln in Hstart ; inversion Hstart.
    2: { eapply r_local. eapply r_label. apply r_simple;eauto. eapply rs_br_table;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    iExists f0.
    iFrame.
    iSplit => //.
    iIntros "?"; iSpecialize ("HP" with "[$]").
    by iApply "HP".
Qed.
Lemma wp_br_table (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i j f0:
  ssrnat.leq (S (Wasm_int.nat_of_uint i32m c)) (length iss) ->
  List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_br j)] @ s; E {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E {{ Φ }}.
Proof.
  iIntros (? ?) "Hf0 HP".
  iApply wp_wasm_empty_ctx. iApply (wp_br_table_ctx with "[$]");eauto.
  iNext. iIntros "?". iApply wp_wasm_empty_ctx. by iApply ("HP" with "[$]"). 
Qed.

Lemma wp_br_table_length_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i j lh f0:
  ssrnat.leq (length iss) (Wasm_int.nat_of_uint i32m c) ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_br i)] @ s; E CTX j; lh {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E CTX j; lh {{ Φ }}.
Proof.
  iIntros (Hiss) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. apply rs_br_table_length;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    iApply bi.sep_exist_l.
    only_one_reduction H ;
     try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 c))] [])
                    [AI_basic (BI_br_table iss i)]
                    [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_br_table iss i)]) ;
      first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
    eapply lfilled_implies_starts in Hfilln => //= ;
    rewrite Hfilln in Hstart ; inversion Hstart.
    iExists f0; iFrame.
    iIntros "?"; by iApply ("HP" with "[$]").
Qed.
Lemma wp_br_table_length_local_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i j lh f0 n1 f1 :
  ssrnat.leq (length iss) (Wasm_int.nat_of_uint i32m c) ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_br i)] @ s; E FRAME n1; f1 CTX j; lh {{ v, Φ v }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E FRAME n1; f1 CTX j; lh {{ v, Φ v }}.
Proof.
  iIntros (Hiss) "Hf0 HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], _, σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //. eapply r_local.
    eapply r_label. apply r_simple;eauto. apply rs_br_table_length;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    assert (first_instr [AI_local n1 f1 LI] = Some (AI_basic (BI_br_table iss i),S (0 + j))) as HH.
    { apply first_instr_local. eapply starts_with_lfilled;[|apply Hfill];auto. }
    iApply bi.sep_exist_l.
    eapply reduce_det in H as [H | [[i0 Hstart] | [ (a & cl & tf' & h & i0 & Hstart & Hstart1 & Hstart2) |
                                               (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
      try congruence;
      try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 n))] [])
                    [AI_basic (BI_if tf e1s e2s)]
                    [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf e1s e2s)]) ;
      first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
    destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
    eapply lfilled_implies_starts in Hfilln => //= ;
    rewrite Hfilln in Hstart ; inversion Hstart.
    2: { eapply r_local. eapply r_label. apply r_simple;eauto. eapply rs_br_table_length;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    iExists f0.
    iFrame.
    iSplit => //.
    iIntros "?"; iSpecialize ("HP" with "[$]").
    by iApply "HP".
Qed.
Lemma wp_br_table_length (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i f0:
  ssrnat.leq (length iss) (Wasm_int.nat_of_uint i32m c) ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP [::AI_basic (BI_br i)] @ s; E {{ Φ }})
  -∗ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E {{ Φ }}.
Proof.
  iIntros (?) "Hf0 HP".
  iApply wp_wasm_empty_ctx. iApply (wp_br_table_length_ctx with "[$]");eauto.
  iNext. iIntros "?". iApply wp_wasm_empty_ctx. by iApply ("HP" with "[$]").
Qed.

End control_rules.
