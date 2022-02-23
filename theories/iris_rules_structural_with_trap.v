From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris_wp_def iris_properties iris_rules_trap iris_rules_structural iris_rules_control stdpp_aux.
Require Export datatypes host operations properties opsem.



(* empty lists, frame and context rules *)

Close Scope byte_scope.

Section structural_rules.
Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}.

Fixpoint get_layer lh i :=
  match lh,i with
  | LH_base vs es, _ => None
  | LH_rec vs' n es lh' es', 0 => Some (vs',n,es,lh',es')
  | LH_rec _ _ _ lh' _, S n => get_layer lh' n
  end.

Definition delete_outer lh :=
  match lh with
  | LH_base _ _ => lh
  | LH_rec vs n es lh es' => lh
  end.
                
Inductive lh_minus_Ind : lholed -> lholed -> lholed -> Prop :=
| lh_minus_base lh : lh_minus_Ind lh (LH_base [] []) lh
| lh_minus_ind lh lh' lh'' vs n es es' :
  lh_minus_Ind lh lh' lh'' ->
  lh_minus_Ind (LH_rec vs n es lh es') (LH_rec vs n es lh' es') lh''.

Global Instance ai_list_eq_dec: EqDecision (seq.seq administrative_instruction).
Proof.
  eapply list_eq_dec.
  Unshelve.
  pose proof administrative_instruction_eq_dec. eauto.
Defined.
Global Instance ai_eq_dec: EqDecision (administrative_instruction).
Proof.
  pose proof administrative_instruction_eq_dec. eauto.
Defined.

Lemma ai_eq_true a a0 : administrative_instruction_eqb a a0 = true <-> a = a0.
Proof.
  split; by move/eqP.
Qed.

Lemma ai_eqseq_true (l1 l2 : seq.seq administrative_instruction) :
  l1 = l2 <-> (l1 == l2) = true.
Proof.
  split; by move/eqP.
Qed.
  
Lemma lh_minus_Ind_Equivalent lh lh' lh'' :
  lh_minus lh lh' = Some lh'' <->
  lh_minus_Ind lh lh' lh''.
Proof.
  revert lh lh''.
  induction lh';intros lh lh''.
  { split; intros Hlh.
    { unfold lh_minus in Hlh.
      destruct lh. destruct l,l0 =>//.
      simplify_eq. constructor.
      destruct l,l0 =>//.
      inversion Hlh;subst.
      constructor. }
    { inversion Hlh;simplify_eq.
      unfold lh_minus.
      destruct lh'';auto. }
  }
  { split;intros Hlh.
    { unfold lh_minus in Hlh.
      destruct lh. done.
      destruct (l2 == l) eqn:Hl1; [|cbn in Hlh;done].
      apply ai_eqseq_true in Hl1 as ->.
      destruct (decide (n0 = n));subst.
      2: { apply PeanoNat.Nat.eqb_neq in n1.
           rewrite n1 in Hlh. cbn in Hlh;done. }
      rewrite PeanoNat.Nat.eqb_refl /= in Hlh.
      destruct (l3 == l0) eqn:Hl2;[simpl in Hlh;apply ai_eqseq_true in Hl2 as ->|cbn in Hlh;done].
      destruct (l4 == l1) eqn:Hl3;[simpl in Hlh;apply ai_eqseq_true in Hl3 as ->|cbn in Hlh;done].
      constructor. apply IHlh'. auto.
    }
    { inversion Hlh. simpl. 
      rewrite !eq_refl PeanoNat.Nat.eqb_refl. cbn.
      apply IHlh';auto.
    }
  }
Qed.

Definition lh_delete_inner lh :=
  let '(lh',_) := empty_base lh in lh'.

Lemma lh_delete_inner_eq lh :
  base_is_empty lh ->
  lh_delete_inner lh = lh.
Proof.
  intros Hbase.
  induction lh.
  { inversion Hbase; subst; auto. }
  { simpl in Hbase. apply IHlh in Hbase.
    unfold lh_delete_inner in Hbase.
    destruct (empty_base lh) eqn:Hlh. simplify_eq.
    unfold lh_delete_inner. rewrite /= Hlh. auto. }
Qed.

Lemma base_is_empty_delete_inner lh :
  base_is_empty (lh_delete_inner lh).
Proof.
  induction lh.
  { simpl. auto. }
  { unfold lh_delete_inner.
    destruct (empty_base (LH_rec l n l0 lh l1)) eqn:Hl.
    inversion Hl. destruct (empty_base lh) eqn:Hlh. simplify_eq.
    simpl. unfold lh_delete_inner in IHlh.
    rewrite Hlh in IHlh. auto. }
Qed.

Lemma lh_minus_eq lh :
  lh_minus lh (LH_base [] []) = Some lh.
Proof.
  induction lh;simpl;auto.
Qed.
 
Lemma get_layer_lh_minus lh i vs' n es lh' es' :
  get_layer lh i = Some (vs', n, es, lh', es') -> ∃ lh'', lh_minus lh lh'' = Some lh'.
Proof.
  revert i vs' n es lh' es'.
  induction lh;intros i vs' m es lh' es' Hl;[done|].
  destruct i.  
  { inversion Hl;simplify_eq.
    exists (LH_rec vs' m es (LH_base [] []) es'). simpl.
    cbn. rewrite !eqseqE !eq_refl PeanoNat.Nat.eqb_refl. cbn.
    apply lh_minus_eq. }
  { inversion Hl.
    apply IHlh in H0. destruct H0 as [hl'' Hlh''].
    exists (LH_rec l n l0 hl'' l1).
    simpl. rewrite Hlh''.
    cbn. rewrite !eqseqE !eq_refl PeanoNat.Nat.eqb_refl. cbn. auto. }
Qed.

Lemma LH_rec_circular vs' m es lh es' : LH_rec vs' m es lh es' = lh -> False.
Proof.
  revert vs' m es es'.
  induction lh;intros vs' m es es' Hcontr;[done|].
  inversion Hcontr;subst.
  apply IHlh in H3. auto.
Qed.

Lemma lminus_base_inv lh lh' : lh_minus_Ind lh lh' lh -> lh' = LH_base [] [].
Proof.
  intros Hlh.
  inversion Hlh;auto.
  exfalso. simplify_eq.
  apply lh_minus_Ind_Equivalent in H.
  apply lh_minus_depth in H. simpl in H. lia.
Qed.
  
Lemma lminus_rec_inv vs' m es lh es' lh'' :
  lh_minus (LH_rec vs' m es lh es') lh'' = Some lh ->
  lh'' = LH_rec vs' m es (LH_base [] []) es'.
Proof.
  intros Hmin%lh_minus_Ind_Equivalent.
  inversion Hmin;subst.
  exfalso. eapply LH_rec_circular. eauto.
  f_equiv. eapply lminus_base_inv;eauto.
Qed.

Lemma get_layer_depth i lh x :
  get_layer lh i = Some x ->
  i < lh_depth lh.
Proof.
  revert i x;induction lh;intros i x Hlayer;[done|].
  destruct x,p,p,p.
  cbn in Hlayer.
  destruct i;simplify_eq.
  { simpl. lia. }
  { apply IHlh in Hlayer.
    simpl. lia. }
Qed.

Lemma get_layer_depth_lt i lh vs' n es lh' es' :
  get_layer lh i = Some (vs',n,es,lh',es') ->
  lh_depth lh' < lh_depth lh.
Proof.
  revert i vs' n es lh' es';induction lh;intros i vs' m es lh' es' Hlayer;[done|].
  cbn in Hlayer.
  destruct i;simplify_eq.
  { simpl. lia. }
  { apply IHlh in Hlayer.
    simpl. lia. }
Qed.

Lemma get_layer_circular lh i vs' m es es' :
  get_layer lh i = Some (vs', m, es, lh, es') ->
  False.
Proof.
  revert lh vs' m es es'.
  induction i;intros lh vs' m es es' Hlayer;auto.
  destruct lh;try done.
  simpl in Hlayer.
  simplify_eq.
  symmetry in H0.
  by apply LH_rec_circular in H0.
  apply get_layer_depth_lt in Hlayer. lia.
Qed.

Lemma get_layer_find i lh' :
  S i < (lh_depth lh') ->
  ∃ vs0' n0 es0 vs' n es lh es' es0' lh'',
    get_layer lh' (lh_depth lh' - (S (S i))) = Some (vs0', n0, es0, (LH_rec vs' n es lh es'), es0') ∧
      lh_minus lh' lh'' = Some (LH_rec vs' n es lh es').
Proof.
  revert i.
  induction lh';intros i Hlt.
  { simpl in Hlt. lia. }
  { destruct lh';[simpl in Hlt;lia|].
    destruct lh'.
    { simpl in Hlt. destruct i;[|lia]. simpl.
      do 9 eexists.
      eexists (LH_rec l n l0 (LH_base [] []) l1).
      split;eauto. rewrite !eq_refl PeanoNat.Nat.eqb_refl.
      cbn. auto. }
    { simpl. simpl in Hlt.
      destruct (decide (i = S (lh_depth lh'))).
      { subst i.
        rewrite PeanoNat.Nat.sub_diag.
        clear IHlh'.
        do 9 eexists.
        eexists (LH_rec l n l0 (LH_base [] []) l1).
        split;eauto.
        rewrite !eq_refl PeanoNat.Nat.eqb_refl. cbn. auto. }
      { assert (S i < S (S (lh_depth lh'))) as Hlt';[lia|].
        apply IHlh' in Hlt'.
        destruct Hlt' as [vs0' [n3 [es0 [vs' [m [es [lh [es' [es0' [lh'' [Heq Hmin]]]]]]]]]]].
        simpl in Heq.
        destruct (lh_depth lh' - i) eqn:Hi1.
        { rewrite Nat.sub_succ_l;[|lia]. rewrite Hi1.
          do 9 eexists.
          eexists (LH_rec l n l0 lh'' l1).
          split;[eauto|].
          rewrite !eq_refl PeanoNat.Nat.eqb_refl. cbn.
          auto. }
        { rewrite Nat.sub_succ_l;[|lia]. rewrite Hi1.
          destruct n4.
          { inversion Heq;subst. do 9 eexists.
            eexists (LH_rec l n l0 lh'' l1).
            split;eauto.
            rewrite !eq_refl !PeanoNat.Nat.eqb_refl. cbn. auto. }
          { do 9 eexists. eexists (LH_rec l n l0 lh'' l1).
            split;eauto.
            rewrite !eq_refl !PeanoNat.Nat.eqb_refl. cbn. auto. }
        }
      }      
    }
  }
Qed.
  
Lemma lfilled_minus lh' i vs' n es lh es' e LI j lh'' :
  lh_minus lh' lh'' = Some lh ->
  i < lh_depth lh' ->
  get_layer lh' (lh_depth lh' - S i) = Some (vs', n, es, lh, es') ->
  lfilled j lh' e LI ->
  ∃ LI', lfilled i lh e LI' ∧ lfilled (j - i) lh'' LI' LI.
Proof.
  intros Hlh%lh_minus_Ind_Equivalent.
  revert vs' n es es' i j e LI.
  induction Hlh;intros vs' m es2 es2' i j e LI Hle Hlayer Hfill.
  { apply get_layer_circular in Hlayer. done. }
  { simpl in *.
    destruct (lh_depth lh - i) eqn:Hi.
    { simplify_eq.
      assert (lh_depth lh'' = i);[lia|simplify_eq].
      apply lfilled_depth in Hfill as Heq. simpl in *;subst.
      apply lfilled_Ind_Equivalent in Hfill.
      inversion Hfill;simplify_eq.
      apply lfilled_Ind_Equivalent in H8.
      eexists. split;eauto.
      apply lfilled_Ind_Equivalent.
      assert (S (lh_depth lh'') - (lh_depth lh'') = S 0) as ->;[lia|].
      constructor;auto.
      apply lminus_base_inv in Hlh as ->.
      apply lfilled_Ind_Equivalent. cbn.
      erewrite app_nil_r. by apply/eqP.
    }
    { assert (lh_depth lh - S i = n0);[lia|simplify_eq].
      apply lfilled_Ind_Equivalent in Hfill.
      inversion Hfill;simplify_eq.
      apply lfilled_Ind_Equivalent in H8.
      eapply IHHlh in Hlayer as HLI';[|lia|eauto].
      destruct HLI' as [LI' [Hfill1 Hfill2]].
      assert (i <= k) as Hlei.
      { apply lh_minus_Ind_Equivalent in Hlh.
        apply lh_minus_depth in Hlh as Hd.
        apply lfilled_depth in Hfill1 as Hieq.
        apply lfilled_depth in Hfill2 as Hkeq.
        rewrite Hieq in Hd.
        rewrite Hkeq in Hd.
        simpl in *. lia. }
      exists LI'.
      split;auto. rewrite Nat.sub_succ_l;auto.
      apply lfilled_Ind_Equivalent. constructor;auto.
      apply lfilled_Ind_Equivalent. auto.
    }
  }
Qed.


Lemma wp_br_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n vs es i j lh lh' lh'' vs' es' f0 vs0' n0 es0 es0' :
  S i < j ->
  get_layer lh' (lh_depth lh' - (S (S i))) = Some (vs0', n0, es0, (LH_rec vs' n es lh es'), es0') ->
  lh_minus lh' lh'' = Some (LH_rec vs' n es lh es') ->
  const_list vs ->
  length vs = n ->
  ↪[frame] f0 -∗
  ▷ (↪[frame] f0 -∗ WP (vs' ++ (vs ++ es) ++ es') @ s; E CTX j - S i ; lh'' {{ Φ }})
  -∗ WP vs ++ [::AI_basic (BI_br i)] @ s; E CTX j ; lh' {{ Φ }}.
Proof.
  iIntros (Hlt Hlayer Hminus Hvs Hlen) "Hf0 HΦ".
  iIntros (LI Hfill).
  destruct (iris.to_val LI) eqn:Hcontr.
  { apply lfilled_to_val in Hfill as [v' Hv];eauto.
    assert (iris.to_val [AI_basic (BI_br i)] = None) as Hnone;auto.
    apply (to_val_cat_None2 (vs)) in Hnone.
    rewrite Hv in Hnone. done. }
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  eapply lfilled_minus with (i:=S i) in Hfill as Hfill';[|eauto..].
  2: { apply lfilled_depth in Hfill as ->. auto. }
  destruct Hfill' as [LI' [Hfill1 Hfill2]].
  apply lfilled_Ind_Equivalent in Hfill1. inversion Hfill1;simplify_eq.
  apply lfilled_swap with (es':=vs' ++ (vs ++ es) ++ es') in Hfill2 as Hfill2'.
  destruct Hfill2' as [LI_r Hfill2'].
  assert (iris.prim_step LI σ [] LI_r σ []) as Hstep.
  { destruct σ as [[[hs ws] locs] inst].
    simpl.
    repeat split => //.
    eapply r_label. 3: apply Hfill2'. 2: eauto.
    eapply r_label with (lh:=(LH_base vs' es')).
    2: { apply lfilled_Ind_Equivalent.
         econstructor;auto. }
    2: { apply lfilled_Ind_Equivalent. econstructor;auto. }
    apply r_simple. eapply rs_br.
    apply Hvs. auto. apply lfilled_Ind_Equivalent. eauto. }
  
  iSplit.
  { 
    iPureIntro. destruct s;auto.
    
    eexists [],LI_r,σ,[]. eauto. }
  destruct σ as [[[hs ws] locs] inst] => //=.
  iApply fupd_mask_intro;[solve_ndisj|].
  iIntros "Hcls !>" (es1 σ2 efs HStep).
  iMod "Hcls". iModIntro.
  destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
  destruct HStep as [HStep [-> ->]].
  iApply bi.sep_exist_l.
  apply lfilled_Ind_Equivalent in H8.
  assert (first_instr LI = Some (AI_basic (BI_br i),(0 + S i) + (j - S i))).
  { eapply starts_with_lfilled. 2:eauto.
    eapply starts_with_lfilled.
    2: { apply lfilled_Ind_Equivalent. constructor;auto.
         apply lfilled_Ind_Equivalent;eauto. }
    rewrite first_instr_const//.
  }
  destruct Hstep as [Hstep _].
  eapply reduce_det in HStep as [Heq | [[i0 Hstart] | [ (a & cl & tf & h & i0 & Hstart & Hstart1 & Hstart2) |
                                                        (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]] ; try congruence.
  2: apply Hstep.
  inversion Heq; subst; clear Heq.
  iExists f0.
  iFrame. iSplit => //.
  iIntros "Hf0".
  iSpecialize ("HΦ" with "[$]").
  iSpecialize ("HΦ" $! _ Hfill2').
  eauto.
Qed.


(* Sequencing rule which is always allowed to trap *)
(* This rule is useful in particular for semantic type soundness, which allows traps *)

Lemma wp_seq_can_trap_ctx (s : stuckness) (E : coPset) (Φ Ψ : iris.val -> iProp Σ) (es1 es2 : language.expr wasm_lang) (i : nat) (lh : lholed) f :
  ((¬ (Ψ trapV)) ∗ (Φ trapV) ∗ ↪[frame] f ∗
  (↪[frame] f -∗ WP es1 @ NotStuck; E {{ w, (⌜w = trapV⌝ ∨ Ψ w) ∗ ∃ f, ↪[frame] f }}) ∗
  ∀ w f, Ψ w ∗ ↪[frame] f -∗ WP (iris.of_val w ++ es2) @ s; E CTX i; lh {{ v, Φ v ∗ ∃ f, ↪[frame] f }})%I
  ⊢ WP (es1 ++ es2) @ s; E CTX i; lh {{ v, Φ v ∗ ∃ f, ↪[frame] f }}.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ i lh f).
{ iIntros "[Hntrap [Ht [Hf [Hes1 Hes2]]]]".
  (* iDestruct (wp_wasm_empty_ctx with "Hes1") as "Hes1". *)
  iIntros (LI Hfilled).
  repeat rewrite wp_unfold /wp_pre /=.
  (* iApply wp_unfold. rewrite /wp_pre /=. *)
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val LI) as [vs|] eqn:Hetov.
  { iApply wp_unfold. rewrite /wp_pre /= Hetov.
    destruct vs.
    { pose proof (filled_is_val_imm _ _ _ _ _ Hetov Hfilled) as
        [vs [es' [-> [-> [Hconst1 Hconst2]]]]].
      apply const_list_is_val in Hconst1 as [v1 Hv1].
      apply const_list_is_val in Hconst2 as [v2 Hv2].
      edestruct fill_val as [vs12 [Hvs12 Heql]];eauto.
      assert (Hvs12':=Hvs12).
      apply to_val_cat in Hvs12' as [-> Hev2].
      apply iris.of_to_val in Hev2 as <-.
      iMod ("Hes1" with "Hf") as "[Hes1 Hf]".
      iDestruct "Hf" as (f') "Hf".
      iSpecialize ("Hes2" with "[Hf Hes1]").
      { iDestruct "Hes1" as "[%Hcontr | Hes1]"; [done|eauto]. iFrame. }
      
      (* iDestruct (wp_unfold with "Hes2") as "Hes2". *)
      (* iMod "Hes2". *)
      unfold iris.of_val.
      rewrite - fmap_app take_drop.
      rewrite of_val_imm.
      pose proof (lfilled_swap (iris.of_val (immV vs12)) Hfilled) as [LI' Hfilled'].
      iSpecialize ("Hes2" $! _ Hfilled').
      iDestruct (wp_unfold with "Hes2") as "Hes2". rewrite /wp_pre /=.
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
        all: iMod ("Hes1" with "Hf") as "[_ Hf]";iDestruct "Hf" as (f') "Hf".
        all: by iFrame; iExists _; iFrame. }
      { destruct es1,es2 =>//=.
        all: iMod ("Hes1" with "Hf") as "[_ Hf]";iDestruct "Hf" as (f') "Hf".
        all: by iFrame; iExists _; iFrame. }
    }
  }
  {
  (* Ind *)
  (* iIntros (σ ns κ κs nt) "Hσ". *)
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod ("Hes1" with "Hf") as "[Hes1 Hf]".
    iDestruct "Hf" as (f') "Hf".
    iDestruct "Hes1" as "[-> | Hes1]".
    { iPoseProof (wp_trap_ctx s E f' i lh [] es2 with "Hf") as "HH";auto.
      iSpecialize ("HH" $! LI with "[]");auto.
      iApply (wp_wand with "HH").
      iIntros (v) "[-> Hf]". iFrame. iExists _. iFrame. 
    }
    { iApply wp_unfold. rewrite /wp_pre /= Hetov.
      iIntros (σ ns κ κs nt) "Hσ".
      iSpecialize ("Hes2" with "[$]").
      iSpecialize ("Hes2" $! _ Hfilled).
      iDestruct (wp_unfold with "Hes2") as "Hes2"; rewrite /wp_pre /=.
      
      rewrite Hetov.
      iSpecialize ("Hes2" $! σ ns κ κs nt with "[$]").
      iMod "Hes2" as "[%H1 H2]".
      iIntros "!>".
      iSplit.
      - iPureIntro. by apply H1. 
      - by iApply "H2".
    }
  }
  { iApply wp_unfold. rewrite /wp_pre /= Hetov.
    iIntros (σ ns κ κs nt) "Hσ".
    iSpecialize ("Hes1" with "[$]").
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
      apply prim_step_obs_efs_empty in HStep' as Hemp. inversion Hemp;subst;clear Hemp.
      destruct Heq as [[e' [HStep'' Hlfilled']] | [[lh' Hlf] <-]].
      + apply prim_step_obs_efs_empty in HStep'' as Hemp. inversion Hemp;subst;clear Hemp.
        iSpecialize ("H2" $! e' σ2 [] HStep'').
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        iModIntro.
        iDestruct "H2" as "(Hσ & Hes)".
        iDestruct "Hes" as (f1) "(Hf & Hes'' & Hefs)".
        iFrame. iExists _. iFrame.
        iSplit =>//.
        iIntros "Hf". (* iSpecialize ("Hes''" with "[$]"). *)
        iDestruct ("IH" with "[Hf Ht $Hntrap $Hes'' $Hes2 ]") as "Hcont". iFrame. by iApply "Hcont".
        
      + assert (iris.prim_step es1 σ [] [AI_trap] σ []) as HStep2.
        { unfold iris.prim_step.
          destruct σ as [[[??]?]?].
          repeat split => //.
          apply r_simple; eapply rs_trap => //.
          move => HContra; subst.
          by simpl in Hes.
        }
        iSpecialize ("H2" $! [AI_trap] σ [] HStep2).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        destruct σ as [[[??] ?]?].
        iDestruct "H2" as "[Hσ H]".
        iDestruct "H" as (f') "(Hf1 & Hes'' & Hefs)".
        iModIntro => /=.
        iFrame. iExists _. iFrame.
        iIntros "?"; iSpecialize ("Hes''" with "[$]").
        replace [AI_trap] with (iris.of_val trapV) => //=.
        iDestruct (wp_unfold with "Hes''") as "Hes''".
        rewrite /wp_pre /=. iMod "Hes''" as "[[_ | Hcontr] Hf]".
        2: by iDestruct ("Hntrap" with "Hcontr") as "?".
        iDestruct "Hf" as (f0) "Hf".
        apply lfilled_Ind_Equivalent in Hlf;inversion Hlf;subst.
        assert ((vs ++ [AI_trap] ++ es')%SEQ ++ es2 =
                  (vs ++ [AI_trap] ++ (es' ++ es2)))%list as Hassoc;[repeat erewrite app_assoc;auto|].
        rewrite Hassoc in Hfilled.
        apply lfilled_Ind_Equivalent in Hfilled.
        eapply lfilledInd_frame in Hfilled;auto.
        apply lfilled_Ind_Equivalent in Hfilled.
        destruct HStep' as [HStep' _].
        eapply trap_reduce_lfilled in HStep';eauto.
        destruct HStep' as [lh2 [j [Hlh' Hle]]].
        iPoseProof (wp_trap_ctx s E f0 j _ [] [] with "Hf") as "HH";auto.
        iSpecialize ("HH" $! _ Hlh').
        iApply (wp_wand with "HH").
        iIntros (v) "[-> Hf]". iFrame. iExists _. iFrame. 
  } } }
Qed.
  
End structural_rules.
