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
  
Context `{!wasmG Σ}.

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
  apply list_eq_dec.
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
      lh_minus lh' lh'' = Some (LH_rec vs' n es lh es') ∧ lh_depth lh = i.
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


Lemma wp_br_ctx_nested (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n vs es i j lh lh' lh'' vs' es' f0 vs0' n0 es0 es0' :
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

  eapply lfilled_minus with (i:=S i) in Hfill as Hfill';[|eauto..].
  2: { apply lfilled_depth in Hfill as ->. auto. }
  destruct Hfill' as [LI' [Hfill1 Hfill2]].
  apply lfilled_Ind_Equivalent in Hfill1. inversion Hfill1;simplify_eq.
  apply lfilled_swap with (es':=vs' ++ (vs ++ es) ++ es') in Hfill2 as Hfill2'.
  destruct Hfill2' as [LI_r Hfill2'].
  
  assert (iris.to_val LI = None) as Hnone.
  { apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill;simplify_eq.
    
    eapply val_head_stuck_reduce.
    eapply r_label. 3: apply Hfill2'. 2: eauto.
    eapply r_label with (lh:=(LH_base vs' es')).
    2: { apply lfilled_Ind_Equivalent.
         econstructor;auto. }
    2: { apply lfilled_Ind_Equivalent. econstructor;auto. }
    apply r_simple. eapply rs_br.
    apply Hvs. auto. apply lfilled_Ind_Equivalent. eauto.
    Unshelve. done. apply (Build_store_record [] [] [] []).
    apply (Build_frame [] (Build_instance [] [] [] [] [])). }
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
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
Lemma wp_seq_can_trap_ctx (s : stuckness) (E : coPset) (Φ Ψ : iris.val -> iProp Σ) (es1 es2 : language.expr wasm_lang) (i : nat) (lh : lholed)
      (Φf : frame -> iProp Σ) f :
  ((¬ (Ψ trapV)) ∗ (Φ trapV) ∗ ↪[frame] f ∗
  (↪[frame] f -∗ WP es1 @ NotStuck; E {{ w, (⌜w = trapV⌝ ∨ Ψ w) ∗ ∃ f0, ↪[frame] f0 ∗ Φf f0 }}) ∗
  ∀ w f0, Ψ w ∗ ↪[frame] f0 ∗ Φf f0 -∗ WP (iris.of_val w ++ es2) @ s; E CTX i; lh {{ v, Φ v ∗ ∃ f, ↪[frame] f ∗ Φf f }})%I
  ⊢ WP (es1 ++ es2) @ s; E CTX i; lh {{ v, Φ v ∗ ∃ f, ↪[frame] f ∗ Φf f }}.
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
    eapply lfilled_to_val_app in Hetov as HH;eauto.
    destruct HH as [vs' [Hvs' Hfilled']].
    unfold iris_wp_def.to_val in Hvs'.
    rewrite Hvs'.
    iMod ("Hes1" with "Hf") as "[Hes1 Hf]".
    iDestruct "Hes1" as "[-> | Hes1]".
    { apply to_val_trap_is_singleton in Hvs' as ->.
      destruct es2;cycle 1.
      { assert (to_val ([AI_trap] ++ a :: es2) = None) as Hnone.
        rewrite -(app_nil_l [AI_trap]) -app_assoc; apply to_val_not_trap_interweave;auto.
        eapply to_val_None_lfilled in Hnone;[|eauto]. congruence. }
      erewrite app_nil_r in Hfilled'.
      eapply lfilled_to_val_0 in Hfilled' as Heq;eauto. subst i.
      apply lfilled_Ind_Equivalent in Hfilled. inversion Hfilled;simplify_eq.
      destruct vs0,es'.
      erewrite app_nil_l, app_nil_r, app_nil_r in Hetov.
      destruct vs;try done. iFrame. eauto.
      all: rewrite to_val_not_trap_interweave in Hetov;try done;auto.
    }
    iDestruct "Hf" as (f0) "[Hf Hfv]".
    iSpecialize ("Hes2" with "[$Hf $Hfv $Hes1]").
    iSpecialize ("Hes2" $! _ Hfilled').
    iDestruct (wp_unfold with "Hes2") as "Hes2".
    rewrite /wp_pre /= Hetov.
    iFrame.
  }
  {
  (* Ind *)
  (* iIntros (σ ns κ κs nt) "Hσ". *)
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod ("Hes1" with "Hf") as "[Hes1 Hf]".
    iDestruct "Hes1" as "[-> | Hes1]".
    { iDestruct "Hf" as (f0) "[Hf Hfv]".
      iPoseProof (wp_trap_ctx s E f0 i lh [] es2 with "Hf") as "HH";auto.
      iSpecialize ("HH" $! LI with "[]");auto.
      iApply (wp_wand with "HH").
      iIntros (v) "[-> Hf]". iFrame. iExists _. iFrame. 
    }
    { iApply wp_unfold. rewrite /wp_pre /= Hetov.
      iIntros (σ ns κ κs nt) "Hσ".
      iDestruct "Hf" as (f0) "[Hf Hfv]".
      iSpecialize ("Hes2" with "[$Hes1 $Hf $Hfv]").
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
        iDestruct "Hf" as (f0) "[Hf Hfv]".
        iPoseProof (wp_trap_ctx s E f0 j _ [] [] with "Hf") as "HH";auto.
        iSpecialize ("HH" $! _ Hlh').
        iApply (wp_wand with "HH").
        iIntros (v) "[-> Hf]". iFrame. iExists _. iFrame. 
  } } }
Qed.



(* ((¬ (Ψ trapV)) ∗ (Φ trapV) ∗ ↪[frame] f ∗ *)
(*   (↪[frame] f -∗ WP es1 @ NotStuck; E {{ w, (⌜w = trapV⌝ ∨ Ψ w) ∗ ∃ f0, ↪[frame] f0 ∗ Φf f0 }}) ∗ *)
(*   ∀ w f0, Ψ w ∗ ↪[frame] f0 ∗ Φf f0 -∗ WP (iris.of_val w ++ es2) @ s; E CTX i; lh {{ v, Φ v ∗ ∃ f, ↪[frame] f ∗ Φf f }})%I *)
(*   ⊢ WP (es1 ++ es2) @ s; E CTX i; lh {{ v, Φ v ∗ ∃ f, ↪[frame] f ∗ Φf f }}. *)

Lemma wp_val_can_trap (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v0 : value) (es : language.expr wasm_lang) f Φf :
  (¬ (Φ trapV) ∗ ↪[frame] f ∗
  (↪[frame] f -∗ WP es @ NotStuck ; E {{ v, (⌜v = trapV⌝ ∨ (Φ (val_combine (immV [v0]) v))) ∗ ∃ f, ↪[frame] f ∗ Φf f }})
  ⊢ WP ((AI_basic (BI_const v0)) :: es) @ s ; E {{ v, (⌜v = trapV⌝ ∨ Φ v) ∗ ∃ f, ↪[frame] f ∗ Φf f }})%I.
Proof.
  (* This also needs an iLob. *)
  iLöb as "IH" forall (v0 es Φ f).
  iIntros "(Hntrap & H & Hf)".
  destruct (iris.to_val es) as [vs|] eqn:Hes.
  { destruct vs.
    { iApply wp_unfold.
      repeat rewrite wp_unfold /wp_pre /=.      
      rewrite Hes. apply of_to_val in Hes as <-. rewrite to_val_cons_immV.
      iMod ("Hf" with "H") as "[[%Heq| HΦ] H]";try done.
      iModIntro. iFrame. }
    { apply to_val_trap_is_singleton in Hes as ->.
      repeat rewrite wp_unfold /wp_pre /=.
      iMod ("Hf" with "H") as "[[_|Hcontr] H]";cycle 1.
      { iDestruct ("Hntrap" with "Hcontr") as "?". done. }
      iDestruct "H" as (f0) "[Hf0 Hf0v]".
      iApply (wp_wand  _ _ _ (λ v, ⌜v = trapV⌝ ∗ ↪[frame] f0)%I with "[Hf0]").
      { rewrite -(take_drop 1 [AI_basic (BI_const v0); AI_trap]);simpl take;simpl drop.
        rewrite -(app_nil_r [AI_trap]).
        iApply (wp_trap with "[] Hf0");auto. }
      iIntros (v) "[-> H]". iSplitR;[|iExists _;iFrame]. by iLeft. }
    { iApply wp_unfold.
      repeat rewrite wp_unfold /wp_pre /=.      
      rewrite Hes. apply of_to_val in Hes as <-; erewrite to_val_cons_brV;[|apply to_of_val].
      iMod ("Hf" with "H") as "[[%Heq| HΦ] H]";try done.
      iModIntro. iFrame. }
    { iApply wp_unfold.
      repeat rewrite wp_unfold /wp_pre /=.      
      rewrite Hes. apply of_to_val in Hes as <-; erewrite to_val_cons_retV;[|apply to_of_val].
      iMod ("Hf" with "H") as "[[%Heq| HΦ] H]";try done.
      iModIntro. iFrame. }
  }
  { iApply wp_unfold.
    repeat rewrite wp_unfold /wp_pre /=.
    rewrite Hes to_val_cons_None //.
    iIntros (σ ns κ κs nt) "Hσ".
    iDestruct ("Hf" with "[$]") as "H".
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
        iDestruct "H" as "[Hσ H]".
        iDestruct "H" as  (f1) "(Hf1 & Hes & Hefs)".
        iSimpl.
        iFrame. iExists _. iFrame.
        iSplit => //.
        iIntros "Hf".
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
        iDestruct "H" as "[Hσ H]".
        iDestruct "H" as (f1) "(Hf1 & Hes & Hefs)".
        iFrame.
        iModIntro. iExists _. iFrame.
        iSplit => //.
        iIntros "Hf".
        iSpecialize ("Hes" with "[$]").
        iDestruct (wp_unfold with "Hes") as "Hes".
        rewrite /wp_pre /=.
        iMod "Hes" as "[[_|Hcontr] Hf]";cycle 1.
        { by iSpecialize ("Hntrap" with "Hcontr"). }
        iDestruct "Hf" as (f0) "[Hf0 Hf0v]".
        iApply (wp_wand  _ _ _ (λ v, ⌜v = trapV⌝ ∗ ↪[frame] f0)%I with "[Hf0]").
        { rewrite separate1.
          iApply (wp_trap with "[] Hf0");auto. }
        iIntros (v) "[-> H]". iSplitR;[|iExists _;iFrame]. by iLeft.
  }
Qed.

Lemma wp_val_can_trap_app' (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs (es : language.expr wasm_lang) f Φf :
  (* □ is required here -- this knowledge needs to be persistent instead of 
     one-off. *)
  (□ (¬ Φ trapV )) ∗ ↪[frame] f ∗
 (↪[frame] f -∗  WP es @ NotStuck ; E {{ v, (⌜v = trapV⌝ ∨ (Φ (val_combine (immV vs) v))) ∗ ∃ f, ↪[frame] f ∗ Φf f }}%I)
  ⊢ WP ((v_to_e_list vs) ++ es) @ s ; E {{ v, (⌜v = trapV⌝ ∨ Φ v) ∗ ∃ f, ↪[frame] f ∗ Φf f }}%I.
Proof.
  iInduction vs as [|c vs] "IH" forall (Φ s E es).
  { simpl.
    iIntros "(#Hntrap & Hf & HWP)".
    destruct s.
    2: iApply wp_stuck_weaken.
    all: iDestruct ("HWP" with "Hf") as "HWP".
    all: iApply (wp_wand with "HWP").
    all: iIntros (v).
    all: destruct v => /=.
    all: iIntros "HΦ" => //.
    all: rewrite vh_push_const_nil + rewrite sh_push_const_nil.
    all: auto.
  }
  { iIntros "(#Hntrap & Hf & HWP)".
    iSimpl.
    iApply wp_val_can_trap.
    iFrame. iSplitR => //. iIntros "Hf".
    iApply "IH" => //=.
    iSplit => //. iFrame. iIntros "Hf".
    iDestruct ("HWP" with "Hf") as "HWP".
    iApply (wp_mono with "HWP").
    iIntros (vs') "HΦ".
    iSimpl. destruct vs';auto.
    all: rewrite -vh_push_const_app + rewrite -sh_push_const_app;auto.
  }
Qed.
  
Lemma wp_val_can_trap_app (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs v' (es : language.expr wasm_lang) f Φf :
  iris.to_val vs = Some (immV v') ->
  (□ (¬ Φ trapV )) ∗ ↪[frame] f ∗
  (↪[frame] f -∗ WP es @ NotStuck ; E {{ v, (⌜v = trapV⌝ ∨ Φ (val_combine (immV v') v)) ∗ ∃ f, ↪[frame] f ∗ Φf f }})%I
  ⊢ WP (vs ++ es) @ s ; E {{ v, (⌜v = trapV⌝ ∨ Φ v) ∗ ∃ f, ↪[frame] f ∗ Φf f }}%I.
Proof.
  iIntros "%Hves [#Hntrap Hwp]".
  apply iris.of_to_val in Hves; subst.
  iApply wp_val_can_trap_app'.
  by iFrame.
Qed.

Lemma wp_val_return' (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs vs' es' es'' n f0 Φf :
  const_list vs ->
  ↪[frame] f0 -∗
  (↪[frame] f0 -∗ WP vs' ++ vs ++ es'' @ s; E {{ v, Φ v ∗ ∃ f, ↪[frame] f ∗ Φf f }})
  -∗ WP vs @ s; E CTX 1; LH_rec vs' n es' (LH_base [] []) es'' {{ v, Φ v ∗ ∃ f, ↪[frame] f ∗ Φf f }}.
Proof.
  iIntros (Hconst) "Hf0 HWP".
  iLöb as "IH".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  inversion Hfill;subst.
  inversion H8;subst.
  assert (vs' ++ [AI_label n es' ([] ++ vs ++ [])] ++ es''
          = ((vs' ++ [AI_label n es' ([] ++ vs ++ [])]) ++ es''))%SEQ as ->.
  { erewrite app_assoc. auto. }
  apply const_list_to_val in Hconst as [v1 Hv1].
  apply const_list_to_val in H7 as [v2 Hv2].
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

Lemma lfilled_push_base_swap i lh n es vs1 es2 es' LI :
  lfilled (S i) (push_base lh n es vs1 es2) es' LI ->
  ∃ LI', lfilled i lh es' LI'.
Proof.
  intros Hfill%lfilled_Ind_Equivalent.
  inversion Hfill;simplify_eq.
  clear Hfill.
  revert es' LI0 i H2 lh vs n0 es'0 es'' H0 H1.
  induction lh';intros es' LI0 i H2 lh vs n1 es'0 es'' H0 H1.
  { inversion H2;simplify_eq.
    destruct lh; simpl in *; simplify_eq.
    2: { destruct lh;simpl in *;done. }
    eexists. apply lfilled_Ind_Equivalent. constructor;auto. }
  { inversion H2;simplify_eq.
    destruct lh;simpl in *;simplify_eq.
    eapply IHlh' in H11 as [LI' HLI'%lfilled_Ind_Equivalent];eauto.
    eexists. apply lfilled_Ind_Equivalent.
    constructor;eauto.
  }
Qed.

Lemma lfilled_push_base_swap_inv i lh n es vs1 es2 es' LI :
  const_list vs1 ->
  lfilled i lh es' LI ->
  ∃ LI', lfilled (S i) (push_base lh n es vs1 es2) es' LI'.
Proof.
  intros Hconst Hfill%lfilled_Ind_Equivalent.
  revert es' i LI Hfill.
  induction lh;intros es' i LI Hfill.
  { simpl. eexists. inversion Hfill;simplify_eq.
    apply lfilled_Ind_Equivalent. constructor;auto. constructor. auto. }
  { inversion Hfill;simplify_eq. simpl.
    eapply IHlh in H8 as [LI' HLI'].
    eexists. apply lfilled_Ind_Equivalent.
    constructor;eauto.
    apply lfilled_Ind_Equivalent;eauto.
  }
Qed.


Lemma wp_br_ctx_shift (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs i lh n es vs1 es2 l n1 l0 l1 :
  const_list vs ->
  length vs = n1 ->
  WP vs ++ [AI_basic (BI_br i)] @ s; E CTX S i; LH_rec l n1 l0 lh l1 {{ Φ }} -∗
  WP vs ++ [AI_basic (BI_br (S i))] @ s; E CTX S (S i); LH_rec l n1 l0 (push_base lh n es vs1 es2) l1 {{ Φ }}.
Proof.
  iIntros (Hlen Hconst) "Hwp".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  inversion Hfill;subst;simplify_eq.
  apply lfilled_Ind_Equivalent in H8 as Hfill'.
  apply lfilled_push_base_swap in Hfill' as Hfill''.
  destruct Hfill'' as [LI' Hfill''].
  apply lfilled_swap with (es' := vs ++ [AI_basic (BI_br i)]) in Hfill'' as Hfilli.
  destruct Hfilli as [LIi Hfilli].
  iSpecialize ("Hwp" with "[]").
  { iPureIntro. apply lfilled_Ind_Equivalent. constructor;auto.
    apply lfilled_Ind_Equivalent. eauto. }

  assert (to_val (l ++ [AI_label (length vs) l0 LIi] ++ l1) = None).
  { apply to_val_cat_None2;auto.
    apply to_val_cat_None1.
    eapply to_val_brV_None;[|eauto|];eauto.
  }
  assert (to_val (l ++ [AI_label (length vs) l0 LI0] ++ l1) = None).
  { apply to_val_cat_None2;auto.
    apply to_val_cat_None1.
    eapply to_val_brV_None;[|eauto|];eauto.
  }

  iApply wp_unfold. iDestruct (wp_unfold with "Hwp") as "Hwp".
  rewrite /wp_pre /= H H0.

  iIntros (σ1 k κ1 κ2 m) "Hσ".
  iSpecialize ("Hwp" $! σ1 k κ1 κ2 m with "Hσ").
  destruct σ1 as [[[? ?] ?] ?].

  assert (reduce (host_instance:=DummyHosts.host_instance) s0 s1
                 {| f_locs := l2; f_inst := i0 |}
                 (l ++ [AI_label (length vs) l0 LI0] ++ l1) s0 s1
                 {| f_locs := l2; f_inst := i0 |}
                 (l ++ (vs ++ l0) ++ l1)).
  { eapply r_label with (k:=0) (lh:=LH_base l l1);cycle 1.
    apply lfilled_Ind_Equivalent. by constructor.
    apply lfilled_Ind_Equivalent. by constructor.
    eapply r_simple, rs_br;eauto. }

  assert (reduce (host_instance:=DummyHosts.host_instance) s0 s1
                 {| f_locs := l2; f_inst := i0 |}
                 (l ++ [AI_label (length vs) l0 LIi] ++ l1) s0 s1
                 {| f_locs := l2; f_inst := i0 |}
                 (l ++ (vs ++ l0) ++ l1)).
  { eapply r_label with (k:=0) (lh:=LH_base l l1);cycle 1.
    apply lfilled_Ind_Equivalent. by constructor.
    apply lfilled_Ind_Equivalent. by constructor.
    eapply r_simple, rs_br;eauto. }
  
  iMod "Hwp". iModIntro.
  iDestruct "Hwp" as "[_ Hwp]".
  iSplitR.
  { destruct s =>//. unfold reducible. iPureIntro.
    eexists [],_,(s0,s1,l2,i0),[]. simpl. repeat split;eauto. }
  iIntros (e2 σ2 efs Hprim).
  destruct σ2 as [[[? ?] ?] ?].
  destruct Hprim as [Hprim [-> ->]].
  apply lfilled_Ind_Equivalent in Hfill.
  assert (first_instr (l ++ [AI_label (length vs) l0 LI0] ++ l1) = Some (AI_basic (BI_br (S i)),0 + S (S i))) as Hfirst0.
  { eapply starts_with_lfilled;cycle 1.
    apply lfilled_Ind_Equivalent. constructor;eauto.
    apply first_instr_const;auto. }
  eapply reduce_det in Hprim as [? | [[? ?]|[[? [? [? [? [? [? [? ?]]]]]]]|[? [? [? [? [? [? ?]]]]]]]]];[..|apply H1].
  all: try by (rewrite separate1 Hfirst0 in H3; inversion H3).
  inversion H3;simplify_eq.
  iSpecialize ("Hwp" $! _ (s2,s3,l3,i1) with "[]").
  { iPureIntro. unfold prim_step. repeat split;eauto. }
  iFrame.
Qed.

Lemma lfilled_split i j lh e LI :
  i <= j ->
  lfilled j lh e LI ->
  ∃ lh' lh'' LI',
    lfilled i lh' e LI' ∧ lfilled (j - i) lh'' LI' LI.
Proof.
  revert i lh e LI.
  induction j;intros i lh e LI Hle Hfill%lfilled_Ind_Equivalent.
  { inversion Hfill;simplify_eq. destruct i;[|lia].
    simpl.
    eexists; eexists; eexists.
    split.
    { apply lfilled_Ind_Equivalent. constructor. eauto. }
    { instantiate (2:=LH_base [] []). cbn. apply/eqP.
      rewrite app_nil_r. eauto. }
  }
  { inversion Hfill;simplify_eq.
    destruct (decide (i = S j)).
    { simplify_eq. rewrite PeanoNat.Nat.sub_diag.
      eexists; eexists; eexists.
      split.
      { apply lfilled_Ind_Equivalent.
        constructor;eauto. }
      { instantiate (4:=LH_base [] []). cbn. apply/eqP.
        rewrite app_nil_r. eauto. }
    }
    { assert (i <= j) as Hle';[lia|].
      apply lfilled_Ind_Equivalent in H1.
      eapply IHj in Hle' as Hres;eauto.
      destruct Hres as [lh2 [lh'' [LI' [Hfill1 Hfill2]]]].
      repeat eexists;eauto.
      apply lfilled_Ind_Equivalent.
      rewrite -minus_Sn_m;eauto.
      constructor;auto. apply lfilled_Ind_Equivalent. eauto.
    }
  }
Qed.

Lemma wp_br_ctx_shift_inv (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs i lh n es vs1 es2 l n1 l0 l1 :
  const_list vs ->
  const_list vs1 ->
  length vs = n1 ->
  WP vs ++ [AI_basic (BI_br (S i))] @ s; E CTX S (S i); LH_rec l n1 l0 (push_base lh n es vs1 es2) l1 {{ Φ }} -∗
  WP vs ++ [AI_basic (BI_br i)] @ s; E CTX (S i); LH_rec l n1 l0 lh l1 {{ Φ }}.
Proof.
  iIntros (Hconst Hconst' Hlen) "Hwp".
  iIntros (LI Hfill).
  apply lfilled_push_base_swap_inv with (n:=n) (es:=es) (vs1:=vs1) (es2:=es2) in Hfill as Hfill';auto.
  destruct Hfill' as [LI' Hfill'].
  simpl in Hfill'.
  
  apply lfilled_swap with (es' := vs ++ [AI_basic (BI_br (S i))]) in Hfill' as Hfilli.
  destruct Hfilli as [LIi Hfilli].
  apply lfilled_Ind_Equivalent in Hfilli.
  inversion Hfilli. simplify_eq.
  apply lfilled_Ind_Equivalent in H8.
  apply lfilled_Ind_Equivalent in Hfilli.

  assert (const_list l) as Hconst''.
  { apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;auto. }
  
  iSpecialize ("Hwp" with "[]").
  { iPureIntro. eauto. }  
  
  assert (to_val (l ++ [AI_label (length vs) l0 LI0] ++ l1) = None).
  { apply to_val_cat_None2;auto.
    apply to_val_cat_None1.
    eapply to_val_brV_None;[|eauto|];eauto.
  }
  assert (to_val LI = None).
  { apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill;simplify_eq.
    apply to_val_cat_None2;auto.
    apply to_val_cat_None1.
    eapply to_val_brV_None. apply Hconst.
    auto. apply lfilled_Ind_Equivalent. eauto. }

  iApply wp_unfold. iDestruct (wp_unfold with "Hwp") as "Hwp".
  rewrite /wp_pre /= H H0.

   apply lfilled_Ind_Equivalent in Hfill.
  inversion Hfill;simplify_eq.

  iIntros (σ1 k κ1 κ2 m) "Hσ".
  iSpecialize ("Hwp" $! σ1 k κ1 κ2 m with "Hσ").
  destruct σ1 as [[[? ?] ?] ?].

  assert (reduce (host_instance:=DummyHosts.host_instance) s0 s1
                 {| f_locs := l2; f_inst := i0 |}
                 (l ++ [AI_label (length vs) l0 LI0] ++ l1) s0 s1
                 {| f_locs := l2; f_inst := i0 |}
                 (l ++ (vs ++ l0) ++ l1)).
  { eapply r_label with (k:=0) (lh:=LH_base l l1);cycle 1.
    apply lfilled_Ind_Equivalent. by constructor.
    apply lfilled_Ind_Equivalent. by constructor.
    eapply r_simple, rs_br;eauto. }

  assert (reduce (host_instance:=DummyHosts.host_instance) s0 s1
                 {| f_locs := l2; f_inst := i0 |}
                 (l ++ [AI_label (length vs) l0 LI1] ++ l1) s0 s1
                 {| f_locs := l2; f_inst := i0 |}
                 (l ++ (vs ++ l0) ++ l1)).
  { eapply r_label with (k:=0) (lh:=LH_base l l1);cycle 1.
    apply lfilled_Ind_Equivalent. by constructor.
    apply lfilled_Ind_Equivalent. by constructor.
    eapply r_simple, rs_br;eauto. apply lfilled_Ind_Equivalent. eauto. }
  
  iMod "Hwp". iModIntro.
  iDestruct "Hwp" as "[_ Hwp]".
  iSplitR.
  { destruct s =>//. unfold reducible. iPureIntro.
    eexists [],_,(s0,s1,l2,i0),[]. simpl. repeat split;eauto. }
  iIntros (e2 σ2 efs Hprim).
  destruct σ2 as [[[? ?] ?] ?].
  destruct Hprim as [Hprim [-> ->]].
  apply lfilled_Ind_Equivalent in Hfill.
  assert (first_instr (l ++ [AI_label (length vs) l0 LI1] ++ l1) = Some (AI_basic (BI_br i),0 + S i)) as Hfirst0.
  { eapply starts_with_lfilled;cycle 1.
    apply lfilled_Ind_Equivalent. constructor;eauto.
    apply first_instr_const;auto. }
  eapply reduce_det in Hprim as [? | [[? ?]|[[? [? [? [? [? [? [? ?]]]]]]]|[? [? [? [? [? [? ?]]]]]]]]];[..|apply H2].
  all: try by (rewrite separate1 Hfirst0 in H3; inversion H3).
  inversion H3;simplify_eq.
  iSpecialize ("Hwp" $! _ (s2,s3,l3,i1) with "[]").
  { iPureIntro. unfold prim_step. repeat split;eauto. }
  iFrame.
Qed.

Lemma wp_ret_shift (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n f i lh j lh' LI LI' vs :
  const_list vs ->
  length vs = n ->
  lfilled i lh (vs ++ [AI_basic BI_return]) LI ->
  lfilled j lh' (vs ++ [AI_basic BI_return]) LI' ->
  WP [AI_local n f LI] @ s; E {{ Φ }} -∗
  WP [AI_local n f LI'] @ s; E {{ Φ }}.
Proof.
  iIntros (Hconst Hlen Hfill1 Hfill2) "Hwp".

  iApply wp_unfold. iDestruct (wp_unfold with "Hwp") as "Hwp".
  rewrite /wp_pre /=.

  iIntros (σ1 k κ1 κ2 m) "Hσ".
  iSpecialize ("Hwp" $! σ1 k κ1 κ2 m with "Hσ").
  destruct σ1 as [[[? ?] ?] ?].

  assert (reduce (host_instance:=DummyHosts.host_instance) s0 s1
                 {| f_locs := l; f_inst := i0 |}
                 ([AI_local n f LI]) s0 s1
                 {| f_locs := l; f_inst := i0 |}
                 vs).
  { eapply r_simple. eapply rs_return;eauto. }
  assert (reduce (host_instance:=DummyHosts.host_instance) s0 s1
                 {| f_locs := l; f_inst := i0 |}
                 ([AI_local n f LI']) s0 s1
                 {| f_locs := l; f_inst := i0 |}
                 vs).
  { eapply r_simple. eapply rs_return;eauto. }
  iMod "Hwp". iModIntro.
  iDestruct "Hwp" as "[_ Hwp]".
  iSplitR.
  { destruct s =>//. unfold reducible. iPureIntro.
    eexists [],_,(s0,s1,l,i0),[]. simpl. repeat split;eauto. }
  iIntros (e2 σ2 efs Hprim).
  destruct σ2 as [[[? ?] ?] ?].
  destruct Hprim as [Hprim [-> ->]].
  assert (first_instr ([AI_local n f LI']) = Some (AI_basic (BI_return),S(0 + j))) as Hfirst0.
  { eapply first_instr_local. eapply starts_with_lfilled;eauto.
    apply first_instr_const;auto. }
  eapply reduce_det in Hprim as [? | [[? ?]|[[? [? [? [? [? [? [? ?]]]]]]]|[? [? [? [? [? [? ?]]]]]]]]];[..|apply H0].
  all: try by (rewrite separate1 Hfirst0 in H1; inversion H1).
  inversion H1;simplify_eq.
  iSpecialize ("Hwp" $! _ (s2,s3,l0,i1) with "[]").
  { iPureIntro. unfold prim_step. repeat split;eauto. }
  iFrame.
Qed.
  
End structural_rules.
