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

Lemma big_sepL2_insert {Σ} {A B : Type} (l1 : list A) (l2 : list B) (i : nat) (a : A) (b : B) (Φ : A -> B -> iProp Σ) : 
  ⊢ Φ a b -∗
    ([∗ list] a0;b0 ∈ l1;l2, Φ a0 b0)%I -∗
    ([∗ list] a0;b0 ∈ <[i:=a]> l1;<[i:=b]> l2, Φ a0 b0)%I.
Proof.
  revert a b i l2.
  iInduction (l1) as [] "IH";
  iIntros (a' b' i l2) "Ha Hl".
  { iDestruct (big_sepL2_length with "Hl") as %Hlen.
    destruct l2;[|done]. done. }
  { iDestruct (big_sepL2_length with "Hl") as %Hlen.
    destruct l2;[done|].
    destruct i.
    { simpl. iDestruct "Hl" as "[_ Hl]". iFrame. }
    { simpl. iDestruct "Hl" as "[$ Hl]". iApply ("IH" with "Ha"). iFrame. }
  }
Qed.

Lemma big_sepL_cond_impl {Σ} {A : Type} (Φ : nat -> A -> iProp Σ) (l : list A) :
  ([∗ list] k↦y ∈ l, Φ k y) ⊣⊢
  ([∗ list] k↦y ∈ l, True → Φ k y).
Proof.
  iSplit; iIntros "Hl".
  all: iApply (big_sepL_mono with "Hl");iIntros (k y Hk) "H";auto.
  iApply "H";auto.
Qed.

Section fundamental.
  Import DummyHosts. (* placeholder *)

  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* ------------------------------ HELPER TACTICS AND LEMMAS ------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)
  
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

  Lemma lh_minus_base_is_empty lh l1 l2 :
    is_Some (lh_minus lh (LH_base l1 l2)) -> l1 = [] ∧ l2 = [].
  Proof.
    intros [lh' Hsome].
    apply lh_minus_Ind_Equivalent in Hsome.
    inversion Hsome;subst;auto.
  Qed.

  Lemma lh_minus_push_base_is_Some lh n es es1 es2 lh'' :
    lh_depth lh'' <= lh_depth lh ->
    is_Some (lh_minus (push_base lh n es es1 es2) lh'') ->
    is_Some (lh_minus lh lh'').
  Proof.
    revert lh'' n es es1 es2. induction lh;intros lh'' m es es1 es2 Hlt Hsome.
    { simpl in Hlt. destruct lh'';simpl in *.
      { destruct l1;[|done].
        destruct l2;[|done].
        eauto. }
      { lia. }
    }
    { simpl in Hlt.
      destruct lh''.
      { destruct l2,l3; done. }
      { simpl in Hsome. simpl.
        destruct ((l == l2) && (n =? n0) && (l0 == l3) && (l1 == l4));[|done].
        simpl in Hlt. apply le_S_n in Hlt.
        eapply IHlh in Hlt;eauto.
      }
    }
  Qed.

  Lemma get_layer_push_base_0 lh n es vs1 es1 :
    base_is_empty lh ->
    get_layer (push_base lh n es vs1 es1) (lh_depth lh) = Some ([],n,es,LH_base vs1 es1,[]).
  Proof.
    induction lh;intros Hemp.
    { simpl in *. destruct Hemp as [-> ->]. eauto. }
    { simpl in *. eauto. }
  Qed.

  Lemma lh_depth_eq_lh_minus lh'' lh n es vs1 es1 :
    base_is_empty lh ->
    lh_depth lh'' = lh_depth lh ->
    is_Some (lh_minus (push_base lh n es vs1 es1) lh'') ->
    lh'' = lh.
  Proof.
    revert lh n es vs1 es1.
    induction lh'';intros lh m es vs1 es1 Hbase Hdep [lh' Hsome].
    { destruct lh;[|done]. simpl in *.
      destruct l,l0;try done.
      destruct Hbase as [-> ->];auto. }
    { destruct lh;[done|]. simpl in *.
      inversion Hdep as [Hdep'].
      destruct ((l2 == l) && (n0 =? n) && (l3 == l0) && (l4 == l1)) eqn:Heq;[|done].
      eapply IHlh'' in Hdep' as ->;eauto.
      revert Heq. rewrite !andb_true_iff =>Heq.
      destruct Heq as [[[->%ai_eqseq_true ->%PeanoNat.Nat.eqb_eq] ->%ai_eqseq_true] ->%ai_eqseq_true].
      auto. }
  Qed.

  Lemma lholed_lengths_gt0_get_snoc lh lbs :
    lh_depth lh > 0 ->
    lholed_lengths (rev lbs) lh ->
    ∃ lbs' tc, lbs = lbs' ++ [tc].
  Proof.
    induction lbs using rev_ind;intros Hlh Hh.
    { destruct lh;[simpl in Hlh;lia|done]. }
    { eauto. }
  Qed.

  Lemma of_val_length ws :
    length (of_val (immV ws)) = length ws.
  Proof.
    by rewrite fmap_length.
  Qed.

  Lemma base_is_empty_push_base lh n es :
    base_is_empty (push_base lh n es [] []).
  Proof.
    induction lh;simpl;auto.
  Qed.

  Lemma lholed_lengths_push_base lh l tn es :
    lholed_lengths l lh ->
    lholed_lengths (l ++ [tn]) (push_base lh (length tn) es [] []).
  Proof.
    revert lh. induction l;intros lh Hlh.
    { destruct lh;inversion Hlh. simpl. eauto. }
    { destruct lh;inversion Hlh. simpl. split;auto. }
  Qed.

  Lemma lholed_valid_push_base lh n es :
    lholed_valid lh ->
    lholed_valid (push_base lh n es [] []).
  Proof.
    intros Hlh;induction lh.
    { simpl in *. auto. }
    { inversion Hlh. simpl. split;auto. }
  Qed.

  Lemma lfilledInd_push_inv i : ∀ lh n es' es LI l1 l2,
      const_list l1 ->
      lfilledInd (S i) (push_base lh n es' l1 l2) es LI ->
      lfilledInd i lh ([::AI_label n es' (l1 ++ es ++ l2)]) LI.
  Proof.
    induction i.
    all: intros lh n es' es LI l1 l2 Hconst Hfill.
    { inversion Hfill;subst.
      destruct lh.
      { simpl in H0. simplify_eq.
        inversion H2. constructor. auto. }
      { simpl in H0. simplify_eq. destruct lh;inversion H2. }
    }
    { inversion Hfill;subst. simpl.
      destruct lh.
      { simpl in H0. simplify_eq.
        inversion H2. }
      { simpl in H0. simplify_eq.
        constructor; auto. 
      }
    }
  Qed.

  Lemma lholed_lengths_length_depth l lh :
    lholed_lengths l lh ->
    length l = lh_depth lh.
  Proof.
    revert lh;induction l;intros lh Hlen.
    { destruct lh;inversion Hlen. auto. }
    { destruct lh;inversion Hlen. subst. simpl. auto. }
  Qed.

  Lemma last_lookup_rev {A : Type} l (a : A) :
    last l = Some a <-> rev l !! 0 = Some a.
  Proof.
    revert a;induction l using rev_ind;intros a0.
    { done. }
    { simpl.
      rewrite rev_unit last_snoc. eauto. }
  Qed.

  Lemma list_app_split {A : Type} (ws : list A) (n1 n2 : nat):
    length ws = n1 + n2 ->
    ∃ ws1 ws2 : list A,
      ws = ws1 ++ ws2 ∧ length ws1 = n1 ∧ length ws2 = n2.
  Proof.
    revert n1 n2.
    induction ws;intros n1 n2.
    { destruct n1,n2;try done.
      intros.
      repeat eexists;eauto. auto. }
    { intros Hlen. simpl in Hlen.
      destruct (decide (length ws = n2)).
      { assert (n1 = 1) as ->;[lia|]. exists [a], ws. auto. }
      { destruct n1.
        { exists [],(a::ws). auto. }
        { assert (length ws = n1 + n2) as [ws1 [ws2 [Heq [Hlen1 Hlen2]]]]%IHws;[lia|].
          simplify_eq.
          exists (a::ws1),ws2. auto. }
      }
    }
  Qed.

  Lemma get_layer_next lh i vs n es lh' es' vs0' n1 es0 vs' n2 es2 lh0 es2' es0' :
    get_layer lh (S i) = Some (vs, n, es, lh', es') ->
    get_layer lh i = Some (vs0', n1, es0, LH_rec vs' n2 es2 lh0 es2', es0') ->
    vs = vs' ∧ n = n2 ∧ es2 = es ∧ lh' = lh0 ∧ es' = es2'.
  Proof.
    revert i vs n es lh' es' vs0' n1 es0 vs' n2 es2 lh0 es2' es0'.
    induction lh;intros i vs m es lh' es' vs0' n1 es0 vs' n2 es2 lh0 es2' es0' Hlayer1 Hlayer2.
    { destruct i;done. }
    { destruct i.
      { simpl in *. simplify_eq. simpl in *. simplify_eq. auto. }
      { simpl in *. eapply IHlh in Hlayer1;eauto. }
    }
  Qed.
    
  Lemma wp_label_push_inv (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es i lh n es' l1 l2 :
    const_list l1 ->
    WP [::AI_label n es' (l1 ++ es ++ l2)] @ s; E CTX i; lh {{ Φ }}
    ⊢ WP es @ s; E CTX S i; push_base lh n es' l1 l2 {{ Φ }}.
  Proof.
    iIntros (Hconst) "HWP".
    iIntros (LI Hfill%lfilled_Ind_Equivalent).
    apply lfilledInd_push_inv in Hfill;auto.
    iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
    iPureIntro. by apply lfilled_Ind_Equivalent.
  Qed.
  Lemma wp_label_push_nil_inv (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es i lh n es' :
    WP [::AI_label n es' es] @ s; E CTX i; lh {{ Φ }}
    ⊢ WP es @ s; E CTX S i; push_base lh n es' [] [] {{ Φ }}.
  Proof.
    iIntros "HWP".
    iDestruct (wp_label_push_inv with "[HWP]") as "HWP";auto.
    { auto. }
    erewrite app_nil_l. erewrite app_nil_r. done.
  Qed.

  Lemma lh_depth_frame_base lh l1 l2 :
    lh_depth (frame_base lh l1 l2) = lh_depth lh.
  Proof.
    induction lh;auto.
    simpl. rewrite IHlh. auto.
  Qed.

  Lemma get_layer_frame_base l1 l2 i lh vs n es lh' es' :
    get_layer lh i = Some (vs,n,es,lh',es') ->
    get_layer (frame_base lh l1 l2) i = Some (vs,n,es,frame_base lh' l1 l2,es').
  Proof.
    revert i;induction lh;intros i;simpl.
    { done. }
    destruct i;simpl;auto.
    intros Heq;simplify_eq. auto.
  Qed.

  Lemma lookup_snoc {A : Type} (l : list A) (a : A) :
    (l ++ [a]) !! (length l) = Some a.
  Proof.
    induction l;auto.
  Qed.

  Lemma get_layer_lookup_lh_lengths l lh i ts vs' n2 es lh' es2' :
    lholed_lengths (rev l) lh ->
    l !! i = Some ts ->
    get_layer lh (lh_depth lh - S i) = Some (vs', n2, es, lh', es2') ->
    n2 = length ts.
  Proof.
    revert lh i ts vs' n2 es lh' es2'.
    induction l using rev_ind;intros lh i ts vs' n2 es lh' es2' Hlen Hlook Hlay.
    { done. }
    { apply lholed_lengths_length_depth in Hlen as Hdep.
      rewrite rev_length in Hdep.
      destruct lh;[done|].
      destruct (decide (i = length l)).
      { subst. simpl in *.
        rewrite app_length /= PeanoNat.Nat.add_1_r in Hdep.
        inversion Hdep as [Heq].
        rewrite Heq PeanoNat.Nat.sub_diag in Hlay. simplify_eq.
        rewrite rev_unit in Hlen. simpl in Hlen. destruct Hlen as [? ?].
        rewrite lookup_snoc in Hlook. by simplify_eq. }
      { apply lookup_lt_Some in Hlook as Hlt.
        rewrite app_length /= PeanoNat.Nat.add_1_r in Hlt.
        assert (i < length l) as Hlt';[lia|].
        rewrite lookup_app_l in Hlook;auto.
        simpl in Hlay.
        rewrite app_length /= PeanoNat.Nat.add_1_r in Hdep.
        inversion Hdep as [Heq].
        destruct (lh_depth lh - i) eqn:Hi;[lia|].
        assert (n1 = lh_depth lh - S i);[lia|subst n1].
        eapply IHl in Hlook;eauto.
        rewrite rev_unit in Hlen. inversion Hlen;auto.
      }
    }
  Qed.

  Lemma lh_minus_is_Some_frame_base lh lh'' l1 l2 :
    is_Some (lh_minus (frame_base lh l1 l2) lh'') ->
    is_Some (lh_minus lh lh'').
  Proof.
    revert lh'';induction lh;intros lh'' [x Hx].
    { destruct lh'';try done. destruct l3,l4;try done. }
    { destruct lh''.
      { apply lh_minus_Ind_Equivalent in Hx.
        inversion Hx;subst. eauto. }
      { apply lh_minus_Ind_Equivalent in Hx.
        inversion Hx;subst.
        destruct IHlh with (lh'':=lh'') as [y Hy].
        { exists x. apply lh_minus_Ind_Equivalent;eauto. }
        exists y. apply lh_minus_Ind_Equivalent.
        constructor. apply lh_minus_Ind_Equivalent. auto. }
    }
  Qed.
  
  Lemma push_base_return v lh tm n es f Φf :
    lholed_valid lh ->
    interp_val tm (immV v) -∗
    ↪[frame] f -∗
    Φf f -∗           
    (∀ f, ↪[frame] f ∗ Φf f -∗ WP of_val (immV v) CTX lh_depth lh; lh {{ vs, interp_val tm vs ∗ ∃ f, ↪[frame]f ∗ Φf f }}) -∗
    WP of_val (immV v) CTX S (lh_depth lh); push_base lh n es [] []
                    {{ vs, interp_val tm vs ∗ ∃ f, ↪[frame]f ∗ Φf f }}.
  Proof.
    iInduction lh as [] "IH".
    { simpl. iIntros (Hvalid) "#Hv Hf Hfv H".
      iApply (wp_val_return' with "[$Hf] [H Hfv]").
      { apply const_list_of_val. }
      { iIntros "Hf". iApply wp_wasm_empty_ctx.
        iApply wp_base_push;auto. simpl. erewrite app_nil_r.
        iApply "H". iFrame.
      }
    }
    { iIntros (Hvalid) "#Hv Hf Hfv H".
      iApply (wp_label_push_nil_inv with "[Hf H Hfv]").
      iSimpl.
      iApply iRewrite_nil_r_ctx.
      iApply (wp_seq_can_trap_ctx _ _ _
                (λ vs, (⌜vs = immV v⌝ ∗ ([∗ list] w;τ ∈ v;tm, interp_value τ w))))%I.
      iFrame. iSplitR.
      { iIntros "Hcontr".
        iDestruct "Hcontr" as "[%Hcontr _]". done. }
      iSplit;[auto|].
      iSplitL "Hfv".
      { iIntros "Hf".
        iApply (wp_wand _ _ _ (λ w, ((⌜w = trapV⌝ ∨ ⌜w = immV v⌝ ∗ ([∗ list] w0;τ ∈ v;tm, interp_value τ w0)) ∗ ↪[frame] f) ∗ Φf f )%I with "[Hf Hfv]").
        { iApply wp_frame_r. iFrame "Hfv".
          iApply (wp_label_value with "Hf");[by rewrite of_val_imm to_of_val|].
          iDestruct "Hv" as "[%Hcontr | #Hv]";[done|].
          iDestruct "Hv" as (ws Heq) "Hv". simplify_eq.
          auto. }
        { iIntros (v0) "[[Hv0 Hf] Hfv]".
          iSplitR "Hf Hfv";[|iExists _; iFrame]. auto. } }
      { iIntros (w f0) "[[-> Hw] [Hf0 Hf0v]]".
        rewrite app_nil_r. iApply "H". iFrame.
      }
    }
  Qed.

  Lemma get_layer_lh_depth lh i vs n lh' es' :
    i < lh_depth lh ->
    get_layer lh (lh_depth lh - S i) = Some (vs,n,lh',es') ->
    lh_depth lh' = i.
  Proof.
    revert i vs n lh' es'.
    induction lh;intros i vs m lh' es' Hlt Hlayer;try done.
    simpl in *.
    destruct (lh_depth lh - i) eqn:Hn.
    { inversion Hlayer;subst.
      lia. }
    { assert (i < lh_depth lh);[lia|].
      eapply IHlh;eauto.
      assert (lh_depth lh - S i = n0) as ->;[lia|].
      eauto. }
  Qed.

  Lemma lh_minus_push_base_Some lh n es vs1 es2 :
    base_is_empty lh ->
    lh_minus (push_base lh n es vs1 es2) lh = Some (LH_rec [] n es (LH_base vs1 es2) []).
  Proof.
    intros Hemp.
    apply lh_minus_Ind_Equivalent.
    induction lh.
    { destruct Hemp as [-> ->]. simpl. constructor. }
    { simpl in *. constructor. apply IHlh;auto. }
  Qed.

  Lemma push_base_lh_minus_is_Some lh n es vs1 es2 lh'' :
    is_Some (lh_minus lh lh'') ->
    is_Some (lh_minus (push_base lh n es vs1 es2) lh'').
  Proof.
    intros [x Hx%lh_minus_Ind_Equivalent].
    induction Hx.
    { destruct lh;simpl;eauto. }
    { destruct IHHx as [y Hy]. eexists. apply lh_minus_Ind_Equivalent. simpl. constructor.
      apply lh_minus_Ind_Equivalent. eauto. }
  Qed.

  Lemma to_val_fmap ws :
    to_val ((λ v : value, AI_basic (BI_const v)) <$> ws) = Some (immV ws).
  Proof.
    induction ws;auto.
    rewrite fmap_cons.
    simpl. rewrite IHws. auto.
  Qed.

  Lemma interp_instance_function_lookup C i tf j :
    ssrnat.leq (S i) (length (tc_func_t C)) ->
    nth_error (tc_func_t C) i = Some tf ->
    ⊢ interp_instance (HWP:=HWP) C j -∗
      ∃ f, ⌜nth_error (inst_funcs j) i = Some f⌝ ∗ interp_function (HWP:=HWP) tf (N.of_nat f).
  Proof.
    iIntros (Hle Hnth) "#Hi".
    destruct C,j.
    iDestruct "Hi" as "[_ [Hi _]]".
    iDestruct (big_sepL2_length with "Hi") as %Hlen.
    simpl in Hle,Hnth.
    destruct (nth_error inst_funcs i) eqn:Hsome;cycle 1.
    { exfalso. apply nth_error_None in Hsome.
      rewrite Hlen in Hsome. revert Hle. move/ssrnat.leP. lia. }
    rewrite nth_error_lookup in Hnth.
    rewrite nth_error_lookup in Hsome.
    iDestruct (big_sepL2_lookup with "Hi") as "HH";eauto.
    iExists f. iSimpl. rewrite nth_error_lookup. auto.
  Qed.

  Lemma interp_instance_lookup_global C j i t :
    option_map tg_t (nth_error (tc_global C) i) = Some t ->
    ⊢ interp_instance (HWP:=HWP) C j -∗
      ∃ gt mut n, ⌜nth_error (tc_global C) i = Some gt⌝ ∗
                ⌜nth_error (inst_globs j) i = Some n⌝ ∗
                ⌜gt = Build_global_type mut t⌝ ∗
                interp_global gt (N.of_nat n).
  Proof.
    destruct C,j.
    iIntros (Hmap) "[_ [_ [_ [_ #Hi]]]]".
    iSimpl. simpl in Hmap.
    destruct (nth_error tc_global i) eqn:Hnth;[|done].
    inversion Hmap;subst t.
    destruct g;simplify_eq.
    rewrite nth_error_lookup in Hnth.
    apply lookup_lt_Some in Hnth as Hlt.
    iDestruct (big_sepL2_length with "Hi") as %Hlen.
    rewrite -Hlen in Hlt.
    apply lookup_lt_is_Some_2 in Hlt as [? ?].
    iExists _,tg_mut,x. repeat iSplit;eauto.
    { rewrite nth_error_lookup;auto. }
    iSimpl.
    iDestruct (big_sepL2_lookup with "Hi") as "Hw";[eauto..|].
    iFrame "Hw".
  Qed.

  Lemma interp_instance_get_mem C i :
    tc_memory C ≠ [] ->
    ⊢ interp_instance (HWP:=HWP) C i -∗
      ∃ τm mem, ⌜nth_error (tc_memory C) 0 = Some τm⌝
              ∗ ⌜nth_error (inst_memory i) 0 = Some mem⌝
              ∗ interp_mem τm (N.of_nat mem).
  Proof.
    destruct C,i.
    iIntros (Hnil) "[_ [_ [ _ [#Hi _]]]]".
    iSimpl.
    simpl in Hnil.
    destruct tc_memory;try done.
    iSimpl in "Hi".
    destruct inst_memory;try done.
    iExists _,_. repeat iSplit;eauto.
  Qed.

  Global Instance global_inhabited : Inhabited global.
  Proof. apply populate. exact (Build_global MUT_mut (VAL_int32 int32_minus_one)). Qed.

  Global Instance value_inhabited : Inhabited value.
  Proof. apply populate. exact (VAL_int32 int32_minus_one). Qed.
  
End fundamental.
