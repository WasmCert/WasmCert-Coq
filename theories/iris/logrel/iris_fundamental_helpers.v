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

  Context `{!wasmG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
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
    rewrite fmap_cons. rewrite to_val_cons_immV.
    auto.
  Qed.

  Lemma interp_instance_function_lookup C i tf j :
    ssrnat.leq (S i) (length (tc_func_t C)) ->
    nth_error (tc_func_t C) i = Some tf ->
    ⊢ interp_instance (HWP:=HWP) C j -∗
      ∃ f, ⌜nth_error (inst_funcs j) i = Some f⌝ ∗ interp_function tf (λ _, interp_closure (HWP:=HWP)) (N.of_nat f).
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
    iExists _. iFrame "HH". simpl. rewrite nth_error_lookup//.
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
              ∗ (N.of_nat mem) ↪[wmlimit] lim_max τm
              ∗ interp_mem (N.of_nat mem).
  Proof.
    destruct C,i.
    iIntros (Hnil) "[_ [_ [ _ [#Hi _]]]]".
    iSimpl.
    simpl in Hnil.
    destruct tc_memory;try done.
    iSimpl in "Hi".
    destruct inst_memory;try done.
    iDestruct "Hi" as "[? ?]".
    iExists _,_. repeat iSplit;eauto.    
  Qed.

  Fixpoint pull_base_l_drop_len {i : nat} (vh : valid_holed i) (len : nat) :=
  match vh with
  | VH_base j vs es => (VH_base j (take len vs) es, drop len vs)
  | @VH_rec j vs m es' lh' es => let '(lh'',l1) := pull_base_l_drop_len lh' len in
                             (@VH_rec j vs m es' lh'' es,l1)
  end.

  Lemma vfill_pull_base_l_take_len {i : nat} (vh : valid_holed i) (len : nat) es vh' vs :
    pull_base_l_drop_len vh len = (vh', vs) ->
    vfill vh es = vfill vh' (((λ x : value, AI_basic (BI_const x)) <$> vs) ++ es).
  Proof.
    intros Heq.
    induction vh.
    { simpl in *. simplify_eq. simpl.
      rewrite -!app_assoc. rewrite fmap_take fmap_drop.
      rewrite (app_assoc (take _ _)).
      rewrite (take_drop len ((λ x : value, AI_basic (BI_const x)) <$> l)). auto. }
    { simpl in *.
      destruct (pull_base_l_drop_len vh len) eqn:Heq'.
      simplify_eq. simpl. f_equiv. f_equiv.
      erewrite IHvh;eauto. 
    }
  Qed.

  Lemma lh_depth_pull_base_l_take_len {i : nat} (vh : valid_holed i) (len : nat) vh' vs :
    pull_base_l_drop_len vh len = (vh', vs) ->
    lh_depth (lh_of_vh vh) = lh_depth (lh_of_vh vh').
  Proof.
    intros Heq.
    induction vh;simpl in *;simplify_eq;auto.
    destruct (pull_base_l_drop_len vh len) eqn:Heq'.
    simplify_eq. simpl. erewrite IHvh;eauto.
  Qed.

  Lemma length_pull_base_l_take_len {i : nat} (vh : valid_holed i) (len : nat) vh' vs vs' :
    get_base_l vh = vs' ->
    pull_base_l_drop_len vh len = (vh', vs) ->
    length vs = length vs' - len.
  Proof.
    intros Hbase Hpull.
    induction vh;simpl in *;simplify_eq.
    { rewrite drop_length. auto. }
    { destruct (pull_base_l_drop_len vh len) eqn:Heq'.
      simplify_eq. simpl. erewrite IHvh;eauto. }
  Qed.

  Lemma take_drop_pull_base_l_take_len {i : nat} (vh : valid_holed i) (len : nat) vh' vs vs' :
    len <= length vs' ->
    get_base_l vh = vs' ->
    pull_base_l_drop_len vh len = (vh', vs) ->
    vs' = take len vs' ++ vs.
  Proof.
    intros Hle Hbase Hpull.
    induction vh;simpl in *;simplify_eq.
    { rewrite take_drop. auto. }
    { destruct (pull_base_l_drop_len vh len) eqn:Heq'.
      simplify_eq. simpl. erewrite IHvh;eauto.
      assert (len = length (take len (get_base_l vh))) as Heq.
      { rewrite take_length. lia. }
      assert (take len (take len (get_base_l vh) ++ vs)%list ++ vs =
                take (length (take len (get_base_l vh)))
                     (take len (get_base_l vh) ++ vs)%list ++ vs) as ->;[rewrite -Heq;auto|].      
      rewrite take_app. auto.
    }
  Qed.

  Lemma vfill_label {i : nat} vh n es e :
    [AI_label n es (vfill vh e)] = vfill (@VH_rec i [] n es vh []) e.
  Proof.
    induction vh;simpl;auto.
  Qed.

  Lemma sfill_label vh n es e :
    [AI_label n es (sfill vh e)] = sfill (SH_rec [] n es vh []) e.
  Proof.
    induction vh;simpl;auto.
  Qed.

  Lemma lh_depth_ge {i : nat} (vh : valid_holed i) p :
    lh_depth (lh_of_vh vh) = p ->
    i >= p.
  Proof.
    revert p.
    induction vh;intros p;simpl;[lia|].
    intros Hlen.
    destruct p;try done.
    inversion Hlen.
    apply IHvh in H0. lia.
  Qed.

  Lemma vh_destruct {i : nat} (vh : valid_holed i) :
    (∃ vs es, vh = VH_base i vs es) ∨
    (∃ vs n es' (vh' : valid_holed i) es, vh_increase vh = @VH_rec i vs n es' vh' es).
  Proof.
    destruct vh;eauto.
    right. simpl.
    repeat eexists.
  Qed.

  Lemma lh_depth_le_None_false {i : nat} (vh : valid_holed (S i)) :
    lh_depth (lh_of_vh vh) <= i ->
    vh_decrease vh = None ->
    False.
  Proof.
    set (m := S i) in vh.
    pose (Logic.eq_refl : m = S i) as Hm.
    change vh with match Hm in _ = w return valid_holed w with
                  | Logic.eq_refl => vh end.
    clearbody m Hm.
    generalize dependent i.
    induction vh;intros m Hm.
    { destruct n;[done|].
      pose proof (eq_add_S _ _ Hm) as Hn.
      assert (Hm = f_equal S Hn) as Hproof.
      { apply Eqdep.EqdepTheory.UIP. }
      
      replace (vh_decrease match Hm in _ = w return valid_holed w with
                           | Logic.eq_refl => VH_base (S n) l l0 end) with
        match Hn in _ = w return option (valid_holed w) with
        | Logic.eq_refl => vh_decrease (VH_base (S n) l l0) end ;
        last by rewrite Hproof ; destruct Hn.
      cbn. destruct Hn. done. }
    { pose proof (eq_add_S _ _ Hm) as Hn.
      assert (Hm = f_equal S Hn) as Hproof.
      { apply Eqdep.EqdepTheory.UIP. }
      replace (vh_decrease match Hm in _ = w return valid_holed w with
                           | Logic.eq_refl => VH_rec l n0 l0 vh l1 end) with
        match Hn in _ = w return option (valid_holed w) with
        | Logic.eq_refl => vh_decrease (VH_rec l n0 l0 vh l1) end ;
        last by rewrite Hproof ; destruct Hn.
      simpl. intros Hdep.
      destruct n ; first destruct Hn.
      { exfalso. rewrite Hproof in Hdep.  simpl in Hdep. lia. }
      destruct m => //.
      pose proof (eq_add_S _ _ Hn) as Hp.
      assert (Hn = f_equal S Hp) as Hproof'.
      { apply Eqdep.EqdepTheory.UIP. }
      replace  match Hn in (_ = w) return (option (valid_holed w)) with
               | Logic.eq_refl =>
                   match vh_decrease vh with
                   | Some vh' => Some (VH_rec l n0 l0 vh' l1)
                   | None => None
                   end
               end with match vh_decrease match Hn in (_ = w) return valid_holed w with
                                          | Logic.eq_refl => vh end with
                        | Some vh' => Some (VH_rec l n0 l0 vh' l1)
                        | None => None end ;
        last by rewrite Hproof' ; destruct Hp.
      
      destruct (vh_decrease _) eqn:Hdecr1 => //.
      apply IHvh in Hdecr1;[done|].
      subst. simpl in *.
      lia.
    }
  Qed.

  Lemma lh_depth_le_vh_decrease {i : nat} (vh : valid_holed (S i)) :
    lh_depth (lh_of_vh vh) <= i ->
    exists vs', vh_decrease vh = Some vs'.
  Proof.
    intros Hdep.
    destruct (vh_decrease vh) eqn:Hvh;eauto.
    exfalso.
    eapply lh_depth_le_None_false;eauto.
  Qed.

  Lemma lh_depth_vh_decrease_eq {i : nat} (vh : valid_holed (S i)) vh' :
    vh_decrease vh = Some vh' ->
    lh_depth (lh_of_vh vh) = (lh_depth (lh_of_vh vh')).
  Proof.
    set (m := S i) in vh.
    pose (Logic.eq_refl : m = S i) as Hm.
    change vh with match Hm in _ = w return valid_holed w with
                  | Logic.eq_refl => vh end.
    clearbody m Hm.
    generalize dependent i.
    induction vh;intros m vh' Hm.
    { destruct n;[done|].
      pose proof (eq_add_S _ _ Hm) as Hn.
      assert (Hm = f_equal S Hn) as Hproof.
      { apply Eqdep.EqdepTheory.UIP. }
      
      replace (vh_decrease match Hm in _ = w return valid_holed w with
                           | Logic.eq_refl => VH_base (S n) l l0 end) with
        match Hn in _ = w return option (valid_holed w) with
        | Logic.eq_refl => vh_decrease (VH_base (S n) l l0) end ;
        last by rewrite Hproof ; destruct Hn.
      cbn. destruct Hn. destruct vh';[|done].
      intros HH. simplify_eq. done. }
    { pose proof (eq_add_S _ _ Hm) as Hn.
      assert (Hm = f_equal S Hn) as Hproof.
      { apply Eqdep.EqdepTheory.UIP. }
      replace (vh_decrease match Hm in _ = w return valid_holed w with
                           | Logic.eq_refl => VH_rec l n0 l0 vh l1 end) with
        match Hn in _ = w return option (valid_holed w) with
        | Logic.eq_refl => vh_decrease (VH_rec l n0 l0 vh l1) end ;
        last by rewrite Hproof ; destruct Hn.
      simpl. intros Hdep.
      destruct n ; first by destruct Hn.
      destruct m => //.
      pose proof (eq_add_S _ _ Hn) as Hp.
      assert (Hn = f_equal S Hp) as Hproof'.
      { apply Eqdep.EqdepTheory.UIP. }
      rewrite Hproof. subst. simpl in *.
      destruct (vh_decrease _)  eqn:Hdecr1 =>//.
      simplify_eq.
      simpl in *. f_equiv.
      pose (Logic.eq_refl : S m = S m) as Hm.
      change vh with match Hm in _ = w return valid_holed w with
                     | Logic.eq_refl => vh end.
      apply IHvh.
      simpl. auto. }
  Qed.

  Lemma get_base_l_vh_decrease_eq {i : nat} (vh : valid_holed (S i)) vh' :
    vh_decrease vh = Some vh' ->
    get_base_l vh = (get_base_l vh').
  Proof.
    set (m := S i) in vh.
    pose (Logic.eq_refl : m = S i) as Hm.
    change vh with match Hm in _ = w return valid_holed w with
                  | Logic.eq_refl => vh end.
    clearbody m Hm.
    generalize dependent i.
    induction vh;intros m vh' Hm.
    { destruct n;[done|].
      pose proof (eq_add_S _ _ Hm) as Hn.
      assert (Hm = f_equal S Hn) as Hproof.
      { apply Eqdep.EqdepTheory.UIP. }
      
      replace (vh_decrease match Hm in _ = w return valid_holed w with
                           | Logic.eq_refl => VH_base (S n) l l0 end) with
        match Hn in _ = w return option (valid_holed w) with
        | Logic.eq_refl => vh_decrease (VH_base (S n) l l0) end ;
        last by rewrite Hproof ; destruct Hn.
      cbn. destruct Hn. destruct vh';[|done].
      intros HH. simplify_eq. done. }
    { pose proof (eq_add_S _ _ Hm) as Hn.
      assert (Hm = f_equal S Hn) as Hproof.
      { apply Eqdep.EqdepTheory.UIP. }
      replace (vh_decrease match Hm in _ = w return valid_holed w with
                           | Logic.eq_refl => VH_rec l n0 l0 vh l1 end) with
        match Hn in _ = w return option (valid_holed w) with
        | Logic.eq_refl => vh_decrease (VH_rec l n0 l0 vh l1) end ;
        last by rewrite Hproof ; destruct Hn.
      simpl. intros Hdep.
      destruct n ; first by destruct Hn.
      destruct m => //.
      pose proof (eq_add_S _ _ Hn) as Hp.
      assert (Hn = f_equal S Hp) as Hproof'.
      { apply Eqdep.EqdepTheory.UIP. }
      rewrite Hproof. subst. simpl in *.
      destruct (vh_decrease _)  eqn:Hdecr1 =>//.
      simplify_eq.
      simpl in *.
      pose (Logic.eq_refl : S m = S m) as Hm.
      change vh with match Hm in _ = w return valid_holed w with
                     | Logic.eq_refl => vh end.
      apply IHvh.
      simpl. auto. }
  Qed.

  Lemma get_layer_push_inv lh n es v e i vs' k es' lh' es'' :
    lh_depth lh - i > 0 ->
    get_layer (push_base lh n es v e) (lh_depth lh - S i) = Some (vs', k, es', lh', es'') ->
    ∃ lh0, lh' = push_base lh0 n es v e ∧
                          get_layer lh (lh_depth lh - S i) = Some (vs',k,es',lh0,es'').
  Proof.
    induction lh;simpl.
    { intros Hgt Heq. simplify_eq. lia. }
    { intros Hgt Heq.
      destruct (lh_depth lh - i) eqn:Hs.
      { simplify_eq. repeat eexists. }
      destruct lh.
      { simpl in *. destruct n1;[|done]. simplify_eq. }
      simpl in *.
      destruct n1.
      { simplify_eq. repeat eexists. }
      assert (Hs':=Hs).
      rewrite -minus_Sn_m in Hs;[|lia].
      inversion Hs.
      rewrite H0 in IHlh.
      apply IHlh;[lia|].
      auto. 
    }
  Qed.

  Lemma interp_br_stuck_push C (j : nat) (vh: valid_holed j) m vs p i tm tm' lh f' e τto :
    m = length tm ->
    get_base_l vh = vs ->
    lh_depth (lh_of_vh vh) = p ->
    j ≠ p ->
    lholed_lengths (rev (tc_label C)) lh ->
    lholed_valid lh ->
    base_is_empty lh ->
    interp_br_body (tc_label (upd_label C ([tm] ++ tc_label C)))
                   (push_base lh (length tm) e [] [])
                   j p vs (tc_local C) i τto -∗
    ↪[frame]f' -∗
    interp_frame (tc_local C) i f' -∗
    WP [AI_label m e
        (vfill vh [AI_basic (BI_br j)])]
      {{ v, (interp_val tm' v ∨ interp_br (tc_local C) i τto v lh (tc_label C) ∨ interp_return_option τto (tc_local C) i v) ∗
           (∃ f0,  ↪[frame]f0 ∗ interp_frame (tc_local C) i f0) }}.
  Proof.
    iIntros (Hlen Hbase Hsize n Hlh_length Hlh_valid Hlh_empty) "Hbr Hf Hfv".
    unfold interp_br_body.
    apply lh_depth_ge in Hsize as Hge.
    assert (j > p);[lia|].
    destruct j;[lia|].
    assert (lh_depth (lh_of_vh vh) <= j) as Hdec.
    { rewrite Hsize. lia. }
    apply lh_depth_le_vh_decrease in Hdec as [vs' Hvs'].
    rewrite vfill_label.
    
    erewrite vfill_decrease;cycle 1.
    { simpl. rewrite Hvs'. eauto. }
    eassert (vfill _ [AI_basic (BI_br (S j))] = of_val (brV _)) as ->.
    { simpl of_val. f_equiv. }
    rewrite -!minus_Sn_m;[|lia].
        
    iApply wp_value;[done|].
    iSplitR "Hf Hfv";[|iExists _;iFrame;iExists _;eauto].
    iRight. iLeft.
    iApply fixpoint_interp_br_eq. iSimpl.
    rewrite lh_depth_push_base.
    rewrite PeanoNat.Nat.sub_succ.
        
    iDestruct "Hbr" as (? ? ? ? ? ? ? ? Hlook Hlayer) "Hbr".
    simpl in Hlook.
    iExists _,_,_,(S p). iSplit;[eauto|].
    iDestruct "Hbr" as (Hdepth Hmin) "[#Hvalvs Hbr]".
    iDestruct "Hvalvs" as "[%Hcontr|Hvalvs]";[done|].
    iDestruct "Hvalvs" as (vs'' Heqv) "Hvalvs".
    iSplit;[eauto|]. iSplit;[eauto|].
    { iPureIntro. simpl. erewrite <-lh_depth_vh_decrease_eq;eauto. }
        
    rewrite !Nat.sub_succ.
    apply lholed_lengths_length_depth in Hlh_length as Hlen'.
    rewrite rev_length in Hlen'. apply lookup_lt_Some in Hlook as Hlt.
    rewrite Hlen' in Hlt.
    apply get_layer_push_inv in Hlayer as Hlayer';[|lia].
    destruct Hlayer' as [lh0 [Hlh'eq Hlayer2]].
    subst lh'.
    iExists _,_,_,_,_,_,_,_. iSplit;[eauto|]. iSplit;[eauto|]. iSplit;[eauto|].
    iSplit.
    { iPureIntro. eapply lh_minus_push_base_is_Some;eauto. rewrite Hdepth. lia. }
    iSimpl. erewrite <-get_base_l_vh_decrease_eq;eauto.
    iSplit.
    { iRight. iExists _. iSplit;eauto. simplify_eq. iFrame "Hvalvs". }
    iIntros (f0) "[Hf0 Hf0v]".
    iSpecialize ("Hbr" with "[$]").
    rewrite Hbase. rewrite lh_depth_push_base.
    apply get_layer_lh_depth in Hlayer2 as Hlh0depth;[|lia].
    rewrite Hlh0depth.
    iDestruct (big_sepL2_length with "Hvalvs") as %Hlen_vs''.
    rewrite -(take_drop (length τs'') vs''). rewrite app_length in Hlen_vs''.
    iDestruct (big_sepL2_app_inv with "Hvalvs") as "[Hvalvs1 Hvalvs2]".
    { right. rewrite drop_length. lia. }
    iDestruct (big_sepL2_length with "Hvalvs2") as %HH.
    iDestruct (wp_br_ctx_shift_inv with "Hbr") as "Hbr".
    { apply const_list_of_val. }
    { auto. }
    { rewrite fmap_length. rewrite drop_length.
      eapply get_layer_lookup_lh_lengths in Hlh_length;eauto.
      simplify_eq. rewrite drop_length in HH. auto. }
    simpl. iFrame.
  Qed.

  Lemma const_list_map ws1 :
    const_list (map (λ x : value, AI_basic (BI_const x)) ws1).
  Proof.
    induction ws1;auto.
  Qed.

  Lemma lfilled_simple_get_base_pull j sh e LI ws1 ws2 :
    simple_get_base_l sh = ws1 ++ ws2 ->
    lfilled j (lh_of_sh sh) e LI ->
    ∃ lh, lfilled j lh (of_val (immV ws2) ++ e) LI.
  Proof.
    revert j e LI ws1 ws2.
    induction sh;intros j e LI ws1 ws2 Hbase Hfill%lfilled_Ind_Equivalent.
    { simpl in *. inversion Hfill;simplify_eq.
      eexists. rewrite map_app.
      repeat erewrite <- app_assoc. erewrite (app_assoc _ e).
      apply lfilled_Ind_Equivalent. constructor.
      apply const_list_map. }
    { simpl in Hfill. inversion Hfill;simplify_eq.
      apply lfilled_Ind_Equivalent in H8.
      eapply IHsh in H8 as Hlh';eauto.
      destruct Hlh' as [lh Hfill'].
      eexists.
      apply lfilled_Ind_Equivalent.
      constructor;eauto.
      apply lfilled_Ind_Equivalent;eauto. }
  Qed.

  Lemma lfilled_get_base_pull {i : nat} j (vh : valid_holed i) e LI ws1 ws2 :
    get_base_l vh = ws1 ++ ws2 ->
    lfilled j (lh_of_vh vh) e LI ->
    ∃ lh, lfilled j lh (of_val (immV ws2) ++ e) LI.
  Proof.
    revert j e LI ws1 ws2.
    induction vh;intros j e LI ws1 ws2 Hbase Hfill%lfilled_Ind_Equivalent.
    { simpl in *. inversion Hfill;simplify_eq.
      eexists. rewrite map_app.
      repeat erewrite <- app_assoc. erewrite (app_assoc _ e).
      apply lfilled_Ind_Equivalent. constructor.
      apply const_list_map. }
    { simpl in Hfill. inversion Hfill;simplify_eq.
      apply lfilled_Ind_Equivalent in H8.
      eapply IHvh in H8 as Hlh';eauto.
      destruct Hlh' as [lh Hfill'].
      eexists.
      apply lfilled_Ind_Equivalent.
      constructor;eauto.
      apply lfilled_Ind_Equivalent;eauto. }
  Qed.

  Lemma interp_return_label C tn i w f' tm lh es m :
    interp_return_option
      (tc_return (upd_label C ([tn] ++ tc_label C)))
      (tc_local (upd_label C ([tn] ++ tc_label C))) i w -∗
  ↪[frame]f' -∗
  interp_frame (tc_local C) i f' -∗
  WP of_val w CTX 1; LH_rec [] m es (LH_base [] []) []
  {{ v, (interp_val tm v ∨ interp_br (tc_local C) i (tc_return C) v lh (tc_label C)
         ∨ interp_return_option (tc_return C) (tc_local C) i v) ∗
           (∃ f0 : frame,  ↪[frame]f0 ∗ interp_frame (tc_local C) i f0) }}.
  Proof.
    iIntros "Hret Hf Hfv".
    iDestruct "Hret" as (sh v -> Hbase) "Hret".
    simpl of_val. 
    destruct (tc_return (upd_label C ([tn] ++ tc_label C))) eqn:Hret;[|done].
    iDestruct "Hret" as (τs'') "[#Hw Hret]".
    iDestruct "Hw" as "[%Hcontr|Hw]";[done|iDestruct "Hw" as (? Heq) "Hw"].
    inversion Heq; subst ws.
    pose proof (sfill_to_lfilled sh ([AI_basic BI_return])) as Hj.
    eapply (lfilled_simple_get_base_pull _ _ _ _ (take (length τs'') v) (drop (length τs'') v)) in Hj as Hj2.
    2: rewrite take_drop;eauto. destruct Hj2 as [lh' Hlh'].
    
    assert (LH_rec [] m es (LH_base [] []) [] =
              push_base (LH_base [] []) m es [] []) as Heq';[auto|].
    rewrite Heq'.
    iApply wp_label_push_nil_inv. iApply wp_wasm_empty_ctx.
    
    rewrite sfill_label.
    eassert (sfill (SH_rec [] m es sh []) [AI_basic BI_return] = of_val (retV _)) as Hval.
    { simpl of_val. f_equiv. eauto. }
    rewrite !Hval.
    iApply wp_value;[done|].
    iSplitR "Hf Hfv";[|iExists _;iFrame;iExists _;eauto].
    iRight. iRight.
    iExists _,_. iSplit;[eauto|]. iSplit;[eauto|].
    assert (tc_return C = Some l) as ->;auto.
    iExists _. iSplitR. { iRight. iExists _. eauto. }
    iIntros (f0 f1) "[Hf Hfv]". iSpecialize ("Hret" $! f0 with "[$]").
    iDestruct (big_sepL2_length with "Hw") as %Hlen'.
    iApply (wp_ret_shift with "Hret");cycle 2.
    { simpl of_val. eauto. }
    { simpl of_val. simpl of_val in Hlh'.
      assert ([AI_label m es (sfill sh [AI_basic BI_return])] =
                [] ++ [AI_label m es (sfill sh [AI_basic BI_return])] ++ []) as ->;auto.
      apply lfilled_Ind_Equivalent. constructor;auto.
      apply lfilled_Ind_Equivalent. eauto.
    }
    { apply const_list_of_val. }
    { rewrite fmap_length drop_length. rewrite app_length in Hlen'.
      apply Nat.add_sub_eq_r. rewrite Hlen'. lia. }
  Qed.    
  
  Global Instance global_inhabited : Inhabited global.
  Proof. apply populate. exact (Build_global MUT_mut (VAL_int32 int32_minus_one)). Qed.

  Global Instance value_inhabited : Inhabited value.
  Proof. apply populate. exact (VAL_int32 int32_minus_one). Qed.

  Global Instance function_closure_inhabited : Inhabited function_closure.
  Proof. apply populate. exact (FC_func_native ({| inst_types := [];
                                                  inst_funcs:=[];
                                                  inst_tab:=[];
                                                  inst_memory:=[];
                                                  inst_globs:=[]|}) (Tf [] []) [] []) . Qed.
  
End fundamental.
