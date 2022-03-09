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

Section fundamental.
  Import DummyHosts. (* placeholder *)

  Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* ------------------------------ HELPER TACTICS AND LEMMAS ------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)
  
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

  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* ----------------------------------------- CONST --------------------------------------- *)
  
  Lemma typing_const C v : ⊢ semantic_typing (HWP:=HWP) C (to_e_list [BI_const v]) (Tf [] [typeof v]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (i lh).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]".
    iIntros (f vs) "[Hf #Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    { iDestruct "Hv" as (ws ->) "Hv".
      iDestruct (big_sepL2_nil_inv_r with "Hv") as %->.
      rewrite app_nil_l. iSimpl.
      assert ([AI_basic (BI_const v)] = of_val (immV [v])) as ->;auto.
      iApply wp_value;[done|]. iSplitR;[|eauto]. iLeft. iRight.
      iExists _. iSplit;eauto.
      iSimpl. iSplit =>//. iApply interp_value_type_of. }
  Qed.

  (* ----------------------------------------- UNOP ---------------------------------------- *)

  Lemma unop_type_agree_interp t op w :
    unop_type_agree t op ->
    ⊢ interp_value t w -∗
      interp_value (Σ:=Σ) t (app_unop op w).
  Proof.
    iIntros (Hunop) "Hv".
    inversion Hunop;subst.
    all: iDestruct "Hv" as (w') "->"; eauto.
  Qed.    
  
  Lemma typing_unop C t op : unop_type_agree t op ->
                             ⊢ semantic_typing (HWP:=HWP) C (to_e_list [BI_unop t op]) (Tf [t] [t]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Hunop i lh).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]".
    iIntros (f vs) "[Hf #Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    { iDestruct "Hv" as (ws ->) "Hv".
      iDestruct (big_sepL2_length with "Hv") as %Hlen.
      destruct ws as [|w ws];[done|destruct ws;[|done]].
      iSimpl in "Hv".
      iDestruct "Hv" as "[Hv _]".
      iSimpl.
      iApply (wp_wand _ _ _ (λ v, ⌜v = immV [app_unop op w]⌝ ∗ ↪[frame] f)%I with "[Hf]").
      { iApply (wp_unop with "Hf");eauto. }
      iIntros (w0) "[-> Hf]".
      iSplitR;[|eauto].
      iLeft. iRight.
      iExists [app_unop op w]. iSplit;auto.
      iSimpl. iSplit;auto.
      iApply unop_type_agree_interp;auto.
    }
  Qed.

  (* ----------------------------------------- BINOP --------------------------------------- *)
  
  Lemma binop_type_agree_interp t op w1 w2 :
    binop_type_agree t op →
    ⊢ interp_value (Σ:=Σ) t w1 -∗
    interp_value t w2 -∗
    ∀ w, ⌜app_binop op w1 w2 = Some w⌝ -∗ interp_value t w.
  Proof.
    iIntros (Hbinop) "Hw1 Hw2".
    inversion Hbinop.
    { iDestruct "Hw1" as (w1') "->".
      iDestruct "Hw2" as (w2') "->".
      iIntros (w Happ).
      cbn in Happ.
      destruct op0;unfold option_map in Happ;simplify_eq;eauto.
      { destruct s;eauto.
        { destruct (Wasm_int.Int32.idiv_s w1' w2');simplify_eq;eauto. }
        { destruct (Wasm_int.Int32.idiv_u w1' w2');simplify_eq;eauto. }
      }
      { destruct s;eauto.
        { destruct (Wasm_int.Int32.irem_s w1' w2');simplify_eq;eauto. }
        { destruct (Wasm_int.Int32.irem_u w1' w2');simplify_eq;eauto. }
      }
      { destruct s;eauto.
        { destruct (Wasm_int.Int32.shr w1' w2');simplify_eq;eauto. }
        { destruct (Wasm_int.Int32.ishr_u w1' w2');simplify_eq;eauto. }
      }
    }
    { iDestruct "Hw1" as (w1') "->".
      iDestruct "Hw2" as (w2') "->".
      iIntros (w Happ).
      destruct op0;simpl in Happ;simplify_eq;eauto.
      { unfold option_map in Happ.
        destruct s;eauto.
        { destruct (Wasm_int.Int64.idiv_s w1' w2');simplify_eq;eauto. }
        { destruct (Wasm_int.Int64.idiv_u w1' w2');simplify_eq;eauto. }
      }
      { unfold option_map in Happ.
        destruct s;eauto.
        { destruct (Wasm_int.Int64.irem_s w1' w2');simplify_eq;eauto. }
        { destruct (Wasm_int.Int64.irem_u w1' w2');simplify_eq;eauto. }
      }
      { unfold option_map in Happ.
        destruct s;eauto.
        { destruct (Wasm_int.Int64.shr w1' w2');simplify_eq;eauto. }
        { destruct (Wasm_int.Int64.ishr_u w1' w2');simplify_eq;eauto. }
      }
    }
    { iDestruct "Hw1" as (w1') "->".
      iDestruct "Hw2" as (w2') "->".
      iIntros (w Happ).
      destruct op0;simpl in Happ;simplify_eq;eauto. }
    { iDestruct "Hw1" as (w1') "->".
      iDestruct "Hw2" as (w2') "->".
      iIntros (w Happ).
      destruct op0;simpl in Happ;simplify_eq;eauto. }
  Qed.
    
  Lemma typing_binop C t op : binop_type_agree t op ->
                              ⊢ semantic_typing (HWP:=HWP) C (to_e_list [BI_binop t op]) (Tf [t; t] [t]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Hbinop i lh).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]".
    iIntros (f vs) "[Hf #Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    { iDestruct "Hv" as (ws ->) "Hv".
      iDestruct (big_sepL2_length with "Hv") as %Hlen.
      destruct ws as [|w1 ws];[done|destruct ws as [|w2 ws];[done|destruct ws;[|done]]].
      iSimpl in "Hv".
      iDestruct "Hv" as "[Hv1 [Hv2 _]]".

      destruct (app_binop op w1 w2) eqn:Hsome.
      
      { iSimpl.
        iApply (wp_wand _ _ _ (λ v, ⌜v = immV [from_option id w1 (app_binop op w1 w2)]⌝ ∗ ↪[frame] f)%I with "[Hf]").
        { iApply (wp_binop with "Hf");eauto. rewrite Hsome. eauto. }
        iIntros (w0) "[-> Hf]".
        iSplitR;[|eauto].
        iLeft. iRight.
        iExists _. iSplit;auto.
        iSimpl. iSplit =>//. iApply (binop_type_agree_interp with "Hv1 Hv2");eauto.
        rewrite Hsome. eauto. }

      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iSimpl.
        iApply wp_binop_failure;auto. }
      { iIntros (v) "[-> Hf]". iSplitR;[|eauto]. iLeft. by iLeft. }
    }
  Qed.

  (* ------------------------------------------ BR ----------------------------------------- *)


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
  
  Lemma typing_br C i t1s ts t2s : ssrnat.leq (S i) (length (tc_label C)) ->
                                   plop2 C i ts ->
                                   ⊢ semantic_typing (HWP:=HWP) C (to_e_list [BI_br i]) (Tf (t1s ++ ts) t2s).
  Proof.
    iIntros (Hleq Hlookup) "".
    iIntros (j lh).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hc]]]" (f vs) "[Hf #Hfv] #Hv".
    unfold interp_expression.
    apply lholed_lengths_length_depth in Hlh_len as Hleneq.
    
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [Hf]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.

    iSimpl.
    rewrite /plop2 nth_error_lookup in Hlookup.
    assert (tc_label C !! i = Some ts) as Hlook;[|clear Hlookup].
    { revert Hlookup. by move/eqP. }
    iApply iRewrite_nil_r. erewrite <- app_assoc.
    pose proof (to_val_br_eq ws i []) as Hval.
    apply of_to_val in Hval.
    iApply wp_value;[done|].
    iSplitR;[|eauto].
    iRight. iApply fixpoint_interp_br_eq. iExists _,_,_. iSplit;[eauto|].
    iDestruct (big_sepL_lookup with "Hc") as (vs n es lh' es' lh'' Hlayer Hdep Hmin) "Hbr";[apply Hlook|].
    rewrite app_length in Hlen.
    apply list_app_split in Hlen as [ws1 [ws2 [-> [Hlen1 Hlen2]]]].
    apply get_layer_lh_depth in Hlayer as Heq;cycle 1.
    { rewrite -(lholed_lengths_length_depth (rev (tc_label C)))//.
      rewrite rev_length. apply lookup_lt_is_Some_1. eauto. }
    eapply get_layer_lookup_lh_lengths in Hlayer as Hn;[|eauto..].
    iExists ts, vs, n, es, lh', es', lh'',t1s.
    repeat (iSplitR;[auto|]).
    { iRight. iExists _. iFrame "Hv". eauto. }
    iIntros (f0) "[Hf0 #Hf0v]".
    rewrite Heq.
    iApply (iris_rules_control.wp_br_ctx with "Hf0").
    { apply v_to_e_is_const_list. }
    { rewrite fmap_length. rewrite -Hlen1 drop_app. simplify_eq;auto. }
    iNext. iIntros "Hf". rewrite -Hlen1 drop_app.

    unfold interp_expression.
    iDestruct (big_sepL2_app_inv with "Hv") as "[Hv1 Hv2]";[auto|].
    iDestruct ("Hbr" with "[] [Hf]") as (τs2) "Hcont".
    { iRight. iExists _. iFrame "Hv2". auto. }
    { iFrame. auto. }
    rewrite !app_assoc. iFrame.
    iApply (wp_wand with "Hcont").
    { iIntros (v) "[[H|H] $]";[auto|].
      iRight. iNext. iFrame. }
  Qed.

  (* ----------------------------------------- LOOP ---------------------------------------- *)

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

  Lemma interp_ctx_continuations_push_label_loop lh C i tm tn es :
    base_is_empty lh ->
    lholed_lengths (rev (tc_label C)) lh ->
    □ (∀ (a : leibnizO frame) (a0 : seq.seq (leibnizO value)),
           ⌜length a0 = length tn⌝
           →  ↪[frame]a -∗
             □ interp_frame (tc_local C) i a -∗
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
    iIntros "#Hw [Hf #Hfv]".
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
             □ interp_frame (tc_local C) i a -∗
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
      iModIntro. iIntros (v f) "#Hv [Hf #Hvf]".
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

    iIntros "#Hc". iIntros (f vs) "[Hf #Hfv] #Hv".
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
    iIntros "#Hlocs #Hv".
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
    { iIntros (f') "#Hfv Hf".
      iDestruct ("HH" with "[] [Hf] []") as "Hcont".
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
  
  (* --------------------------------------------------------------------------------------- *)
  (* ------------------------------- FTLR: simple typing ----------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)
  
  Theorem be_fundamental C es τ : be_typing C es τ -> ⊢ semantic_typing (HWP:=HWP) C (to_e_list es) τ.
  Proof.
    induction 1.
    { by apply typing_const. }
    { by apply typing_unop. }
    { by apply typing_binop. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { by apply typing_loop. }
    { admit. }
    { by apply typing_br. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
  Admitted.

End fundamental.
