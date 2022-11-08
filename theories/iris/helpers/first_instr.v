From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Import iris_wasm_lang_properties.

Fixpoint find_first_some {A : Type} (l : seq.seq (option A)) :=
  match l with
  | [] => None
  | Some e :: q => Some e
  | None :: q => find_first_some q end.

Fixpoint first_instr_instr e :=
  match e with
  | AI_basic (BI_const _) => None
  | AI_label n es LI =>
    match find_first_some (List.map first_instr_instr LI)
    with Some (e',i) => Some (e',S i) | None => Some (e,0) end
  | AI_local n es LI =>
    match find_first_some (List.map first_instr_instr LI)
    with Some (e',i) => Some (e',S i) | None => Some (e,0) end
  | _ => Some (e,0) end.

Definition first_instr es :=
  find_first_some (List.map first_instr_instr es).


Lemma first_instr_const vs es :
  const_list vs -> first_instr (vs ++ es) = first_instr es.
Proof.
  intro Hvs.
  induction vs => //=.
  destruct a ; try by inversion Hvs.
  destruct b ; try by inversion Hvs.
  simpl in Hvs. rewrite <- (IHvs Hvs).
    by unfold first_instr.
Qed.


Lemma starts_with_lfilled e i es k lh les :
  first_instr es = Some (e,i) ->
  lfilled k lh es les ->
  first_instr les = Some (e,i + k).
Proof.
  generalize dependent es. generalize dependent lh. generalize dependent les.
  induction k ; intros les lh es Hstart Hfill ; unfold lfilled, lfill in Hfill.
  { destruct lh ; last by false_assumption.
    remember (const_list l) as b eqn:Hl ; destruct b ; last by false_assumption.
    move/eqP in Hfill. rewrite Hfill ; clear Hfill.
    rewrite (first_instr_const l (es ++ l0) (Logic.eq_sym Hl)).
    induction es ; first by inversion Hstart. rewrite PeanoNat.Nat.add_0_r.
    destruct a ; unfold first_instr ; simpl ; unfold first_instr in Hstart ;
      simpl in Hstart ; try done.
    destruct b ; unfold first_instr ; simpl ;
      unfold first_instr in Hstart ; simpl in Hstart ; eauto; try done.
    all: rewrite PeanoNat.Nat.add_0_r in IHes.
    unfold first_instr in IHes. eauto. eauto.
    destruct (find_first_some _) => //=. destruct p; try done. eauto. eauto.
    destruct (find_first_some _) => //=;eauto. destruct p =>//. }
  fold lfill in Hfill. destruct lh ; first by false_assumption.
  remember (const_list l) as b eqn:Hl ; destruct b ; last by false_assumption.
  remember (lfill k lh es) as fill ; destruct fill ; last by false_assumption.
  move/eqP in Hfill.
  assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite <- Heqfill.
  subst. rewrite (first_instr_const _ _ (Logic.eq_sym Hl)). 
  unfold first_instr => //=.
  unfold first_instr in IHk. eapply IHk in H;eauto. rewrite H => //=.
  repeat f_equiv. lia.
Qed.

Lemma lfilled_implies_starts k lh e es :
  (forall n es' LI, e <> AI_label n es' LI) ->
  (forall n es' LI, e <> AI_local n es' LI) ->
  (is_const e -> False) ->
  lfilled k lh [e] es ->
  first_instr es = Some (e,k).
Proof.
  generalize dependent es. generalize dependent lh.
  induction k ; intros lh es Hlabel Hlocal Hconst Hfill ; unfold lfilled, lfill in Hfill ;
    destruct lh ; (try by false_assumption) ; remember (const_list l) as b eqn:Hl ;
      destruct b ; try by false_assumption.
  { move/eqP in Hfill. destruct e ; subst ;
                         rewrite (first_instr_const _ _ (Logic.eq_sym Hl)) ; try by unfold first_instr.
    destruct b ; try by unfold first_instr. exfalso ; by apply Hconst.
      by exfalso ; eapply Hlabel. by exfalso ; eapply Hlocal. }
  fold lfill in Hfill.
  remember (lfill _ _ _) as fill ; destruct fill ; last by false_assumption.
  move/eqP in Hfill. subst. rewrite (first_instr_const _ _ (Logic.eq_sym Hl)).
  unfold first_instr => //=. unfold first_instr in IHk.
  assert (lfilled k lh [e] l2) ; first by unfold lfilled ; rewrite <- Heqfill.
  eapply IHk in H => //=. rewrite H => //=.
Qed.

Lemma starts_implies_not_constant e es :
  first_instr es = Some e ->
  const_list es -> False.
Proof.
  intros Hstart Hconst.
  induction es ; try by inversion Hstart.
  destruct a ; try by inversion Hconst.
  destruct b ; try by inversion Hconst.
  simpl in Hconst. unfold first_instr in Hstart.
  unfold first_instr in IHes.
  simpl in Hstart. by apply IHes.
Qed.

Lemma first_instr_local es e i n f :
  first_instr es = Some (e,i) ->
  first_instr [AI_local n f es] = Some (e,S i).
Proof.
  intros Hfirst.
  induction es.
  { inversion Hfirst. }
  { rewrite /first_instr /=.
    rewrite /first_instr /= in Hfirst.
    destruct (first_instr_instr a) eqn:Ha;auto.
    destruct p;eauto. simplify_eq. auto. rewrite Hfirst //. }
Qed.

Lemma find_first_const es n f :
  const_list es ->
  first_instr [AI_local n f es] = Some (AI_local n f es, 0).
Proof.
  intros Hconst.
  destruct es.
  all: rewrite /first_instr /= //.
  assert (first_instr_instr a = None) as ->.
  { apply andb_true_iff in Hconst as [Hconst _].
    destruct a;try done. destruct b;try done. }
  assert (find_first_some (map first_instr_instr es) = None) as ->.
  { simpl in Hconst.
    apply andb_true_iff in Hconst as [_ Hconst]. clear -Hconst.
    induction es;[done|].
    simpl. apply andb_true_iff in Hconst as [Ha Hconst].
    destruct a;try done. destruct b;try done. simpl.
    apply IHes. auto. }
  auto. 
Qed.

Inductive first_instr_Ind : list administrative_instruction -> administrative_instruction -> nat -> Prop :=
| first_instr_const_base vs es a i : const_list vs -> first_instr_Ind es a i -> first_instr_Ind (vs ++ es) a i
| first_instr_trap es : first_instr_Ind (AI_trap :: es) AI_trap 0
| first_instr_invoke es a : first_instr_Ind (AI_invoke a :: es) (AI_invoke a) 0
| first_instr_call_host es tf h cvs : first_instr_Ind (AI_call_host tf h cvs :: es)
                                                      (AI_call_host tf h cvs) 0
| first_instr_local_ind n f es es' a i : first_instr_Ind es a i -> first_instr_Ind (AI_local n f es :: es') a (S i)
| first_instr_label n es1 es es' a i : first_instr_Ind es a i -> first_instr_Ind (AI_label n es1 es :: es') a (S i)
| first_instr_local_base n f es es' : const_list es -> first_instr_Ind (AI_local n f es :: es') (AI_local n f es) 0
| first_instr_label_base n es1 es es' : const_list es -> first_instr_Ind (AI_label n es1 es :: es') (AI_label n es1 es) 0
| first_instr_basic bi es': (∀ b, bi ≠ BI_const b) -> first_instr_Ind (AI_basic bi :: es' ) (AI_basic bi) 0.

Lemma first_instr_Ind_not_empty es a i :
  first_instr_Ind es a i -> es ≠ [].
Proof.
  intros Hf. induction Hf;auto.
  intros Hcontr. destruct vs,es =>//.
Qed.
Lemma first_instr_app e :
  ∀ a es', first_instr e = Some a -> first_instr (e ++ es') = Some a.
Proof.
  induction e; intros a0 es';try done.
  cbn. destruct (first_instr_instr a) eqn:Ha;auto.
  intros Hf. eapply IHe with (es':=es') in Hf. auto.
Qed.
Lemma first_instr_app_skip e :
  ∀ es', first_instr e = None -> first_instr (e ++ es') = first_instr es'.
Proof.
  induction e; intros a0;try done.
  cbn. destruct (first_instr_instr a) eqn:Ha;auto. done.
  intros Hf. eapply IHe in Hf. eauto.
Qed.

Lemma first_instr_None_const es :
  first_instr es = None -> const_list es.
Proof.
  induction es;auto.
  cbn.
  destruct (first_instr_instr a) eqn:Ha;[done|].
  intros H. apply IHes in H.
  unfold first_instr_instr in Ha.
  destruct a =>//.
  destruct b =>//.
  destruct (first_instr l0) eqn:Hl0.
  { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha. destruct p;done. }
  { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha. done. }
  destruct (first_instr l) eqn:Hl0.
  { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha. destruct p;done. }
  { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha. done. }
Qed.

Lemma find_first_const_label es es1 n :
  const_list es ->
  first_instr [AI_label n es1 es] = Some (AI_label n es1 es, 0).
Proof.
  intros Hconst.
  destruct es.
  all: rewrite /first_instr /= //.
  assert (first_instr_instr a = None) as ->.
  { apply andb_true_iff in Hconst as [Hconst _].
    destruct a;try done. destruct b;try done. }
  assert (find_first_some (map first_instr_instr es) = None) as ->.
  { simpl in Hconst.
    apply andb_true_iff in Hconst as [_ Hconst]. clear -Hconst.
    induction es;[done|].
    simpl. apply andb_true_iff in Hconst as [Ha Hconst].
    destruct a;try done. destruct b;try done. simpl.
    apply IHes. auto. }
  auto. 
Qed.

Lemma first_instr_Ind_Equivalent es a i :
  first_instr es = Some (a,i) <-> first_instr_Ind es a i.
Proof.
  revert es a.
  induction i;intros es a.
  { split.
    { intros Hf.
      destruct es;try done.
      destruct a0;try done.
      { all: cbn in Hf. rewrite separate1. destruct b; try done; simplify_eq; try by constructor.
        constructor;auto.
        induction es;try done.
        simpl in Hf.
        destruct (first_instr_instr a0) eqn:Ha0; simplify_eq.
        { unfold first_instr_instr in Ha0.
          destruct a0; try done; simplify_eq; try by constructor.
          destruct b; try done; simplify_eq; try by constructor.
          destruct (first_instr l0) eqn:Hl0.
          { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha0.
            destruct p;done. }
          { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha0. simplify_eq.
            constructor. apply first_instr_None_const. auto. }
          destruct (first_instr l) eqn:Hl0.
          { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha0.
            destruct p;done. }
          { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha0. simplify_eq.
            constructor. apply first_instr_None_const. auto. } 
          
        }
        
        unfold first_instr_instr in Ha0. destruct a0 =>//.
        destruct b  =>//.
        rewrite separate1. apply first_instr_const_base;auto.
        destruct (first_instr l0) eqn:Hl0.
        { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha0. destruct p;done. }
        { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha0. done. }
        destruct (first_instr l) eqn:Hl0.
        { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha0. destruct p;done. }
        { unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha0. done. }
      }
      { cbn in Hf. simplify_eq. constructor. }
      { cbn in Hf. simplify_eq. constructor. }
      { cbn in Hf.
        destruct (find_first_some (map first_instr_instr l0)) eqn:Hl0.
        destruct p;try done. 
        simplify_eq. constructor. apply first_instr_None_const. auto. }
      { cbn in Hf.
        destruct (find_first_some (map first_instr_instr l)) eqn:Hl0.
        destruct p;try done. 
        simplify_eq. constructor. apply first_instr_None_const. auto. }
      { cbn in Hf.
        inversion Hf ; subst. by constructor. } 
    }
    { intros Hi. induction Hi;subst;auto.
      { rewrite first_instr_const;auto. }
      { cbn. unfold first_instr in IHHi. by rewrite IHHi. }
      { cbn. unfold first_instr in IHHi. by rewrite IHHi. }
      { eapply find_first_const in H.
        rewrite separate1. erewrite first_instr_app;eauto. }
      { eapply find_first_const_label in H.
        rewrite separate1. erewrite first_instr_app;eauto. }
      { cbn. destruct bi;try done. specialize (H v). done. }
    }
  }
  { split.
    { intros Hf.
      induction es;try done.
      destruct a0;try done.
      { destruct b; try done. cbn in Hf. apply IHes in Hf.
        rewrite separate1. constructor;auto. }
      { constructor. apply IHi.
        cbn in Hf.
        destruct (find_first_some (map first_instr_instr l0)) eqn:Hl0;try done.
        destruct p;try done. simplify_eq. auto. }
      { constructor. apply IHi.
        cbn in Hf.
        destruct (find_first_some (map first_instr_instr l)) eqn:Hl0;try done.
        destruct p;try done. simplify_eq. auto. }
    }
    { intros Hf.
      induction Hf;subst;try (by cbn).
      { rewrite first_instr_const;auto. }
      { cbn. unfold first_instr in IHHf. by rewrite IHHf. }
      { cbn. unfold first_instr in IHHf. by rewrite IHHf. }
      { eapply find_first_const in H.
        rewrite separate1. erewrite first_instr_app;eauto. }
      { eapply find_first_const_label in H.
        rewrite separate1. erewrite first_instr_app;eauto. }
      { cbn. destruct bi;try done. specialize (H v). done. }
    }
  }
Qed.
