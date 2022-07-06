From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
Require Export iris stdpp_aux iris_lfilled_properties.
Require Export datatypes (* host *) operations properties opsem.

Ltac false_assumption := exfalso ; apply ssrbool.not_false_is_true ; assumption.

Ltac first_not_const Hconst :=
  unfold const_list, forallb in Hconst ;
  subst ; simpl in Hconst ;
  repeat rewrite andb_false_r in Hconst ;
  false_assumption.

Ltac const_list_app :=
   unfold const_list ; 
   rewrite forallb_app ;
   apply andb_true_iff ; split => //=.

Lemma last_inj {A : Type} (l1 l2 : list A) (a b : A) :
    l1 = l2 -> last l1 = Some a -> last l2 = Some b -> a = b.
Proof.
  intros Heq Hla1 Hla2.
  subst. rewrite Hla1 in Hla2. inversion Hla2. done.
Qed.

Lemma separate1 {A} (a : A) l :
  a :: l = [a] ++ l.
Proof. done. Qed.

Lemma separate2 {A} (a : A) b l :
  a :: b :: l = [a ; b] ++ l.
Proof. done. Qed.

Lemma separate3 {A} (a : A) b c l :
  a :: b :: c :: l = [a ; b ; c] ++ l.
Proof. done. Qed.

Lemma separate4 {A} (a : A) b c d l :
  a :: b :: c :: d :: l  = [a ; b ; c ; d ] ++ l.
Proof. done. Qed.

Lemma destruct_list_rev {A : Type} (l : list A) :
  l = [] ∨ ∃ a l', l = l' ++ [a].
Proof.
  induction l;eauto.
  right. destruct l;eauto.
  exists a,[]. auto.
  destruct IHl as [Hcontr | [a' [l' Heq]]].
  done. rewrite Heq.
  eexists. eexists.
  rewrite separate1 app_assoc. eauto.
Qed.

Lemma elem_of_app_l :
  ∀ (A : Type) (l1 l2 : seq.seq A) (x : A) (eqA : EqDecision A), x ∈ l1 ++ l2 ↔ x ∈ l1 ∨ (x ∈ l2 ∧ x ∉ l1).
Proof.
  intros A l1 l2 x eqA.
  induction l1.
  { rewrite app_nil_l.
    split;intros.
    right.
    split;auto.
    apply not_elem_of_nil.
    destruct H as [? | [? ?]];try done.
    inversion H.
  }
  { simpl. destruct (decide (x = a)).
    { simplify_eq. split.
      intros Ha. left. constructor.
      intros _. constructor. }
    { split.
      { intros [Hcontr|[Ha | [Ha Hnin]]%IHl1]%elem_of_cons;[done|..].
        left. by constructor.
        right. split;auto. apply not_elem_of_cons;auto. }
      { intros [[Hcontr|Ha]%elem_of_cons|[Hin Hnin]];[done|..].
        constructor. apply elem_of_app. by left.
        constructor. apply elem_of_app. by right. }
    }
  }
Qed.

(* Note : the following lemma exists already in Coq's standard library, and 
   is called app_eq_unit *)
Lemma app_eq_singleton: ∀ T (l1 l2 : list T) (a : T),
    l1 ++ l2 = [a] ->
    (l1 = [a] ∧ l2 = []) ∨ (l1 = [] ∧ l2 = [a]).
Proof.
  move =>T.
  elim.
  move => l2 a Heq. right. by rewrite app_nil_l in Heq.
  move => a l l2 a0 a1 Heq. inversion Heq;subst.
  left. split. f_equiv.
  all: destruct l, a0;try done.
Qed.

Section wasm_lang_properties.
  (*
  Let reducible := @reducible wasm_lang.
  Let reduce := @reduce host_function host_instance. *)

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.

  Lemma v_to_e_is_fmap vs :
    v_to_e_list vs = (fun x => AI_basic (BI_const x)) <$> vs.
  Proof. done. Qed. 


  
  Lemma to_val_cat (es1 es2: list administrative_instruction) (vs: list value) :
    iris.to_val (es1 ++ es2) = Some (immV vs) ->
    iris.to_val es1 = Some (immV (take (length es1) vs)) /\
      iris.to_val es2 = Some (immV ((drop (length es1) vs))).
  Proof.
    move => H.
    apply iris.of_to_val in H. 
    apply fmap_split in H; destruct H as [H1 H2].
    remember (length es1) as n1.
    remember (length es2) as n2.
    rewrite - H1.
    rewrite - H2.
    specialize (of_val_imm (take n1 vs)) as H.
    do 2 rewrite - v_to_e_is_fmap. 
    rewrite !of_val_imm.
    by repeat rewrite iris.to_of_val.
  Qed.

  Lemma to_val_cat_inv (es1 es2: list administrative_instruction) (vs1 vs2: list value) :
    iris.to_val es1 = Some (immV vs1) ->
    iris.to_val es2 = Some (immV vs2) ->
    iris.to_val (es1 ++ es2) = Some (immV (vs1 ++ vs2)).
  Proof.
    intros. apply of_to_val in H, H0. subst.
    unfold of_val, iris.to_val.
    induction vs1 => //=.
    induction vs2 => //=.
    rewrite merge_prepend => //=.
    destruct (merge_values_list _ ) => //=.
    inversion IHvs2 => //=.
    rewrite merge_prepend => //=.
    destruct (merge_values_list _) ; inversion IHvs1 => //.
  Qed.

  Lemma to_val_cat_None1 (es1 es2: list administrative_instruction) :
    iris.to_val es1 = None ->
    iris.to_val (es1 ++ es2) = None.
  Proof.
    apply to_val_None_append.
  Qed.

  Lemma to_val_cat_None2 (es1 es2: list administrative_instruction) :
    const_list es1 ->
    iris.to_val es2 = None ->
    iris.to_val (es1 ++ es2) = None.
  Proof.
    apply to_val_None_prepend_const.
  Qed.

  Lemma app_to_val vs es es' :
    const_list vs ->
    is_Some (iris.to_val (vs ++ es ++ es')) ->
    is_Some (iris.to_val es).
  Proof.
    intros Hconst [x Hx].
    destruct (iris.to_val es) eqn:Hes;eauto.
    apply to_val_cat_None1 with _ es' in Hes.
    apply to_val_cat_None2 with vs _ in Hes;auto.
    congruence.
  Qed.
  
  Lemma lfilled_to_val i  :
    ∀ lh es LI, is_Some (iris.to_val LI) ->
                lfilled i lh es LI ->
                is_Some (iris.to_val es).
  Proof.
    induction i.
    { intros lh es LI [x Hsome] Hfill.
      apply lfilled_Ind_Equivalent in Hfill.
      inversion Hfill;subst.
      destruct (to_val es) eqn:Hnone;eauto.
      exfalso.
      apply (to_val_cat_None1 _ es') in Hnone.
      apply (to_val_cat_None2 vs) in Hnone.
      rewrite Hnone in Hsome. done. auto.
    }
    { intros lh es LI Hsome Hfill.
      apply lfilled_Ind_Equivalent in Hfill.
      inversion Hfill;simplify_eq.
      apply app_to_val in Hsome;auto.
      inversion Hsome.
      unfold iris.to_val in H ; simpl in H.
      destruct (merge_values_list _) eqn:Hmerge => //.
      destruct v => //.
      + apply lfilled_Ind_Equivalent in H1.
        apply (IHi lh' es LI0) => //.
        unfold iris.to_val.
        by rewrite Hmerge.
      + apply lfilled_Ind_Equivalent in H1.
        apply (IHi lh' es LI0) => //.
        unfold iris.to_val.
        by rewrite Hmerge.
      + apply lfilled_Ind_Equivalent in H1.
        apply (IHi lh' es LI0) => //.
        unfold iris.to_val.
        by rewrite Hmerge.
    }
  Qed.

  Lemma first_values_elem_of vs1 e1 es1 vs2 e2 es2 :
    (is_const e1 = false) ->
    (is_const e2 = false) ->
    e2 ∉ vs1 ->
    e1 ∉ vs2 ->
    vs1 ++ e1 :: es1 = vs2 ++ e2 :: es2 ->
    vs1 = vs2 /\ e1 = e2 /\ es1 = es2.
  Proof.
    intros He1 He2 Hvs1 Hvs2 Heq.
    generalize dependent vs2; induction vs1 ; intros.
    { destruct vs2 ; inversion Heq => //=. rewrite <- H0 in Hvs2.
      simpl in Hvs2. apply not_elem_of_cons in Hvs2 as [Hcontr _]. done. }
    destruct vs2 ; inversion Heq.
    { rewrite H0 in Hvs1.
      simpl in Hvs1. apply not_elem_of_cons in Hvs1 as [Hcontr _]. done. }
    assert (vs1 = vs2 /\ e1 = e2 /\ es1 = es2) as H ; last by destruct H ; subst.
    apply not_elem_of_cons in Hvs1 as [Hne Hvs1].
    apply not_elem_of_cons in Hvs2 as [Hne' Hvs2].
    apply IHvs1 => //=.
  Qed.
  Lemma const_list_elem_of e es :
    const_list es ->
    (is_const e = false) ->
    e ∉ es.
  Proof.
    intros Hes Hv.
    intro Hin.
    unfold const_list in Hes.
    edestruct forallb_forall.
    eapply H in Hes ; last first.
    by apply elem_of_list_In.
    rewrite Hes in Hv => //. 
  Qed.

  Lemma to_val_br_base es1 n l e :
    iris.to_val es1 = Some (brV (VH_base n l e)) ->
    es1 = (fmap (fun v => AI_basic (BI_const v)) l) ++ [AI_basic (BI_br n)] ++ e.
  Proof.
    intro.
    apply of_to_val in H.
    simpl in H. by rewrite H.
  Qed.

  Lemma to_val_br_rec es1 n bef m es (vh : valid_holed n) aft :
    iris.to_val es1 = Some (brV (VH_rec bef m es vh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_basic (BI_const v)) bef) ++ [AI_label m es LI] ++ aft
          /\ iris.to_val LI = Some (brV (vh_increase vh)).
  Proof.
    intro.
    apply of_to_val in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_val (brV (vh_increase vh))).
    unfold of_val, iris.of_val.
    by rewrite vfill_increase.
  Qed.

  Lemma to_val_ret_base es1 l e :
    iris.to_val es1 = Some (retV (SH_base l e)) ->
    es1 = (fmap (fun v => AI_basic (BI_const v)) l) ++ [AI_basic BI_return] ++ e.
  Proof.
    intro.
    apply of_to_val in H.
    simpl in H. by rewrite H.
  Qed.

  Lemma to_val_call_host_base es1 l e tf h vcs:
    iris.to_val es1 = Some (callHostV tf h vcs (LL_base l e)) ->
    es1 = (fmap (fun v => AI_basic (BI_const v)) l) ++ [AI_call_host tf h vcs] ++ e.
  Proof.
    intro.
    apply of_to_val in H.
    simpl in H. by rewrite H.
  Qed.

  Lemma to_val_ret_rec es1 bef m es sh aft :
    iris.to_val es1 = Some (retV (SH_rec bef m es sh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_basic (BI_const v)) bef) ++ [AI_label m es LI] ++ aft
          /\ iris.to_val LI = Some (retV sh).
  Proof.
    intro.
    apply of_to_val in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_val (retV sh)).
    unfold of_val.
    done.
  Qed.

  Lemma to_val_call_host_rec_label es1 bef m es sh aft tf h vcs:
    iris.to_val es1 = Some (callHostV tf h vcs (LL_label bef m es sh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_basic (BI_const v)) bef) ++ [AI_label m es LI] ++ aft
          /\ iris.to_val LI = Some (callHostV tf h vcs sh).
  Proof.
    intro.
    apply of_to_val in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_val (callHostV tf h vcs sh)).
    unfold of_val.
    done.
  Qed.

  Lemma to_val_call_host_rec_local es1 bef n f sh aft tf h vcs:
    iris.to_val es1 = Some (callHostV tf h vcs (LL_local bef n f sh aft)) ->
    exists LI, es1 = (v_to_e_list bef) ++ [AI_local n f LI] ++ aft /\
            iris.to_val LI = Some (callHostV tf h vcs sh).
  Proof.
    intro.
    apply of_to_val in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_val (callHostV tf h vcs sh)).
    unfold of_val => //.
  Qed.  

  Lemma to_val_br_eq vs j es0 :
    iris.to_val (v_to_e_list vs ++ [AI_basic (BI_br j)] ++ es0) = Some (brV (VH_base j vs es0)).
  Proof.
    induction vs ; unfold iris.to_val => //=.
    rewrite merge_br flatten_simplify => //.
    rewrite merge_prepend.
    unfold iris.to_val in IHvs.
    destruct (merge_values_list _ ) => //.
    inversion IHvs => //=.
  Qed.

  Lemma to_val_ret_eq vs es0 :
    iris.to_val (v_to_e_list vs ++ [AI_basic BI_return] ++ es0) = Some (retV (SH_base vs es0)).
  Proof.
    induction vs; unfold iris.to_val => /=.
    rewrite merge_return flatten_simplify => //.
    rewrite merge_prepend.
    unfold iris.to_val in IHvs.
    destruct (merge_values_list _) => //=.
    inversion IHvs => //.
  Qed.


  Lemma to_val_call_host_eq vs es0 tf h vcs:
    iris.to_val (v_to_e_list vs ++ [AI_call_host tf h vcs] ++ es0) = Some (callHostV tf h vcs ((LL_base vs es0))).
  Proof.
    induction vs; unfold iris.to_val => /=.
    rewrite merge_call_host flatten_simplify => //.
    rewrite merge_prepend.
    unfold iris.to_val in IHvs.
    destruct (merge_values_list _) => //=.
    inversion IHvs => //.
  Qed.

  Lemma first_non_value es :
    iris.to_val es = None ->
    exists vs e es', const_list vs /\ (to_val [e] = None \/ e = AI_trap) /\ es = vs ++ e :: es'.
  Proof.
    intros Hes.
    induction es ; first by inversion Hes.
    remember a as a'.
    destruct a ; try by exists [], a', es ; repeat split => //= ; left ; rewrite Heqa'.
    { subst ; remember b as b'.
      destruct b ;
        try by exists [], (AI_basic b'), es ; repeat split => //= ; left ; rewrite Heqb'; simplify_eq.
      unfold iris.to_val in Hes ; simpl in Hes.
      subst. rewrite merge_br flatten_simplify in Hes => //.
      unfold iris.to_val in Hes ; simpl in Hes ; subst.
      by rewrite merge_return flatten_simplify in Hes.
      subst. unfold iris.to_val in Hes ; simpl in Hes.
      rewrite merge_prepend in Hes.
      unfold iris.to_val in IHes.
      destruct (merge_values_list _) eqn:Hmerge => //.
      destruct v0 => //.
      assert (to_val es = Some trapV) ;
        first by unfold to_val, iris.to_val ; rewrite Hmerge.
      apply to_val_trap_is_singleton in H as ->.
      exists [AI_basic (BI_const v)], AI_trap, [] ; repeat split => //.
      by right.
      destruct IHes as (vs & e0 & es' & Hvs & He & Hes0) => //.
      exists (AI_basic (BI_const v) :: vs), e0, es' ;
        repeat split => //.
      by rewrite Hes0. }
    subst. exists [], AI_trap, es. repeat split => //=. by right.
    subst. exists [], (AI_label n l l0), es. repeat split => //=.
    left.
    unfold to_val, iris.to_val => /=.
    unfold iris.to_val in Hes ; simpl in Hes.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v => //.
    destruct i => //.
    destruct (vh_decrease _) => //.
    rewrite merge_br flatten_simplify in Hes => //.
    rewrite merge_return flatten_simplify in Hes => //.
    rewrite merge_call_host flatten_simplify in Hes => //.
    exists [], (AI_local n f l), es. subst.
    repeat split => //. left.
    unfold iris.to_val in Hes ; simpl in Hes.
    unfold to_val, iris.to_val => /=. 
    destruct (merge_values_list _) => //.
    destruct v => //.
    rewrite merge_call_host flatten_simplify in Hes => //. 
    subst ; unfold iris.to_val in Hes ; simpl in Hes.
    by rewrite merge_call_host flatten_simplify in Hes.
  Qed.

  Lemma to_val_None_first_singleton es :
    (const_list es = false) ->
    (es <> [AI_trap]) ->
    ∃ vs e es', es = vs ++ [e] ++ es' ∧ const_list vs ∧
                  ((to_val ([e]) = None)
                   ∨ (e = AI_trap ∧ (vs ≠ [] ∨ es' ≠ []))
                   ∨ (∃ n, e = (AI_basic (BI_br n)))
                   ∨ (e = (AI_basic BI_return))
                   \/ (∃ tf h vcs, e = (AI_call_host tf h vcs))
                   \/ (exists n es LI, e = AI_label n es LI
                                 /\ ((exists i (vh: valid_holed i), to_val LI = Some (brV vh))
                                    \/ (exists sh, to_val LI = Some (retV sh))
                                    \/ (exists tf h vcs sh, to_val LI = Some (callHostV tf h vcs sh))))
                  \/ (exists n f LI tf h vcs sh, e = AI_local n f LI /\ to_val LI = Some (callHostV tf h vcs sh)))
                   .
  Proof.
    induction es;intros Hes1 Hes2.
    { exfalso. simpl in Hes1. eauto. }
    { destruct (to_val [a]) eqn:Ha.
      { destruct v.
        { destruct (to_val es) eqn:Hes.
          { unfold to_val in Hes.
            unfold to_val in Ha.
            destruct v. 
            { eapply to_val_cat_inv in Hes;[|apply Ha].
              rewrite -separate1 in Hes. unfold to_val in Hes1.
              exfalso. by erewrite to_val_const_list in Hes1. }
            { apply to_val_trap_is_singleton in Hes as ->.
              apply to_val_const_list in Ha.
              exists [a],AI_trap,[]. cbn. repeat split;auto. }
            { destruct lh.
              - apply to_val_br_base in Hes as ->.
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat. eexists _,_,_. split;eauto.
                split;[apply v_to_e_is_const_list|]. right. right. left. eauto.
              - apply to_val_br_rec in Hes as (LI & -> & Htv).
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat. eexists _,_,_. split ; eauto.
                split ; [apply v_to_e_is_const_list |].
                do 5 right. left. eexists _,_,_ ; split => //=.
                left. eauto.
            }
            { destruct s.
              - apply to_val_ret_base in Hes as ->.
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat.
                eexists _,_,_. split;eauto.
                split;[apply v_to_e_is_const_list|]. right. right. right. eauto.
              - apply to_val_ret_rec in Hes as (LI & -> & Htv).
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat.
                eexists _,_,_. split ; eauto.
                split;[apply v_to_e_is_const_list|]. do 5 right.
                left.
                eexists _,_,_. split => //=.
                right. eauto.
            }
            { destruct l1. 
              - apply to_val_call_host_base in Hes as ->.
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat.
                eexists _,_,_. split;eauto.
                split;[apply v_to_e_is_const_list|]. right. right. right. right. left. eauto.
              - apply to_val_call_host_rec_label in Hes as (LI & -> & Htv).
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat.
                eexists _,_,_. split ; eauto.
                split;[apply v_to_e_is_const_list|]. do 5 right.  left.
                eexists _,_,_. split => //=.
                right. right.  by repeat eexists.
              - apply to_val_call_host_rec_local in Hes as (LI & -> & Htv).
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat. 
                eexists _,_,_. split ; eauto.
                split ; first apply v_to_e_is_const_list.
                do 6 right. eexists _,_,_,_,_,_,_. split => //=.
          } }
          { destruct IHes as [vs [e [es' [Heq [Hconst HH]]]]];auto.
            destruct (const_list es) eqn:Hconst => //. apply const_list_to_val in Hconst as [??]. unfold to_val in Hes ; congruence. intro. rewrite H in Hes. unfold to_val, iris.to_val in Hes ; done.
            apply to_val_const_list in Ha.
            destruct HH as [Hnone | [[-> Hne] | [[? Hne] | Hne]]].
            { exists (a::vs),e,es'. subst. split;auto. split;[|left;auto].
              rewrite separate1. apply const_list_app. auto. }
            { exists (a::vs),AI_trap,es'. subst. split;auto.
              split;[|right;auto]. rewrite separate1. apply const_list_app. auto. }
            { subst. rewrite separate1 app_assoc.
              eexists _,_,_. split;eauto. split;[apply const_list_app;auto|].
              right;right;left. eauto. }
            { subst. rewrite separate1 app_assoc.
              eexists _,_,_. split;eauto. split;[apply const_list_app;auto|].
              right;right;right. eauto. }
          }
        }
        { unfold to_val in Ha.
          apply to_val_trap_is_singleton in Ha as Heq.
          simplify_eq.
          unfold to_val in Hes1.
          unfold to_val in Hes2.
          destruct es => //.
          exists [],AI_trap,(a :: es).
          repeat split;auto. }
        { destruct a;try done. destruct b;try done.
          unfold to_val, iris.to_val in Ha ; simpl in Ha.
          inversion Ha.
          apply Eqdep.EqdepTheory.inj_pair2 in H1 ; subst.
          exists [], (AI_basic (BI_br i)), es.
          repeat split => //=.
          right ; right ; left. eauto.
          unfold to_val, iris.to_val in Ha. simpl in Ha.
          destruct (merge_values_list _) eqn:Hmerge => //.
          destruct v => //.
          destruct i0 => //.
          destruct (vh_decrease _) => //.
          inversion Ha.
          destruct H0.
          apply Eqdep.EqdepTheory.inj_pair2 in H1 ; subst.
          exists [], (AI_label n l l0), es.
          repeat split => //.
          do 5 right. left.
          eexists _,_,_ ; split => //.
          left.
          unfold to_val, iris.to_val.
          rewrite Hmerge. eauto.
          unfold to_val, iris.to_val in Ha ; simpl in Ha.
          destruct (merge_values_list _) => //.
          destruct v => //.
        }
        { destruct a;try done. destruct b;try done.
          unfold to_val, iris.to_val in Ha ; simpl in Ha.
          inversion Ha ; subst.
          exists [], (AI_basic BI_return), es.
          repeat split => //=.
          right; right; right ; left ; eauto.
          unfold to_val, iris.to_val in Ha ; simpl in Ha.
          destruct (merge_values_list _) eqn:Hmerge => //.
          destruct v => //.
          destruct i => //.
          destruct (vh_decrease _) => //.
          inversion Ha ; subst.
          exists [], (AI_label n l l0), es.
          repeat split => //.
          do 5 right. left.
          eexists _,_,_ ; split => //.
          right.
          unfold to_val, iris.to_val.
          rewrite Hmerge ; eauto.
          unfold to_val, iris.to_val in Ha ; simpl in Ha.
          destruct (merge_values_list _) => //.
          destruct v => //.
        }
        { destruct a;try done. destruct b;try done.
          unfold to_val, iris.to_val in Ha ; simpl in Ha.
          destruct (merge_values_list _) eqn:Hmerge => //.
          destruct v => //.
          destruct i => //.
          destruct (vh_decrease _) => //.
          inversion Ha ; subst.
          eexists [], (AI_label _ _ _), es.
          repeat split => //.
          do 5 right. left.
          eexists _,_,_ ; split => //.
          right. right.
          unfold to_val, iris.to_val.
          rewrite Hmerge ; eauto.
          unfold to_val, iris.to_val in Ha ; simpl in Ha.
          destruct (merge_values_list _) eqn:Hmerge => //.
          destruct v => //.
          eexists [], (AI_local _ _ _), es.
          repeat split => //.
          do 6 right => //=.
          repeat eexists.
          unfold to_val, iris.to_val.
          rewrite Hmerge => //.  

          
          unfold to_val, iris.to_val in Ha ; simpl in Ha.
          inversion Ha ; subst.
          eexists [], (AI_call_host _ _ _), es.
          repeat split => //=.
          right; right; right ; right ; left ; eauto.
          
        }
        }
      
      { exists [],a,es. auto. }
    }
  Qed.

  Lemma const_list_snoc_eq3 es'' :
    forall vs es ves e es',
      const_list ves ->
      const_list vs ->
      es ≠ [] ->
      (const_list es = false) ->
      (es <> [AI_trap]) ->
      (is_const e = false ) ->
      (vs ++ es ++ es')%SEQ = ves ++ [e] ++ es'' ->
      ∃ vs2 es2, ves = vs ++ vs2 ∧ es = vs2 ++ [e] ++ es2 ∧ es'' = es2 ++ es' ∧ const_list vs2.
  Proof.
    intros vs es ves e es' Hconst1 Hconst2 Hneq Hnval1 Hnval2 He Heq.
    apply to_val_None_first_singleton in Hnval2 as HH;auto.
    destruct HH as [vs' [e' [es2 [Heq' [Hconst HH]]]]].
    assert (Heqcopy:=Heq).
    rewrite Heq' in Heqcopy.
    assert (vs ++ (vs' ++ [e'] ++ es2)%list ++ es' = (vs ++ vs') ++ [e'] ++ (es2 ++ es'))%SEQ as Heq2.
    { rewrite !app_assoc. repeat erewrite app_assoc. auto. }
    rewrite Heq2 in Heqcopy. clear Heq2. unfold to_val in He. unfold to_val in HH.
    apply first_values in Heqcopy as [Heq1 [Heq2 Heq3]];auto.
    2:{ (destruct HH as [He' | [[-> _] | [[?  ->] | [-> | [ (?&?&?& ->) | [ (? & ? & ? & -> & [ (? & ? & HLI) | [[? HLI] | (?&?&?&?&HLI) ] ]) | (? & ? & ? & ? & ? & ? & ? & -> & HLI) ] ]]]]]) => //. destruct e' => //. destruct b => //. }
    2: by apply const_list_app. 
    subst e'.
    rewrite -Heq1 in Heq.
    rewrite -Heq3 in Heq.
    assert ((vs ++ vs')%SEQ ++ [e] ++ (es2 ++ es')%SEQ =
              (vs ++ (vs' ++ [e] ++ es2) ++ es')%SEQ) as Hassoc.
    { rewrite !app_assoc. repeat erewrite app_assoc. auto. }
    rewrite Hassoc in Heq;clear Hassoc.
    apply app_inv_head in Heq.
    apply app_inv_tail in Heq.
    eexists _,_. eauto.
  Qed.     

  Lemma const_list_l_snoc_eq3 es'' :
    forall vs es ves e es',
      const_list ves ->
      e ∉ vs ->
      es ≠ [] ->
      (const_list es = false) ->
      (es <> [AI_trap]) ->
      (is_const e = false ) ->
      (vs ++ es ++ es')%SEQ = ves ++ [e] ++ es'' ->
      ∃ vs2 es2, ves = vs ++ vs2 ∧ es = vs2 ++ [e] ++ es2 ∧ es'' = es2 ++ es' ∧ const_list vs2.
  Proof.
    intros vs es ves e es' Hconst1 Hnin Hneq Hnval1 Hnval2 He Heq.
    apply to_val_None_first_singleton in Hnval2 as HH;auto.
    destruct HH as [vs' [e' [es2 [Heq' [Hconst HH]]]]].
    assert (Heqcopy:=Heq).
    rewrite Heq' in Heqcopy.
    assert (vs ++ (vs' ++ [e'] ++ es2)%list ++ es' = (vs ++ vs') ++ [e'] ++ (es2 ++ es'))%SEQ as Heq2.
    { rewrite !app_assoc. repeat erewrite app_assoc. auto. }
    rewrite Heq2 in Heqcopy. clear Heq2. unfold to_val in He. (* unfold to_val in HH. *)
    apply first_values_elem_of in Heqcopy as [Heq1 [Heq2 Heq3]];auto.
    (* all: unfold iris.to_val in HH. *)
    2: (destruct HH as [He' | [[-> _] | [[? ->] | [-> | [(?&?&?& ->) | [(? & ? & ? & -> & ?) |(?&?&?&?&?&?&?& -> & ?)]]]]]] => //).
    2: destruct e' => //; destruct b => //.
    2: { apply not_elem_of_app. split;[|apply const_list_elem_of;auto]. auto. }
    2: apply const_list_elem_of;auto.
    2: (destruct HH as [He' | [[-> _] | [[? ->] | [-> | [(?&?&?& ->) | [(? & ? & ? & -> & ?) |(?&?&?&?&?&?&?& -> & ?)] ]]]]] => //).
    2: destruct e' => // ; destruct b => //.
    subst e'.
    rewrite -Heq1 in Heq.
    rewrite -Heq3 in Heq.
    assert ((vs ++ vs')%SEQ ++ [e] ++ (es2 ++ es')%SEQ =
              (vs ++ (vs' ++ [e] ++ es2) ++ es')%SEQ) as Hassoc.
    { rewrite !app_assoc. repeat erewrite app_assoc. auto. }
    rewrite Hassoc in Heq;clear Hassoc.
    apply app_inv_head in Heq.
    apply app_inv_tail in Heq.
    eexists _,_. eauto.    
  Qed.

  Lemma filled_is_val_imm : ∀ i lh es LI vals,
      iris.to_val LI = Some (immV vals) ->
      lfilled i lh es LI ->
      ∃ vs es', i = 0 ∧ lh = LH_base vs es' ∧ const_list vs ∧ const_list es'.
  Proof.
    intros i.
    destruct i;
      intros lh es LI vals Hval Hfill%lfilled_Ind_Equivalent.
    { inversion Hfill;subst.
      apply to_val_cat in Hval as [Hval1 Hval2].
      apply to_val_cat in Hval2 as [Hval21 Hval22].
      eexists _,_. repeat split;eauto.
      eapply to_val_const_list. eauto. }
    { exfalso. inversion Hfill;subst.
      apply to_val_cat in Hval as [Hval1 Hval2].
      apply to_val_cat in Hval2 as [Hval21 Hval22].
      rewrite /= in Hval21. unfold iris.to_val in Hval21.
      simpl in Hval21. destruct (merge_values_list _) => //.
      destruct v => //. destruct i0 => //.
      destruct (vh_decrease _) => //.
    }
  Qed.
  Lemma filled_is_val_trap : ∀ i lh es LI,
      iris.to_val LI = Some trapV ->
      lfilled i lh es LI ->
      es ≠ [] ->
      i = 0 ∧ lh = LH_base [] [].
  Proof.
    intros i.
    destruct i;
      intros lh es LI Hval Hfill%lfilled_Ind_Equivalent Hne.
    { inversion Hfill;subst.
      apply to_val_trap_is_singleton in Hval.
      destruct es,vs,es' => //=.
      destruct es => //=.
      destruct vs => //=.
      destruct vs => //=. }
    { inversion Hfill;subst.
      apply to_val_trap_is_singleton in Hval.
      repeat destruct vs => //=. }
  Qed.

  Lemma filled_is_val_br_base : ∀ i lh es LI j v1 e1 ,
      iris.to_val LI = Some (brV (VH_base j v1 e1)) ->
      lfilled i lh es LI ->
      es ≠ [] ->
      i = 0.
  Proof.
    intros i.
    destruct i;
      intros lh es LI j v1 v2 Hval Hfill%lfilled_Ind_Equivalent Hne.
    { inversion Hfill;subst;auto. }
    { inversion Hfill;subst.
      apply to_val_br_base in Hval.
      apply first_values in Hval as [? [? ?]];auto.
      done.   
      apply v_to_e_is_const_list.
    }
  Qed.


  Lemma filled_is_val_ret_base : ∀ i lh es LI v1 e1 ,
      iris.to_val LI = Some (retV (SH_base v1 e1)) ->
      lfilled i lh es LI ->
      es ≠ [] ->
      i = 0.
  Proof.
    intros i.
    destruct i;
      intros lh es LI v1 v2 Hval Hfill%lfilled_Ind_Equivalent Hne.
    { inversion Hfill;subst;auto. }
    { inversion Hfill;subst.
      apply to_val_ret_base in Hval.
      apply first_values in Hval as [? [? ?]];auto.
      2: apply v_to_e_is_const_list.
      done. }
  Qed.

  Lemma filled_is_val_call_host_base : ∀ i lh es LI v1 e1 tf h cvs,
      iris.to_val LI = Some (callHostV tf h cvs (LL_base v1 e1)) ->
      lfilled i lh es LI ->
      es ≠ [] ->
      i = 0.
  Proof.
    intros i.
    destruct i;
      intros lh es LI v1 v2 tf h cvs Hval Hfill%lfilled_Ind_Equivalent Hne.
    { inversion Hfill;subst;auto. }
    { inversion Hfill;subst.
      apply to_val_call_host_base in Hval.
      apply first_values in Hval as [? [? ?]];auto.
      2: apply v_to_e_is_const_list.
      done. }
  Qed. 
  
  Lemma filled_is_val_trap_nil : ∀ i lh LI,
      iris.to_val LI = Some trapV ->
      lfilled i lh [] LI ->
      ∃ vs es, i = 0 ∧ lh = LH_base vs es ∧
                 ((vs = [] ∧ es = [::AI_trap])
                  ∨ (es = [] ∧ vs = [::AI_trap])).
  Proof.
    intros i.
    destruct i;
      intros lh LI Hval Hfill%lfilled_Ind_Equivalent.
    { inversion Hfill;subst.
      apply to_val_trap_is_singleton in Hval.
      destruct vs,es' => //=.
      repeat destruct es' => //=.
      repeat erewrite app_nil_l in Hval. simplify_eq.
      eexists _,_. eauto.
      repeat destruct vs => //=.
      repeat erewrite app_nil_r in Hval. simplify_eq.
      eexists _,_. eauto.
      repeat destruct vs => //=. }
    { exfalso. inversion Hfill;subst.
      apply to_val_trap_is_singleton in Hval.
      repeat destruct vs => //=. }
  Qed.

  Lemma to_val_nil : ∀ e,
      iris.to_val e = Some (immV []) -> e = [].
  Proof.
    intros e He. destruct e;auto.
    unfold iris.to_val in He ; simpl in He.
    destruct a => //= ; simpl in He.
    destruct b => //= ; simpl in He.
    rewrite merge_br flatten_simplify in He => //.
    rewrite merge_return flatten_simplify in He => //.
    rewrite merge_prepend in He.
    destruct (merge_values_list _) ; simpl in He => //. 
    destruct v0 ; simpl in He => //.
    rewrite merge_trap in He ; simpl in He.
    rewrite flatten_simplify in He.
    destruct e => //.
    destruct (merge_values_list _) ; simpl in He => //.
    destruct v => //.
    destruct i => //.
    destruct (vh_decrease _) => //.
    rewrite merge_br flatten_simplify in He => //.
    rewrite merge_return flatten_simplify in He => //.
    rewrite merge_call_host flatten_simplify in He => //.
    destruct (merge_values_list _) => //.
    destruct v => //.
    rewrite merge_call_host flatten_simplify in He => //. 
    rewrite merge_call_host flatten_simplify in He => //. 
  Qed.

  Lemma fill_val : ∀ l LI v1 v2 vs es' es,
      lfilled 0 (LH_base vs es') es LI ->
      iris.to_val LI = Some (immV l) ->
      iris.to_val vs = Some (immV v1) ->
      iris.to_val es' = Some (immV v2) ->
      ∃ vs, iris.to_val es = Some (immV vs) ∧ l = v1 ++ vs ++ v2.
  Proof.
    intros l LI v1 v2 vs es' es
           Hfill%lfilled_Ind_Equivalent
           HLI Hvs Hes'.
    inversion Hfill ; subst.
    specialize (to_val_const_list HLI) as Hconst.
    unfold const_list in Hconst.
    repeat rewrite forallb_app in Hconst.
    repeat apply andb_true_iff in Hconst as [? Hconst].
    apply const_list_to_val in H0 as [vs0 Hes].
    eexists ; split => //.
    pose proof (to_val_cat_inv _ _ _ _ Hes Hes') as Hi.
    pose proof (to_val_cat_inv _ _ _ _ Hvs Hi) as Hl.
    inversion Hfill;subst. rewrite Hl in HLI. simplify_eq. eauto.
  Qed.

  Lemma lfilled_eq i1 i2 lh1 lh2 e1 e2 LI :
    lfilled i1 lh1 [e1] LI -> lfilled i2 lh2 [e2] LI ->
    (* (to_val [e1] = None /\ (forall a b c, e1 <> AI_label a b c) \/ e1 = AI_trap) -> *)
    (* (to_val [e2] = None /\ (forall a b c, e2 <> AI_label a b c) \/ e2 = AI_trap) -> *)
    ((is_const e1 = false ) /\ (forall a b c, e1 <> AI_label a b c)) ->
    ((is_const e2 = false ) /\ (forall a b c, e2 <> AI_label a b c)) ->
    i1 = i2 /\ lh1 = lh2 /\ e1 = e2.
  Proof.
    intros Hfill1 Hfill2 He1 He2.
    generalize dependent lh2 ; generalize dependent i2.
    generalize dependent lh1 ; generalize dependent LI.
    induction i1 ; intros LI lh1 Hfill1 i2 lh2 Hfill2.
    { unfold lfilled, lfill in Hfill1.
      destruct lh1 as [bef aft |]; last by false_assumption.
      destruct (const_list bef) eqn:Hbef ; last by false_assumption.
      move/eqP in Hfill1.
      rewrite Hfill1 in Hfill2.
      unfold lfilled, lfill in Hfill2.
      destruct i2.
      { destruct lh2 as [bef' aft' |] ; last by false_assumption.
        destruct (const_list bef') eqn:Hbef' ; last by false_assumption.
        move/eqP in Hfill2.
        eapply first_values in Hfill2 as (-> & -> & ->) => //=.
        destruct He1 as [? ?]. done. 
        destruct He2 as [? ?]. done. 
      }
      fold lfill in Hfill2.
      destruct lh2 ; first by false_assumption.
      destruct (const_list l) eqn:Hl ; last by false_assumption.
      destruct (lfill _ _ _) ; last by false_assumption.
      move/eqP in Hfill2.
      eapply first_values in Hfill2 as (-> & -> & ->) => //=.
      destruct He1 as [_ Habs] ; try by inversion Habs.
      exfalso ; by eapply Habs.
      destruct He1 as [? ?]. destruct e1; try done; destruct b;try done.
    }
    unfold lfilled, lfill in Hfill1 ; fold lfill in Hfill1.
    destruct lh1 as [| bef n es1 lh1 es'1] ; first by false_assumption.
    destruct (const_list bef) eqn:Hbef ; last by false_assumption.
    destruct (lfill i1 _ _) eqn:Hfill'1 ; last by false_assumption.
    move/eqP in Hfill1.
    unfold lfilled, lfill in Hfill2 ; destruct i2.
    { destruct lh2 as [bef2 aft2 |] ; last by false_assumption.
      destruct (const_list bef2) eqn:Hbef2 ; last by false_assumption.
      move/eqP in Hfill2.
      rewrite Hfill2 in Hfill1.
      eapply first_values in Hfill1 as (-> & -> & ->) => //=.
      destruct He2 as  [_ Habs ] ; try by inversion Habs.
      exfalso ; by eapply Habs.
      destruct He2 as [? ?]. destruct e2; try done; destruct b;try done. }    
    fold lfill in Hfill2.
    destruct lh2 as [| bef2 n2 es2 lh2 es'2] ; first by false_assumption.
    destruct (const_list bef2) eqn:Hbef2 ; last by false_assumption.
    destruct (lfill i2 _ _) eqn:Hfill'2 ; last by false_assumption.
    move/eqP in Hfill2.
    assert (lfilled i1 lh1 [e1] l) ; first by unfold lfilled ; rewrite Hfill'1.
    assert (lfilled i2 lh2 [e2] l0) ; first by unfold lfilled ; rewrite Hfill'2.
    rewrite Hfill1 in Hfill2.
    eapply first_values in Hfill2 as (-> & Hlab & ->) => //= ; try by intros [? ?].
    inversion Hlab ; subst ; clear Hlab.
    eapply IHi1 in H as (-> & -> & ->) => //=.
  Qed.


  Lemma lfilled_trans2 : forall k lh es1 es1' es2 es2' k' lh' es3 es3',
      lfilled k lh es1 es2 -> lfilled k lh es1' es2' -> 
      lfilled k' lh' es2 es3 -> lfilled k' lh' es2' es3' ->
      exists lh'', lfilled (k+k') lh'' es1 es3 /\ lfilled (k+k') lh'' es1' es3'.
  Proof.
    intros k lh es1 es1' es2 es2' k' ; generalize dependent es2' ;
      generalize dependent es2 ; generalize dependent es1' ; generalize dependent es1 ;
      generalize dependent lh ; generalize dependent k ; induction k' ;
      intros k lh es1 es1' es2 es2' lh' es3 es3' Hfill2 Hfill2' Hfill3 Hfill3'.
    { unfold lfilled, lfill in Hfill3. unfold lfilled, lfill in Hfill3'.
      destruct lh' as [ bef' aft' |] ; last by false_assumption.
      remember (const_list bef') as b eqn:Hbef' ; destruct b ; last by false_assumption.
      move/eqP in Hfill3. move/eqP in Hfill3'.
      unfold lfilled, lfill in Hfill2. unfold lfilled, lfill in Hfill2'.
      destruct k. { destruct lh as [bef aft |] ; last by false_assumption.
                    remember (const_list bef) as b eqn:Hbef ; destruct b ;
                      last by false_assumption.
                    move/eqP in Hfill2 ; move/eqP in Hfill2' ; subst.
                    exists (LH_base (bef' ++ bef) (aft ++ aft')) => //=.
                    split ; unfold lfilled, lfill, const_list ;
                      rewrite forallb_app ; unfold const_list in Hbef ; rewrite <- Hbef ;
                      unfold const_list in Hbef' ; rewrite <- Hbef' ; simpl ;
                      by repeat rewrite app_assoc. }
      fold lfill in Hfill2. fold lfill in Hfill2'.
      destruct lh as [| bef n es lh aft ] ; first by false_assumption.
      remember (const_list bef) as b eqn:Hbef ; destruct b ; last by false_assumption.
      remember (lfill k lh es1) as fill ; destruct fill ; last by false_assumption.
      remember (lfill k lh es1') as fill' ; destruct fill' ; last by false_assumption.
      move/eqP in Hfill2 ; move/eqP in Hfill2' ; subst.
      exists (LH_rec (bef' ++ bef) n es lh (aft ++ aft')) ; rewrite <- plus_n_O.
      unfold lfilled, lfill ; fold lfill ; unfold const_list.
      rewrite forallb_app. unfold const_list in Hbef ; rewrite <- Hbef.
      unfold const_list in Hbef' ; rewrite <- Hbef' => //=.
      rewrite <- Heqfill. rewrite <- Heqfill'.
      repeat rewrite app_assoc. split ; by rewrite <- app_assoc. }
    unfold lfilled, lfill in Hfill3 ; fold lfill in Hfill3.
    unfold lfilled, lfill in Hfill3' ; fold lfill in Hfill3'.
    destruct lh' as [| bef' n' es' lh' aft' ] ; first by false_assumption.
    remember (const_list bef') as b eqn:Hbef' ; destruct b ; last by false_assumption.
    remember (lfill k' lh' es2) as fill' ; destruct fill' ; last by false_assumption.
    remember (lfill k' lh' es2') as fill'' ; destruct fill'' ; last by false_assumption.
    move/eqP in Hfill3.  move/eqP in Hfill3'. assert (lfilled k' lh' es2 l) as Hfill.
    by unfold lfilled ; rewrite <- Heqfill'.
    assert (lfilled k' lh' es2' l0) as Hfill'.
    by unfold lfilled ; rewrite <- Heqfill''.
    destruct (IHk' _ _ _ _ _ _ _ _ _ Hfill2 Hfill2' Hfill Hfill')
      as (lh'' & Hfilln & Hfilln').
    exists (LH_rec bef' n' es' lh'' aft'). rewrite plus_comm => //=.  rewrite plus_comm.
    unfold lfilled, lfill ; fold lfill. rewrite <- Hbef'. unfold lfilled in Hfilln.
    destruct (lfill (k + k') lh'' es1) ; last by false_assumption.
    unfold lfilled in Hfilln'. destruct (lfill (k+k') lh'' es1') ; last by false_assumption.
    move/eqP in Hfilln ; move/eqP in Hfilln' ; by subst.
  Qed.

  Lemma assoc_list_seq {A} (a : list A) b c :
    (a ++ (b ++ c)%list)%SEQ = (a ++ b) ++ c.
  Proof. rewrite catA. done. Qed.

  Lemma const_list_singleton e :
    is_const e -> const_list [e].
  Proof. unfold const_list => //=. intros H ; rewrite H => //. Qed.

  Lemma const_list_In es e:
    In e es ->
    const_list es ->
    is_const e.
  Proof.
    elim: es => //=.
    move => e' es HIn [-> | HIn2] Hcontra; move/andP in Hcontra; destruct Hcontra as [He Hes] => //.
    by apply HIn => //.
  Qed.

  Lemma to_val_immV_inj es es' vs :
    iris.to_val es = Some (immV vs) ->
    iris.to_val es' = Some (immV vs) ->
    es = es'.
  Proof.
    intros. apply to_val_is_immV in H as ->.
    apply to_val_is_immV in H0 as -> => //.
  Qed. 
(*    revert es' vs.
    induction es;intros es' vs Hsome Heq.
    { unfold iris.to_val in Hsome. simpl in Hsome. simplify_eq.
      apply to_val_nil in Heq. auto. }
    { destruct vs.
      apply to_val_nil in Hsome. done.
      destruct es'.
      symmetry in Heq. unfold iris.to_val in Heq. simpl in *. simplify_eq.
      unfold iris.to_val in *.
      simpl in *.
      destruct a,a0 ; simpl in * ; (try done) ;
        (try destruct b ; simpl in * ; try done) ;
        (try destruct b0 ; simpl in * ; try done) ;
        (try destruct (merge_values_list (map _ l0)) as [vv|]; try done) ;
        try destruct vv ;
        try destruct i ;
        try destruct (vh_decrease _) ;
        try rewrite merge_br flatten_simplify in Hsome ;
        try rewrite merge_br flatten_simplify in Heq ;
        try rewrite merge_return flatten_simplify in Hsome ;
        try rewrite merge_return flatten_simplify in Heq ;
        try rewrite merge_call_host flatten_simplify in Hsome ;
        try rewrite merge_call_host flatten_simplify in Heq ;
        try rewrite merge_trap flatten_simplify in Hsome ;
        try rewrite merge_trap flatten_simplify in Heq ;
        simpl in * ; simplify_eq.
      - rewrite merge_prepend in Hsome.
        rewrite merge_prepend in Heq.
        destruct (merge_values_list _) => //.
        destruct (merge_values_list _) eqn:Hmerge => //.
        simpl in *.
        destruct v2 => //.
        destruct v3 => //.
        simplify_eq.
        erewrite IHes => //.
        by rewrite Hmerge.
      - destruct es' => //.
      - destruct es => //.
      - 
      - destruct es, es' => //. }
  Qed. *)

  Lemma const_list_snoc_eq vs :
    forall ves es es' e,
      const_list ves ->
      const_list vs ->
      es ≠ [] ->
      to_val es = None ->
      (vs ++ es ++ es')%SEQ = ves ++ [e] ->
      es' = [] ∧ ∃ vs2, ves = vs ++ vs2 ∧ es = vs2 ++ [e] ∧ const_list vs2.
  Proof.
    induction vs;
      intros ves es es' e Hconst1 Hconst2 Hneq Hnval Heq.
    { erewrite app_nil_l in Heq.
      apply app_eq_inv in Heq as [[k [Hk1 Hk2]] | [k [Hk1 Hk2]]].
      { destruct k.
        { rewrite app_nil_r in Hk1.
          rewrite app_nil_l in Hk2.
          simplify_eq.
          assert (is_Some (to_val (ves))) as [c Hc];[|congruence].
          unfold to_val in Hnval. unfold to_val.
          apply const_list_to_val in Hconst1 as [v ->]. eauto. }
        { destruct k,es' =>//.
          rewrite app_nil_r in Hk2. simplify_eq.
          eauto. }  }
      { rewrite Hk1 in Hconst1.
        apply to_val_cat_None1 with (es2:=k) in Hnval.
        apply const_list_to_val in Hconst1 as [v Hv].
        congruence. } }
    { destruct ves.
      { destruct vs,es,es' =>//. }
      inversion Heq;subst.
      simpl in Hconst1,Hconst2.
      apply andb_true_iff in Hconst1,Hconst2.
      destruct Hconst1 as [Ha0 Hconst1].
      destruct Hconst2 as [_ Hconst2].
      apply IHvs in H1;auto.
      destruct H1 as [Heqes' [vs2 [Heq1 Heq2]]].
      subst. eauto.
    }
  Qed.
  Lemma length_to_val_immV v1 :
    forall vs1, to_val v1 = Some (immV vs1)
           -> length v1 = length vs1.
  Proof.
    induction v1;intros vs1 Hval.
    destruct vs1 => //.
    destruct vs1.
    apply to_val_nil in Hval. done.
    unfold to_val, iris.to_val in Hval.
    simpl in *.
    destruct a;try done ; simpl in *.
    destruct b;try done ; simpl in *.
    - rewrite merge_br flatten_simplify in Hval ; inversion Hval.
    - rewrite merge_return flatten_simplify in Hval ; inversion Hval.
    - rewrite merge_prepend in Hval. unfold to_val, iris.to_val in IHv1.
      destruct (merge_values_list _) => //. destruct v2 => //.
      inversion Hval ; subst. by erewrite IHv1.
    - rewrite merge_trap flatten_simplify in Hval.
      destruct v1 => //.
    - destruct (merge_values_list _) => //.
      destruct v0 => //.
      destruct i => //.
      destruct (vh_decrease _) => //.
      rewrite merge_br flatten_simplify in Hval ; inversion Hval.
      rewrite merge_return flatten_simplify in Hval ; inversion Hval.
      rewrite merge_call_host flatten_simplify in Hval ; done.
    - destruct (merge_values_list _) => //.
      destruct v0 => //.
      rewrite merge_call_host flatten_simplify in Hval => //. 
    - rewrite merge_call_host flatten_simplify in Hval ; done.
  Qed.
    

  Lemma lfilled_one_depth_trap k lh es vs n es' es'' :
    const_list vs ->
    lfilled k lh es (vs ++ [AI_label n es' [AI_trap]] ++ es'') ->
    k = 0 ∨ k = 1.
  Proof.
    revert lh es vs n es' es''.
    induction k;intros lh es vs n es' es'';auto.
    destruct k;auto.
    intros Hconst Hfill%lfilled_Ind_Equivalent.
    exfalso.
    inversion Hfill;subst.
    apply first_values in H0 as [? [? ?]];auto.
    simplify_eq.
    inversion H4;subst.
    do 2 destruct vs0 => //. 
  Qed.

  Lemma lfilled_trap_not_br i lh LI :
    lfilled i lh [AI_trap] LI ->
    (∀ i j lh vs0, const_list vs0 -> lfilled i lh (vs0 ++ [AI_basic (BI_br j)]) LI -> False).
  Proof.
    revert lh LI.
    induction i; intros lh LI Hfill%lfilled_Ind_Equivalent.
    { inversion Hfill;subst.
      intros i j lh vs' Hconst Hfill'.
      apply lfilled_Ind_Equivalent in Hfill'.
      inversion Hfill'.
      { simplify_eq.
        assert (vs0 ++ (vs' ++ [AI_basic (BI_br j)]) ++ es'0 =
                (vs0 ++ vs') ++ (AI_basic (BI_br j)) :: es'0)%SEQ as Heq.
        { repeat erewrite app_assoc. rewrite (separate1 _ es'0).
          repeat erewrite app_assoc. auto. }
        rewrite Heq in H0;clear Heq.
        apply first_values in H0 as [? [? ?]];auto.
        all: try by intros [? ?].
        2: apply const_list_app;auto. done.
      }
      { subst.
        apply first_values in H0 as [? [? ?]];auto. done.
      }      
    }
    { inversion Hfill;subst.
      intros i' j lh vs' Hconst Hfill'.
      apply lfilled_Ind_Equivalent in Hfill'.
      inversion Hfill'.
      { simplify_eq.
        assert (vs0 ++ (vs' ++ [AI_basic (BI_br j)]) ++ es'0 =
                (vs0 ++ vs') ++ (AI_basic (BI_br j)) :: es'0)%SEQ as Heq.
        { repeat erewrite app_assoc. rewrite (separate1 _ es'0).
          repeat erewrite app_assoc. auto. }
        rewrite Heq in H;clear Heq.
        apply first_values in H as [? [? ?]];auto.
        2: apply const_list_app;auto. done.
      }
      { simplify_eq.
        eapply first_values in H as [? [? ?]];auto.
        simplify_eq.
        apply lfilled_Ind_Equivalent in H6.
        apply lfilled_Ind_Equivalent in H1.
        eapply IHi in H1;eauto. all: try by intros [? ?]. Unshelve. apply 0. apply 0. apply lh'.
      }
    }
  Qed.

  Lemma lfilled_singleton (a : administrative_instruction) k lh es (les : list administrative_instruction) i lh'  :
    es ≠ [] ->
    (const_list es = false ) ->
    (es <> [AI_trap]) ->
    (is_const a = false ) ->
    (∀ n e1 e2, a ≠ AI_label n e1 e2) ->
    lfilled k lh es les -> 
    lfilled i lh' [a] les ->
    ∃ j lh, lfilled j lh [a] es ∧ j + k = i.
  Proof.
    revert a k lh es les lh'.
    induction i;intros a k lh es les lh' Hne Hnone1 Hnone2 Ha Hnlabel
                       Hfill1%lfilled_Ind_Equivalent Hfill2%lfilled_Ind_Equivalent.
    { inversion Hfill2;subst.
      inversion Hfill1;subst.
      { apply const_list_snoc_eq3 in H0 as [? [? [? [? [? ?]]]]];auto.
        subst. exists 0, (LH_base x x0). split;[|lia]. apply lfilled_Ind_Equivalent. by constructor. }
      { apply first_values in H0 as [? [? ?]];auto. subst.
        specialize (Hnlabel n es'0 LI). done. }
    }
    { inversion Hfill2;subst.
      inversion Hfill1;subst.
      { apply const_list_snoc_eq3 in H as [? [? [? [? [? ?]]]]];auto.
        subst.
        exists (S i),(LH_rec x n es' lh'0 x0).
        split;[|lia].
        apply lfilled_Ind_Equivalent. constructor;auto. }
      { apply first_values in H as [? [? ?]];auto. simplify_eq.
        apply lfilled_Ind_Equivalent in H1.
        apply lfilled_Ind_Equivalent in H6.
        eapply IHi in H1;[|eauto..].
        destruct H1 as [? [? ?]].
        eexists _,_. split;[apply H|lia]. }
    }
  Qed.

  Lemma filled_is_val_br_base_app_cases : ∀ i lh es1 es2 LI j v1 e1 ,
      iris.to_val LI = Some (brV (VH_base j v1 e1)) ->
      (es1 ++ es2) ≠ [] ->
      lfilled i lh (es1 ++ es2) LI ->
      i = 0 ∧ ∃ vs es, lh = LH_base vs es ∧ ((∃ es11 es12, es1 = es11 ++ (AI_basic (BI_br j)) :: es12 ∧ const_list es11) ∨
                                               (∃ es21 es22, es2 = es21 ++ (AI_basic (BI_br j)) :: es22 ∧ const_list es21 ∧ const_list es1) ∨
                                               (∃ es1' es2', es = es1' ++ (AI_basic (BI_br j)) :: es2' ∧ const_list es1 ∧ const_list es2 ∧ const_list es1')).
  Proof.
    assert (EqDecision administrative_instruction) as Heqa.
    { unfold EqDecision. apply administrative_instruction_eq_dec. }
    
    intros i lh es1 es2 LI j v1 e1 HLI Hnil Hfill.
    eapply filled_is_val_br_base in Hfill as Heq;eauto. subst.
    apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill.
    simplify_eq. split;auto.
    exists vs,es'. split;auto.
    clear Hfill.
    apply to_val_br_base in HLI as Heq.
    repeat erewrite app_assoc in Heq.
    rewrite -!app_assoc in Heq.
    assert ((AI_basic (BI_br j)) ∈ (vs ++ es1 ++ es2 ++ es')) as Hin.
    { rewrite Heq. apply elem_of_app. right. constructor. }
    
    apply elem_of_app in Hin as [Hcontr | Hin].
    { apply elem_of_list_split in Hcontr as [l1 [l2 Hl]]. subst.
      apply const_list_app in H as [_ H]. done. }

    apply elem_of_app_l in Hin as [Hin | [Hin Hnin]].
    { left.
      eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin]]].
      rewrite (app_assoc _ es2) in Heq.
      apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
      2: apply v_to_e_is_const_list.
      2: apply const_list_elem_of;auto;by intros [? ?].
      2:{ unfold const_list ; repeat rewrite forallb_app.
          simpl. rewrite andb_false_iff. left.
          by rewrite andb_false_iff ; right. } 
      2: do 2 destruct l1 => //.
      destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]]. Unshelve.
      rewrite separate1 in Heq2. rewrite -!app_assoc in Heq2.
      apply const_list_l_snoc_eq3 in Heq2;auto;try by intros [? ?].
      destruct Heq2 as [vs3 [es4 [Heq21 [Heq22 [Heq23 Hconst']]]]].
      destruct vs3 =>//;[|destruct vs3 =>//].
      destruct es4 =>//. rewrite app_nil_l in Heq23.
      rewrite app_nil_l app_nil_r in Heq22.
      rewrite app_nil_r in Heq21. simplify_eq.
      exists l1,l2. split;auto. }
    apply elem_of_app_l in Hin as [Hin | [Hin Hnin2]].
    { right;left.
      eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
      rewrite separate1 in Heq. rewrite -!app_assoc in Heq.
      do 2 rewrite app_assoc in Heq. exists l1,l2. split;auto.
      apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
      2: apply v_to_e_is_const_list.
      2: { apply not_elem_of_app;split;auto.
           apply not_elem_of_app;split;auto.
           apply const_list_elem_of;auto. }
      destruct Heq as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      simplify_eq.
      destruct vs2 => //;[|destruct vs2 => //].
      destruct es2 => //. rewrite app_nil_r in Heq1.
      pose proof (v_to_e_is_const_list v1) as Hc.
      rewrite -to_e_list_fmap Heq1 in Hc.
      apply const_list_app in Hc as [[? ?]%const_list_app ?]. auto. }
    { right;right.
      eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
      rewrite separate1 in Heq.
      do 3 rewrite app_assoc in Heq.
      exists l1,l2. split;auto.
      apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
      2: apply v_to_e_is_const_list.
      2: { repeat (apply not_elem_of_app;split;auto).
           apply const_list_elem_of;auto. }
      destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      simplify_eq.
      destruct vs2 =>//;[|destruct vs2 =>//].
      destruct es3 =>//.
      rewrite app_nil_r in Heq1.
      pose proof (v_to_e_is_const_list v1) as Hc.
      rewrite -to_e_list_fmap Heq1 in Hc.
      apply const_list_app in Hc as [[[? ?]%const_list_app ?]%const_list_app ?]. auto.
    }
    all: auto.
  Qed.

  Lemma filled_is_val_ret_base_app_cases : ∀ i lh es1 es2 LI v1 e1 ,
      iris.to_val LI = Some (retV (SH_base v1 e1)) ->
      (es1 ++ es2) ≠ [] ->
      lfilled i lh (es1 ++ es2) LI ->
      i = 0 ∧ ∃ vs es, lh = LH_base vs es ∧ ((∃ es11 es12, es1 = es11 ++ (AI_basic (BI_return)) :: es12 ∧ const_list es11) ∨
                                               (∃ es21 es22, es2 = es21 ++ (AI_basic (BI_return)) :: es22 ∧ const_list es21 ∧ const_list es1) ∨
                                               (∃ es1' es2', es = es1' ++ (AI_basic (BI_return)) :: es2' ∧ const_list es1 ∧ const_list es2 ∧ const_list es1')).
  Proof.
    assert (EqDecision administrative_instruction) as Heqa.
    { unfold EqDecision. apply administrative_instruction_eq_dec. }
    
    intros i lh es1 es2 LI v1 e1 HLI Hnil Hfill.
    eapply filled_is_val_ret_base in Hfill as Heq;eauto. subst.
    apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill.
    simplify_eq. split;auto.
    exists vs,es'. split;auto.
    clear Hfill.
    apply to_val_ret_base in HLI as Heq.
    repeat erewrite app_assoc in Heq.
    rewrite -!app_assoc in Heq.
    assert ((AI_basic (BI_return)) ∈ (vs ++ es1 ++ es2 ++ es')) as Hin.
    { rewrite Heq. apply elem_of_app. right. constructor. }
    
    apply elem_of_app in Hin as [Hcontr | Hin].
    { apply elem_of_list_split in Hcontr as [l1 [l2 Hl]]. subst.
      apply const_list_app in H as [_ H]. done. }

    apply elem_of_app_l in Hin as [Hin | [Hin Hnin]].
    { left.
      eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin]]].
      rewrite (app_assoc _ es2) in Heq.
      apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
      2: apply v_to_e_is_const_list.
      2: apply const_list_elem_of;auto;by intros [? ?].
      2: unfold const_list ; repeat rewrite forallb_app ; simpl ; 
      apply andb_false_iff ; left ; apply andb_false_iff ; by right.
      2: do 2 destruct l1 => //.
      destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]]. Unshelve.
      rewrite separate1 in Heq2. rewrite -!app_assoc in Heq2.
      apply const_list_l_snoc_eq3 in Heq2;auto;try by intros [? ?].
      destruct Heq2 as [vs3 [es4 [Heq21 [Heq22 [Heq23 Hconst']]]]].
      destruct vs3 =>//;[|destruct vs3 =>//].
      destruct es4 =>//. rewrite app_nil_l in Heq23.
      rewrite app_nil_l app_nil_r in Heq22.
      rewrite app_nil_r in Heq21. simplify_eq.
      exists l1,l2. split;auto. }
    apply elem_of_app_l in Hin as [Hin | [Hin Hnin2]].
    { right;left.
      eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
      rewrite separate1 in Heq. rewrite -!app_assoc in Heq.
      do 2 rewrite app_assoc in Heq. exists l1,l2. split;auto.
      apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
      2: apply v_to_e_is_const_list.
      2: { apply not_elem_of_app;split;auto.
           apply not_elem_of_app;split;auto.
           apply const_list_elem_of;auto. }
      destruct Heq as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      simplify_eq.
      destruct vs2 =>//;[|destruct vs2 =>//].
      destruct es2 =>//. rewrite app_nil_r in Heq1.
      pose proof (v_to_e_is_const_list v1) as Hc.
      rewrite -to_e_list_fmap Heq1 in Hc.
      apply const_list_app in Hc as [[? ?]%const_list_app ?]. auto. }
    { right;right.
      eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
      rewrite separate1 in Heq.
      do 3 rewrite app_assoc in Heq.
      exists l1,l2. split;auto.
      apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
      2: apply v_to_e_is_const_list.
      2: { repeat (apply not_elem_of_app;split;auto).
           apply const_list_elem_of;auto. }
      destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      simplify_eq.
      destruct vs2 =>//;[|destruct vs2 =>//].
      destruct es3 =>//.
      rewrite app_nil_r in Heq1.
      pose proof (v_to_e_is_const_list v1) as Hc.
      rewrite -to_e_list_fmap Heq1 in Hc.
      apply const_list_app in Hc as [[[? ?]%const_list_app ?]%const_list_app ?]. auto.
    }
    all: auto.
  Qed.


  Lemma filled_is_val_call_host_base_app_cases : ∀ i lh es1 es2 LI v1 e1 tf h cvs,
      iris.to_val LI = Some (callHostV tf h cvs ((LL_base v1 e1))) ->
      (es1 ++ es2) ≠ [] ->
      lfilled i lh (es1 ++ es2) LI ->
      i = 0 ∧ ∃ vs es, lh = LH_base vs es ∧ ((∃ es11 es12, es1 = es11 ++ (AI_call_host tf h cvs) :: es12 ∧ const_list es11) ∨
                                               (∃ es21 es22, es2 = es21 ++ (AI_call_host tf h cvs) :: es22 ∧ const_list es21 ∧ const_list es1) ∨
                                               (∃ es1' es2', es = es1' ++ (AI_call_host tf h cvs) :: es2' ∧ const_list es1 ∧ const_list es2 ∧ const_list es1')).
  Proof.
    assert (EqDecision administrative_instruction) as Heqa.
    { unfold EqDecision. apply administrative_instruction_eq_dec. }
    
    intros i lh es1 es2 LI v1 e1 tf h cvs HLI Hnil Hfill.
    eapply filled_is_val_call_host_base in Hfill as Heq;eauto. subst.
    apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill.
    simplify_eq. split;auto.
    exists vs,es'. split;auto.
    clear Hfill.
    apply to_val_call_host_base in HLI as Heq.
    repeat erewrite app_assoc in Heq.
    rewrite -!app_assoc in Heq.
    assert ((AI_call_host tf h cvs) ∈ (vs ++ es1 ++ es2 ++ es')) as Hin.
    { rewrite Heq. apply elem_of_app. right. constructor. }
    
    apply elem_of_app in Hin as [Hcontr | Hin].
    { apply elem_of_list_split in Hcontr as [l1 [l2 Hl]]. subst.
      apply const_list_app in H as [_ H]. done. }

    apply elem_of_app_l in Hin as [Hin | [Hin Hnin]].
    { left.
      eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin]]].
      rewrite (app_assoc _ es2) in Heq.
      apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
      2: apply v_to_e_is_const_list.
      2: apply const_list_elem_of;auto;by intros [? ?].
      2: unfold const_list ; repeat rewrite forallb_app ; simpl ;
      apply andb_false_iff ; left ; apply andb_false_iff ; by right.      2: do 2 destruct l1 => //.
      destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]]. Unshelve.
      rewrite separate1 in Heq2. rewrite -!app_assoc in Heq2.
      apply const_list_l_snoc_eq3 in Heq2;auto;try by intros [? ?].
      destruct Heq2 as [vs3 [es4 [Heq21 [Heq22 [Heq23 Hconst']]]]].
      destruct vs3 => //;[|destruct vs3 => //].
      destruct es4 => //. rewrite app_nil_l in Heq23.
      rewrite app_nil_l app_nil_r in Heq22.
      rewrite app_nil_r in Heq21. simplify_eq.
      exists l1,l2. split;auto. }
    apply elem_of_app_l in Hin as [Hin | [Hin Hnin2]].
    { right;left.
      eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
      rewrite separate1 in Heq. rewrite -!app_assoc in Heq.
      do 2 rewrite app_assoc in Heq. exists l1,l2. split;auto.
      apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
      2: apply v_to_e_is_const_list.
      2: { apply not_elem_of_app;split;auto.
           apply not_elem_of_app;split;auto.
           apply const_list_elem_of;auto. }
      destruct Heq as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      simplify_eq.
      destruct vs2 =>//;[|destruct vs2 =>//].
      destruct es2 =>//. rewrite app_nil_r in Heq1.
      pose proof (v_to_e_is_const_list v1) as Hc.
      rewrite -to_e_list_fmap Heq1 in Hc.
      apply const_list_app in Hc as [[? ?]%const_list_app ?]. auto. }
    { right;right.
      eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
      rewrite separate1 in Heq.
      do 3 rewrite app_assoc in Heq.
      exists l1,l2. split;auto.
      apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
      2: apply v_to_e_is_const_list.
      2: { repeat (apply not_elem_of_app;split;auto).
           apply const_list_elem_of;auto. }
      destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      simplify_eq.
      destruct vs2 =>//;[|destruct vs2 =>//].
      destruct es3 =>//.
      rewrite app_nil_r in Heq1.
      pose proof (v_to_e_is_const_list v1) as Hc.
      rewrite -to_e_list_fmap Heq1 in Hc.
      apply const_list_app in Hc as [[[? ?]%const_list_app ?]%const_list_app ?]. auto.
    }
    all: auto.
  Qed.

  Lemma of_val_br_app_r n (vh : valid_holed n) es2 :
    of_val (brV vh) ++ es2 = of_val (brV (vh_append vh es2)).
  Proof.
    simpl. destruct vh => //= ; by rewrite app_comm_cons app_assoc. 
  Qed.

  Lemma of_val_ret_app_r sh es2 :
    of_val (retV sh) ++ es2 = of_val (retV (sh_append sh es2)).
  Proof.
    simpl. destruct sh => //= ; by rewrite app_comm_cons app_assoc.
  Qed.

  
  Lemma lfilled_to_val_app i lh es1 es2 LI vs :
    lfilled i lh (es1 ++ es2)%list LI ->
    to_val LI = Some vs ->
    (∃ vs', to_val es1 = Some vs' ∧ lfilled i lh ((iris.of_val vs') ++ es2) LI).
  Proof.
    intros Hfilled Hetov.
    destruct vs.
    { pose proof (filled_is_val_imm _ _ _ _ _ Hetov Hfilled) as
        [vs [es' [-> [-> [Hconst1 Hconst2]]]]].
      apply const_list_to_val in Hconst1 as [v1 Hv1].
      apply const_list_to_val in Hconst2 as [v2 Hv2].
      edestruct fill_val as [vs12 [Hvs12 Heql]];eauto.
      assert (Hvs12':=Hvs12). unfold to_val.
      apply to_val_cat in Hvs12' as [-> Hev2].
      apply iris.of_to_val in Hev2 as <-. eexists. split; eauto.
      rewrite -!of_val_imm.
      repeat rewrite v_to_e_is_fmap.
      erewrite <- fmap_app. rewrite take_drop.
      rewrite - v_to_e_is_fmap. rewrite of_val_imm.
      apply lfilled_Ind_Equivalent in Hfilled.
      inversion Hfilled;simplify_eq.
      erewrite of_to_val;eauto.
      apply lfilled_Ind_Equivalent. constructor. auto. }
    { apply to_val_trap_is_singleton in Hetov as Heq. subst.
      apply lfilled_Ind_Equivalent in Hfilled.
      inversion Hfilled.
      2: { exfalso. do 2 destruct vs =>//=. }
      simplify_eq.
      apply app_eq_singleton in H as [[HH HH']|[HH HH']];subst.
      { exfalso. destruct es1,es2,es' =>//=. }
      apply app_eq_singleton in HH' as [[HH HH']|[HH HH']];subst.
      { apply app_eq_singleton in HH as [[-> ->]|[-> ->]].
        simpl. eauto. eauto. }
      { apply app_nil in HH as [-> ->]. eauto. }
    }
    { (* destruct es1 (*(decide (es1 ++ es2 = [])).*) ; first eauto. *)
      (*    { apply app_nil in e as [-> ->]. eauto. } *)
      remember (length_rec LI) as n.
      assert (length_rec LI < S n) ; first lia.
      remember (S n) as m.
      clear Heqn Heqm n.
      generalize dependent i0. generalize dependent es1. generalize dependent lh.
      generalize dependent i.
      generalize dependent LI.
      induction m ; intros LI Hsize ; intros ; first lia.
      (*     { destruct i ; destruct lh ; unfold lfilled, lfill in Hfilled => //. } *)
      destruct es1 ; first eauto.
      unfold to_val, iris.to_val in Hetov ; simpl in Hetov.
      destruct LI ; first by inversion Hetov.
      destruct a0 ; try destruct b ; simpl in Hetov  => //.
      - rewrite merge_br flatten_simplify in Hetov.
        inversion Hetov.
        apply Eqdep.EqdepTheory.inj_pair2 in H1 ; subst.
        eapply filled_is_val_br_base_app_cases in Hfilled as HH;[|eauto..].
        destruct HH as [-> [vs [es [-> HH]]]].
        destruct HH as [[es11 [es12 [Heq Hconst]]]
                       |[[es11 [es12 [Heq (Hconst & Hconst')]]]
                        |[es11 [es12 [Heq (Hconst&Hconst'&Hconst'')]]]]].
        { apply const_es_exists in Hconst as Hv.
          destruct Hv as [v Hv].
          exists (brV (VH_base i0 v es12)). rewrite -to_val_br_eq Heq -Hv.
          split;auto. rewrite Hv in Heq. erewrite of_to_val. 2: apply to_val_br_eq.
          rewrite -Heq. auto. }
        { apply const_list_to_val in Hconst' as Hv.
          destruct Hv as [v Hv].
          exists (immV v). split;auto. erewrite of_to_val;eauto. }
        { apply const_list_to_val in Hconst as Hv.
          destruct Hv as [v Hv].
          exists (immV v). split;auto. erewrite of_to_val;eauto. }
        unfold iris.to_val => /=.
        rewrite merge_br flatten_simplify => //=.
      - rewrite merge_return flatten_simplify in Hetov => //.
      - rewrite merge_prepend in Hetov.
        destruct (merge_values_list _) eqn:Hmerge => //.
        destruct v0 => //.
        simpl in Hetov.
        rewrite - app_comm_cons in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        + rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (cons_length_rec (AI_basic (BI_const v)) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i1 lh1).
          unfold to_val in IHm at 1.
          unfold iris.to_val in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        + assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (cons_length_rec (AI_basic (BI_const v))
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i1 lh1).
          unfold to_val in IHm at 1.
          unfold iris.to_val in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).        
          exists (val_combine (immV [v]) vs') ; split => //=.
          * unfold to_val, iris.to_val => /=.
            rewrite merge_prepend.
            unfold to_val, iris.to_val in Htv.
            destruct (merge_values_list (map _ es1)) eqn:Hmerge1 => //=.
            inversion Htv.
            destruct vs' => //.
            assert (to_val es1 = Some trapV) ;
              first by unfold to_val, iris.to_val ; rewrite Hmerge1 H2.
            apply to_val_trap_is_singleton in H1 as ->.
            simpl in Hmerge.
            rewrite merge_trap flatten_simplify in Hmerge.
            by destruct (es2 ++ aft).
          * unfold lfilled, lfill => //=.
            unfold lfilled, lfill in Hfill ; simpl in Hfill.
            apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
            destruct vs' => //.
            apply to_val_trap_is_singleton in Htv as ->.
            simpl in Hmerge.
            rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
            unfold iris.of_val. destruct lh => //.
            unfold iris.of_val. destruct s => //.
            unfold iris.of_val. destruct l0 => //. 
            
           
      - rewrite merge_trap flatten_simplify in Hetov.
        by destruct LI.
      - destruct (merge_values_list _) eqn:Hmerge => //.
        destruct v => // ; (try by rewrite merge_return flatten_simplify in Hetov) ;
                     try by rewrite merge_call_host flatten_simplify in Hetov.
        destruct i1 => //.
        destruct (vh_decrease _) eqn:Hdecr => //.
        rewrite merge_br flatten_simplify in Hetov.
        inversion Hetov.
        destruct H0.
        apply Eqdep.EqdepTheory.inj_pair2 in H1 ; subst.
        assert (length_rec l0 < m).
        { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
        unfold lfilled, lfill in Hfilled ; 
          destruct i,lh ; fold lfill in Hfilled => //.
        + destruct (const_list l1) eqn:Hl1 => //.
          apply b2p in Hfilled.
          destruct l1 ; inversion Hfilled ; subst ; 
            last by unfold const_list in Hl1; inversion Hl1.
          eexists. split.
          * unfold to_val, iris.to_val => /=.
            rewrite Hmerge Hdecr merge_br flatten_simplify => //.
          * unfold lfilled, lfill => //=.
            replace l0 with (vfill v [AI_basic (BI_br (S i1))]) ; first done.
            assert (iris.to_val l0 = Some (brV lh1)) ;
              first by unfold iris.to_val ; rewrite Hmerge.          
            apply iris.of_to_val in H0 as <-.
            unfold iris.of_val. by rewrite (vfill_decrease _ Hdecr).
        + destruct (const_list l1) eqn:Hl1 => //.
          destruct (lfill _ _ _) eqn:Hfill => //.
          apply b2p in Hfilled.
          destruct l1 ; inversion Hfilled ; subst ;
            last by unfold const_list in Hl1.
          assert (lfilled i lh ((a :: es1) ++ es2) l4); 
            first by unfold lfilled ; rewrite Hfill.
          specialize (IHm l4 H i lh (a :: es1) H0 (S i1) lh1).
          unfold to_val in IHm at 1.
          unfold iris.to_val in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill').
          eexists ; split => //.
          unfold lfilled, lfill ; fold lfill => //=.
          unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
          apply b2p in Hfill' ; by subst.
      - destruct (merge_values_list _) => //.
        destruct v => //.
        rewrite merge_call_host flatten_simplify in Hetov => //. 
      - rewrite merge_call_host flatten_simplify in Hetov.
        by destruct LI. }
    { remember (length_rec LI) as n.
      assert (length_rec LI < S n) ; first lia.
      remember (S n) as m.
      clear Heqn Heqm n.
      generalize dependent s. generalize dependent es1. generalize dependent lh.
      generalize dependent i. 
      generalize dependent LI.
      induction m ; intros LI Hsize ; intros ; first lia.
      (*     { destruct i ; destruct lh ; unfold lfilled, lfill in Hfilled => //. } *)
      destruct es1 ; first eauto.
      unfold to_val, iris.to_val in Hetov ; simpl in Hetov.
      destruct LI ; first by inversion Hetov.
      destruct a0 ; try destruct b ; simpl in Hetov  => //.
      - rewrite merge_br flatten_simplify in Hetov => //.
      - rewrite merge_return flatten_simplify in Hetov.
        inversion Hetov ; subst.
        eapply filled_is_val_ret_base_app_cases in Hfilled as HH;[|eauto..].
        destruct HH as [-> [vs [es [-> HH]]]].
        destruct HH as [[es11 [es12 [Heq Hconst]]]
                       |[[es11 [es12 [Heq (Hconst & Hconst')]]]
                        |[es11 [es12 [Heq (Hconst&Hconst'&Hconst'')]]]]].
        { apply const_es_exists in Hconst as Hv.
          destruct Hv as [v Hv].
          exists (retV (SH_base v es12)). rewrite -to_val_ret_eq Heq -Hv.
          split;auto. rewrite Hv in Heq. erewrite of_to_val. 2: apply to_val_ret_eq.
          rewrite -Heq. auto. }
        { apply const_list_to_val in Hconst' as Hv.
          destruct Hv as [v Hv].
          exists (immV v). split;auto. erewrite of_to_val;eauto. }
        { apply const_list_to_val in Hconst as Hv.
          destruct Hv as [v Hv].
          exists (immV v). split;auto. erewrite of_to_val;eauto. }
        unfold iris.to_val => /=.
        rewrite merge_return flatten_simplify => //=.
      - rewrite merge_prepend in Hetov.
        destruct (merge_values_list _) eqn:Hmerge => //.
        destruct v0 => //.
        simpl in Hetov.
        rewrite - app_comm_cons in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        + rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (cons_length_rec (AI_basic (BI_const v)) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled s0).
          unfold to_val in IHm at 1.
          unfold iris.to_val in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        + assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (cons_length_rec (AI_basic (BI_const v))
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H s0).
          unfold to_val in IHm at 1.
          unfold iris.to_val in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).        
          exists (val_combine (immV [v]) vs') ; split => //=.
          * unfold to_val, iris.to_val => /=.
            rewrite merge_prepend.
            unfold to_val, iris.to_val in Htv.
            destruct (merge_values_list (map _ es1)) eqn:Hmerge1 => //=.
            inversion Htv.
            destruct vs' => //.
            assert (to_val es1 = Some trapV) ;
              first by unfold to_val, iris.to_val ; rewrite Hmerge1 H2.
            apply to_val_trap_is_singleton in H1 as ->.
            simpl in Hmerge.
            rewrite merge_trap flatten_simplify in Hmerge.
            by destruct (es2 ++ aft).
          * unfold lfilled, lfill => //=.
            unfold lfilled, lfill in Hfill ; simpl in Hfill.
            apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
            destruct vs' => //.
            apply to_val_trap_is_singleton in Htv as ->.
            simpl in Hmerge.
            rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
            unfold iris.of_val. destruct lh => //.
            unfold iris.of_val. destruct s1 => //.
            unfold iris.of_val. destruct l0 => //.
      - rewrite merge_trap flatten_simplify in Hetov.
        by destruct LI.
      - destruct (merge_values_list _) eqn:Hmerge => //.
        destruct v => //.
        destruct i0 => //.
        destruct (vh_decrease _) eqn:Hdecr => //.
        rewrite merge_br flatten_simplify in Hetov => //.
        rewrite merge_return flatten_simplify in Hetov.
        inversion Hetov ; subst.
        assert (length_rec l0 < m).
        { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
        unfold lfilled, lfill in Hfilled ; 
          destruct i,lh ; fold lfill in Hfilled => //.
        + destruct (const_list l1) eqn:Hl1 => //.
          apply b2p in Hfilled.
          destruct l1 ; inversion Hfilled ; subst ; 
            last by unfold const_list in Hl1; inversion Hl1.
          eexists. split.
          * unfold to_val, iris.to_val => /=.
            rewrite Hmerge merge_return flatten_simplify => //.
          * unfold lfilled, lfill => //=.
            replace l0 with (sfill s0 [AI_basic BI_return]) ; first done.
            assert (iris.to_val l0 = Some (retV s0)) ;
              first by unfold iris.to_val ; rewrite Hmerge.          
            apply iris.of_to_val in H0 as <-.
            unfold iris.of_val. done.
        + destruct (const_list l1) eqn:Hl1 => //.
          destruct (lfill _ _ _) eqn:Hfill => //.
          apply b2p in Hfilled.
          destruct l1 ; inversion Hfilled ; subst ;
            last by unfold const_list in Hl1.
          assert (lfilled i lh ((a :: es1) ++ es2) l4); 
            first by unfold lfilled ; rewrite Hfill.
          specialize (IHm l4 H i lh (a :: es1) H0 s0).
          unfold to_val in IHm at 1.
          unfold iris.to_val in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill').
          eexists ; split => //.
          unfold lfilled, lfill ; fold lfill => //=.
          unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
          apply b2p in Hfill' ; by subst.
        + rewrite merge_call_host flatten_simplify in Hetov => //.
      - destruct (merge_values_list _) => //.
        destruct v => //.
        rewrite merge_call_host flatten_simplify in Hetov => //. 
      - rewrite merge_call_host flatten_simplify in Hetov. done. }
    { remember (length_rec LI) as n.
      assert (length_rec LI < S n) ; first lia.
      remember (S n) as m.
      clear Heqn Heqm n.
      generalize dependent l0.
      generalize dependent es1. generalize dependent lh.
      generalize dependent i. 
      generalize dependent LI.
      induction m ; intros LI Hsize ; intros ; first lia.
      (*     { destruct i ; destruct lh ; unfold lfilled, lfill in Hfilled => //. } *)
      destruct es1 ; first eauto.
      unfold to_val, iris.to_val in Hetov ; simpl in Hetov.
      destruct LI ; first by inversion Hetov.
      destruct a0 ; try destruct b ; simpl in Hetov  => //.
      - rewrite merge_br flatten_simplify in Hetov => //.
      - rewrite merge_return flatten_simplify in Hetov => //.
       
      - rewrite merge_prepend in Hetov.
        destruct (merge_values_list _) eqn:Hmerge => //.
        destruct v0 => //.
        simpl in Hetov.
        inversion Hetov ; subst.
        rewrite - app_comm_cons in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        + rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (cons_length_rec (AI_basic (BI_const v)) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled l2).
          unfold to_val in IHm at 1.
          unfold iris.to_val in IHm.
          rewrite Hmerge in IHm.
          
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        + assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (cons_length_rec (AI_basic (BI_const v))
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H l2).
          unfold to_val in IHm at 1.
          unfold iris.to_val in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).        
          exists (val_combine (immV [v]) vs') ; split => //=.
          * unfold to_val, iris.to_val => /=.
            rewrite merge_prepend.
            unfold to_val, iris.to_val in Htv.
            destruct (merge_values_list (map _ es1)) eqn:Hmerge1 => //=.
            inversion Htv.
            destruct vs' => //.
            assert (to_val es1 = Some trapV) ;
              first by unfold to_val, iris.to_val ; rewrite Hmerge1 H2.
            apply to_val_trap_is_singleton in H1 as ->.
            simpl in Hmerge.
            rewrite merge_trap flatten_simplify in Hmerge.
            by destruct (es2 ++ aft).
          * unfold lfilled, lfill => //=.
            unfold lfilled, lfill in Hfill ; simpl in Hfill.
            apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
            destruct vs' => //.
            apply to_val_trap_is_singleton in Htv as ->.
            simpl in Hmerge.
            rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
            unfold iris.of_val. destruct lh => //.
            unfold iris.of_val. destruct s => //.
            unfold iris.of_val. destruct l1 => //.
      - rewrite merge_trap flatten_simplify in Hetov.
        by destruct LI.
      - destruct (merge_values_list _) eqn:Hmerge => //.
        destruct v => //.
        destruct i0 => //.
        destruct (vh_decrease _) eqn:Hdecr => //.
        rewrite merge_br flatten_simplify in Hetov => //.
        rewrite merge_return flatten_simplify in Hetov => //.
        rewrite merge_call_host flatten_simplify in Hetov.
        inversion Hetov ; subst.
        assert (length_rec l2 < m).
        { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
        unfold lfilled, lfill in Hfilled ; 
          destruct i,lh ; fold lfill in Hfilled => //.
        + destruct (const_list l0) eqn:Hl1 => //.
          apply b2p in Hfilled.
          destruct l0 ; inversion Hfilled ; subst ; 
            last by unfold const_list in Hl1; inversion Hl1.
          eexists. split.
          * unfold to_val, iris.to_val => /=.
            rewrite Hmerge merge_call_host flatten_simplify => //.
          * unfold lfilled, lfill => //=.
            replace l2 with (llfill l4 [AI_call_host f h l]) ; first done.
            assert (iris.to_val l2 = Some (callHostV f h l l4)) ;
              first by unfold iris.to_val ; rewrite Hmerge.          
            apply iris.of_to_val in H0 as <-.
            unfold iris.of_val. done.
        + destruct (const_list _) eqn:Hl1 => //.
          destruct (lfill _ _ _) eqn:Hfill => //.
          apply b2p in Hfilled.
          destruct l0 ; inversion Hfilled ; subst ;
            last by unfold const_list in Hl1.
          assert (lfilled i lh ((a :: es1) ++ es2) l6); 
            first by unfold lfilled ; rewrite Hfill.
          specialize (IHm l6 H i lh (a :: es1) H0 ).
          unfold to_val in IHm at 1.
          unfold iris.to_val in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm _ Logic.eq_refl) as (vs' & Htv & Hfill').
          eexists ; split => //.
          unfold lfilled, lfill ; fold lfill => //=.
          unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
          apply b2p in Hfill' ; by subst.
      - destruct (merge_values_list _) eqn:Hmerge => //.
        destruct v => //.
        rewrite merge_call_host flatten_simplify in Hetov.
        simpl in Hetov.
        inversion Hetov ; subst.
        unfold lfilled, lfill in Hfilled.
        destruct i, lh => // ; last first.
        fold lfill in Hfilled.
        destruct (const_list l0) eqn:Hl0, (lfill i lh ((a :: es1)%SEQ ++ es2)%list) => //.
        apply b2p in Hfilled ; destruct l0 ; inversion Hfilled => //.
        subst ; simpl in Hl0. done.
        destruct (const_list l0) eqn:Hl0 => //.
        apply b2p in Hfilled ; destruct l0 ; inversion Hfilled ;
          last by subst ; simpl in Hl0.
        subst.
        eexists ; split.
        unfold to_val, iris.to_val => /=.
        rewrite Hmerge merge_call_host flatten_simplify.
        done.
        unfold lfilled, lfill => /=.
        replace l1 with (llfill l3 [AI_call_host f h l]) => //.
        specialize (of_to_val (es := l1)) as H.
        unfold iris.to_val in H. rewrite Hmerge in H.
        specialize (H _ Logic.eq_refl).
        by unfold of_val, iris.of_val in H. 
      - rewrite merge_call_host flatten_simplify in Hetov. 
        inversion Hetov ; subst.
        eapply filled_is_val_call_host_base_app_cases in Hfilled as HH;[|eauto..].
        destruct HH as [-> [vs [es [-> HH]]]].
        destruct HH as [[es11 [es12 [Heq Hconst]]]
                       |[[es11 [es12 [Heq (Hconst & Hconst')]]]
                        |[es11 [es12 [Heq (Hconst&Hconst'&Hconst'')]]]]].
        { apply const_es_exists in Hconst as Hv.
          destruct Hv as [v Hv].
          exists (callHostV f h l ((LL_base v es12))).
          rewrite -to_val_call_host_eq Heq -Hv.
          split;auto. rewrite Hv in Heq. erewrite of_to_val. 2: apply to_val_call_host_eq.
          rewrite -Heq. auto. }
        { apply const_list_to_val in Hconst' as Hv.
          destruct Hv as [v Hv].
          exists (immV v). split;auto. erewrite of_to_val;eauto. }
        { apply const_list_to_val in Hconst as Hv.
          destruct Hv as [v Hv].
          exists (immV v). split;auto. erewrite of_to_val;eauto. }
        unfold iris.to_val => /=.
        rewrite merge_call_host flatten_simplify => //=. }
  Qed.

  Lemma to_val_brV_None vs n i lh es LI :
    const_list vs ->
    length vs = n ->
    lfilled i lh (vs ++ [AI_basic (BI_br i)]) LI ->
    iris.to_val [AI_label n es LI] = None.
  Proof.
    intros Hconst Hlen Hlfill.
    eapply val_head_stuck_reduce.
    apply r_simple. eapply rs_br;eauto.
    Unshelve. apply (Build_store_record [] [] [] []).
    apply (Build_frame [] (Build_instance [] [] [] [] [])).
  Qed.

  Lemma to_val_immV_label_None es v m ctx :
    iris.to_val es = Some (immV v) ->
    iris.to_val [AI_label m ctx es] = None.
  Proof.
    intros Hes.
    eapply val_head_stuck_reduce.
    eapply r_simple, rs_label_const. eapply to_val_const_list;eauto.
    Unshelve. apply (Build_store_record [] [] [] []).
    apply (Build_frame [] (Build_instance [] [] [] [] [])).
  Qed.  
  
  Lemma to_val_trapV_label_None es m ctx :
    iris.to_val es = Some trapV ->
    iris.to_val [AI_label m ctx es] = None.
  Proof.
    intros Hes.
    apply to_val_trap_is_singleton in Hes as ->.
    eapply val_head_stuck_reduce.
    eapply r_simple, rs_label_trap.
    Unshelve. apply (Build_store_record [] [] [] []).
    apply (Build_frame [] (Build_instance [] [] [] [] [])).
  Qed.

  Lemma to_val_cons_immV v l :
    iris.to_val (AI_basic (BI_const v) :: iris.of_val (immV l)) = Some (immV (v :: l)).
  Proof.
    rewrite separate1.
    erewrite to_val_cat_inv;eauto.
    2: apply to_of_val.
    auto.
  Qed.
  Lemma to_val_cons_brV i (lh : valid_holed i) v es :
    iris.to_val es = Some (brV lh) ->
    iris.to_val (AI_basic (BI_const v) :: es) = Some (brV (vh_push_const lh [v])).
  Proof.
    intros Hes.
    unfold to_val,iris.to_val. cbn.
    unfold to_val,iris.to_val in Hes.
    destruct (merge_values_list (map to_val_instr es)) eqn:Hsome;[|done].
    simplify_eq.
    unfold merge_values_list in Hsome.
    destruct (map to_val_instr es) eqn:Hmap;try done.
    destruct v0;try done.
    rewrite merge_prepend. by rewrite /= Hsome.
  Qed.
  Lemma to_val_cons_retV s v es :
    iris.to_val es = Some (retV s) ->
    iris.to_val (AI_basic (BI_const v) :: es) = Some (retV (sh_push_const s [v])).
  Proof.
    intros Hes.
    unfold to_val,iris.to_val. cbn.
    unfold to_val,iris.to_val in Hes.
    destruct (merge_values_list (map to_val_instr es)) eqn:Hsome;[|done].
    simplify_eq.
    unfold merge_values_list in Hsome.
    destruct (map to_val_instr es) eqn:Hmap;try done.
    destruct v0;try done.
    rewrite merge_prepend. by rewrite /= Hsome.
  Qed.
  Lemma to_val_cons_callHostV tf h cvs s v es :
    iris.to_val es = Some (callHostV tf h cvs s) ->
    iris.to_val (AI_basic (BI_const v) :: es) = Some (callHostV tf h cvs (llh_push_const s [v])).
  Proof.
    intros Hes.
    unfold to_val,iris.to_val. cbn.
    unfold to_val,iris.to_val in Hes.
    destruct (merge_values_list (map to_val_instr es)) eqn:Hsome;[|done].
    simplify_eq.
    unfold merge_values_list in Hsome.
    destruct (map to_val_instr es) eqn:Hmap;try done.
    destruct v0;try done.
    rewrite merge_prepend. by rewrite /= Hsome.
  Qed.
  Lemma to_val_cons_None es v :
    iris.to_val es = None ->
    iris.to_val (AI_basic (BI_const v) :: es) = None.
  Proof.
    intros Hes.
    rewrite separate1.
    apply to_val_cat_None2;auto.
  Qed.
  
  Lemma to_val_AI_trap_Some_nil es vs :
    iris.to_val ([AI_trap] ++ es) = Some vs -> es = [].
  Proof.
    destruct es =>//.
    intros Hes;exfalso.
    assert (iris.to_val ([AI_trap] ++ (a :: es)) = None).
    { rewrite -(app_nil_l [AI_trap]).
      rewrite -app_assoc.
      apply to_val_not_trap_interweave;auto. }
    congruence.
  Qed.

  Lemma to_val_None_label n es' LI :
    iris.to_val LI = None ->
    iris.to_val [AI_label n es' LI] = None.
  Proof.
    intros HLI.
    unfold iris.to_val. cbn. 
    unfold iris.to_val in HLI.
    destruct (merge_values_list (map to_val_instr LI)) eqn:Hmerge;done.
  Qed.

  Lemma to_val_None_lfilled LI k lh es :
    iris.to_val es = None → lfilled k lh es LI -> iris.to_val LI = None.
  Proof.
    revert LI lh es;induction k;intros LI lh es Hnone Hfill%lfilled_Ind_Equivalent.
    { inversion Hfill;simplify_eq.
      apply to_val_cat_None2;auto.
      apply to_val_cat_None1;auto. }
    { inversion Hfill;simplify_eq.
      apply lfilled_Ind_Equivalent in H1.
      apply IHk in H1;auto.
      apply to_val_cat_None2;auto.
      apply to_val_cat_None1;auto.
      apply to_val_None_label. auto.
    }
  Qed.

  Lemma to_val_app_retV v :
  ∀ (s : simple_valid_holed) (es : iris.expr),
    iris.to_val es = Some (retV s)
    → iris.to_val (v_to_e_list v ++ es)%SEQ =
        Some (retV (sh_push_const s v)).
  Proof.
    induction v;intros s es Hes.
    simpl. rewrite sh_push_const_nil;auto.
    simpl.
    apply IHv in Hes.
    rewrite (separate1 a).
    erewrite sh_push_const_app.
    apply to_val_cons_retV with (v:=a) in Hes.
    rewrite Hes. auto.
  Qed.

  Lemma to_val_local_inv n f LI v :
    iris.to_val [AI_local n f LI] = Some v ->
    ∃ tf h w vh, v = callHostV tf h w (LL_local [] n f vh []).
  Proof.
    intros Hv.
    unfold iris.to_val in Hv. cbn in Hv.
    destruct (merge_values_list (map to_val_instr LI));try done.
    destruct v0;try done.
    inversion Hv;eauto.
  Qed.

  Lemma to_val_local_add_frame LI' tf h w vh n f :
    iris.to_val LI' = Some (callHostV tf h w vh) ->
    iris.to_val [AI_local n f LI'] = Some (callHostV tf h w (LL_local [] n f vh [])).
  Proof.
    intros Hv.
    unfold iris.to_val in Hv. cbn in Hv.
    unfold iris.to_val. cbn.
    destruct (merge_values_list (map to_val_instr LI'));try done.
    simplify_eq.  auto.
  Qed.

  Lemma sfill_call_host_compose wh vh tf h w es1 :
    iris.to_val es1 = None ->
    sfill wh [AI_call_host tf h w] = sfill vh es1 ->
    ∃ vh', es1 = sfill vh' [AI_call_host tf h w].
    intros Hnone Hs.
    assert (es1 ≠ []);[intros Hcontr;subst;done|].
    assert (const_list es1 = false).
    { destruct (const_list es1) eqn:Hcontr; auto. apply const_list_to_val in Hcontr as [? ?]. congruence. }
    assert (es1 = [AI_trap] → False).
    { intros Hcontr. subst. done. }
    
    revert wh Hs. induction vh;intros wh Hs.
    { destruct wh.
      { cbn in *.
        rewrite separate1 in Hs.
        symmetry in Hs.
        apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
        destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        apply const_es_exists in Hconst as [? ?].
        simplify_eq. exists (SH_base x es2). cbn. auto.
      }
      { cbn in *.
        rewrite separate1 in Hs.
        symmetry in Hs.
        apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
        destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        apply const_es_exists in Hconst as [? ?].
        simplify_eq. exists (SH_rec x n l2 wh es2). cbn. auto.
      }    
    }
    { destruct wh.
      { cbn in *.
        rewrite separate1 in Hs.
        rewrite (separate1 _ l1) in Hs.
        apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
        destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        apply const_es_exists in Hconst as [? ?].
        simplify_eq. destruct x =>//.
      }
      { cbn in *.
        rewrite separate1 in Hs.
        rewrite (separate1 _ l1) in Hs.
        apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
        destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        apply const_es_exists in Hconst as [? ?].
        simplify_eq. destruct x =>//. destruct es2 =>//.
        rewrite app_nil_l app_nil_r in Heq2. simplify_eq.
        apply IHvh in H5 as [vh' Hvh'].
        subst es1. eauto.
      }
    }
  Qed.

  Lemma llfill_call_host_compose wh vh tf h w es1 :
    iris.to_val es1 = None ->
    llfill wh [AI_call_host tf h w] = llfill vh es1 ->
    ∃ vh', es1 = llfill vh' [AI_call_host tf h w].
    intros Hnone Hs.
    assert (es1 ≠ []);[intros Hcontr;subst;done|].
    assert (const_list es1 = false).
    { destruct (const_list es1) eqn:Hcontr; auto. apply const_list_to_val in Hcontr as [? ?]. congruence. }
    assert (es1 = [AI_trap] → False).
    { intros Hcontr. subst. done. }
    
    revert wh Hs. induction vh;intros wh Hs.
    { destruct wh.
      { cbn in *.
        rewrite separate1 in Hs.
        symmetry in Hs.
        apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
        destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        apply const_es_exists in Hconst as [? ?].
        simplify_eq. exists (LL_base x es2). cbn. auto.
      }
      { cbn in *.
        rewrite separate1 in Hs.
        symmetry in Hs.
        apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
        destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        apply const_es_exists in Hconst as [? ?].
        simplify_eq. exists (LL_label x n l2 wh es2). cbn. auto.
      }
      { cbn in *.
        rewrite separate1 in Hs.
        symmetry in Hs.
        apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
        destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        apply const_es_exists in Hconst as [? ?].
        simplify_eq. exists (LL_local x n f wh es2). cbn. auto.
      }
    }
    { destruct wh.
      { cbn in *.
        rewrite separate1 in Hs.
        rewrite (separate1 _ l1) in Hs.
        apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
        destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        apply const_es_exists in Hconst as [? ?].
        simplify_eq. destruct x =>//.
      }
      { cbn in *.
        rewrite separate1 in Hs.
        rewrite (separate1 _ l1) in Hs.
        apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
        destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        apply const_es_exists in Hconst as [? ?].
        simplify_eq. destruct x =>//. destruct es2 =>//.
        rewrite app_nil_l app_nil_r in Heq2. simplify_eq.
        apply IHvh in H5 as [vh' Hvh'].
        subst es1. eauto.
      }
      { cbn in *.
        rewrite separate1 in Hs.
        rewrite (separate1 _ l1) in Hs.
        apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
        destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        apply const_es_exists in Hconst as [? ?].
        simplify_eq. destruct x =>//.
      }
    }
    { destruct wh.
      { cbn in *.
        rewrite separate1 in Hs.
        rewrite (separate1 _ l0) in Hs.
        apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
        destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        apply const_es_exists in Hconst as [? ?].
        simplify_eq. destruct x =>//.
      }
      { cbn in *.
        rewrite separate1 in Hs.
        rewrite (separate1 _ l0) in Hs.
        apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
        destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        apply const_es_exists in Hconst as [? ?].
        simplify_eq. destruct x =>//.
      }
      { cbn in *.
        rewrite separate1 in Hs.
        rewrite (separate1 _ l0) in Hs.
        apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
        destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        apply const_es_exists in Hconst as [? ?].
        simplify_eq.
        destruct x =>//. destruct es2 =>//.
        rewrite app_nil_l app_nil_r in Heq2. simplify_eq.
        apply IHvh in H5 as [vh' Hvh'].
        subst es1. eauto.
      }
    }  
  Qed.

  Lemma sfill_nested vh wh e :
    ∃ vh', sfill vh (sfill wh e) = sfill vh' e.
  Proof.
    induction vh.
    { destruct wh.
      { exists (SH_base (l ++ l1) (l2 ++ l0)).
        cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc. auto. }
      { exists (SH_rec (l ++ l1) n l2 wh (l3 ++ l0)).
        cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc.
        rewrite app_comm_cons. rewrite (separate1 _ l3).
        repeat erewrite app_assoc. auto. } }
    { destruct IHvh as [vh' Heq].
      cbn. rewrite Heq.
      exists (SH_rec l n l0 vh' l1). cbn. auto. }
  Qed.

  Lemma llfill_nested vh wh e :
    ∃ vh', llfill vh (llfill wh e) = llfill vh' e.
  Proof.
    induction vh.
    { destruct wh.
      { exists (LL_base (l ++ l1) (l2 ++ l0)).
        cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc. auto. }
      { exists (LL_label (l ++ l1) n l2 wh (l3 ++ l0)).
        cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc.
        rewrite app_comm_cons. rewrite (separate1 _ l3).
        repeat erewrite app_assoc. auto. }
      { exists (LL_local (l ++ l1) n f wh (l2 ++ l0)).
        cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc.
        rewrite app_comm_cons.
        repeat erewrite app_assoc. auto. }
    }
    { destruct IHvh as [vh' Heq].
      cbn. rewrite Heq.
      exists (LL_label l n l0 vh' l1). cbn. auto. }
    { destruct IHvh as [vh' Heq].
      cbn. rewrite Heq.
      exists (LL_local l n f vh' l0). cbn. auto. }
  Qed.

  Lemma to_val_local_none n f es1 vh :
    iris.to_val [AI_local n f (llfill vh es1)] = None ->
    iris.to_val [AI_local n f es1] = None.
  Proof.
    intros Hv.
    destruct (iris.to_val [AI_local n f es1]) eqn:Hsome;auto.
    exfalso.
    apply to_val_local_inv in Hsome as Heq.
    destruct Heq as [tf [h [w [wh Heq]]]]. subst v.
    assert ([AI_local n f es1] = llfill (LL_local [] n f (LL_base [] []) []) es1) as Heq.
    { simpl. rewrite app_nil_r. auto. }
    rewrite Heq in Hsome.
    apply of_to_val in Hsome.
    simpl in Hsome. inversion Hsome.
    rewrite app_nil_r in H0. subst es1.
    simplify_eq. pose proof (llfill_nested vh wh [AI_call_host tf h w]) as [vh' Hvh'].
    rewrite Hvh' in Hv.
    assert (iris.of_val (callHostV tf h w (LL_local [] n f vh' [])) =
              [AI_local n f (llfill vh' [AI_call_host tf h w])]).
    { cbn. auto. }
    assert (iris.to_val [AI_local n f (llfill vh' [AI_call_host tf h w])] =
              Some (callHostV tf h w (LL_local [] n f vh' []))).
    { rewrite -H0. apply to_of_val. }
    congruence.
  Qed.

  Lemma to_val_local_none_inv n f es1 vh :
    iris.to_val es1 = None ->
    iris.to_val [AI_local n f es1] = None ->
    iris.to_val [AI_local n f (llfill vh es1)] = None.
  Proof.
    intros Hnone Hv.
    destruct (iris.to_val [AI_local n f (llfill vh es1)]) eqn:Hsome;auto.
    exfalso.
    apply to_val_local_inv in Hsome as Heq.
    destruct Heq as [tf [h [w [wh Heq]]]]. subst v.
    assert ([AI_local n f (llfill vh es1)] = llfill (LL_local [] n f vh []) es1) as Heq.
    { simpl. auto. }
    rewrite Heq in Hsome.
    apply of_to_val in Hsome.
    simpl in Hsome. inversion Hsome.
    apply llfill_call_host_compose in H0 as [vh' Hvh'];auto.
    assert ([AI_local n f es1] =
              iris.of_val (callHostV tf h w (LL_local [] n f vh' []))).
    { cbn. rewrite Hvh'. auto. }
    
    assert (iris.to_val [AI_local n f es1] = Some (callHostV tf h w (LL_local [] n f vh' [])));[|congruence].
    rewrite H. apply to_of_val.
  Qed.

  (* The following lemma will generalise to any local fill *)
  Lemma to_val_local_no_local_none n f e :
    iris.to_val [AI_local n f e] = None ->
    match iris.to_val e with
    | Some (callHostV _ _ _ _) => False
    | _ => True
    end.
  Proof.
    intros Hv.
    destruct (iris.to_val e) eqn:He;auto.
    destruct v;auto.
    unfold iris.to_val in Hv.
    unfold iris.to_val in He.
    cbn in *.
    destruct (merge_values_list (map to_val_instr e)) eqn:Hmerge;try done.
    destruct v;try done.
  Qed.

  Fixpoint ll_of_sh sh :=
    match sh with
    | SH_base bef aft => LL_base bef aft
    | SH_rec bef n es sh aft => LL_label bef n es (ll_of_sh sh) aft end.

  Lemma sfill_to_llfill sh e :
    sfill sh e = llfill (ll_of_sh sh) e.
  Proof.
    induction sh;auto.
    simpl. rewrite IHsh.
    auto.
  Qed.

  Lemma to_val_local_ret_none n f e vh :
    iris.to_val e = Some (retV vh) ->
    iris.to_val [AI_local n f e] = None.
  Proof.
    unfold iris.to_val. cbn.
    destruct (merge_values_list (map to_val_instr e)); try done.
    destruct v; done.
  Qed.

  Lemma to_val_local_none_none n f e :
    iris.to_val e = None ->
    iris.to_val [AI_local n f e] = None.
  Proof.
    unfold iris.to_val. cbn.
    destruct (merge_values_list (map to_val_instr e)); try done.
  Qed.
  
End wasm_lang_properties.
