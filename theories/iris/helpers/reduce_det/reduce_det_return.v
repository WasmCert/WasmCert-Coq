From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export iris_reduce_det_prelude.

Lemma return_det vs n i lh s f f0 es s' f' es' :
  const_list vs ->
  length vs = n ->
  lfilled i lh (vs ++ [AI_basic BI_return]) es ->
  reduce s f [AI_local n f0 es] s' f' es' ->
  reduce_det_goal s f vs s' f' es' [AI_local n f0 es].
Proof.
  move => H H0 H1 Hred.
  (* this is the rs_return case. It combines the difficulties of rs_br with
         the fact that, as for the previous few cases, [ only_one ] cannot be applied
         and thus all the work must be performed by hand *)
  left ; remember [AI_local n f0 es] as es0.
  rewrite <- app_nil_l in Heqes0.
  induction Hred ; try by inversion Heqes0 ;
    try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
  { destruct H2 ; try by inversion Heqes0 ;
      try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
    - inversion Heqes0 ; subst.
      destruct i ; unfold lfilled, lfill in H1.
      { destruct lh ; last by false_assumption.
        destruct (const_list l) ; last by false_assumption.
        move/eqP in H1. rewrite H1 in H2.
        unfold const_list in H2 ; do 3 rewrite forallb_app in H2.
        apply andb_true_iff in H2 as [_ Habs].
        apply andb_true_iff in Habs as [Habs _].
        apply andb_true_iff in Habs as [_ Habs].
        apply andb_true_iff in Habs as [Habs _].
        inversion Habs. }
      fold lfill in H1. destruct lh ; first by false_assumption.
      destruct (const_list l) ; last by false_assumption.
      destruct (lfill _ _ _) ; last by false_assumption.
      move/eqP in H1. rewrite H1 in H2. unfold const_list in H2.
      rewrite forallb_app in H2. apply andb_true_iff in H2 as [_ Habs].
      simpl in Habs. false_assumption.
    - inversion Heqes0. rewrite <- H5 in H1.
      destruct i ; unfold lfilled, lfill in H1.
      { destruct lh ; last by false_assumption.
        destruct (const_list l) ; last by false_assumption. move/eqP in H1.
        found_intruse (AI_basic BI_return) H1 Hxl1.
        apply in_or_app ; right. apply in_or_app ; left.
        apply in_or_app ; right. by left. }
      fold lfill in H1. destruct lh ; first by false_assumption.
      destruct (const_list l) ; last by false_assumption.
      destruct (lfill _ _ _) ; last by false_assumption.
      move/eqP in H1. found_intruse (AI_label n1 l0 l2) H1 Hxl1.
    - inversion Heqes0 ; subst.
      destruct (lfilled_first_values H1 H4) as (_ & _ & Hvs) => //=.
      destruct (Hvs (Logic.eq_sym H6)) as [Hrew _].
        by rewrite Hrew.
    - rewrite Heqes0 in H3. filled_trap H3 Hxl1. }
  + rewrite Heqes0 in H2. simple_filled H2 k lh0 bef aft nn ll ll'.
    simpl in H2. apply Logic.eq_sym, app_eq_unit in H2 as [[-> Hes] | [_ Hes]].
    apply app_eq_unit in Hes as [[-> _]|[Hes ->]].
    empty_list_no_reduce.
    unfold lfilled, lfill in H3. simpl in H3. move/eqP in H3.
    rewrite app_nil_r in H3. subst. apply IHHred => //=.
    apply app_eq_nil in Hes as [-> _] ; empty_list_no_reduce.
  + { inversion Heqes0 ; subst.
      induction Hred ;
        (try by simple_filled H1 i lh bef aft nn ll ll' ;
         found_intruse (AI_basic BI_return) H1 Hxl1 ;
         apply in_or_app ; right ; apply in_or_app ; left ;
         apply in_or_app ; right ; left) ;
        try by simple_filled H1 i lh bef aft nn ll ll' ;
        [ found_intruse (AI_basic BI_return) H1 Hxl2 ;
          [ apply in_app_or in Hxl2 as [Habs | Habs] ;
            [ assert (const_list ves) as Hconst ;
              [ rewrite H3 ; apply v_to_e_is_const_list => //=
              | intruse_among_values ves Habs Hconst ]
            | destruct Habs as [Habs | Habs] => //=]
          | apply in_or_app ; right ; apply in_or_app ; left ;
            apply in_or_app ; right ; by left] 
        | apply in_app_or in Hxl1 as [Habs | Habs] ;
          [ assert (const_list ves) as Hconst ;
            [ rewrite H3 ; apply v_to_e_is_const_list => //=
            | intruse_among_values ves Habs Hconst ]
          | destruct Habs as [Habs | Habs] => //=]].
      { destruct H0 ;
          (try by simple_filled H1 i lh bef aft nn ll ll' ;
           found_intruse (AI_basic BI_return) H1 Hxl1 ;
           apply in_or_app ; right ; apply in_or_app ; left ;
           apply in_or_app ; right ; left) ;
          try by simple_filled H1 i lh bef aft nn ll ll' ;
          [ found_intruse (AI_basic BI_return) H1 Hxl2 ;
            [ apply in_app_or in Hxl2 as [Habs | Habs] ; 
              [ intruse_among_values vs0 Habs H0
              | destruct Habs as [Habs | Habs] => //=]
            | apply in_or_app ; right ; apply in_or_app ; left ;
              apply in_or_app ; right ; by left] 
          | apply in_app_or in Hxl1 as [Habs | Habs] ;
            [ intruse_among_values vs0 Habs H0
            | destruct Habs as [Habs | Habs] => //=]].
        - simple_filled2 H1 i lh bef aft nn ll ll'.
          found_intruse (AI_basic BI_return) H1 Hxl1 ;
            apply in_or_app ; right ; apply in_or_app ; left ;
              apply in_or_app ; right ; by left.
          destruct bef ; last by inversion H1 as [[ Hhd Htl ]];
            apply Logic.eq_sym, app_eq_nil in Htl as [_ Habs] ;
            inversion Habs.
          inversion H1 ; subst ; clear H1.
          unfold lfill in Heqles ; destruct i.
          { destruct lh0 ; last by inversion Heqles.
            destruct (const_list l) ; inversion Heqles.
            rewrite H2 in H0. unfold const_list in H0.
            do 3 rewrite forallb_app in H0.
            simpl in H0. repeat (rewrite andb_false_r in H0 + rewrite andb_false_l in H0).
            false_assumption. }
          fold lfill in Heqles. destruct lh0 ; first by inversion Heqles.
          destruct (const_list l) ; last by inversion Heqles.
          destruct (lfill _ _ _) ; inversion Heqles.
          rewrite H2 in H0. unfold const_list in H0. rewrite forallb_app in H0.
          simpl in H0. rewrite andb_false_r in H0. false_assumption.
        - simple_filled2 H1 i lh bef aft nn ll ll'.
          found_intruse (AI_basic BI_return) H1 Hxl1 ;
            apply in_or_app ; right ; apply in_or_app ; left ;
              apply in_or_app ; right ; by left.
          destruct bef ; last by inversion H1 as [[ Hhd Htl ]];
            apply Logic.eq_sym, app_eq_nil in Htl as [_ Habs] ;
            inversion Habs.
          inversion H1 ; subst ; clear H1.
          unfold lfill in Heqles ; destruct i.
          { destruct lh0 ; last by inversion Heqles.
            destruct (const_list l) ; inversion Heqles.
            found_intruse (AI_basic (BI_return)) H1 Hxl1.
            apply in_or_app ; right ; apply in_or_app ; left ;
              apply in_or_app ; right ; by left. }
          fold lfill in Heqles. destruct lh0 ; first by inversion Heqles.
          destruct (const_list l) ; last by inversion Heqles.
          destruct (lfill _ _ _) ; inversion Heqles.
          found_intruse (AI_label n l0 l2) H1 Hxl1.
        - assert (lfilled 1 (LH_rec [] n es (LH_base [] []) [])
                          LI [AI_label n es LI]).
          { unfold lfilled, lfill ; fold lfill => //=. by rewrite app_nil_r. }
          destruct (lfilled_trans H3 H4) as [lh' Hfill].
          destruct (lfilled_first_values Hfill H1) as (Habs & _ & _);
            try done.
        - simple_filled H1 i lh bef aft nn ll ll'.
          found_intruse (AI_basic BI_return) H1 Hxl1.
          rewrite Hxl1 in H0. inversion H0.
          apply in_or_app ; right ; apply in_or_app ; left ;
            apply in_or_app ; right ; by left.
          rewrite Hxl1 in H0 ; inversion H0.
        - replace [AI_trap] with ([] ++ [AI_trap])%SEQ in H2 => //=.
          destruct (lfilled_first_values H2 H1)
            as (Habs & _ & _) => //=. } 
      * exfalso. eapply lfilled_return_and_reduce => //=. }
Qed.
