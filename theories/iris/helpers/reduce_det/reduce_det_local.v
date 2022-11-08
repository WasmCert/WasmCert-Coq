From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export iris_reduce_det_prelude iris_split_reduce.

Lemma local_det s f es s' f' es' ws2 n f0 f2 es2 nnn:
  (∀ (f f2 f1 : frame) (es2 es1 es : seq.seq administrative_instruction),
    reduce s f es s' f1 es1
    → reduce s f es ws2 f2 es2 → length_rec es < nnn → reduce_det_goal s' f1 es1 ws2 f2 es2 es) ->
  reduce s f es s' f' es' ->
  reduce s f0 [AI_local n f es] ws2 f2 es2 ->
  length_rec [AI_local n f es] < S nnn ->
  ((∀ (f f2 f1 : frame) (es2 es1 es : seq.seq administrative_instruction),
      reduce s f es s' f1 es1
      → reduce s f es ws2 f2 es2 → length_rec es < nnn → reduce_det_goal s' f1 es1 ws2 f2 es2 es)
   → reduce s f es ws2 f2 es2 → length_rec es < S nnn → reduce_det_goal s' f' es' ws2 f2 es2 es) ->
  reduce_det_goal s' f0 [AI_local n f' es'] ws2 f2 es2 [AI_local n f es].
Proof.
  move => IHnnn Hred1 Hred2 Hlen IHHred1.
  (* final case : the r_local case. We perform the case analysis on Hred2 by hand *)
  clear IHHred1. remember [AI_local n f es] as es0.
  rewrite <- (app_nil_l [AI_local n f es]) in Heqes0.
  induction Hred2 ; (try by inversion Heqes0) ;
    try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
  { destruct H ; (try by inversion Heqes0) ;
      try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
    - inversion Heqes0 ; subst. exfalso ; values_no_reduce.
    - inversion Heqes0 ; subst.
      exfalso ; by apply (test_no_reduce_trap _ _ _ _ _ Hred1).
    - { inversion Heqes0 ; subst.
        induction Hred1 ;
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
              found_intruse (AI_basic (BI_return)) H1 Hxl.
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
    - rewrite Heqes0 in H0. filled_trap H0 Hxl1. }
  + rewrite Heqes0 in H. simple_filled H k lh bef aft nn ll ll'.
    simpl in H. apply Logic.eq_sym, app_eq_unit in H as [[ -> Hes] | [_ Hes]].
    apply app_eq_unit in Hes as [[ -> _ ] | [-> ->]].
    empty_list_no_reduce.
    unfold lfilled, lfill in H0 ; simpl in H0 ; rewrite app_nil_r in H0 ;
      move/eqP in H0 ; subst.
      by apply IHHred2.
      apply app_eq_nil in Hes as [-> _ ] ; empty_list_no_reduce.
  + (* In case Hred2 was also proved using r_local, we make use of the induction
         hypothesis IHnnn *)
    inversion Heqes0 ; subst. clear IHHred2.
    assert (length_rec es < nnn).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec ; lia.
    destruct (IHnnn _ _ _ _ _ _ Hred1 Hred2 H)
      as [Hσ | [ [i Hstart] | (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3 & Hσ) (* ] *)]].
    * left. by inversion Hσ ; subst.
    * right ; left. exists (i + 1). unfold first_instr => //=. unfold first_instr in Hstart.
      rewrite Hstart => //=. repeat f_equiv. lia.
    * repeat right. exists (i1 + 1),(i2 + 1),(i3 + 1). repeat split => //=.
      unfold first_instr => //= ; unfold first_instr in Hstart1 ;
                             rewrite Hstart1 => //=; repeat f_equiv; lia.
      unfold first_instr => //= ; unfold first_instr in Hstart2 ;
                             rewrite Hstart2 => //=; repeat f_equiv; lia.
      unfold first_instr => //= ; unfold first_instr in Hstart3 ;
                             rewrite Hstart3 => //=; repeat f_equiv; lia.
        by inversion Hσ ; subst.
Qed.
