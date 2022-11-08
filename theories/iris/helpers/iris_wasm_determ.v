From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export iris_reduce_properties first_instr.
Require Export reduce_det_invoke_native reduce_det_unop reduce_det_binop reduce_det_binop_none
        reduce_det_testop_i32 reduce_det_testop_i64 reduce_det_relop reduce_det_cvtop_convert
        reduce_det_cvtop_convert_none reduce_det_cvtop_reinterpret reduce_det_select
        reduce_det_block reduce_det_loop reduce_det_return reduce_det_label reduce_det_local.

Section determ.
  
  Let reducible := @iris.program_logic.language.reducible wasm_lang.

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.

  Lemma reduce_det: forall (ws: store_record) (f: frame) es ws1 f1 es1 ws2 f2 es2,
      reduce ws f es ws1 f1 es1 ->
      reduce ws f es ws2 f2 es2 ->
      reduce_det_goal ws1 f1 es1 ws2 f2 es2 es.
  Proof.
    intros ws f es ws1 f1 es1 ws2 f2 es2 Hred1 Hred2.
    (* we perform an (strong) induction on the length_rec of es, i.e. its number of
     instructions, counting recursively under AI_locals and AI_labels *)
    cut (forall n, length_rec es < n -> reduce_det_goal ws1 f1 es1 ws2 f2 es2 es).
    (* the next few lines simply help put the induction into place *)
    { intro Hn ; apply (Hn (S (length_rec es))) ; lia. }
    intro nnn. generalize dependent es. generalize dependent es1.
    generalize dependent es2. generalize dependent f1. generalize dependent f2.
    generalize dependent f.
    induction nnn ; intros f f2 f1 es2 es1 es Hred1 Hred2 Hlen ; first lia.
    (* begining of the actual reasoning *)
    (* We have hypotheses [ Hred1 : es -> es1 ] and  [ Hred2 : es -> es2 ]. We perform
     a case analysis on Hred1 (induction because of the r_label case) *)
    induction Hred1.
    (* Most cases are dealt with using the [ only_one ] tactic. This tactic assumes that
     hypothesis Hred2 is of the form [ objs -> es2 ] where objs is an explicit list
     that [ only_one ] requires as an argument. It then performs a case analysis on
     Hred2 and exfalsos away as many cases as it can. See 2 commented examples below. 
     Most of the time, it exfalsos away all cases but one, so we are left with 
     reductions [ es -> es1 ] and [ es -> es2 ] being derived by the same rule, 
     so the leftmost disjunct of the conclusion holds. In some cases, 
     the tactic [only_one] will leave us with more than one case, and we will have to
     manually exfalso away some cases *)
    (* Technical point : before calling [ only_one ], we must clear the induction hypothesis
     IHnnn, because [ only_one ] performs an induction which will not work if IHnnn is
     present *)
    { destruct H ; clear IHnnn.
      - by apply unop_det.
      - by apply binop_det.
      - by apply binop_none_det.
      - by apply testop_i32_det.
      - by apply testop_i64_det.
      - by apply relop_det.
      - by apply cvtop_convert_det.
      - by apply cvtop_convert_none_det.
      - by apply cvtop_reinterpret_det.
      - by only_one [AI_basic BI_unreachable] Hred2.
      - by only_one [AI_basic BI_nop] Hred2.
      - by only_one [AI_basic (BI_const v) ; AI_basic BI_drop] Hred2.
      - by apply select_false_det.
      - by apply select_true_det.
      - by eapply block_det.
      - by eapply loop_det.
      - only_one [AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] Hred2 ;
          [done | by inversion Heqes ; subst].
      - only_one [AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] Hred2 ;
          [by inversion Heqes ; subst | done].
      - only_one [AI_label n es vs] Hred2.
        (* This is the rs_label_const case (i.e. Hred1 was [ [AI_label n es vs] -> es ]
         with vs a list of values). Now when called, [ only_one ] can only reduce the 
         amount of possibilities for how [ Hred2 : [AI_label n es vs] -> es2 ] was
         proved to 4 : rs_label_const (which leeds to the correct conclusion), or
         rs_label_trap (could be exfalsoed but coq is actually very happy to take done as
         an answer here), or rs_br or r_label (these last two require some work to
         exfalso away) *)
        (* Likewise, [ only_one ] will only be able to narrow down the possiblities to
         these for when we will handle the rs_label_trap and rs_br cases (the next 2) ;
         the r_label case will also face this difficulty (among many others inherent to
         the nature of r_label *)
        + done.
        + done.
        + unfold lfilled, lfill in H2.
          destruct i. { destruct lh ; last by false_assumption.
                        destruct (const_list l) ; last by false_assumption.
                        move/eqP in H2. subst.
                        unfold const_list in H.
                        do 3 rewrite forallb_app in H.
                        apply andb_true_iff in H as [_ H].
                        apply andb_true_iff in H as [H _].
                        apply andb_true_iff in H as [_ H].
                        inversion H. }
          fold lfill in H2. destruct lh ; first by false_assumption.
          destruct (const_list l) ; last by false_assumption.
          destruct (lfill _ _ _) ; last by false_assumption.
          move/eqP in H2. subst. unfold const_list in H.
          rewrite forallb_app in H. apply andb_true_iff in H as [_ Habs].
          inversion Habs.
        + destruct bef ; inversion H1.
          exfalso ; values_no_reduce.
          unfold lfill in Heqles1. destruct k. { destruct lh0 ; last by false_assumption.
                                                 destruct (const_list l2) ;
                                                   inversion Heqles1.
                                                 subst. unfold const_list in H.
                                                 do 2 rewrite forallb_app in H.
                                                 apply andb_true_iff in H as [_ H].
                                                 by apply andb_true_iff in H as [H _]. }
          fold lfill in Heqles1. destruct lh0 ; first by false_assumption.
          destruct (const_list l2) ; last by inversion Heqles1.
          destruct (lfill _ _ _) ; inversion Heqles1.
          subst. unfold const_list in H. rewrite forallb_app in H.
          apply andb_true_iff in H as [_ Habs] ; by inversion Habs.
          apply Logic.eq_sym, app_eq_nil in H4 as [_ Habs] ; inversion Habs.
      - only_one [AI_label n es [AI_trap]] Hred2.
        + done.
        + done.
        + rewrite <- H5 in H1. unfold lfilled, lfill in H1.
          destruct i. { destruct lh ; last by false_assumption.
                        destruct (const_list l) ; last by false_assumption.
                        move/eqP in H1. found_intruse (AI_basic (BI_br 0)) H1 Hxl1.
                        apply in_or_app. right.
                        apply in_or_app. left.
                        apply in_or_app. right => //=. by left. }
          fold lfill in H1. destruct lh ; first by false_assumption.
          destruct (const_list l) ; last by false_assumption.
          destruct (lfill _ _ _) ; last by false_assumption.
          move/eqP in H1. found_intruse (AI_label n1 l0 l2) H1 Hxl1.
        + destruct bef ; inversion H0. rewrite <- H4 in Heqles1.
          unfold lfill in Heqles1. destruct k. { destruct lh0 ; last by false_assumption.
                                                 destruct (const_list l2) ;
                                                   inversion Heqles1.
                                                 destruct l2.
                                                 { destruct es1 ;
                                                     first by empty_list_no_reduce.
                                                   inversion H6.
                                                   apply Logic.eq_sym,
                                                     app_eq_nil in H8 as [Hes1 _].
                                                   subst.
                                                   exfalso ;
                                                     apply (AI_trap_irreducible
                                                              _ _ _ _ _ Hred2). }
                                                 inversion H6.
                                                 apply Logic.eq_sym,
                                                   app_eq_nil in H8 as [_ Hes1].
                                                 apply app_eq_nil in Hes1 as [Hes1 _].
                                                 subst ; empty_list_no_reduce. }
          fold lfill in Heqles1. destruct lh0 ; first by false_assumption.
          destruct (const_list l2) ; last by inversion Heqles1.
          destruct (lfill _ _ _) ; inversion Heqles1.
          subst. found_intruse (AI_label n1 l3 l5) H6 Hxl1. 
          apply Logic.eq_sym, app_eq_nil in H3 as [_ Habs] ; inversion Habs.
      - only_one [AI_label n es LI] Hred2.
        + subst. unfold lfilled, lfill in H1. destruct i.
          { destruct lh ; last by false_assumption.
            destruct (const_list l) ; last by false_assumption.
            move/eqP in H1. rewrite H1 in H2.
            unfold const_list in H2. do 3 rewrite forallb_app in H2.
            apply andb_true_iff in H2 as [_ Habs].
            apply andb_true_iff in Habs as [Habs _].
            apply andb_true_iff in Habs as [_ Habs].
            inversion Habs. }
          fold lfill in H1. destruct lh ; first by false_assumption.
          destruct (const_list l) ; last by false_assumption.
          destruct (lfill _ _ _) ; last by false_assumption.
          move/eqP in H1. rewrite H1 in H2. unfold const_list in H2.
          rewrite forallb_app in H2. apply andb_true_iff in H2 as [_ Habs].
          inversion Habs.
        + subst. unfold lfilled, lfill in H1. destruct i.
          { destruct lh ; last by false_assumption.
            destruct (const_list l) ; last by false_assumption.
            move/eqP in H1. found_intruse (AI_basic (BI_br 0)) H1 Hxl1.
            apply in_or_app. right. apply in_or_app. left.
            apply in_or_app. right. by left. } 
          fold lfill in H1. destruct lh ; first by false_assumption.
          destruct (const_list l) ; last by false_assumption.
          destruct (lfill _ _ _) ; last by false_assumption.
          move/eqP in H1. found_intruse (AI_label n l0 l2) H1 Hxl1.
        + subst.
          destruct (lfilled_first_values H4 H1) as (? & ? & ?) => //=.
          destruct (H5 (Logic.eq_sym H6)) as [Hrew ?].
          by rewrite Hrew.
        + destruct bef ; last by inversion H3 as [[ Hhd Htl ]];
            apply Logic.eq_sym, app_eq_nil in Htl as [_ Habs] ;
            inversion Habs.
          inversion H3 ; subst ; clear H3. 
          assert (lfilled k lh1 es1 l0) as Hfill ;
            first by unfold lfilled ; rewrite <- Heqles1. exfalso.
          assert (lfilled 0 (LH_base vs []) [AI_basic (BI_br i)]
                          (vs ++ [AI_basic (BI_br i)])) ;
            first by unfold lfilled, lfill ; rewrite H app_nil_r.
          eapply lfilled_trans in H1 as [lh' Hfill'] => //=.
          simpl in Hfill'.
          rewrite - (app_nil_l [_]) in Hfill'.
          rewrite - cat_app in Hfill'.
          eapply lfilled_br_and_reduce ; try exact Hfill ; try exact Hfill' ; try done.
      - only_one [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_br_if i)] Hred2 ;
          [ done | subst ; exfalso ; by apply H0 ].
      - only_one [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_br_if i)] Hred2 ;
          [ subst ; exfalso ; by apply H | done].
      - only_one [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_br_table iss i)] Hred2.
        subst. rewrite H0 in H2. inversion H2 ; by subst.
        subst. apply (ssrnat.leq_trans H) in H1. rewrite ssrnat.ltnn in H1. false_assumption.
      - only_one [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_br_table iss i)] Hred2.
        subst. apply (ssrnat.leq_trans H0) in H. rewrite ssrnat.ltnn in H. false_assumption.
        done.
      - (* [ only_one ] cannot be applied in the following cases, so we perform the 
         case analysis by hand *)
        left ; remember [AI_local n f0 es] as es0.
        rewrite <- app_nil_l in Heqes0.
        induction Hred2 ; try by inversion Heqes0 ;
          try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
        { destruct H1 ; try by inversion Heqes0 ;
            try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
          - inversion Heqes0 ; subst.
            destruct i ; unfold lfilled, lfill in H3.
            { destruct lh ; last by false_assumption.
              destruct (const_list l) ; last by false_assumption.
              move/eqP in H3. rewrite H3 in H.
              unfold const_list in H ; do 3 rewrite forallb_app in H.
              apply andb_true_iff in H as [_ Habs].
              apply andb_true_iff in Habs as [Habs _].
              apply andb_true_iff in Habs as [_ Habs].
              apply andb_true_iff in Habs as [Habs _].
              inversion Habs. }
            fold lfill in H3. destruct lh ; first by false_assumption.
            destruct (const_list l) ; last by false_assumption.
            destruct (lfill _ _ _) ; last by false_assumption.
            move/eqP in H3. rewrite H3 in H. unfold const_list in H.
            rewrite forallb_app in H. apply andb_true_iff in H as [_ Habs].
            simpl in Habs. false_assumption.
          - rewrite Heqes0 in H2. filled_trap H2 Hxl1. }
        + rewrite Heqes0 in H1. simple_filled H1 k lh bef aft nn ll ll'.
          simpl in H1. apply Logic.eq_sym, app_eq_unit in H1 as [[-> Hes] | [_ Hes]].
          apply app_eq_unit in Hes as [[-> _]|[Hes ->]].
          empty_list_no_reduce.
          unfold lfilled, lfill in H2. simpl in H2. move/eqP in H2.
          rewrite app_nil_r in H2. subst. apply IHHred2 => //=.
          apply app_eq_nil in Hes as [-> _] ; empty_list_no_reduce.
        + inversion Heqes0 ; subst. exfalso ; values_no_reduce.
      - left ; remember [AI_local n f0 [AI_trap]] as es0.
        rewrite <- app_nil_l in Heqes0.
        induction Hred2 ; try by inversion Heqes0 ;
          try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
        { destruct H ; try by inversion Heqes0 ;
            try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
          - inversion Heqes0 ; subst.
            destruct i ; unfold lfilled, lfill in H1.
            { destruct lh ; last by false_assumption.
              destruct (const_list l) ; last by false_assumption.
              move/eqP in H1. found_intruse (AI_basic (BI_return)) H1 Hxl1.
              apply in_or_app ; right.
              apply in_or_app ; left.
              apply in_or_app ; right. by left. }
            fold lfill in H1. destruct lh ; first by false_assumption.
            destruct (const_list l) ; last by false_assumption.
            destruct (lfill _ _ _) ; last by false_assumption.
            move/eqP in H1. found_intruse (AI_label n l0 l2) H1 Hxl1. }
        + rewrite Heqes0 in H. simple_filled H k lh bef aft nn ll ll'.
          simpl in H. apply Logic.eq_sym, app_eq_unit in H as [[-> Hes] | [_ Hes]].
          apply app_eq_unit in Hes as [[-> _]|[Hes ->]].
          empty_list_no_reduce.
          unfold lfilled, lfill in H0. simpl in H0. move/eqP in H0.
          rewrite app_nil_r in H0. subst. apply IHHred2 => //=.
          apply app_eq_nil in Hes as [-> _] ; empty_list_no_reduce.
        + inversion Heqes0 ; subst. exfalso ; apply AI_trap_irreducible in Hred2 => //=.
      - by eapply return_det.
      - (* rs_tee_local case. [ only_one ] cannot be applied, so we do the case analysis
         by hand *)
        left ; remember [v ; AI_basic (BI_tee_local i)] as es0.
        replace [ v ; AI_basic (BI_tee_local i)] with ([v] ++ [AI_basic (BI_tee_local i)])
          in Heqes0 => //=.
        induction Hred2 ; try by inversion Heqes0 ;
          try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
        { destruct H0 ; try by inversion Heqes0 ;
            try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
          rewrite Heqes0 in H1 ; filled_trap H1 Hxl1. rewrite Hxl1 in H ; inversion H. }
        rewrite Heqes0 in H0. simple_filled H0 k lh bef aft nn ll ll'.
        destruct bef. { destruct es ; first by empty_list_no_reduce.
                        inversion H0. apply Logic.eq_sym, app_eq_unit in H4
                                          as [[ -> _ ]|[ -> -> ]].
                        subst ; exfalso ; values_no_reduce.
                        apply andb_true_iff ; split => //=.
                        unfold lfilled, lfill in H1 ; simpl in H1.
                        move/eqP in H1. rewrite app_nil_r in H1 ; subst.
                        apply IHHred2 => //=. }
        inversion H0. apply Logic.eq_sym, app_eq_unit in H4 as [[ _ Hes ]|[ _ Hes]].
        apply app_eq_unit in Hes as [[ -> _ ]|[ Hes _]].
        empty_list_no_reduce.
        apply Logic.eq_sym in Hes ; exfalso ; no_reduce Hes Hred2.
        apply app_eq_nil in Hes as [-> _]. empty_list_no_reduce.
        rewrite Hxl1 in H ; inversion H.
      - (* rs_trap case. [ only_one ] cannot be applied because the left-hand-side of Hred2
         is not an explicit list. We perform the case analysis by hand.
         We make extensive use of the [ filled_trap ] tactic, which concludes false
         from a hypothesis [ lfilled k lh [AI_trap] [some explicit list] ] *)
        induction Hred2 ; try by filled_trap H0 Hxl1.
        { destruct H1 ; try by filled_trap H0 Hxl1.
          - filled_trap H0 Hxl1. apply in_app_or in Hxl1 as [Habs | Habs].
            intruse_among_values vs Habs H1. destruct Habs => //=.
          - filled_trap H0 Hxl1. apply in_app_or in Hxl1 as [Habs | Habs].
            intruse_among_values vs Habs H1. destruct Habs => //=.
          - filled_trap H0 Hxl1. rewrite Hxl1 in H1. inversion H1.
          - left ; done. }
        + filled_trap H0 Hxl1. apply in_app_or in Hxl1 as [Habs | Habs].
          assert (const_list ves) as Hconst ;
            first by rewrite H3 ; apply v_to_e_is_const_list.
          intruse_among_values ves Habs Hconst. destruct Habs => //=.
        + filled_trap H0 Hxl1. apply in_app_or in Hxl1 as [Habs | Habs].
        assert (const_list ves) as Hconst ;
          first by rewrite H3 ; apply v_to_e_is_const_list.
        intruse_among_values ves Habs Hconst. destruct Habs => //=.
        + do 2 right. exists k,0,k. (* in this case, we might not have determinism, but the last 
                       disjunct of the conclusion holds *)
          unfold lfilled, lfill in H0. destruct lh as [bef aft|] ; last by false_assumption.
          remember (const_list bef) as b eqn:Hbef ; destruct b ; last by false_assumption.
          move/eqP in H0. rewrite H0 in H1.
          unfold lfilled, lfill in H1 ; destruct k.
          { destruct lh0 ; last by false_assumption.
            remember (const_list l) as b eqn:Hl ; destruct b ; last by false_assumption.
            move/eqP in H1. 
            destruct (first_non_value_reduce _ _ _ _ _ _ Hred2)
              as (vs & e & esf & Hvs & He & Hes).
            rewrite Hes in H1. do 3 rewrite app_assoc in H1.
            rewrite <- (app_assoc (l ++ vs)) in H1. rewrite <- app_assoc in H1.
            rewrite <- (app_comm_cons esf) in H1.
            apply first_values in H1 as (Hbefvs & Htrap & Hesf) => //= ; try by intros [? ?].
            assert (lfilled 0 (LH_base vs esf) [AI_trap] es).
            { unfold lfilled, lfill ; rewrite Hvs. rewrite Hes => //=. by rewrite <- Htrap. }
            destruct (trap_reduce _ _ _ _ _ _ _ H1 Hred2) as (lh' & Hfill & Hσ).
            assert (H2':=H2).
            apply (lfilled_trans Hfill) in H2 as [lh'' Hfill'].
            simpl in Hfill'. subst.
            
            repeat split => //=. rewrite first_instr_const => //=. 
            
            by eapply lfilled_implies_starts.
            destruct e => // ; destruct b => //.
            unfold to_val, iris.to_val in He ; simpl in He.
            destruct He as [ He | He ] => //.
            unfold const_list ; rewrite forallb_app.
            apply andb_true_iff ; split => //=.
          }
          fold lfill in H1. destruct lh0 ; first by false_assumption.
          remember (const_list l) as b eqn:Hl ; destruct b ; last by false_assumption.
          destruct (lfill _ _ _) ; last by false_assumption.
          move/eqP in H1. apply first_values in H1 as (_ & Habs & _) ; (try done) ;
                            (try by (intros [? ?])). }
    (* We carry on using [ only_one ]. Recall that hypothesis IHnnn must be cleared
     in order to use it (in the cases above, the [ clear IHnnn ] instruction was
     after the semicolon after the [ destruct H ] at the very top. *)
    - clear IHnnn ; only_one [AI_basic (BI_call i)] Hred2.
      inversion Heqes ; subst ; rewrite H in H0 ; inversion H0 ; by subst.
    - clear IHnnn ;
        only_one [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_call_indirect i)] Hred2.
      + inversion Heqes ; subst ; rewrite H in H2 ; inversion H2 ; by subst.
      + inversion Heqes ; subst ; rewrite H in H2 ; inversion H2 ; subst ;
          rewrite H0 in H3 ; inversion H3 ; subst ; rewrite H1 in H4 ;
          exfalso ; by apply H4.
      + inversion Heqes ; subst ; rewrite H in H2 ; inversion H2.
    - clear IHnnn ;
        only_one [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_call_indirect i)] Hred2.
      inversion Heqes ; subst ; rewrite H in H2 ; inversion H2 ; subst ;
        rewrite H0 in H3 ; inversion H3 ; subst ; rewrite H4 in H1 ;
        exfalso ; by apply H1.
    - clear IHnnn ;
        only_one [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_call_indirect i)] Hred2.
      inversion Heqes ; subst ; rewrite H in H0 ; inversion H0.
    (* Invoke native *)
    - clear IHnnn.
      subst.
      left.
      by eapply invoke_native_det.
    (* The following 2 cases are the r_invoke host cases. We do not guarantee determinism in
     these cases, but the third disjunct of the conclusion holds *)
    - clear IHnnn.
      left.
      remember (ves ++ [AI_invoke a])%SEQ as es.
      induction Hred2 ;
           (try by rewrite - (app_nil_l [_]) in Heqes ;
            apply app_inj_tail in Heqes as [_ ?]) ;
          (try by rewrite (separate1) in Heqes ;
           apply app_inj_tail in Heqes as [_ ?]) ;
         (try by rewrite (separate2 (AI_basic (BI_const _))) in Heqes ;
          apply app_inj_tail in Heqes as [_ ?]) ;
         (try by rewrite (separate3 (AI_basic (BI_const _))) in Heqes ;
          apply app_inj_tail in Heqes as [_ ?]).
      { destruct H5 ;
           (try by rewrite - (app_nil_l [_]) in Heqes ;
            apply app_inj_tail in Heqes as [_ ?]) ;
          (try by rewrite (separate1) in Heqes ;
           apply app_inj_tail in Heqes as [_ ?]) ;
         (try by rewrite (separate2 (AI_basic (BI_const _))) in Heqes ;
          apply app_inj_tail in Heqes as [_ ?]) ;
         (try by rewrite (separate3 (AI_basic (BI_const _))) in Heqes ;
          apply app_inj_tail in Heqes as [_ ?]).
        subst. filled_trap H6 Hxl1. apply in_app_or in Hxl1 as [|[|]] => //.
        assert (const_list (v_to_e_list vcs)) ; first by apply v_to_e_is_const_list.
        intruse_among_values (v_to_e_list vcs) H0 H1. }
      apply app_inj_tail in Heqes as [-> Ha].
      inversion Ha ; subst.
      rewrite H in H5 => //.
      apply app_inj_tail in Heqes as [-> Ha] ; inversion Ha ; subst.
      rewrite H in H5 ; inversion H5 ; subst.
      apply v_to_e_inj in H7 as -> => //.
      simple_filled H5 k lh bef aft nn ll ll1.
      destruct bef. { destruct aft. { rewrite app_nil_r app_nil_l in H5 ; subst.
                                      unfold lfilled, lfill in H6 ; simpl in H6.
                                      apply b2p in H6; rewrite app_nil_r in H6 ; subst.
                                      apply IHHred2 => //. }
        simpl in H5 ; rewrite H5 in Heqes.
                      get_tail a0 aft ys y Htail.
                      rewrite Htail app_assoc in Heqes.
                      apply app_inj_tail in Heqes as [<- _].
                      assert (const_list (es ++ ys)%list) ;
                        first by rewrite H1 ; apply v_to_e_is_const_list.
                      unfold const_list in H7.
                      rewrite forallb_app in H7.
                      apply andb_true_iff in H7 as [Hes _].
                      exfalso ; values_no_reduce. }
      rewrite H5 in Heqes.
      destruct ves.
      { inversion Heqes. destruct bef, es, aft => //.
        empty_list_no_reduce. }
      inversion Heqes.
      destruct aft.
      { rewrite app_nil_r in H9.
        destruct es ; first by empty_list_no_reduce.
        get_tail a2 es ys y Htail.
        rewrite Htail app_assoc in H9.
        apply app_inj_tail in H9 as [<- ->].
        rewrite Htail in Hred2.
        eapply invoke_not_enough_arguments_no_reduce_host in Hred2 => //.
        by rewrite H H0.
        assert (const_list (a1 :: (bef ++ ys)%list)%SEQ) ;
          first by rewrite H1 ; apply v_to_e_is_const_list.
        unfold const_list in H7 ; simpl in H7.
        rewrite forallb_app in H7.
        apply andb_true_iff in H7 as [_ H7].
        by apply andb_true_iff in H7 as [??].
        assert (length (a1 :: (bef ++ ys)) = length t1s) ;
          first by rewrite H1 v_to_e_length ; subst.
        simpl in H7.
        rewrite app_length in H7.
        lia. } 
      get_tail a2 aft ys y Htail.
      rewrite Htail app_assoc app_assoc in H9.
      apply app_inj_tail in H9 as [<- _].
      assert (const_list (a1 :: (bef ++ es) ++ ys)) ;
        first by rewrite H1 ;apply v_to_e_is_const_list.
      simpl in H7 ; unfold const_list in H7.
      repeat rewrite forallb_app in H7.
      apply andb_true_iff in H7 as [_ H7].
      apply andb_true_iff in H7 as [H7 _].
      apply andb_true_iff in H7 as [_ H7].
      exfalso ; values_no_reduce.
      rewrite Heqes in Hxl1.
      apply in_app_or in Hxl1 as [|[|]] => //.
      assert (const_list ves) ; first by rewrite H1 ; apply v_to_e_is_const_list.
      intruse_among_values ves H7 H8.
                      
                                      
       
    - clear IHnnn ; only_one [AI_basic (BI_get_local j)] Hred2.
      inversion Heqes ; subst ; rewrite H in H0 ; by inversion H0.
    - clear IHnnn ; only_one [AI_basic (BI_const v) ; AI_basic (BI_set_local i)] Hred2.
      inversion Heqes ; subst ; clear Heqes H3 Hlen.
      assert (forall l i (v:value) vd vd', ssrnat.leq (S i) (length l) ->
                                      set_nth vd l i v = set_nth vd' l i v).
      { intro. induction l ; intros i v vd1 vd2 Hlen. inversion Hlen.
        destruct i => //=. simpl in Hlen ; apply ssrnat.ltnSE in Hlen.
        by rewrite (IHl i v vd1 vd2 Hlen). }
      rewrite (H3 _ _ v0 vd0 vd H0) in H4. rewrite <- H4 in H1.
      destruct f' ; destruct f'0 ; destruct f.
      simpl in H ; simpl in H1 ; simpl in H2 ; by subst.
    - clear IHnnn ; only_one [AI_basic (BI_get_global i)] Hred2.
      inversion Heqes ; subst ; rewrite H in H0 ; by inversion H0.
    - clear IHnnn ; only_one [AI_basic (BI_const v) ; AI_basic (BI_set_global i)] Hred2.
      inversion Heqes ; subst ; rewrite H in H0 ; by inversion H0.
    - clear IHnnn ; only_one [AI_basic (BI_const (VAL_int32 k)) ;
                              AI_basic (BI_load t None a off)] Hred2 ;
        inversion Heqes ; subst ; rewrite H in H2 ; inversion H2 ; subst ;
        rewrite H0 in H3 ; inversion H3 ; subst ; rewrite H1 in H4 ; inversion H4 ;
        try by subst.
    - clear IHnnn ; only_one [AI_basic (BI_const (VAL_int32 k)) ;
                              AI_basic (BI_load t None a off)] Hred2 ;
        inversion Heqes ; subst ; rewrite H in H2 ; inversion H2 ; subst ;
        rewrite H0 in H3 ; inversion H3 ; subst ; rewrite H1 in H4 ; inversion H4 ;
        try by subst.
    - clear IHnnn ; only_one [AI_basic (BI_const (VAL_int32 k)) ;
                              AI_basic (BI_load t (Some (tp, sx)) a off)] Hred2 ;
        inversion Heqes ; subst ; rewrite H in H2 ; inversion H2 ; subst ;
        rewrite H0 in H3 ; inversion H3 ; subst ; rewrite H1 in H4 ; inversion H4 ;
        try by subst. 
    - clear IHnnn ; only_one [AI_basic (BI_const (VAL_int32 k)) ;
                              AI_basic (BI_load t (Some (tp, sx)) a off)] Hred2 ;
        inversion Heqes ; subst ; rewrite H in H2 ; inversion H2 ; subst ;
        rewrite H0 in H3 ; inversion H3 ; subst ; rewrite H1 in H4 ; inversion H4 ;
        try by subst.   
    - clear IHnnn ; only_one [AI_basic (BI_const (VAL_int32 k)) ; AI_basic (BI_const v) ;
                              AI_basic (BI_store t None a off)] Hred2 ;
        inversion Heqes ; subst ; rewrite H0 in H4 ; inversion H4 ; subst ;
        rewrite H1 in H5 ; inversion H5 ; subst ; rewrite H2 in H6 ; by inversion H6.
    - clear IHnnn ; only_one [AI_basic (BI_const (VAL_int32 k)) ; AI_basic (BI_const v) ;
                              AI_basic (BI_store t None a off)] Hred2 ;
        inversion Heqes ; subst ; rewrite H0 in H4 ; inversion H4 ; subst ;
        rewrite H1 in H5 ; inversion H5 ; subst ; rewrite H2 in H6 ; by inversion H6.
    - clear IHnnn ; only_one [AI_basic (BI_const (VAL_int32 k)) ; AI_basic (BI_const v) ;
                              AI_basic (BI_store t (Some tp) a off)] Hred2 ;
        inversion Heqes ; subst ; rewrite H0 in H4 ; inversion H4 ; subst ;
        rewrite H1 in H5 ; inversion H5 ; subst ; rewrite H2 in H6 ; by inversion H6.
    - clear IHnnn ; only_one [AI_basic (BI_const (VAL_int32 k)) ; AI_basic (BI_const v) ;
                              AI_basic (BI_store t (Some tp) a off)] Hred2 ;
        inversion Heqes ; subst ; rewrite H0 in H4 ; inversion H4 ; subst ;
        rewrite H1 in H5 ; inversion H5 ; subst ; rewrite H2 in H6 ; by inversion H6.
    - clear IHnnn ; only_one [AI_basic BI_current_memory] Hred2.
      rewrite H in H2 ; inversion H2 ; subst ; rewrite H0 in H3 ; by inversion H3.
    (* the following two cases are the r_grow_memory cases. We do not guarantee
       determinism in these cases, but the second disjunct of the conclusion holds *)
    - right ; left.
      exists 0.
      replace [AI_basic (BI_const (VAL_int32 c)); AI_basic BI_grow_memory] with
        ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic BI_grow_memory] ++ []).
      constructor => //=. by rewrite app_nil_r.
    - right ; left.
      exists 0.
      replace [AI_basic (BI_const (VAL_int32 c)); AI_basic BI_grow_memory] with
        ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic BI_grow_memory] ++ []).
      constructor => //=. by rewrite app_nil_r.
    - by eapply label_det.
    - by eapply local_det.
  Qed.
  
End determ.

