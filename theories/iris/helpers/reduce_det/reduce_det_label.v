From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export iris_reduce_det_prelude iris_split_reduce.

Local Definition reducible := @iris.program_logic.language.reducible wasm_lang.

Lemma label_det s f es s' f' es' les les' k lh ws2 f2 es2 nnn:
  (∀ (f f2 f1 : frame) (es2 es1 es : seq.seq administrative_instruction),
    reduce s f es s' f1 es1
    → reduce s f es ws2 f2 es2 → length_rec es < nnn → reduce_det_goal s' f1 es1 ws2 f2 es2 es) ->
  reduce s f es s' f' es' ->
  lfilled k lh es les ->
  lfilled k lh es' les' ->
  reduce s f les ws2 f2 es2 ->
  length_rec les < S nnn ->
  ((∀ (f f2 f1 : frame) (es2 es1 es : seq.seq administrative_instruction),
      reduce s f es s' f1 es1
      → reduce s f es ws2 f2 es2 → length_rec es < nnn → reduce_det_goal s' f1 es1 ws2 f2 es2 es)
   → reduce s f es ws2 f2 es2 → length_rec es < S nnn → reduce_det_goal s' f' es' ws2 f2 es2 es) ->
  reduce_det_goal s' f' les' ws2 f2 es2 les.
Proof.
  move => IHnnn Hred1 H H0 Hred2 Hlen IHHred1.
  (* r_label case. The proof is tedious and relies on cleverly calling the induction
       hypothesis IHnnn. For this, we need to have some term es0 smaller than the original
       es (in terms of length_rec, i.e. number of instructions, including recursively under
       AI_labels and AI_locals). To find this, we first look at whether the lfilled
       statement is at level 0 or at a higher level : *)
  destruct k ; unfold lfilled, lfill in H.
  { destruct lh as [bef aft |] ; last by false_assumption.
    remember (const_list bef) as b eqn:Hbef ; destruct b ; last by false_assumption.
    move/eqP in H.
    (* in this case, Hred1 was [ les -> les1 ] with [ les = bef ++ es ++ aft ],
         [ les1 = bef ++ es1 ++ aft ] and [ es -> es1 ]. 
         Hred2 is hypothesis [ les -> es2 ] with nothing known of [ es2 ]. *)
    unfold lfilled, lfill in H0. rewrite <- Hbef in H0. move/eqP in H0.
    destruct bef.
    { destruct aft. { (*  If bef and aft are both empty, induction hypothesis 
                            IHHred1 can be used. *)
        rewrite app_nil_l app_nil_r in H.
        rewrite app_nil_l app_nil_r in H0.
        subst. apply IHHred1 => //=. }
      (* Else, if bef is empty and aft is nonempty, then let us call y the last 
           instruction in les. We have [ les = es ++ ys ++ [y] ]. r_label gives us
           that [ es ++ ys -> es1 ++ ys ], and Hred2 is still [ les -> es2 ].
           Using lemma reduce_append (the append equivalent of reduce_ves), 
           we know es2 ends in y and [ es ++ ys -> take (all but 1) es2 ].
           We can thus apply IHnnn to [ es ++ ys ] (shorter than les since we 
           removed y) *)
      get_tail a aft ys y Htail.
      rewrite Htail in H. rewrite Htail in H0. simpl in H. simpl in H0.
      rewrite app_assoc in H. rewrite app_assoc in H0.
      assert (reducible (es ++ ys) (s, f_locs f, f_inst f)) as Hred.
      { exists [], (es' ++ ys), (s', f_locs f', f_inst f'), [].
        repeat split => //=.
        apply (r_label (k:=0) (lh:=LH_base [] ys) (es:=es) (es':=es')) ;
          unfold lfilled, lfill => //=.
        destruct f ; destruct f' => //=. }
      assert (prim_step ((es ++ ys) ++ [y]) (s, f_locs f, f_inst f)
                        [] es2 (ws2, f_locs f2, f_inst f2) []) as Hstep.
      { repeat split => //=. rewrite <- H. by destruct f ; destruct f2. }
      destruct (reduce_append _ _ _ _ _ _ _ Hred Hstep) as [[ Hes2y Htakestep ]|
                                                            (lh & lh' & Htrap &
                                                             Htrap' & Hσ)].
      { assert (reduce s f (es ++ ys) s' f' (es' ++ ys)).
        { apply (r_label (k:=0) (lh:=LH_base [] ys) (es:=es) (es':=es')) ;
            (try done) ; by unfold lfilled, lfill => //=. }
        destruct Htakestep as (H2 & _ & _).
        destruct f ; destruct f2.
        assert (length_rec (es ++ ys) < nnn).
        { rewrite H in Hlen. rewrite app_length_rec in Hlen.
          assert (length_rec [y] > 0) ; first by apply cons_length_rec.
          replace (es ++ ys)%list with (es ++ ys)%SEQ in Hlen => //=.
          lia. }
        destruct (IHnnn _ _ _ _ _ _ H1 H2 H3) as [Hσ | [[i Hstart] |
                                                        (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3 & Hσ)
                                                        (*] *)]].
        - left. rewrite H0. inversion Hσ ; subst.
          replace (es' ++ ys)%SEQ with (es' ++ ys)%list in H7 => //=.
          rewrite H7. by rewrite <- Hes2y.
        - right ; left. exists (i + 0). assert (lfilled 0 (LH_base [] [y]) (es ++ ys) les).
          unfold lfilled, lfill => //=. by subst.
            by eapply starts_with_lfilled => //=.
        - repeat right. exists (i1 + 0),(i2 + 0),(i3 + 0). repeat split => //=.
          assert (lfilled 0 (LH_base [] [y]) (es ++ ys) les).
          unfold lfilled, lfill => //= ; by subst.
          apply (starts_with_lfilled _ _ _ _ _ _ Hstart1 H4) => //=.
          assert (lfilled 0 (LH_base [] [y]) (es' ++ ys) les').
          unfold lfilled, lfill => //= ; by subst.
          apply (starts_with_lfilled _ _ _ _ _ _ Hstart2 H4) => //=.
          assert (lfilled 0 (LH_base [] [y])
                          (take (length es2 - 1) es2) es2).
          unfold lfilled, lfill => //=. by rewrite <- Hes2y.
          apply (starts_with_lfilled _ _ _ _ _ _ Hstart3 H4) => //=. }
      repeat right. assert (lfilled 0 (LH_base [] [y]) (es ++ ys) les) as Hfill.
      { unfold lfilled, lfill => //=. by subst. }
      destruct (lfilled_trans Htrap' Hfill) as [lh'' ?]. simpl in H1.
      assert (reduce s f (es ++ ys) s' f' (es' ++ ys)) as Hles.
      { apply (r_label (k:=0) (lh:=LH_base [] ys) (es:=es) (es':=es')) => //=.
        unfold lfilled, lfill => //=.
        unfold lfilled, lfill => //=. }
      destruct (trap_reduce _ _ _ _ _ _ _ Htrap' Hles) as (lh''' & ? & Hσ').
      assert (lfilled 0 (LH_base [] [y]) (es' ++ ys) les') as Hfill'.
      { unfold lfilled, lfill => //=. rewrite H0 => //=. }
      destruct (lfilled_trans H2 Hfill') as [lh0 ?]. simpl in H3.
      exists 0,0,0.
      repeat split => //= ; try by eapply lfilled_implies_starts.
      inversion Hσ ; subst.
      destruct f ; destruct f2 ; simpl in H6 ; simpl in H7 ; by subst. }
    (* if bef is nonempty, then we proceed like before, but on the left side.
         Calling v the first value in bef, we know that [ les = v :: bef' ++ es ++ aft ]
         r_label gives us [ bef' ++ es ++ aft -> bef' ++ es1 ++ aft ] and we still
         have Hred2 telling [ les -> es2 ]. Using reduce_ves, we know that es2 starts
         with v and that [ bef' ++ es ++ aft -> drop 1 es2 ]. We can thus apply
         induction hypothesis on [ bef' ++ es ++ aft ], which is indeed shorter than
         les since we removed v *)
    unfold const_list in Hbef.
    simpl in Hbef. apply Logic.eq_sym, andb_true_iff in Hbef as [Ha Hbef].
    assert (reduce s f (bef ++ es ++ aft) s' f' (bef ++ es' ++ aft)) as Hles.
    { apply (r_label (k:=0) (lh:=LH_base bef aft) (es:=es) (es':=es')) => //=.
      unfold lfilled, lfill, const_list ; by rewrite Hbef. 
      unfold lfilled, lfill, const_list ; by rewrite Hbef. }
    assert (reducible (bef ++ es ++ aft) (s, f.(f_locs), f.(f_inst))) as Hred.
    { exists [], (bef ++ es' ++ aft), (s', f_locs f', f_inst f'), [].
      repeat split => //=. destruct f ; destruct f' => //=. } 
    destruct a ; try by inversion Ha.
    destruct b ; try by inversion Ha.
    assert (prim_step ([AI_basic (BI_const v)] ++ bef ++ es ++ aft)
                      (s, f_locs f, f_inst f) [] es2
                      (ws2, f_locs f2, f_inst f2) []) as Hstep.
    { repeat split => //=. rewrite <- app_comm_cons in H. rewrite <- H.
        by destruct f ; destruct f2. } 
    destruct (reduce_ves _ _ _ _ _ _ _ Hred Hstep) as [[ Hves2 Hdropstep] |
                                                       ( lh & lh' & Htrap & Htrap' &
                                                         Hσ )].
    { assert (reduce s f (bef ++ es ++ aft) s' f' (bef ++ es' ++ aft)).
      { apply (r_label (k:=0) (lh:=LH_base bef aft) (es:=es) (es':=es'))
        ; (try done) ; by unfold lfilled, lfill, const_list ; rewrite Hbef. }
      destruct Hdropstep as (H2 & _ & _).
      replace (bef ++ es ++ aft)%list with (bef ++ es ++ aft)%SEQ in H2 => //=.
      destruct f ; simpl in H2. destruct f2 ; simpl in H2.
      assert (length_rec (bef ++ es ++ aft) < nnn).
      { rewrite H in Hlen. rewrite <- app_comm_cons in Hlen.
        replace (AI_basic (BI_const v) :: (bef ++ es ++ aft)) with
            ([AI_basic (BI_const v)] ++ (bef ++ es ++ aft)) in Hlen => //=.
        rewrite app_length_rec in Hlen. simpl in Hlen. 
          by apply lt_S_n. }
      destruct (IHnnn _ _ _ _ _ _ H1 H2 H3) as [Hσ | [[i Hstart] |
                                                      (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3 & Hσ)
                                               ]].
      - left. rewrite H0. rewrite <- app_comm_cons.
        inversion Hσ ; subst.
        replace (bef ++ es' ++ aft)%SEQ with (bef ++ es' ++ aft)%list in H7 => //=.
        rewrite H7. by rewrite Hves2.
      - right ; left. exists (i + 0). assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                                                 (bef ++ es ++ aft) les).
        unfold lfilled, lfill => //=. by subst ; rewrite app_nil_r.
        eapply starts_with_lfilled => //=.
      - repeat right. exists (i1 + 0),(i2 + 0),(i3 + 0). repeat split => //=.
        assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                        (bef ++ es ++ aft) les).
        unfold lfilled, lfill => //=. by subst ; rewrite app_nil_r.
          by apply (starts_with_lfilled _ _ _ _ _ _ Hstart1 H4).
          assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                          (bef ++ es' ++ aft) les').
          unfold lfilled, lfill => //=. by subst ; rewrite app_nil_r.
            by apply (starts_with_lfilled _ _ _ _ _ _ Hstart2 H4).
            destruct es2 ; simpl in Hstart3 ; first by inversion Hves2.
            unfold drop in Hstart3. inversion Hves2 ; subst.
            assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                            es2 (AI_basic (BI_const v) :: es2)).
            unfold lfilled, lfill => //= ; by rewrite app_nil_r.
              by apply (starts_with_lfilled _ _ _ _ _ _ Hstart3 H). } 
    repeat right. exists 0,0,0.
    assert (lfilled 0 (LH_base [AI_basic (BI_const v)] []) (bef ++ es ++ aft) les)
      as Hfill.
    { unfold lfilled, lfill => //=. rewrite H.
        by rewrite app_comm_cons app_nil_r. } 
    destruct (lfilled_trans Htrap' Hfill) as [lh'' ?]. simpl in H1.
    destruct (trap_reduce _ _ _ _ _ _ _ Htrap' Hles) as (lh''' & ? & Hσ').
    assert (lfilled 0 (LH_base [AI_basic (BI_const v)] []) (bef ++ es' ++ aft) les')
      as Hfill'.
    { unfold lfilled, lfill => //=. rewrite H0.
        by rewrite app_comm_cons app_nil_r. }
    destruct (lfilled_trans H2 Hfill') as [lh0 ?]. simpl in H3.
    repeat split => //= ; try by eapply lfilled_implies_starts.
    inversion Hσ ; subst.
    destruct f ; destruct f2 ; simpl in H7 ; simpl in H6 ; by subst. }
  (* in this case, Hred1 was [ les -> les1 ] with 
       [ les = bef ++ AI_label n es0 l :: aft ], [ les1 = bef ++ AI_label n es0 l1 :: aft ],
       [ lfilled k lh es l ], [ lfilled k lh es1 l1 ] and [ es -> es1 ]. We still have
       Hred2 being [ les -> es2 ] with nothing known of es2. *)
  fold lfill in H. destruct lh as [|bef n es0 lh aft] ; first by false_assumption.
  remember (const_list bef) as b eqn:Hbef ; destruct b ; last by false_assumption.
  remember (lfill _ _ _) as fill ; destruct fill ; last by false_assumption.
  move/eqP in H.
  { unfold lfilled, lfill in H0 ; fold lfill in H0. rewrite <- Hbef in H0.
    remember (lfill _ _ es') as fill ; destruct fill ; last by false_assumption.
    move/eqP in H0. destruct bef.
    { destruct aft. {
        (* if bef and aft are empty, then Hred2 is [ [AI_label n es0 l] -> es2 ].
             We painstakingly show, by case analysis, that this means es2 is of the
             form [AI_label n es0 l'] with [ l -> l' ].
             Knowing that, and since r_label gives [ l -> l1 ], we can apply the 
             induction hypothesis IHnnn on l, which is shorter than les since there is
             one less AI_label node.
         *)
        induction Hred2 ; (try by inversion H) ;
          try by apply app_inj_tail in H as [_ Habs] ; inversion Habs.
        { destruct H1 ; (try by inversion H) ;
            try by apply app_inj_tail in H as [_ Habs] ; inversion Habs.
          - inversion H ; subst. destruct k ; unfold lfill in Heqfill.
            { destruct lh ; last by inversion Heqfill.
              destruct (const_list l1) ; inversion Heqfill.
              exfalso ; values_no_reduce.
              rewrite H2 in H1 ; unfold const_list in H1 ; do 2 rewrite forallb_app in H1.
              apply andb_true_iff in H1 as [_ H1].
                by apply andb_true_iff in H1 as [H1 _]. }
            fold lfill in Heqfill. destruct lh ; first by inversion Heqfill.
            destruct (const_list l1) ; last by inversion Heqfill.
            destruct (lfill _ _ _) ; inversion Heqfill.
            rewrite H2 in H1 ; unfold const_list in H1 ; rewrite forallb_app in H1.
            simpl in H1. apply andb_true_iff in H1 as [_ Hf] ; false_assumption.
          - inversion H ; subst. destruct k ; unfold lfill in Heqfill.
            { destruct lh ; last by inversion Heqfill.
              destruct (const_list l) ; inversion Heqfill.
              apply Logic.eq_sym, app_eq_unit in H1 as [[ _ Hes] | [ _ Hes]].
              apply app_eq_unit in Hes as [[ -> _ ] | [ -> _]].
              empty_list_no_reduce.
              exfalso ; by eapply test_no_reduce_trap.
              apply app_eq_nil in Hes as [-> _] ; empty_list_no_reduce. } 
            fold lfill in Heqfill. destruct lh ; first by inversion Heqfill.
            destruct (const_list l) ; last by inversion Heqfill.
            destruct (lfill _ _ _) ; inversion Heqfill.
            found_intruse (AI_label n0 l1 l3) H1 Hxl1.
          - inversion H ; subst.
            assert (lfilled k lh es l) as Hfill ;
              first by unfold lfilled ; rewrite <- Heqfill. exfalso.
            eapply lfilled_br_and_reduce ; try exact Hfill ; try exact H3 ; try done.
          - rewrite H in H2. filled_trap H2 Hxl1. }
        rewrite H in H1.
        destruct k0 ; unfold lfilled, lfill in H1.
        { destruct lh0 ; last by false_assumption.
          destruct (const_list l1) ; last by false_assumption.
          move/eqP in H1. simpl in H1.
          apply Logic.eq_sym, app_eq_unit in H1 as [[ ->  Hes1 ] | [ _ Hes1]].
          apply app_eq_unit in Hes1 as [[ -> _ ] | [ -> -> ]].
          empty_list_no_reduce.
          unfold lfilled, lfill in H2 ; simpl in H2 ; move/eqP in H2.
          rewrite app_nil_r in H2. subst. apply IHHred2 => //=.
          apply app_eq_nil in Hes1 as [-> _ ] ; empty_list_no_reduce. }
        fold lfill in H1. clear IHHred1 IHHred2.
        destruct lh0 ; first by false_assumption.
        destruct (const_list l1) ; last by false_assumption.
        remember (lfill k0 _ _) as fill ; destruct fill ; last by false_assumption.
        move/eqP in H1.
        destruct l1 ; last by inversion H1 ; found_intruse (AI_label n0 l2 l4) H5 Hxl1.
        inversion H1 ; subst.
        assert (reduce s f l4 s' f' l0).
        { eapply r_label. exact Hred1. unfold lfilled. by rewrite <- Heqfill.
          unfold lfilled ; by rewrite <- Heqfill0. }
        unfold lfilled, lfill in H2 ; fold lfill in H2. simpl in H2.
        remember (lfill k0 lh0 es'0) as fill ; destruct fill ; last by false_assumption.
        assert (reduce s f l4 s'0 f'0 l).
        { eapply r_label. exact Hred2. unfold lfilled ; by rewrite <- Heqfill1.
          unfold lfilled. by rewrite <- Heqfill2. }
        assert (length_rec l4 < nnn).
        { simpl in Hlen. unfold length_rec in Hlen. simpl in Hlen. unfold length_rec.
          lia. }
        assert (lfilled 1 (LH_rec [] n0 l2 (LH_base [] []) []) l4
                        [AI_label n0 l2 l4]).
        unfold lfilled, lfill => //=. by rewrite app_nil_r.
        destruct (IHnnn _ _ _ _ _ _ H H0 H3)
          as [ Hσ | [ [i Hstart] | (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3 & Hσ) (* ] *)]].
        - left. move/eqP in H2. inversion Hσ ; by subst.
        - right ; left. exists (i + 1).
          eapply starts_with_lfilled => //=.
        - repeat right. exists (S i1),(S i2),(S i3). repeat split => //=.
          unfold first_instr => //=.
          unfold first_instr in Hstart1 ; rewrite Hstart1 => //=.
          unfold first_instr => //=.
          unfold first_instr in Hstart2 ; rewrite Hstart2 => //=.
          move/eqP in H2 ; rewrite H2.
          unfold first_instr => //=.
          unfold first_instr in Hstart3 ; rewrite Hstart3 => //=. } 
      (* in the cases where aft is nonempty or bef is nonempty, we proceed exactly
           like in the corresponding cases when k was 0 *)
      get_tail a aft ys y Htail.
      rewrite Htail in H. rewrite Htail in H0. simpl in H. simpl in H0.
      rewrite app_comm_cons in H. rewrite app_comm_cons in H0.
      assert (reducible (AI_label n es0 l :: ys) (s, f_locs f, f_inst f)) as Hred.
      { exists [], (AI_label n es0 l0 :: ys), (s', f_locs f', f_inst f'), [].
        repeat split => //=.
        apply (r_label (k:=S k) (lh:=LH_rec [] n es0 lh ys) (es:=es) (es':=es')) ;
          unfold lfilled, lfill ; fold lfill => //=.
        destruct f ; destruct f' => //=.
        rewrite <- Heqfill => //=.
        rewrite <- Heqfill0 => //=.
      }
      assert (prim_step ((AI_label n es0 l :: ys) ++ [y]) (s, f_locs f, f_inst f)
                        [] es2 (ws2, f_locs f2, f_inst f2) []) as Hstep.
      { repeat split => //=. simpl in H ; rewrite <- H. by destruct f ; destruct f2. }
      destruct (reduce_append _ _ _ _ _ _ _ Hred Hstep) as [[ Hes2y Htakestep ]|
                                                            (lh0 & lh' & Htrap &
                                                             Htrap' & Hσ)].
      { assert (reduce s f (AI_label n es0 l :: ys) s' f'
                       (AI_label n es0 l0 :: ys)).
        { apply (r_label (k:=S k) (lh:=LH_rec [] n es0 lh ys) (es:=es) (es':=es')) ;
            (try done) ; unfold lfilled, lfill ; fold lfill => //=.
          rewrite <- Heqfill => //=. rewrite <- Heqfill0 => //=. }
        destruct Htakestep as (H2 & _ & _).
        destruct f ; destruct f2.
        assert (length_rec (AI_label n es0 l :: ys) < nnn).
        { rewrite H in Hlen. rewrite app_length_rec in Hlen.
          assert (length_rec [y] > 0) ; first by apply cons_length_rec.
          replace (es ++ ys)%list with (es ++ ys)%SEQ in Hlen => //=.
          lia. }
        destruct (IHnnn _ _ _ _ _ _ H1 H2 H3) as [Hσ | [ [i Hstart] |
                                                         (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3 & Hσ)
                                                 ]].
        - left. rewrite H0. inversion Hσ ; subst.
          replace (AI_label n es0 l0 :: ys)%SEQ with
              (AI_label n es0 l0 :: ys)%list in H7 => //=.
          rewrite app_comm_cons H7. by rewrite <- Hes2y.
        - right ; left. exists (i + 0). assert (lfilled 0 (LH_base [] [y]) (AI_label n es0 l ::  ys) les).
          unfold lfilled, lfill => //=. by subst.
          eapply starts_with_lfilled => //=.
        - repeat right. exists (i1 + 0),(i2 + 0),(i3 + 0). repeat split => //=.
          assert (lfilled 0 (LH_base [] [y]) (AI_label n es0 l :: ys) les).
          unfold lfilled, lfill => //= ; by subst.
            by apply (starts_with_lfilled _ _ _ _ _ _ Hstart1 H4).
            assert (lfilled 0 (LH_base [] [y]) (AI_label n es0 l0 :: ys) les').
            unfold lfilled, lfill => //= ; by subst.
              by apply (starts_with_lfilled _ _ _ _ _ _ Hstart2 H4).
              assert (lfilled 0 (LH_base [] [y])
                              (take (length es2 - 1) es2) es2).
              unfold lfilled, lfill => //=. by rewrite <- Hes2y.
                by apply (starts_with_lfilled _ _ _ _ _ _ Hstart3 H4). }
      repeat right.
      assert (lfilled 0 (LH_base [] [y]) (AI_label n es0 l :: ys) les) as Hfill.
      { unfold lfilled, lfill => //=. by subst. }
      destruct (lfilled_trans Htrap' Hfill) as [lh'' ?]. simpl in H1.
      assert (reduce s f (AI_label n es0 l :: ys) s' f'
                     (AI_label n es0 l0 :: ys)) as Hles.
      { apply (r_label (k:=S k) (lh:=LH_rec [] n es0 lh ys) (es:=es) (es':=es')) => //=.
        unfold lfilled, lfill ; fold lfill => //=. rewrite <- Heqfill => //=.
        unfold lfilled, lfill ; fold lfill => //=. rewrite <- Heqfill0 => //=. }
      destruct (trap_reduce _ _ _ _ _ _ _ Htrap' Hles) as (lh''' & ? & Hσ').
      assert (lfilled 0 (LH_base [] [y]) (AI_label n es0 l0 :: ys) les') as Hfill'.
      { unfold lfilled, lfill => //=. rewrite H0 => //=. }
      destruct (lfilled_trans H2 Hfill') as [lh0' ?]. simpl in H3.

      exists (0 + 0),(0 + 0),(0 + 0).        
      repeat split => //= ; try by eapply lfilled_implies_starts.
      inversion Hσ ; subst.
      destruct f ; destruct f2 ; simpl in H7 ; simpl in H6 ; by subst. } 
    unfold const_list in Hbef.
    simpl in Hbef. apply Logic.eq_sym, andb_true_iff in Hbef as [Ha Hbef].
    assert (reduce s f (bef ++ AI_label n es0 l :: aft) s' f'
                   (bef ++ AI_label n es0 l0 :: aft)) as Hles.
    { apply (r_label (k:=S k) (lh:=LH_rec bef n es0 lh aft) (es:=es) (es':=es')) => //=.
      unfold lfilled, lfill ; fold lfill. unfold const_list ; rewrite Hbef.
      rewrite <- Heqfill => //=.
      unfold lfilled, lfill ; fold lfill ; unfold  const_list ; rewrite Hbef.
      rewrite <- Heqfill0 => //=. }
    assert (reducible (bef ++ AI_label n es0 l :: aft)
                      (s, f.(f_locs), f.(f_inst))) as Hred.
    { exists [], (bef ++ AI_label n es0 l0 :: aft), (s', f_locs f', f_inst f'), [].
      repeat split => //=. destruct f ; destruct f' => //=. } 
    destruct a ; try by inversion Ha.
    destruct b ; try by inversion Ha.
    assert (prim_step ([AI_basic (BI_const v)] ++ bef ++ AI_label n es0 l :: aft)
                      (s, f_locs f, f_inst f) [] es2
                      (ws2, f_locs f2, f_inst f2) []) as Hstep.
    { repeat split => //=. rewrite <- app_comm_cons in H. rewrite <- H.
        by destruct f ; destruct f2. } 
    destruct (reduce_ves _ _ _ _ _ _ _ Hred Hstep) as [[ Hves2 Hdropstep] |
                                                       ( lh0 & lh' & Htrap & Htrap' &
                                                         Hσ )].
    { destruct Hdropstep as (H2 & _ & _).
      replace (bef ++ AI_label n es0 l :: aft)%list with
          (bef ++ AI_label n es0 l :: aft)%SEQ in H2 => //=.
      destruct f ; simpl in H2. destruct f2 ; simpl in H2.
      assert (length_rec (bef ++ AI_label n es0 l :: aft) < nnn).
      { rewrite H in Hlen. rewrite <- app_comm_cons in Hlen.
        replace (AI_basic (BI_const v) :: (bef ++ AI_label n es0 l :: aft)) with
            ([AI_basic (BI_const v)] ++ (bef ++ AI_label n es0 l :: aft)) in Hlen => //=.
        rewrite app_length_rec in Hlen. simpl in Hlen. 
          by apply lt_S_n. }          
      destruct (IHnnn _ _ _ _ _ _ Hles H2 H1) as [Hσ | [ [i Hstart] |
                                                         (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3 & Hσ)
                                                 ]].
      - left. rewrite H0. rewrite <- app_comm_cons.
        inversion Hσ ; subst.
        replace (bef ++ AI_label n es0 l0 :: aft)%SEQ with
            (bef ++ AI_label n es0 l0 :: aft)%list in H6 => //=.
        rewrite H6. by rewrite Hves2.
      - right ; left. exists (i + 0). assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                                                 (bef ++ AI_label n es0 l :: aft) les).
        unfold lfilled, lfill => //=. by subst ; rewrite app_nil_r.
        eapply starts_with_lfilled => //=.
      - repeat right. exists (i1+0),(i2 + 0),(i3+0). repeat split => //=.
        assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                        (bef ++ AI_label n es0 l :: aft) les).
        unfold lfilled, lfill => //=. by subst ; rewrite app_nil_r.
          by apply (starts_with_lfilled _ _ _ _ _ _ Hstart1 H3).
          assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                          (bef ++ AI_label n es0 l0 :: aft) les').
          unfold lfilled, lfill => //=. by subst ; rewrite app_nil_r.
            by apply (starts_with_lfilled _ _ _ _ _ _ Hstart2 H3).
            destruct es2 ; simpl in Hstart3 ; first by inversion Hves2.
            unfold drop in Hstart3. inversion Hves2 ; subst.
            assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                            es2 (AI_basic (BI_const v) :: es2)).
            unfold lfilled, lfill => //= ; by rewrite app_nil_r.
              by apply (starts_with_lfilled _ _ _ _ _ _ Hstart3 H). } 
    repeat right. exists (0+0),(0+0),(0+0).
    assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                    (bef ++ AI_label n es0 l :: aft) les) as Hfill.
    { unfold lfilled, lfill => //=. rewrite H.
        by rewrite app_comm_cons app_nil_r. }
    destruct (lfilled_trans Htrap' Hfill) as [lh'' ?]. simpl in H1.
    destruct (trap_reduce _ _ _ _ _ _ _ Htrap' Hles) as (lh''' & ? & Hσ').
    assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                    (bef ++ AI_label n es0 l0 :: aft) les') as Hfill'.
    { unfold lfilled, lfill => //=. rewrite H0.
        by rewrite app_comm_cons app_nil_r. }
    destruct (lfilled_trans H2 Hfill') as [lh0' ?]. simpl in H3.
    repeat split => //= ; try by eapply lfilled_implies_starts.
    inversion Hσ ; subst.
    destruct f ; destruct f2 ; simpl in H7 ; simpl in H6 ; by subst. }
Qed.
