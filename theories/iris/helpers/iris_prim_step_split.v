From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export stdpp_aux lfilled_reduce iris_split_reduce.

Ltac solve_prim_step_split_reduce_r H objs Heqf0 :=
  left ; subst ;
  apply Logic.eq_sym, app_eq_nil in H as [? ?] ;
  exists objs ; subst ; rewrite app_nil_r ;
  repeat split => //= ; rewrite Heqf0.

Section prim_step_split_properties.
  
  Let reducible := @iris.program_logic.language.reducible wasm_lang.

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.
  
  Lemma lfilled_prim_step_split_reduce_r i lh es1 es2 σ LI e2 σ2 obs2 efs2 :
    lfilled i lh (es1 ++ es2)%list LI ->
    reducible es1 σ ->
    prim_step LI σ obs2 e2 σ2 efs2 ->
    (∃ e', prim_step es1 σ obs2 e' σ2 efs2 ∧ lfilled i lh (e' ++ es2) e2)
    \/ (exists lh, lfilled 0 lh [AI_trap] es1) /\ σ = σ2.
  Proof.
    intros Hfill Hred Hstep.
    edestruct lfilled_reduce as [(es' & Hstep' & Hfill') | (lh0 & Htrap & Hσ) ] => //=.
    - destruct σ as [[s locs ] inst ].
      destruct Hred as (obs & e1 & [[ s1 locs1 ] inst1] & efs & (Hes1 & -> & ->)).
      exists [], (e1 ++ es2), (s1, locs1, inst1), [].
      repeat split => //=.
      eapply (r_label (k:=0) (lh := LH_base [] es2)) ; try done ;
        unfold lfilled, lfill => //=.
    - eapply prim_step_split_reduce_r in Hstep' as
          [ (es'' & Hes' & Hes1) | (n & m & lh0 & Htrap' & Htrap & Hσ)].
      + left. eexists ; split => //=.
        replace (cat es'' es2) with (app es'' es2) ; last done.
        rewrite - Hes'.
        done.
      + right. split => //=.
        by eexists.
      + destruct (iris.to_val es1) eqn:Htv => //=.
        destruct σ as [[ ?  ? ] ?].
        destruct Hred as (? & ? & [[ ?  ? ] ? ] & ? & (? & ? & ?)).
        apply val_head_stuck_reduce in H. congruence.
    - right. split => //=.
      unfold lfilled, lfill in Htrap.
      destruct lh0 as [bef aft|] ; last by false_assumption.
      destruct (const_list bef) eqn : Hbef ; last by false_assumption.
      move/eqP in Htrap.
      destruct σ as [[s  locs ] inst ].
      destruct Hred as (?&?&[[??]?]&?&(?&?&?)).
      edestruct first_non_value_reduce as (vs & e & afte & Hvs & He & Hes1) => //=.
      rewrite Hes1 in Htrap.
      rewrite - app_assoc in Htrap.
      rewrite - app_comm_cons in Htrap.
      apply first_values in Htrap as (-> & -> & <-) => //= ; try by right.
      exists (LH_base bef afte).
      by unfold lfilled, lfill ; rewrite Hbef Hes1.
      destruct e => // ; destruct b => //.
      unfold to_val, iris.to_val in He ; simpl in He ; destruct He as [?|?] => //.
  Qed.


  Lemma local_frame_lfilled_prim_step_split_reduce_r es1 es2 s v i n v' i' e2 s2 v2 i2 efs2 obs2 j lh LI :
    lfilled j lh (es1 ++ es2)%list LI ->
    reducible es1 (s,v,i) ->
    prim_step [AI_local n (Build_frame v i) LI] (s,v',i') obs2 e2 (s2,v2,i2) efs2 ->
    (∃ e' v'' i'' LI', prim_step es1 (s,v,i) obs2 e' (s2,v'',i'') efs2 ∧ v' = v2 ∧ i' = i2 ∧ e2 = [AI_local n (Build_frame v'' i'') LI'] ∧ lfilled j lh (e' ++ es2) LI') \/
      ∃ lh0, lfilled 0 lh0 [AI_trap] es1 /\ (s,v',i') = (s2,v2,i2) .
  Proof.
    intros Hfill (obs & e1 & [[s1  v1 ] i1] & efs & (Hes1 & -> & ->)) (Hstep & -> & ->).
    remember {| f_locs := v ; f_inst := i |} as f.
    remember {| f_locs := v1 ; f_inst := i1 |} as f1.
    remember {| f_locs := v' ; f_inst := i' |} as f'.
    remember {| f_locs := v2 ; f_inst := i2 |} as f2.
    remember [AI_local n f LI] as es.
    induction Hstep ; try (by inversion Heqes) ;
      try (by rewrite <- (app_nil_l [AI_local _ _ _]) in Heqes ;
           apply app_inj_tail in Heqes as [_ Habs] ;
           inversion Habs).
    { destruct H ; try (by inversion Heqes) ;
        try (by rewrite <- (app_nil_l [AI_local _ _ _]) in Heqes ;
             apply app_inj_tail in Heqes as [_ Habs] ;
             inversion Habs).
      - inversion Heqes ; subst ; clear Heqes.
        destruct (lfilled_const j lh (es1 ++ es2) LI) as [-> Hconst] => //=.
        unfold const_list in Hconst.
        rewrite forallb_app in Hconst.
        apply andb_true_iff in Hconst as [? _].
        exfalso ; values_no_reduce.
      - inversion Heqes ; subst ; clear Heqes.
        assert (es1 ++ es2 <> []).
        intro.
        apply app_eq_nil in H as [-> _ ] ; empty_list_no_reduce.
        eapply (filled_singleton j lh (es1 ++ es2)) in H as (-> & -> & Hes) => //=.
        apply app_eq_unit in Hes as [[ -> ->]|[-> ->]].
        empty_list_no_reduce.
        by exfalso ; eapply AI_trap_irreducible.
      - inversion Heqes ; subst ; clear Heqes.
        exfalso.
        eapply (lfilled_return_and_reduce (s := s) (es := es1 ++ es2) (LI:=LI)).
        eapply r_label.
        exact Hes1.
        instantiate (1 := LH_base [] es2).
        instantiate (1 := 0).
        unfold lfilled, lfill => //=.
        unfold lfilled, lfill => //=.
        exact H.
        exact H1.
        exact Hfill.
      - subst. filled_trap H0 Hxl1. }
    - subst les.
      assert (es <> []) ; first by intro ; subst ;  empty_list_no_reduce.
      eapply (filled_singleton k lh0 es) in H1 as (-> & -> & Hes) => //=.
      unfold lfilled, lfill in H0 ; simpl in H0 ; rewrite app_nil_r in H0.
      move/eqP in H0; rewrite H0.
      apply IHHstep => //=.
    - inversion Heqes ; subst n0 f0 es ; clear Heqes.
      rewrite Heqf' in Heqf2 ; inversion Heqf2 ; subst v' i'.
      assert (reducible es1 (s, v, i)).
      { eexists _, _ , (_,_,_), _. repeat split => //=.
        subst ; exact Hes1. }
      destruct f' as [v' i'] eqn:Hf'.
      assert (prim_step LI (s, v, i) [] es' (s', v', i') []).
      { repeat split => //=. subst ; exact Hstep. }
      edestruct lfilled_prim_step_split_reduce_r
        as [(e' & Hes1' & Hfill') | [[lh0 Htrap] Hσ]].
      exact Hfill.
      exact H.
      exact H0.
      left.
      eexists _,_,_,_. repeat split => //=.
      right.
      eexists.
      split => //=.
      inversion Hσ ; subst.
      done.
  Qed.    


  Lemma local_frame_prim_step_split_reduce_r es1 es2 s v i n v' i' e2 s2 v2 i2 efs2 obs2 :
    reducible es1 (s,v,i) ->
    prim_step [AI_local n (Build_frame v i) (es1 ++ es2)] (s,v',i') obs2 e2 (s2,v2,i2) efs2 ->
    (∃ e' v'' i'', prim_step es1 (s,v,i) obs2 e' (s2,v'',i'') efs2 ∧ v' = v2 ∧ i' = i2 ∧ e2 = [AI_local n (Build_frame v'' i'') (e' ++ es2)]) \/
      (∃ lh0, lfilled 0 lh0 [AI_trap] es1 /\ (s,v',i') = (s2,v2,i2)).
  Proof.
    intros Hred Hprim.
    apply local_frame_lfilled_prim_step_split_reduce_r with (es1 := es1) (es2:=es2) (j:=0) (lh:= LH_base [] []) in Hprim;auto.
    destruct Hprim as [[e' [v'' [i'' [LI' Hprim]]]]|[lh' [Hlh' HH]]].
    destruct Hprim as [Hprim [-> [-> [-> Hfill]]]].
    { left. eexists _,_,_. split.  apply Hprim. repeat split;eauto.
      apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;subst.
      erewrite app_nil_l; erewrite app_nil_r. auto. }
    { right. simplify_eq. eexists. eauto. }
    cbn. rewrite app_nil_r. rewrite eqseqE. apply eq_refl.
  Qed.
  
End prim_step_split_properties.
