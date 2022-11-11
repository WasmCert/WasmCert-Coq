From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export stdpp_aux iris_reduction_core.


Ltac filled0 Hfill i lh :=
  let bef := fresh "bef" in
  let aft := fresh "aft" in
  let nn := fresh "nn" in
  let ll := fresh "ll" in
  let ll' := fresh "ll" in
  left ; simple_filled Hfill i lh bef aft nn ll ll' ;
  apply Logic.eq_sym, app_eq_unit in Hfill as [[ -> Hfill ] | [ _ Hfill ]] ;
  [ apply app_eq_unit in Hfill as [[ -> _ ] | [ -> -> ]] ;
    [ by empty_list_no_reduce
      | eexists ; repeat split ; (try done) ;
        [ 
        | unfold lfilled, lfill => //= ; try by rewrite app_nil_r 
        ]
    ]
  |
    apply app_eq_nil in Hfill as [-> ->]; 
      by empty_list_no_reduce ].

Ltac filled1 Hfill i lh Hes1 es1 :=
  let a := fresh "a" in
  let a0 := fresh "a" in
  let Ha := fresh "Ha" in
  let Ha0 := fresh "Ha" in
  let Hnil := fresh "Hnil" in
  let es := fresh "es" in
  let Heqes := fresh "Heqes" in
  let bef := fresh "bef" in
  let aft := fresh "aft" in
  let nn := fresh "nn" in
  let ll := fresh "ll" in
  let ll' := fresh "ll" in
  left ; simple_filled Hfill i lh bef aft nn ll ll' ;
  destruct bef as [| a bef];
  [ destruct es1 as [| a es1]; first (by empty_list_no_reduce) ;
    destruct es1 as [ | a0 es1] ;
    first (by inversion Hfill ; subst ; exfalso ; values_no_reduce) ;
    inversion Hfill as [[ Ha Ha0 Hnil ]] ;
    apply Logic.eq_sym in Hnil ;
    apply app_eq_nil in Hnil as [-> ->] ;
    eexists ; 
    repeat split ; (simpl ; try done) ;
    [ 
    | unfold lfilled, lfill => //= ; try by rewrite app_nil_r 
    ]
  | destruct bef as [|a0 bef];
    [ destruct es1 as [| a0 es1] ; first (by empty_list_no_reduce) ;
      inversion Hfill as [[ Ha Ha0 Hnil ]] ;
      apply Logic.eq_sym, app_eq_nil in Hnil as [-> ->] ;
      remember [a0] as es eqn:Heqes ;
      rewrite - Ha0 in Heqes ;
      apply Logic.eq_sym in Heqes ; 
      exfalso ;  no_reduce Heqes Hes1
    | inversion Hfill as [[ Ha Ha0 Hnil ]];
      apply Logic.eq_sym, app_eq_nil in Hnil as [-> Hnil] ;
      apply app_eq_nil in Hnil as [-> ->] ;
        by empty_list_no_reduce ]].

Ltac filled2 Hfill i lh Hes1 es1 :=
  let a := fresh "a" in
  let a0 := fresh "a" in
  let a1 := fresh "a" in
  let Ha := fresh "Ha" in
  let Ha0 := fresh "Ha" in
  let Ha1 := fresh "Ha" in
  let Hnil := fresh "Hnil" in
  let es := fresh "es" in
  let Heqes := fresh "Heqes" in
  let bef := fresh "bef" in
  let aft := fresh "aft" in
  let nn := fresh "nn" in
  let ll := fresh "ll" in
  let ll' := fresh "ll'" in
  left ; simple_filled Hfill i lh bef aft nn ll ll' ;
  destruct bef as [| a bef];
  [ destruct es1 as [| a es1] ; first (by empty_list_no_reduce ) ;
    destruct es1 as [| a0 es1] ;
    first (by inversion Hfill ; subst ; exfalso ; values_no_reduce ) ;
    destruct es1 as [| a1 es1];
    first (by inversion Hfill ; subst ; exfalso ; values_no_reduce ) ;
    inversion Hfill as [[ Ha Ha0 Ha1 Hnil]] ;
    apply Logic.eq_sym, app_eq_nil in Hnil as [-> ->] ;
    eexists ; 
    repeat split ; (simpl ; try done) ;
    [ 
    | unfold lfilled, lfill => //= ; try by rewrite app_nil_r 
    ]
  | destruct bef as [| a0 bef] ;
    [ destruct es1 as [| a0 es1] ; first (by empty_list_no_reduce ) ;
      destruct es1 as [| a1 es1] ;
      first (by inversion Hfill ; subst ; exfalso ; values_no_reduce ) ;
      inversion Hfill as [[ Ha Ha0 Ha1 Hnil ]] ;
      apply Logic.eq_sym, app_eq_nil in Hnil as [-> ->] ;
      remember [a0 ; a1] as es eqn:Heqes ;
      rewrite - Ha0 - Ha1 in Heqes ;
      apply Logic.eq_sym in Heqes ;
      exfalso ; no_reduce Heqes Hes1
    | destruct bef as [| a1 bef ];
      [ destruct es1 as [| a1 es1] ; first (by empty_list_no_reduce ) ;
        inversion Hfill as [[ Ha Ha0 Ha1 Hnil ]] ;
        apply Logic.eq_sym, app_eq_nil in Hnil as [-> ->] ;
        remember [a1] as es eqn:Heqes ;
        rewrite - Ha1 in Heqes ;
        apply Logic.eq_sym in Heqes ;
        exfalso ; no_reduce Heqes Hes1
      | inversion Hfill as [[ Ha Ha0 Ha1 Hnil ]] ;
        apply Logic.eq_sym, app_eq_nil in Hnil as [-> Hnil] ;
        apply app_eq_nil in Hnil as [-> ->] ;
          by empty_list_no_reduce ]]].


Section lfilled_reduce_properties.
  
  Let reducible := @iris.program_logic.language.reducible wasm_lang.

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.

  (*
This lemma basically states that, enclosing es in an lh context cannot generate
new reduction paths. It can almost be proved using the determinacy lemma, but the arbitrary level of labels in the r_label case prevents an easy proof.

Note that this is a property very similar to Iris context.
*)
  Lemma lfilled_reduce i lh es LI σ LI' σ' obs efs :
    lfilled i lh es LI ->
    reducible es σ ->
    prim_step LI σ obs LI' σ' efs ->
    (exists es', prim_step es σ obs es' σ' efs /\ lfilled i lh es' LI') \/
      (exists lh0, lfilled 0 lh0 [AI_trap] es /\ σ = σ').

  Proof.
    intros Hfill Hred Hstep.
    destruct σ as [[s locs ] inst].
    destruct Hred as (obs0 & es' & [[[ ws0 i0 ] locs0 ] inst0] & efs0 & (Hes & -> & ->)).
    destruct σ' as [[s' locs' ] inst'].
    destruct Hstep as (HLI & -> & ->).
    remember {| f_locs := locs ; f_inst := inst |} as f.
    remember {| f_locs := locs0 ; f_inst := inst0 |} as f0.
    remember {| f_locs := locs' ; f_inst := inst' |} as f'.
    generalize dependent LI. generalize dependent i.
    generalize dependent lh. generalize dependent LI'.
    cut (forall nnn LI' lh i LI, length_rec LI < nnn ->
                            lfilled i lh es LI
                            → opsem.reduce s f LI s' f' LI'
                            → (∃ es'0 : iris.expr,
                                  prim_step es (s, locs, inst) [] es'0 (s', locs', inst') []
                                  ∧ lfilled i lh es'0 LI') ∨
                                (∃ lh0 : lholed, lfilled 0 lh0 [AI_trap] es /\
                                                   (s,locs,inst) = (s', locs', inst'))).
    { intros H LI' lh i LI ;
        assert (length_rec LI < S (length_rec LI)) ; first lia ; by eapply H. }  
    induction nnn ; intros LI' lh i LI Hlen Hfill HLI.
    lia.
    induction HLI ;
      try (filled0 Hfill i lh ;
           rewrite - Heqf - Heqf' ; by econstructor) ;
      try (filled1 Hfill i lh Hes es ;
           rewrite - Heqf - Heqf' ; by econstructor) ;
      try (filled2 Hfill i lh Hes es ;
           rewrite - Heqf - Heqf' ; by econstructor).
    { rewrite Heqf' in Heqf ; inversion Heqf ; subst ; clear Heqf.
      destruct H ;
        try (by filled0 Hfill i lh ;
             repeat econstructor) ;
        try (destruct v ; try (by inversion H) ; destruct b ; try (by inversion H)) ;
        try (by filled1 Hfill i lh Hes es ;
             repeat econstructor) ;
        try (by filled2 Hfill i lh Hes es ;
             repeat econstructor).
      - simple_filled Hfill i lh bef aft nn ll ll'.
        destruct bef.
        repeat (destruct es; first by inversion Hfill ; subst ; exfalso ; values_no_reduce).
        inversion Hfill ; subst.
        apply Logic.eq_sym, app_eq_nil in H5 as [-> ->].
        left ; eexists.
        repeat split ; first by repeat econstructor.
        by unfold lfilled, lfill => //=.
        destruct bef.
        repeat (destruct es; first by inversion Hfill ; subst ; exfalso ; values_no_reduce).
        inversion Hfill.
        apply Logic.eq_sym, app_eq_nil in H5 as [-> ->].
        remember [a0 ; a1 ; a2] as es0.
        subst a0 a1 a2.
        apply Logic.eq_sym in Heqes0.
        exfalso ; no_reduce Heqes0 Hes.
        destruct bef.
        repeat (destruct es ; first by inversion Hfill ; subst ; exfalso ; values_no_reduce).
        inversion Hfill.
        apply Logic.eq_sym, app_eq_nil in H5 as [-> ->].
        remember [a1 ; a2] as es0.
        subst a1 a2.
        apply Logic.eq_sym in Heqes0.
        exfalso ; no_reduce Heqes0 Hes.
        destruct bef.
        repeat (destruct es ; first by inversion Hfill ; subst ; exfalso ; values_no_reduce).
        inversion Hfill.
        apply Logic.eq_sym, app_eq_nil in H5 as [-> ->].
        remember [a2] as es0.
        subst a2.
        apply Logic.eq_sym in Heqes0.
        exfalso ; no_reduce Heqes0 Hes.
        inversion Hfill.
        apply Logic.eq_sym, app_eq_nil in H5 as [_ Hnil].
        apply app_eq_nil in Hnil as [-> _] ; by empty_list_no_reduce.
      - simple_filled Hfill i lh bef aft nn ll ll'.
        destruct bef.
        repeat (destruct es; first by inversion Hfill ; subst ; exfalso ; values_no_reduce).
        inversion Hfill ; subst.
        apply Logic.eq_sym, app_eq_nil in H5 as [-> ->].
        left ; eexists.
        repeat split ; first by repeat econstructor.
        by unfold lfilled, lfill => //=.
        destruct bef.
        repeat (destruct es; first by inversion Hfill ; subst ; exfalso ; values_no_reduce).
        inversion Hfill.
        apply Logic.eq_sym, app_eq_nil in H5 as [-> ->].
        remember [a0 ; a1 ; a2] as es0.
        subst a0 a1 a2.
        apply Logic.eq_sym in Heqes0.
        exfalso ; no_reduce Heqes0 Hes.
        destruct bef.
        repeat (destruct es ; first by inversion Hfill ; subst ; exfalso ; values_no_reduce).
        inversion Hfill.
        apply Logic.eq_sym, app_eq_nil in H5 as [-> ->].
        remember [a1 ; a2] as es0.
        subst a1 a2.
        apply Logic.eq_sym in Heqes0.
        exfalso ; no_reduce Heqes0 Hes.
        destruct bef.
        repeat (destruct es ; first by inversion Hfill ; subst ; exfalso ; values_no_reduce).
        inversion Hfill.
        apply Logic.eq_sym, app_eq_nil in H5 as [-> ->].
        remember [a2] as es0.
        subst a2.
        apply Logic.eq_sym in Heqes0.
        exfalso ; no_reduce Heqes0 Hes.
        inversion Hfill.
        apply Logic.eq_sym, app_eq_nil in H5 as [_ Hnil].
        apply app_eq_nil in Hnil as [-> _] ; by empty_list_no_reduce.
      - left ; simple_filled Hfill i lh bef aft nn ll ll'.
        edestruct first_non_value_reduce as (vs1 & e & es'1 & Hvs1 & He & Heq) => //=.
        rewrite Heq in Hfill.
        repeat rewrite app_assoc in Hfill.
        repeat rewrite - (app_assoc (bef ++ vs1)) in Hfill.
        repeat rewrite - app_comm_cons in Hfill.
        apply first_values in Hfill as (Hvs' & <- & Hnil) => //= ; try by intros [? ?].
        apply Logic.eq_sym, app_eq_nil in Hnil as [-> ->].
        rewrite Heq in Hes.
        destruct bef.
        subst.
        eexists _.
        repeat split => //=.
        by repeat econstructor.
        unfold lfilled, lfill => //=.
        exfalso ; eapply block_not_enough_arguments_no_reduce => //=.
        subst.
        rewrite H1.
        simpl.
        rewrite app_length.
        lia.
        destruct He ; destruct e => //. destruct b => //. 
        by const_list_app.
        apply in_app_or in Hxl1 as [Habs | Habs].
        intruse_among_values vs Habs H.
        inversion Habs ; inversion H3.
      - left ; simple_filled Hfill i lh bef aft nn ll ll'.
        edestruct first_non_value_reduce as (vs1 & e & es'1 & Hvs1 & He & Heq) => //=.
        rewrite Heq in Hfill.
        repeat rewrite app_assoc in Hfill.
        repeat rewrite - (app_assoc (bef ++ vs1)) in Hfill.
        repeat rewrite - app_comm_cons in Hfill.
        apply first_values in Hfill as (Hvs' & <- & Hnil) => //= ; try by intros [? ?].
        apply Logic.eq_sym, app_eq_nil in Hnil as [-> ->].
        rewrite Heq in Hes.
        destruct bef.
        subst.
        eexists _.
        repeat split => //=.
        by repeat econstructor.
        unfold lfilled, lfill => //=.
        exfalso ; eapply loop_not_enough_arguments_no_reduce => //=.
        subst.
        rewrite H1.
        simpl.
        rewrite app_length.
        lia.
        destruct He ; destruct e => //. destruct b => //. 
        by const_list_app.
        apply in_app_or in Hxl1 as [Habs | Habs].
        intruse_among_values vs Habs H.
        inversion Habs ; inversion H3.
      - left ; simple_filled Hfill i lh bef aft nn ll ll'.
        apply Logic.eq_sym, app_eq_unit in Hfill as [[ -> Hfill ] | [ _ Hfill ]].
        apply app_eq_unit in Hfill as [[ -> _ ] | [ -> -> ]] ; first by empty_list_no_reduce.
        eexists _.
        repeat split => //=.
        by repeat econstructor.
        unfold lfilled, lfill => //=.
        by rewrite app_nil_r.
        apply app_eq_nil in Hfill as [-> _] ; by empty_list_no_reduce.
        subst.
        unfold lfill in Heqles.
        destruct i.
        destruct lh0 as [vs aft | ]; try by inversion Heqles.
        destruct (const_list vs) ; inversion Heqles.
        rewrite H1 in H.
        values_no_reduce .
        unfold const_list in H.
        repeat rewrite forallb_app in H.
        apply andb_true_iff in H as [_ H].
        apply andb_true_iff in H as [H _].
        by unfold const_list.
        fold lfill in Heqles.
        destruct lh0 ; try by inversion Heqles.
        destruct (const_list l0) ; try by inversion Heqles.
        destruct (lfill i lh0 es) ; inversion Heqles.
        rewrite H1 in H.
        unfold const_list in H.
        rewrite forallb_app in H.
        simpl in H.
        rewrite andb_false_r in H.
        false_assumption.
      - simple_filled Hfill i lh bef aft nn ll ll'.
        apply Logic.eq_sym, app_eq_unit in Hfill as [[ -> Hfill ] | [ _ Hfill ]].
        apply app_eq_unit in Hfill as [[ -> _ ] | [ -> -> ]] ; first by empty_list_no_reduce.
        left.
        eexists _.
        repeat split => //=.
        by repeat econstructor.
        unfold lfilled, lfill => //=.
        apply app_eq_nil in Hfill as [-> ->] ; by empty_list_no_reduce .
        subst.
        unfold lfill in Heqles.
        destruct i.
        destruct lh0 as [vs aft | ]; try by inversion Heqles.
        destruct (const_list vs) ; inversion Heqles.
        destruct vs.
        destruct es ; first by empty_list_no_reduce .
        inversion H0.
        apply Logic.eq_sym, app_eq_nil in H2 as [-> ->].
        subst.
        by eapply AI_trap_irreducible.
        inversion H0.
        apply Logic.eq_sym, app_eq_nil in H2 as [_ Hnil].
        apply app_eq_nil in Hnil as [-> _] ; by empty_list_no_reduce .
        fold lfill in Heqles.
        destruct lh0 ; try by inversion Heqles.
        destruct (const_list l0) ; try by inversion Heqles.
        destruct (lfill i lh0 es) ;  inversion Heqles.
        found_intruse (AI_label n l1 l3) H0 Hxl2.
      - left ; simple_filled Hfill i lh bef aft nn ll ll'.
        apply Logic.eq_sym, app_eq_unit in Hfill as [[ -> Hfill ] | [ _ Hfill ]].
        apply app_eq_unit in Hfill as [[ -> _ ] | [ -> -> ]] ; first by empty_list_no_reduce.
        eexists _.
        repeat split => //=.
        eapply r_simple. clear Hvs.
        by econstructor.
        unfold lfilled, lfill => //=.
        by rewrite app_nil_r.  
        apply app_eq_nil in Hfill as [-> ->] ; by empty_list_no_reduce .
        destruct bef ; last by destruct bef ; inversion Hfill.
        inversion Hfill ; subst nn ll ll' l ; clear Hfill.
        assert (lfilled i lh1 es LI) ; first by unfold lfilled ; rewrite - Heqles.
        eapply lfilled_br_and_reduce ; try exact H2 ; try exact H1.
        exact Hes. done. lia.
      - unfold lfilled, lfill in H0.
        destruct lh0 as [bef0 aft0 |] ; last by false_assumption.
        destruct (const_list bef0) eqn:Hbef0 ; last by false_assumption.
        move/eqP in H0.
        edestruct first_non_value_reduce as (vs & e & aft' & Hcvs & He & Hainas) => //=.
        subst es.
        rewrite H0 in Hfill.
        simple_filled Hfill i lh bef aft nn ll ll'.
        repeat rewrite app_assoc in Hfill.
        rewrite - (app_assoc bef0) in Hfill.
        repeat rewrite - (app_assoc (bef ++ vs)) in Hfill.
        rewrite - (app_comm_cons _ _ e) in Hfill.
        apply first_values in Hfill as (-> & <- & ->) => //= ; try by right.
        right.
        exists (LH_base vs aft').
        unfold lfilled, lfill.
        rewrite Hcvs.
        done.
        destruct He ; destruct e => // ; destruct b => //.
        by const_list_app.
        apply first_values in Hfill as (_ & Habs & _) => //= ; try by (intros [? ?]). } 
    - left ; simple_filled Hfill i lh bef aft nn ll ll'.
      edestruct first_non_value_reduce as (vs1 & e & es'1 & Hvs1 & He & Heq) => //=.
      rewrite Heq in Hfill.
      repeat rewrite app_assoc in Hfill.
      repeat rewrite - (app_assoc (bef ++ vs1)) in Hfill.
      repeat rewrite - app_comm_cons in Hfill.
      apply first_values in Hfill as (Hvs' & <- & Hnil) => //= ; try by intros [? ?].
      apply Logic.eq_sym, app_eq_nil in Hnil as [-> ->].
      rewrite Heq in Hes.
      destruct bef.
      subst.
      eexists _.
      repeat split => //=.
      rewrite Heqf'.
      by econstructor.
      unfold lfilled, lfill => //=.
      exfalso ; eapply invoke_not_enough_arguments_no_reduce_native => //=.
      by subst.
      subst.
      rewrite H4.
      rewrite - v_to_e_length.
      rewrite Hvs'. simpl.
      rewrite app_length.
      lia.
      destruct He ; destruct e => // ; destruct b => //. 
      rewrite H1.
      by eapply v_to_e_is_const_list.
      unfold const_list.
      rewrite forallb_app.
      apply andb_true_iff ; split => //=.
      apply in_app_or in Hxl1 as [Habs | Habs].
      assert (const_list ves) ; first by rewrite H1 ; eapply v_to_e_is_const_list.
      intruse_among_values ves Habs H9.
      inversion Habs ; inversion H9.
    - left ; simple_filled Hfill i lh bef aft nn ll ll'.
      edestruct first_non_value_reduce as (vs1 & e & es'1 & Hvs1 & He & Heq) => //=.
      rewrite Heq in Hfill.
      repeat rewrite app_assoc in Hfill.
      repeat rewrite - (app_assoc (bef ++ vs1)) in Hfill.
      repeat rewrite - app_comm_cons in Hfill.
      apply first_values in Hfill as (Hvs' & <- & Hnil) => //= ; try by intros [? ?].
      apply Logic.eq_sym, app_eq_nil in Hnil as [-> ->].
      rewrite Heq in Hes.
      destruct bef.
      subst.
      eexists _.
      repeat split => //=.
      rewrite Heqf'.
      by econstructor.
      unfold lfilled, lfill => //=.
      exfalso ; eapply invoke_not_enough_arguments_no_reduce_host => //=.
      by subst.
      subst.
      rewrite H3.
      rewrite - v_to_e_length.
      rewrite Hvs'. simpl.
      rewrite app_length.
      lia.
      destruct He ; destruct e => // ; destruct b => //. 
      rewrite H1.
      by eapply v_to_e_is_const_list.
      unfold const_list.
      rewrite forallb_app.
      apply andb_true_iff ; split => //=.
      apply in_app_or in Hxl1 as [Habs | Habs].
      assert (const_list ves) ; first by rewrite H1 ; eapply v_to_e_is_const_list.
      intruse_among_values ves Habs H5.
      inversion Habs ; inversion H5.
    - destruct (decide (i <= k)).
      { destruct (empty_base lh) eqn:Hlh.
        eapply can_empty_base in Hfill as (besa & Hfill0 & Hfill12 & Hempty) => //=.
        edestruct (filled_twice k i lh0 l0 es0 besa les) as [lh2 Hminus] => //=.
        specialize (lh_minus_minus _ _ _ _ _ _ _ _ Hminus H Hfill12) ; intro Hfillm.
        unfold lfilled, lfill in Hfill0.
        destruct l1 as [bef0 aft0|] ; last by false_assumption.
        destruct (const_list bef0) eqn:Hbef0 ; last by false_assumption.
        move/eqP in Hfill0 ; subst besa.
        destruct (k - i) eqn:Hki.
        { unfold lfilled, lfill in Hfillm.
          destruct lh2 as [bef2 aft2 |] ; last by false_assumption.
          destruct (const_list bef2) eqn:Hbef2 ; last by false_assumption.
          move/eqP in Hfillm.
          edestruct reduction_core as
            [(core & bc0 & ac0 & bc2 & ac2 & core' & Hbc0 & Hbc2 &
                Heqes & Heqes0 & Hbefs & Hafts &
                Hcore & Hes0')
            | (lht0 & lht1 & Hfill0 & Hfill1 & Hσ)].
          - exact Hes.
            exact HLI.
            exact Hbef0.
            exact Hbef2.
            exact Hfillm.
            left.
            exists (bc0 ++ core' ++ ac0).
            repeat split.
            eapply r_label.
            subst ; exact Hcore.
            instantiate (1 := LH_base bc0 ac0).
            instantiate (1 := 0).
            unfold lfilled, lfill.
            rewrite Hbc0.
            by rewrite Heqes.
            unfold lfilled, lfill.
            by rewrite Hbc0.
            eapply can_fill_base => //=.
            unfold lfilled, lfill.
            rewrite Hbef0.
            repeat rewrite app_assoc.
            rewrite Hbefs.
            repeat rewrite - app_assoc.
            rewrite Hafts.
            rewrite (app_assoc bc2).
            rewrite (app_assoc (bc2 ++ core')).
            rewrite - (app_assoc bc2).
            rewrite Hes0'.
            done.
            eapply lh_minus_minus2.
            exact Hminus.
            exact l.
            exact H0.
            rewrite Hki.
            unfold lfilled, lfill.
            rewrite Hbef2.
            done.
          - right ; eexists ; split => //=.
            subst. by inversion Hσ. }
        unfold lfilled, lfill in Hfillm ; fold lfill in Hfillm.
        destruct lh2 as [| bef2 n2 es2 lh2 aft2 ] ; first by false_assumption.
        destruct (const_list bef2) eqn:Hbef2 ; last by false_assumption.
        destruct (lfill n lh2 es0) eqn:Hfill ; last by false_assumption.
        move/eqP in Hfillm.
        edestruct first_non_value_reduce as (vs & e & aftes & Hvs & He & Heq) ;
          try exact Hes.
        rewrite Heq in Hfillm.
        repeat rewrite app_assoc in Hfillm.
        repeat rewrite - (app_assoc (bef0 ++ vs)) in Hfillm.
        rewrite - app_comm_cons in Hfillm.
        apply first_values in Hfillm as (<- & -> & <-) => //= ; try by intros [? ?].
        assert (lfilled (S n) (LH_rec vs n2 es2 lh2 aftes) es0 es).
        { unfold lfilled, lfill ; fold lfill.
          rewrite Hvs.
          rewrite Hfill.
          by rewrite Heq. }
        edestruct lfilled_swap as [es'' Hfill'] ; first exact H1.
        assert (reduce s f es s' f' es'').
        { eapply r_label.
          exact HLI.
          exact H1.
          exact Hfill'. }
        left ; exists es''.
        repeat split => //=.
        by subst.
        eapply (can_fill_base i lh es'' _ les') => //=.
        unfold lfilled, lfill.
        rewrite Hbef0.
        done.
        eapply lh_minus_minus2.
        exact Hminus.
        exact l.
        exact H0.
        rewrite Hki.
        unfold lfilled, lfill ; fold lfill.
        unfold lfilled, lfill in Hfill' ; fold lfill in Hfill'.
        unfold const_list.
        rewrite forallb_app.
        unfold const_list in Hbef0 ; rewrite Hbef0.
        rewrite Hvs in Hfill'.
        unfold const_list in Hvs ; rewrite Hvs.
        simpl.
        destruct (lfill n lh2 es'0) ; last by false_assumption.
        move/eqP in Hfill'; rewrite Hfill'.
        repeat rewrite app_assoc.
        repeat rewrite - app_assoc.
        done.
        destruct He ; destruct e => // ; destruct b => //. 
        unfold const_list.
        rewrite forallb_app.
        apply andb_true_iff ; split => //=. }
      assert (k < i) ; first lia.
      destruct (empty_base lh0) eqn:Hlh.
      eapply can_empty_base in H as (besa0 & Hfill0 & Hfill12 & Hempty) => //=.
      edestruct (filled_twice i k lh l es besa0 les) as [lh2 Hminus] => //=.
      lia.
      specialize (lh_minus_minus _ _ _ _ _ _ _ _ Hminus Hfill Hfill12) ; intro Hfillm.
      unfold lfilled, lfill in Hfill0.
      destruct l0 as [bef0 aft0|] ; last by false_assumption.
      destruct (const_list bef0) eqn:Hbef0 ; last by false_assumption.
      move/eqP in Hfill0 ; subst besa0.
      destruct (i-k) eqn:Hik ; first lia.
      unfold lfilled, lfill in Hfillm ; fold lfill in Hfillm.
      destruct lh2 as [| bef2 n2 es2 lh2 aft2 ] ; first by false_assumption.
      destruct (const_list bef2) eqn:Hbef2 ; last by false_assumption.
      destruct (lfill n0 lh2 es) eqn:Hfill' ; last by false_assumption.
      move/eqP in Hfillm.
      edestruct first_non_value_reduce as (vs & e & aftes & Hvs & He & Heq) ;
        try exact HLI.
      rewrite Heq in Hfillm.
      repeat rewrite app_assoc in Hfillm.
      repeat rewrite - (app_assoc (bef0 ++ vs)) in Hfillm.
      rewrite - app_comm_cons in Hfillm.
      apply first_values in Hfillm as (<- & -> & <-) => //= ; try by left.
      assert (lfilled (S n0) (LH_rec vs n2 es2 lh2 aftes) es es0).
      { unfold lfilled, lfill ; fold lfill.
        rewrite Hvs.
        rewrite Hfill'.
        by rewrite Heq. }
      assert (lfilled k lh0 es0 les).
      { eapply can_fill_base => //=.
        unfold lfilled, lfill => //=.
        rewrite Hbef0.
        done. }
      destruct (lfilled_length_rec_or_same k lh0 es0 les) as [Hlenr | Heqes] => //=.
      assert (length_rec es0 < nnn) ; first lia.
      eapply IHnnn in H3 as [( es'' & (Hstep & _ & _) & Hfill0) | [lhtrap Htrap]] => //=.
      + left ; exists es''.
        repeat split => //=.
        eapply lh_minus_plus.
        exact Hminus.
        instantiate (1 := k).
        lia.
        rewrite Hik.
        unfold lfilled, lfill ; fold lfill.
        unfold lfilled, lfill in Hfill0 ; fold lfill in Hfill0.
        rewrite Hvs in Hfill0.
        unfold const_list.
        rewrite forallb_app.
        unfold const_list in Hbef0 ; rewrite Hbef0.
        unfold const_list in Hvs ; rewrite Hvs => /=.
        destruct (lfill n0 lh2 es'') ; last by false_assumption.
        move/eqP in Hfill0.
        rewrite - app_assoc.
        rewrite app_comm_cons.
        rewrite (app_assoc vs).
        rewrite - Hfill0.
        done.
        eapply can_empty_base in H0 as (besa & Hfill1 & Hfill2 & _) => //=.
        unfold lfilled, lfill in Hfill1.
        rewrite Hbef0 in Hfill1.
        move/eqP in Hfill1; subst.
        done.
      + right ; by eexists.
      + rewrite Heqes in H2.
        apply filled_trivial in H2 as [-> ->].
        unfold lfilled, lfill in H0 ; simpl in H0.
        move/eqP in H0.
        rewrite app_nil_r in H0.
        subst.
        apply IHHLI => //=.
        destruct He ; destruct e => // ; destruct b => //. 
      + by const_list_app.
  Qed.

End lfilled_reduce_properties.
