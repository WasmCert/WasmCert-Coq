From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap proph_map.
Require Export iris iris_locations stdpp_aux.
Require Export datatypes (* host *) operations properties opsem.
Require Import iris_reduce_properties iris_wasm_lang_properties iris_reduction_core.



Ltac solve_prim_step_split_reduce_r H objs Heqf0 :=
  (* this code has to be written so many times in the following proof, with just
     minor changes, so I wrote a tactic. *)
  left ; subst ;
  apply Logic.eq_sym, app_eq_nil in H as [? ?] ;
  exists objs ; subst ; rewrite app_nil_r ;
  repeat split => //= ; rewrite Heqf0.


 
Ltac filled0 Hfill i lh :=
  let bef := fresh "bef" in
  let aft := fresh "aft" in
  let nn := fresh "nn" in
  let ll := fresh "ll" in
  let ll' := fresh "ll" in
  left ; simple_filled Hfill i lh bef aft nn ll ll' ;
  apply Logic.eq_sym, app_eq_unit in Hfill as [[ -> Hfill ] | [ _ Hfill ]] ;
  [ apply app_eq_unit in Hfill as [[ -> _ ] | [ -> -> ]] ;
    [ (*apply app_eq_nil in Hfill as [-> ->] ; *) by empty_list_no_reduce
    | (*apply app_eq_unit in Hfill as [[ -> _ ] | [ -> -> ]] ;
      [ by empty_list_no_reduce
      | *) eexists ; repeat split ; (try done) ;
        [ 
        | unfold lfilled, lfill => //= ; try by rewrite app_nil_r 
        ]
(*      ] *)
    ]
  | (* apply app_eq_nil in Hfill as [Hfill _] ; *)
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
    (* apply app_eq_nil in Hnil as [Hnil ->] ; *)
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
(*      apply app_eq_nil in Hnil as [-> ->] ; *)
      remember [a0] as es eqn:Heqes ;
      rewrite - Ha0 in Heqes ;
      apply Logic.eq_sym in Heqes ; 
      exfalso ;  no_reduce Heqes Hes1
    | inversion Hfill as [[ Ha Ha0 Hnil ]];
      apply Logic.eq_sym, app_eq_nil in Hnil as [-> Hnil] ;
(*      apply app_eq_nil in Hnil as [Hnil ->] ; *)
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
(*    apply app_eq_nil in Hnil as [-> ->] ;  *)
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
(*      apply app_eq_nil in Hnil as [-> ->] ; *)
      remember [a0 ; a1] as es eqn:Heqes ;
      rewrite - Ha0 - Ha1 in Heqes ;
      apply Logic.eq_sym in Heqes ;
      exfalso ; no_reduce Heqes Hes1
    | destruct bef as [| a1 bef ];
      [ destruct es1 as [| a1 es1] ; first (by empty_list_no_reduce ) ;
        inversion Hfill as [[ Ha Ha0 Ha1 Hnil ]] ;
        apply Logic.eq_sym, app_eq_nil in Hnil as [-> ->] ;
(*        apply app_eq_nil in Hnil as [-> ->] ; *)
        remember [a1] as es eqn:Heqes ;
        rewrite - Ha1 in Heqes ;
        apply Logic.eq_sym in Heqes ;
        exfalso ; no_reduce Heqes Hes1
      | inversion Hfill as [[ Ha Ha0 Ha1 Hnil ]] ;
        apply Logic.eq_sym, app_eq_nil in Hnil as [-> Hnil] ;
(*        apply app_eq_nil in Hnil as [Hnil ->] ; *)
        apply app_eq_nil in Hnil as [-> ->] ;
          by empty_list_no_reduce ]]].


Section split_reduce_properties.
  
  Let reducible := @reducible wasm_lang.

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.

  
  Lemma prim_step_split_reduce_r (es1 es2 es' : list administrative_instruction) σ σ' obs efs :
    iris.to_val es1 = None -> 
    prim_step (es1 ++ es2) σ obs es' σ' efs ->
    (exists es'', es' = es'' ++ es2 /\ prim_step es1 σ obs es'' σ' efs) \/
      (exists n m lh, lfilled 0 (LH_base (take n es1)
                                    (drop m (es1 ++ es2)))
                         [AI_trap] es' /\ lfilled 0 lh [AI_trap] es1 ∧ σ' = σ). 
  Proof.
    intros Hes1 Hstep. 
    cut (forall n, length es' < n ->
              (exists es'', es' = es'' ++ es2 /\ prim_step es1 σ obs es'' σ' efs) \/
                (exists n m lh, n <= length es1 /\ m <= length (es1 ++ es2) /\
                             lfilled 0 (LH_base (take n es1)
                                                (drop m (es1 ++ es2)))
                                     [AI_trap] es' /\ lfilled 0 lh [AI_trap] es1 ∧ σ'=σ)). 
    { intro Hn ; assert (length es' < S (length es')) as Hlen ; first lia.
      destruct (Hn (S (length es')) Hlen) as [ Hl | (n0 & m & lh & _ & _ & ? & ? & ?) ].
      by left. right ; exists n0, m, lh. 
      repeat split => //=. } 
    intros len Hlen.
    generalize dependent es' ; generalize dependent es1 ; generalize dependent es2.
    induction len ; intros es2 es1 Hes1 es' Hstep Hlen ; first lia.
    unfold prim_step, iris.prim_step in Hstep.
    destruct σ as [[[??]?]?] ;
      destruct σ' as [[[??]?]?] ;
      destruct Hstep as (Hstep & -> & ->).
    remember (es1 ++ es2) as es.
    remember {| f_locs := l ; f_inst := i |} as f.
    remember {| f_locs := l0 ; f_inst := i0 |} as f0.
    induction Hstep ; do 5 try (destruct es1 ; first (by inversion Heqes ; subst ;
                                                      inversion Hes1)) ;
      inversion Heqes.
    { destruct H ;
        repeat (destruct es1 ; first (by inversion Heqes ; subst ; inversion Hes1)) ;
        inversion Heqes.
      - solve_prim_step_split_reduce_r H3 [AI_basic (BI_const (app_unop op v))]
                                       Heqf0 ; by apply r_simple, rs_unop.
      - solve_prim_step_split_reduce_r H5 [AI_basic (BI_const v)] Heqf0 ;
          by apply r_simple, rs_binop_success.
      - solve_prim_step_split_reduce_r H5 [AI_trap] Heqf0 ; by apply r_simple,
            rs_binop_failure.
      - solve_prim_step_split_reduce_r
          H3 [AI_basic (BI_const (VAL_int32 (wasm_bool (app_testop_i (e:=i32t) testop c))))]
          Heqf0 ; by apply r_simple, rs_testop_i32.
      - solve_prim_step_split_reduce_r
          H3 [AI_basic (BI_const (VAL_int32 (wasm_bool (app_testop_i (e:=i64t) testop c))))]
          Heqf0 ; by apply r_simple, rs_testop_i64.
      - solve_prim_step_split_reduce_r
          H4 [AI_basic (BI_const (VAL_int32 (wasm_bool (app_relop op v1 v2))))]
          Heqf0 ; by apply r_simple,  rs_relop.
      - solve_prim_step_split_reduce_r H5 [AI_basic (BI_const v')] Heqf0 ;
          by apply r_simple, rs_convert_success.
      - solve_prim_step_split_reduce_r H5 [AI_trap] Heqf0 ;
          by apply r_simple, rs_convert_failure.
      - solve_prim_step_split_reduce_r
          H4 [AI_basic (BI_const (wasm_deserialise (bits v) t2))] Heqf0 ;
          by apply r_simple, rs_reinterpret.
      - solve_prim_step_split_reduce_r H2 [AI_trap] Heqf0 ;
          by apply r_simple, rs_unreachable.
      - solve_prim_step_split_reduce_r H2 ([] : seq.seq administrative_instruction)
                                       Heqf0 ; by apply r_simple, rs_nop.
      - solve_prim_step_split_reduce_r H3 ([] : seq.seq administrative_instruction)
                                       Heqf0 ; by apply r_simple, rs_drop.
      - solve_prim_step_split_reduce_r H6 [AI_basic (BI_const v2)] Heqf0 ;
          by apply r_simple, rs_select_false.
      - solve_prim_step_split_reduce_r H6 [AI_basic (BI_const v1)] Heqf0 ;
          by apply r_simple, rs_select_true.
      - left ; destruct (first_non_value _ Hes1) as (vs1 & e1 & es'1 & Hvs1 & He1 & Hes'1).
        rewrite Hes'1 in Heqes. rewrite <- app_assoc in Heqes.
        rewrite <- app_comm_cons in Heqes.
        apply first_values in Heqes as (Hvs & He & Hnil) => //= ;try (intros ; destruct He1 as [? | ?] ; done).
        apply Logic.eq_sym, app_eq_nil in Hnil as [Hn1 Hn2].
        exists [AI_label m [] (vs ++ to_e_list es)].
        repeat (split => //= ; try by subst). rewrite Hes'1. rewrite <- Hvs.
        rewrite <- He. rewrite <- Heqf. rewrite <- Heqf0. rewrite Hn1.
        apply r_simple. apply (rs_block es H H1 H2 H3).
        destruct He1 as [? | ?] => //.
        intro He1'. assert (const_list [e1]) ;
                      first by unfold const_list => /= ; rewrite He1'.
        apply const_list_to_val in H6 as [? ?] => //.
        unfold to_val in H4 ; congruence.
        subst => //. 
      - left ; destruct (first_non_value _ Hes1) as (vs1 & e1 & es'1 & Hvs1 & He1 & Hes'1).
        rewrite Hes'1 in Heqes. rewrite <- app_assoc in Heqes.
        rewrite <- app_comm_cons in Heqes.
        apply first_values in Heqes as (Hvs & He & Hnil) => //=;try (intros [? ?];done).
        apply Logic.eq_sym, app_eq_nil in Hnil as [Hn1 Hn2].
        exists [AI_label n [AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)].
        repeat (split => //= ; try by subst). rewrite Hes'1. rewrite <- Hvs.
        rewrite <- He. rewrite <- Heqf. rewrite <- Heqf0. rewrite Hn1.
        apply r_simple. apply (rs_loop es H H1 H2 H3).
        intros ; unfold to_val in He1.
        destruct He1 as [?| ?].
        assert (const_list [e1]) ; first by unfold const_list => /= ; rewrite H4.
        apply const_list_to_val in H7 as [? ?] ; congruence.
        subst ; by unfold iris.to_val in H4.
      - solve_prim_step_split_reduce_r H4 [AI_basic (BI_block tf e2s)] Heqf0 ;
          by apply r_simple, rs_if_false.
      - solve_prim_step_split_reduce_r H4 [AI_basic (BI_block tf e1s)] Heqf0 ;
          by apply r_simple, rs_if_true.
      - solve_prim_step_split_reduce_r H3 vs Heqf0 ; by apply r_simple, rs_label_const.
      - solve_prim_step_split_reduce_r H2 [AI_trap] Heqf0 ;
          by apply r_simple, rs_label_trap.
      - left ; apply Logic.eq_sym, app_eq_nil in H5 as [Hn1 Hn2].
        exists (vs ++ es). repeat ( split => //= ; try by subst ; rewrite app_nil_r).
        rewrite <- Heqf. rewrite <- Heqf0. apply r_simple. rewrite Hn1.
        apply (rs_br es H H1 H2).
      - solve_prim_step_split_reduce_r H4 ([] : seq.seq administrative_instruction)
                                       Heqf0 ; by apply r_simple , rs_br_if_false.
      - solve_prim_step_split_reduce_r H4 [AI_basic (BI_br i1)] Heqf0 ;
          by apply r_simple, rs_br_if_true.
      - solve_prim_step_split_reduce_r H5 [AI_basic (BI_br j)] Heqf0 ;
          by apply r_simple, rs_br_table.
      - solve_prim_step_split_reduce_r H4 [AI_basic (BI_br i1)] Heqf0 ;
          by apply r_simple, rs_br_table_length.
      - solve_prim_step_split_reduce_r H4 es Heqf0 ; by apply r_simple, rs_local_const.
      - solve_prim_step_split_reduce_r H2 [AI_trap] Heqf0 ;
          by apply r_simple, rs_local_trap.
      - left ; apply Logic.eq_sym, app_eq_nil in H5 as [Hn1 Hn2].
        exists vs. repeat (split => //= ; try by subst ; rewrite app_nil_r).
        rewrite <- Heqf. rewrite Heqf0. apply r_simple. rewrite Hn1.
        apply (rs_return f0 H H1 H2).
      - destruct es1. subst. destruct a ; try by inversion H.
        destruct b ; try by inversion H. inversion H3. subst.
        solve_prim_step_split_reduce_r H5 [a; a; AI_basic (BI_set_local i1)]
                                       Heqf0 ;
          by apply r_simple , rs_tee_local.
      - right. exists 0, (length (a :: es1 ++ es2)). rewrite take_0. rewrite drop_all.
        rewrite Heqf in Heqf0 ; inversion Heqf0. 
        destruct (first_non_value _ Hes1) as (vs1 & e1 & es'1 & Hvs1 & He1 & Hes'1).
        rewrite Hes'1 in Heqes. unfold lfilled, lfill in H1.
        destruct lh ; last by false_assumption.
        remember (const_list l1) as b eqn:Hl1. destruct b ; last by false_assumption.
        move/eqP in H1. rewrite H1 in Heqes.
        rewrite <- app_assoc in Heqes. rewrite <- app_comm_cons in Heqes.
        apply first_values in Heqes as (Hvs & He & Hnil) => //= ; try (intros [? ?];done).
        rewrite <- He in Hes'1. rewrite Hes'1.
        exists (LH_base vs1 es'1). repeat (split => //=). lia.
        by unfold lfilled, lfill ; rewrite Hvs1.
        intros ; unfold to_val in He1.
        destruct He1 as [?| ?].
        assert (const_list [e1]) ; first by unfold const_list => /= ; rewrite H3.
        apply const_list_to_val in H7 as [? ?] ; congruence.
        subst ; by unfold iris.to_val in H3. }
    - solve_prim_step_split_reduce_r H2 [AI_invoke a] Heqf0 ; apply r_call ;
        by rewrite Heqf0 in H.
    - solve_prim_step_split_reduce_r H5 [AI_invoke a] Heqf0.
      apply (r_call_indirect_success (cl:=cl)) => //=.
      by rewrite Heqf0 in H. by rewrite Heqf0 in H1.
    - solve_prim_step_split_reduce_r H5 [AI_trap] Heqf0.
      apply (r_call_indirect_failure1 (a:=a) (cl:=cl)) => //=.
      by rewrite Heqf0 in H. by rewrite Heqf0 in H1.
    - solve_prim_step_split_reduce_r H3 [AI_trap] Heqf0.
      apply r_call_indirect_failure2 => //=. 
      by rewrite Heqf0 in H.
    - left ; destruct (first_non_value _ Hes1) as (vs1 & e1 & es'1 & Hvs1 & He1 & Hes'1).
      rewrite Hes'1 in Heqes. rewrite <- app_assoc in Heqes.
      rewrite <- app_comm_cons in Heqes.
      apply first_values in Heqes as (Hvs & He & Hnil) => //=;try (intros [? ?];done).
      apply Logic.eq_sym, app_eq_nil in Hnil as [Hn1 Hn2].
      exists [AI_local m f' [AI_basic (BI_block (Tf [] t2s) es)]].
      rewrite Hn2.
      repeat split => //=. rewrite <- Heqf0. rewrite <- Heqf. rewrite Hes'1.
      rewrite Hn1. rewrite <- He. rewrite <- Hvs.
      by apply (r_invoke_native f H H0 H1 H2 H3 H4 H5 H6).
      intros ; unfold to_val in He1.
      destruct He1 as [?| ?].
      assert (const_list [e1]) ; first by unfold const_list => /= ; rewrite H9.
      apply const_list_to_val in H12 as [??] ; congruence.
      subst ; by unfold iris.to_val in H9.
      rewrite H1. by apply v_to_e_is_const_list.
    - left ; destruct (first_non_value _ Hes1) as (vs1 & e1 & es'1 & Hvs1 & He1 & Hes'1).
      rewrite Hes'1 in Heqes. rewrite <- app_assoc in Heqes.
      rewrite <- app_comm_cons in Heqes.
      apply first_values in Heqes as (Hvs & He & Hnil) => //=;try (intros [? ?];done).
      apply Logic.eq_sym, app_eq_nil in Hnil as [Hn1 Hn2].
      eexists [AI_call_host (Tf t1s t2s) h _].
      rewrite Hn2.
      repeat split => //=. rewrite <- Heqf0. rewrite <- Heqf. rewrite Hes'1.
      rewrite Hn1. rewrite <- He. rewrite <- Hvs.
      by eapply (r_invoke_host). 
      intros ; unfold to_val in He1.
      destruct He1 as [?| ?].
      assert (const_list [e1]) ; first by unfold const_list => /= ; rewrite H5.
      apply const_list_to_val in H8 as [??] ; congruence.
      subst ; by unfold iris.to_val in H5.
      rewrite H1. by apply v_to_e_is_const_list. 
 (*    - left ; destruct (first_non_value _ Hes1) as (vs1 & e1 & es'1 & Hvs1 & He1 & Hes'1).
      rewrite Hes'1 in Heqes. rewrite <- app_assoc in Heqes.
      rewrite <- app_comm_cons in Heqes.
      apply first_values in Heqes as (Hvs & He & Hnil) => //=.
    (*  apply Logic.eq_sym, app_eq_nil in Hnil as [Hn1 Hn2].
    exists (result_to_stack r). rewrite Hn2. rewrite app_nil_r.
    repeat split => //=. rewrite <- Heqf0. rewrite <- Heqf. rewrite Hes'1.
    rewrite Hn1. rewrite <- He. rewrite <- Hvs.
    by apply (r_invoke_host_success f H H0 H1 H2 H3 H4 H5).
    by left. rewrite H1. by apply v_to_e_is_const_list.*)
    - left ; destruct (first_non_value _ Hes1) as (vs1 & e1 & es'1 & Hvs1 & He1 & Hes'1).
      rewrite Hes'1 in Heqes. rewrite <- app_assoc in Heqes.
      rewrite <- app_comm_cons in Heqes.
      apply first_values in Heqes as (Hvs & He & Hnil) => //=.
    (*  apply Logic.eq_sym, app_eq_nil in Hnil as [Hn1 Hn2].
    exists (ves ++ [AI_invoke a]). rewrite Hn2. rewrite app_nil_r.
    repeat split => //=. rewrite <- Heqf0. rewrite <- Heqf. rewrite Hes'1.
    rewrite Hn1. rewrite <- He. rewrite <- Hvs.
    by apply (r_invoke_host_diverge f H H0 H1 H2 H3 H4 H5).
    by left. rewrite H1. by apply v_to_e_is_const_list.*) *)
    - solve_prim_step_split_reduce_r H2 [AI_basic (BI_const v)] Heqf0.
      apply r_get_local. by rewrite <- Heqf0.
    - apply Logic.eq_sym, app_eq_nil in H5 as [Hn1 Hn2] ; rewrite Hn1 ; rewrite Hn2.
      left ; exists []. repeat split => //=. subst.
      by apply (r_set_local s H H0 H1).
    - solve_prim_step_split_reduce_r H2 [AI_basic (BI_const v)] Heqf0.
      apply r_get_global. by rewrite <- Heqf0.
    - solve_prim_step_split_reduce_r H3 ([] : seq.seq administrative_instruction)
                                     Heqf0.
      by apply r_set_global ; rewrite <- Heqf0.
    - solve_prim_step_split_reduce_r H5 [AI_basic (BI_const (wasm_deserialise bs t))]
                                     Heqf0.
      rewrite <- Heqf0.
      by apply (r_load_success a H H0).
    - solve_prim_step_split_reduce_r H5 [AI_trap] Heqf0.
      rewrite <- Heqf0.
      by apply (r_load_failure a H H0).
    - solve_prim_step_split_reduce_r H5 [AI_basic (BI_const (wasm_deserialise bs t))]
                                     Heqf0.
      rewrite <- Heqf0 ;
        by apply (r_load_packed_success a H H0).
    - solve_prim_step_split_reduce_r H5 [AI_trap] Heqf0 ;
        rewrite <- Heqf0 ; by apply (r_load_packed_failure a H H0).
    - solve_prim_step_split_reduce_r H7 ([] : seq.seq administrative_instruction) Heqf0.
      by rewrite <- Heqf0 ; apply (r_store_success a H H0 H1 H2).
    - solve_prim_step_split_reduce_r H7 [AI_trap] Heqf0 ;
        by rewrite <- Heqf0 ; apply (r_store_failure a H H0 H1 H2).
    - solve_prim_step_split_reduce_r H7 ([] : seq.seq administrative_instruction) Heqf0 ;
        by rewrite <- Heqf0 ; apply (r_store_packed_success a H H0 H1 H2).
    - solve_prim_step_split_reduce_r H7 [AI_trap] Heqf0 ;
        by rewrite <- Heqf0 ; apply (r_store_packed_failure a H H0 H1 H2).
    - apply Logic.eq_sym, app_eq_nil in H4 as [Hn1 Hn2] ; rewrite Hn1 ; rewrite Hn2.
      left ;
        exists [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin n))))].
      repeat split => //=. rewrite <- Heqf0. rewrite <- Heqf.
      by apply (r_current_memory H H0 H1).
    - apply Logic.eq_sym, app_eq_nil in H6 as [Hn1 Hn2] ; rewrite Hn1 ; rewrite Hn2.
      left ;
        exists [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin n))))].
      repeat split => //=. rewrite <- Heqf0. rewrite <- Heqf.
      by apply (r_grow_memory_success H H0 H1).
    - apply Logic.eq_sym, app_eq_nil in H5 as [Hn1 Hn2] ; rewrite Hn1 ; rewrite Hn2.
      left ; exists [AI_basic (BI_const (VAL_int32 int32_minus_one))].
      repeat split => //=. rewrite <- Heqf0. rewrite <- Heqf.
      by apply (r_grow_memory_failure (n := n) _ H H0).
    - unfold lfilled, lfill in H.
      destruct k.
      { destruct lh as [bef aft|] ; last by false_assumption.
        remember (const_list bef) as b eqn:Hbef ; destruct b ; last by false_assumption.
        move/eqP in H. rewrite H in Heqes.
        unfold lfilled, lfill in H0. rewrite <- Hbef in H0. move/eqP in H0.
        rewrite H0.       
        destruct bef.
        { destruct aft.
          { rewrite app_nil_l app_nil_r in Heqes.
            rewrite app_nil_l app_nil_r.
            rewrite H0 app_nil_l app_nil_r in Hlen.
            by apply IHHstep. }
          destruct es2. { left. exists (es' ++ (a0 :: aft)). repeat split => //=.
                          by rewrite app_nil_r. rewrite app_nil_r in Heqes.
                          rewrite <- Heqes.
                          apply (r_label (es:=es) (es':=es') (k:=0)
                                         (lh:=LH_base [] (a0::aft))).
                          by subst. unfold lfilled, lfill => //=.
                          unfold lfilled, lfill => //=. }
          get_tail a0 aft aft' ult Hult.
          get_tail a1 es2 es2' ult' Hult'.
          rewrite Hult in Heqes. rewrite Hult' in Heqes.
          rewrite app_nil_l in Heqes. do 2 rewrite app_assoc in Heqes.
          apply app_inj_tail in Heqes as [Heqes Hults].
          assert (prim_step ((a :: es1) ++ es2') (s,l,i) [] (es' ++ aft')
                            (s',l0,i0) []) as Hstep'.
          { repeat split => //=.
            simpl in Heqes. rewrite <- Heqes.
            apply (r_label (es:=es) (es':=es') (k:=0) (lh:=LH_base [] aft')) ;
              try by unfold lfilled, lfill ; simpl.
            by subst. } 
          assert (length (es' ++ aft') < len) as Hlen'.
          { rewrite H0 in Hlen. rewrite Hult in Hlen. rewrite app_nil_l in Hlen.
            rewrite app_assoc in Hlen. rewrite app_length in Hlen. simpl in Hlen.
            rewrite plus_comm in Hlen. rewrite Nat.add_1_l in Hlen.
            apply lt_S_n. assumption. } 
          destruct (IHlen es2' _ Hes1 (es' ++ aft') Hstep' Hlen')
            as [(es'' & Heq & Hred) | (n & m & lh & Hn & Hm & Hfill & Hcontext)].
          { left. rewrite Hult. rewrite Hult'. rewrite Hults.
            exists es''. repeat split => //=. rewrite app_assoc ; rewrite Heq.
            by rewrite app_assoc. }
          { right. rewrite Hult. rewrite Hult'. exists n, m.
            unfold lfilled, lfill. unfold lfilled, lfill in Hfill.
            destruct (const_list (take n (a :: es1))) ; last by false_assumption.
            simpl.
            move/eqP in Hfill ; rewrite app_assoc Hfill.
            rewrite <- app_assoc. rewrite <- (app_assoc [AI_trap]).
            rewrite Hults. exists lh.
            repeat split => //=. do 2 rewrite app_length. simpl in Hm.
            rewrite app_length in Hm. lia.
            cut (forall es0, m <= length es0 -> drop m es0 ++ [ult'] =
                                           drop m (es0 ++ [ult'])).
            intro Hdrop. rewrite (Hdrop ((a :: es1) ++ es2') Hm).
            rewrite <- app_assoc. rewrite app_comm_cons. done.
            clear Hm Hfill.
            induction m ; intros es0 Hm => //=.
            destruct es0 ; first by inversion Hm.
            simpl. apply IHm. simpl in Hm ; lia. }
        }
        inversion Heqes.
        remember (iris.to_val es1) as tv.
        destruct tv.
        { rewrite H3 in Hbef ; simpl in Hbef.
          apply Logic.eq_sym, andb_true_iff in Hbef as [Ha Hbef].
          destruct a ; try by inversion Ha.
          destruct b ; try by inversion Ha.
          unfold iris.to_val in Hes1. simpl in Hes1.
          rewrite merge_prepend in Hes1.
          unfold iris.to_val in Heqtv.
          destruct (merge_values_list _) eqn:Hmerge => //.
          inversion Heqtv ; subst v1.
          destruct v ; first by inversion Hes1.
          assert (to_val es1 = Some trapV) ;
            first by unfold to_val, iris.to_val ; rewrite Hmerge.
          
          apply to_val_trap_is_singleton in H2.
          rewrite H2 in H4.
          destruct bef ; last by inversion H4 as [[ Hhd Htl ]] ;
            simpl in Hbef ; apply andb_true_iff in Hbef as [Htrap _] ;
            rewrite Hhd in Htrap ; inversion Htrap.
          destruct es ; first by empty_list_no_reduce.
          inversion H4. subst a es2 es1 les' a0 les.
          right.
          remember (AI_trap :: es) as es0. clear IHHstep IHlen.
          exists 1. simpl.
          cut (forall n, (length es0 < n ->
                     exists m, 1 <= 2
                          /\ m <= S (S (length (es ++ aft)%list))
                          /\ lfilled 0
                                    (LH_base [AI_basic (BI_const v0)]
                                             (drop m ([AI_basic (BI_const v0) ; AI_trap]
                                                        ++ (es ++ aft))))
                                    [AI_trap] (AI_basic (BI_const v0) :: (es' ++ aft)%list)
                          /\ (s', l0, i0) = (s, l, i)
                          /\ opsem.reduce s
                                         {| f_locs := l ; f_inst := i |}
                                         [AI_basic (BI_const v0); AI_trap] s
                                         {| f_locs := l ; f_inst := i |} [AI_trap] /\
                            ([] : seq.seq administrative_instruction) = [] /\
                            ([] : seq.seq administrative_instruction) = [])).
          { intro Hn. assert (length es0 < S (length es0)) ; first lia.
            destruct (Hn _ H0) as (m & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7).
            exists m. repeat split => //=. exists (LH_base [AI_basic (BI_const v0)] []).
            unfold lfilled, lfill => //=. }
          intros len' Hlen'. clear H4 Hes1 Hbef Ha Heqtv Heqes H Hmerge.
          generalize dependent es0. generalize dependent es.
          generalize dependent es'. generalize dependent aft.
          induction len' ; intros aft es' Hlen es es0 Heqes0 Hstep Hlen' ; first lia.
          induction Hstep ; try by inversion Heqes0.
          { destruct H ; try by inversion Heqes0.
            destruct vs ; inversion Heqes0.
            rewrite H4 in H. simpl in H ; false_assumption.
            destruct vs ; inversion Heqes0.
            rewrite H4 in H ; simpl in H ; false_assumption.
            inversion Heqes0. rewrite H1 in H ; simpl in H ; false_assumption.
            exists (2 + length es).
            repeat split => //=. lia. rewrite app_length. lia.
            unfold lfilled, lfill. simpl. by rewrite drop_app.
            rewrite Heqf in Heqf0 ; by inversion Heqf0.
            apply r_simple. apply (rs_trap (lh := LH_base [AI_basic (BI_const v0)] [])).
            intro Habs ; inversion Habs. unfold lfilled, lfill => //=. }
          destruct ves ; inversion Heqes0.
          rewrite H10 in H1. cut (const_list (AI_trap :: ves) = true).
          intro Habs ; simpl in Habs ; false_assumption.
          rewrite H1 ; by apply v_to_e_is_const_list.
          destruct ves ; inversion Heqes0.
          rewrite H6 in H1. cut (const_list (AI_trap :: ves) = true).
          intro Habs ; simpl in Habs ; false_assumption.
          rewrite H1 ; by apply v_to_e_is_const_list.
(*        destruct ves ; inversion Heqes0.
        rewrite H10 in H2. cut (const_list (AI_trap :: ves) = true).
        intro Habs ; simpl in Habs ; false_assumption.
        rewrite H2 ; by apply v_to_e_is_const_list.*)
          unfold lfilled, lfill in H.
          destruct k.
          { destruct lh as [bef0 aft0 |] ; last by false_assumption.
            remember (const_list bef0) as b eqn:Hbef0 ; destruct b ; last by false_assumption.
            move/eqP in H. rewrite Heqes0 in H.
            unfold lfilled, lfill in H0. rewrite <- Hbef0 in H0.
            move/eqP in H0. rewrite H0.
            destruct bef0. {
              destruct aft0. {
                rewrite app_nil_l app_nil_r in H. subst.
                rewrite app_nil_l app_nil_r.
                apply IHHstep => //=. simpl in Hlen.
                repeat rewrite app_length in Hlen.
                rewrite app_length. lia. }
              clear IHHstep. destruct es.
              { destruct es0 ; first by empty_list_no_reduce.
                inversion H. apply Logic.eq_sym, app_eq_nil in H3 as [_ Habs].
                inversion Habs. }
              rewrite H in Heqes0.
              get_tail a0 es ys y Hy. rewrite Hy in H.
              get_tail a aft0 zs z Hz ; rewrite Hz in H.
              rewrite app_comm_cons in H. do 2 rewrite app_assoc in H.
              apply app_inj_tail in H as [Heq Hyz]. simpl in Heq.
              assert (reduce s f (es0 ++ zs) s' f' (es' ++ zs)).
              apply (r_label (es:=es0) (es':=es') (k:=0) (lh:=LH_base [] zs)) ;
                try done ;
                by unfold lfilled, lfill => //=.
              assert (length (es0 ++ zs) < len').
              rewrite Heqes0 in Hlen'. rewrite Hz in Hlen'. simpl in Hlen'.
              rewrite app_assoc in Hlen'. rewrite app_length in Hlen'. simpl in Hlen'.
              rewrite Nat.add_1_r in Hlen'. by apply lt_S_n.
              assert (length ([AI_basic (BI_const v0)] ++ (es' ++ zs)%SEQ ++ (z :: aft)%SEQ)%list < S len).
              subst les'. rewrite Hz in Hlen.
              repeat rewrite app_length in Hlen.
              repeat rewrite app_length.
              simpl in Hlen.
              simpl.
              lia.
              destruct (IHlen' (z :: aft) _ H2 ys (es0 ++ zs) (Logic.eq_sym Heq) H H1) as
                (m & Hn & Hm & Hfill & Hσ & Hred & _ & _).
              unfold lfilled, lfill in Hfill. simpl in Hfill.
              move/eqP in Hfill. simpl. rewrite (app_comm_cons es) Hy Hz Hyz.
              exists m. repeat split => //=.
              { replace (ys ++ (z :: aft)) with ((ys ++ [z]) ++ aft) in Hm ;
                  last by rewrite <- app_assoc.
                rewrite <- Hyz in Hm. rewrite <- Hy in Hm. simpl in Hm. lia. }
              unfold lfilled, lfill => //=. do 2 rewrite <- app_assoc => //=.
              rewrite app_assoc. rewrite Hfill. rewrite <- app_assoc => //=. }
            inversion H.
            rewrite <- H2 in Hbef0 ; simpl in Hbef0 ; inversion Hbef0. }
          { fold lfill in H. destruct lh ; first by false_assumption.
            remember (const_list l1) as b eqn:Hl1 ; destruct b ; last by false_assumption.
            remember (lfill k lh es0) as lfilledk ;
              destruct lfilledk ; last by false_assumption.
            move/eqP in H.
            rewrite Heqes0 in H. destruct l1 ; inversion H.
            rewrite <- H2 in Hl1 ; simpl in Hl1 ; inversion Hl1. }
          { simplify_eq. }
          { simplify_eq. }
          { simplify_eq. } }
        clear IHHstep.
        simpl in Hbef ; apply Logic.eq_sym, andb_true_iff in Hbef as [Ha Hbef].
        assert (prim_step (es1 ++ es2) (s, l, i) [] (bef ++ es' ++ aft)
                          (s', l0, i0) []).
        { repeat split => //=.
          apply (r_label (es:=es) (es':=es') (k:=0) (lh:=LH_base bef aft)) ;
            try by unfold lfilled, lfill ; rewrite Hbef ; try rewrite H4.
          by subst. }
        assert (length (bef ++ es' ++ aft) < len).
        { rewrite H0 in Hlen ; simpl in Hlen. by apply lt_S_n. }
        destruct (IHlen es2 es1 (Logic.eq_sym Heqtv) (bef ++ es' ++ aft) H2 H5)
          as [(es'' & Heq & Hred) | (n & m & lh & Hn & Hm & Hfill & Hcontext & Hσ)].
        { left. exists (a :: es''). repeat split => //=. by rewrite Heq.
          apply (r_label (es:= es1) (es':=es'') (k:=0) (lh:=LH_base [a] [])).
          by destruct Hred as (? & _ & _).
          unfold lfilled, lfill. simpl. subst. rewrite Ha => //=.
          by rewrite app_nil_r.
          unfold lfilled, lfill. simpl ; subst ; rewrite Ha => //=.
          by rewrite app_nil_r. }
        { right. exists (S n), (S m). 
          unfold lfilled, lfill. unfold lfilled, lfill in Hfill.
          subst. 
          simpl. rewrite Ha. destruct (const_list (take n es1)) ; last by false_assumption.
          simpl. move/eqP in Hfill.
          unfold lfilled, lfill in Hcontext.
          destruct lh ; last by false_assumption.
          exists (LH_base (a :: l1) l2).
          repeat split => //= ; try lia. by rewrite Hfill. unfold lfilled, lfill.
          simpl ; subst ; rewrite Ha. destruct (const_list l1) ; last by false_assumption.
          simpl. move/eqP in Hcontext ; by rewrite Hcontext. }
      }          
      clear IHHstep. fold lfill in H. destruct lh ; first by false_assumption.
      remember (const_list l1) as b eqn:Hl1 ; destruct b ; last by false_assumption.
      remember (lfill k lh es) as lfilledk ;
        destruct lfilledk ; last by false_assumption.
      move/eqP in H. rewrite H1 in H.
      destruct (first_non_value _ Hes1) as (vs & e & ult & Hvs & He & Hult).
      rewrite Hult in H. rewrite <- app_assoc in H. rewrite <- app_comm_cons in H.
      apply first_values in H as (Hvsl1 & Hlab & Hlast) => //= ; try by left.
      unfold lfilled, lfill in H0 ; fold lfill in H0.
      rewrite <- Hl1 in H0.
      remember (lfill k lh es') as lfilledk' ;
        destruct lfilledk' ; last by false_assumption.
      move/eqP in H0.
      left ; exists (l1 ++ AI_label n l2 l5 :: ult).
      repeat split => //=.
      rewrite <- app_assoc. rewrite <- app_comm_cons. by rewrite Hlast.
      rewrite Hult. rewrite Hlab. rewrite Hvsl1.
      apply (r_label (es:=es) (es':=es') (k:=S k) (lh:=LH_rec l1 n l2 lh ult)) ;
        first (by subst) ;
        unfold lfilled, lfill ; fold lfill ; rewrite <- Hl1.
      by rewrite <- Heqlfilledk.
      by rewrite <- Heqlfilledk'.
      intros ; unfold to_val in He.
      destruct He as [? | ?].
      assert (const_list [e]) ; first by unfold const_list => /= ; rewrite H2.
      apply const_list_to_val in H4 as [??] ; congruence.
      subst ; by unfold iris.to_val in H2.
      unfold iris.to_val => /=.
    (*    destruct (merge_values_list _) ; try by intros [? ?].
    destruct v ; try by intros [? ?].
    destruct i1 ; try by intros [? ?].
    destruct (vh_decrease _) ; try by intros [? ?]. *)
    - solve_prim_step_split_reduce_r H1 [AI_local n f' es'] Heqf0.
      by apply r_local.
  Qed.

  
  Lemma reduce_ves: forall v es es' σ σ' efs obs,
      reducible es σ ->
      prim_step ([AI_basic (BI_const v)] ++ es) σ obs es' σ' efs ->
      (es' = [AI_basic (BI_const v)] ++ drop 1 es' /\ prim_step es σ obs (drop 1 es') σ' efs)
      \/ (exists lh lh', lfilled 0 lh [AI_trap] es' /\ lfilled 0 lh' [AI_trap] es /\ σ = σ'). (* prim_step es σ obs [AI_trap] σ' efs). *)
  Proof.
    cut (forall n v es es' σ σ' efs obs,
            length es < n ->
            reducible es σ ->
            prim_step ([AI_basic (BI_const v)] ++ es) σ obs es' σ' efs ->
            (es' = [AI_basic (BI_const v)] ++ drop 1 es' /\
               prim_step es σ obs (drop 1 es') σ' efs)
            \/ (exists lh lh', lfilled 0 lh [AI_trap] es' /\
                           lfilled 0 lh' [AI_trap] es /\ σ = σ')). (* prim_step es σ obs [AI_trap] σ' efs)). *)
    { intros H v es es' σ σ' efs obs. apply (H (S (length es)) v es). lia. } 
    intro len. induction len.
    { intros v es es' σ σ' efs obs Habs ; inversion Habs. }
    intros v es es' σ σ' efs obs Hlen Hes Hves.
    destruct Hes as (obs0 & es0 & σ0 & efs0 & H).
    unfold prim_step, iris.prim_step in Hves.
    destruct σ as [[[??]?]?].
    destruct σ' as [[[??]?]?]. 
    destruct Hves as (Hred & Hobs & Hefs).
    remember ([AI_basic (BI_const v)] ++ es)%list as ves.
    remember {| f_locs := l ; f_inst := i |} as f.
    remember {| f_locs := l0 ; f_inst := i0 |} as f0.
    induction Hred as [e e' s f Hredsimpl | | | | |
                        a cl t1s t2s ts es' ves vcs n m k zs s f f' i' Hlistcl Hcl Hves
                          Hvcs Hts Ht1s Ht2s Hzts Hinst Hlocs |
                        a cl h t1s t2s ves vcs m n s f Hlistcl Hcl Hves Hvcs
                          Ht1s Ht2s |
                      (*  a cl t1s t2s h ves vcs n m s f hs hs' Hlistcl Hcl Hves Hvcs Ht1s
                          Ht2s Hhost | *)
                      | | | | | | | | | | | | | | | 
                        s f ces les s' f' ces' les' k lh Hred IHreduce Hles Hles' | ] ;
      (try by inversion Heqves );
      (try by exfalso ; unfold language.prim_step, wasm_lang, iris.prim_step in H ;
       destruct σ0 as [[[??]?]?] ; destruct H as (Hred0 & Hobs0 & Hefs0) ;
       inversion Heqves as [[ Hhd Htl ]] ; no_reduce Htl Hred0 ).
    {  unfold language.prim_step, wasm_lang, iris.prim_step in H ;
         destruct σ0 as [[[??]?]?] ; destruct H as (Hred0 & Hobs0 & Hefs0).
       destruct Hredsimpl as [ | | | | | | | | | | | | | |
                               vs es' n m t1s t2s Hconst Hlenvs Ht1s Ht2s |
                               vs es' n m t1s t2s Hconst Hlenvs Ht1s Ht2s |
                             | | | | | | | | | | | | | ] ;
         inversion Heqves as [[ Hhd Htl ]] ;
         (try by exfalso ; no_reduce Htl Hred0).
       { destruct es. { rewrite app_nil_r in Heqves ;
                          rewrite <- app_nil_l in Heqves ; apply app_inj_tail in Heqves ;
                          destruct Heqves as [_ Habs] ; inversion Habs. }
         get_tail a es b l' Htail ; rewrite Htail in Heqves ;
           rewrite app_assoc in Heqves ; apply app_inj_tail in Heqves ;
           destruct Heqves as [Hvs Hl'] ; rewrite Htail in Hred0 ;
           rewrite <- Hl' in Hred0.
         remember {| f_locs := l0 ; f_inst := i0 |} as f'.
         exfalso.
         apply (block_not_enough_arguments_no_reduce _ _ _ _ _ _ _ _ _ Hred0).
         - rewrite Hvs in Hconst ; unfold const_list in Hconst ;
             rewrite forallb_app in Hconst ; apply andb_true_iff in Hconst ;
             destruct Hconst as [_ Hconst] ; exact Hconst.
         - rewrite Hvs in Hlenvs ; simpl in Hlenvs ; lia.
       }
       { destruct es. { rewrite app_nil_r in Heqves ; rewrite <- app_nil_l in Heqves ;
                          apply app_inj_tail in Heqves ; destruct Heqves as [_ Habs ] ;
                          inversion Habs. }
         get_tail a es b l' Htail ; rewrite Htail in Heqves ;
           rewrite app_assoc in Heqves ; apply app_inj_tail in Heqves ;
           destruct Heqves as [Hvs Hl'] ; rewrite Htail in Hred0 ;
           rewrite <- Hl' in Hred0 ; exfalso ;
           apply (loop_not_enough_arguments_no_reduce _ _ _ _ _ _ _ _ _ Hred0).
         - rewrite Hvs in Hconst ; unfold const_list in Hconst ;
             rewrite forallb_app in Hconst ; apply andb_true_iff in Hconst ;
             destruct Hconst as [_ Hconst] ; exact Hconst.
         - rewrite Hvs in Hlenvs ; simpl in Hlenvs ; lia.
       }
       { right. exists (LH_base [] []).
         unfold lfilled, lfill in H0. destruct lh ; last by false_assumption.
         remember (const_list l2) as b eqn:Hl2.
         destruct b ; last by false_assumption.
         move/eqP in H0.
         destruct l2 ; rewrite H0 in Heqves ; inversion Heqves as [[ Ha Hes ]].
         exists (LH_base l2 l3). split => //=.
         unfold lfilled, lfill.
         simpl in Hl2 ; apply Logic.eq_sym, andb_true_iff in Hl2 as [_ Hl2] ; rewrite Hl2; subst; split => //.
         by inversion Heqf0.
       (* rewrite <- Heqf0 ; rewrite <- Heqf. apply r_simple.
      apply (rs_trap (lh:= LH_base l2 l3)). intro Htrap ; rewrite Htrap in Hes.
      no_reduce Hes Hred0.
      unfold lfilled, lfill. simpl in Hl2.
      apply Logic.eq_sym in Hl2.
      apply andb_true_iff in Hl2 as [_ Hl2]. by rewrite Hl2. *)
       }
    }
    { exfalso. destruct es. { rewrite app_nil_r in Heqves ;
                                rewrite <- app_nil_l in Heqves ;
                                apply app_inj_tail in Heqves ;
                                destruct Heqves as [_ Habs] ; inversion Habs. }
      get_tail a0 es b l' Htail. rewrite Htail in Heqves.
      rewrite app_assoc in Heqves. apply app_inj_tail in Heqves.
      destruct Heqves as [Hvs Hl'].
      unfold language.prim_step, wasm_lang, iris.prim_step in H ;
        destruct σ0 as [[[??]?]?] ;
        destruct H as (Hred0 & Hobs0 & Hefs0). rewrite Htail in Hred0.
      rewrite <- Hl' in Hred0. rewrite Hcl in Hlistcl.
      apply (invoke_not_enough_arguments_no_reduce_native
               _ _ _ _ _ _ _ _ _ _ _ _ Hlistcl Hred0).
      + assert (const_list ves). rewrite Hves. apply v_to_e_is_const_list.
        rewrite Hvs in H. unfold const_list in H. rewrite forallb_app in H.
        apply andb_true_iff in H. destruct H as [ _ H ] ; exact H.
      + rewrite Ht1s. assert (length vcs = length ves).
        rewrite Hves. rewrite v_to_e_length. trivial.
        rewrite Hvs in H. rewrite app_length in H. simpl in H. lia.
    }
       { exfalso. destruct es. { rewrite app_nil_r in Heqves ;
                                rewrite <- app_nil_l in Heqves ;
                                apply app_inj_tail in Heqves ;
                                destruct Heqves as [_ Habs] ; inversion Habs. }
      get_tail a0 es b l' Htail. rewrite Htail in Heqves.
      rewrite app_assoc in Heqves. apply app_inj_tail in Heqves.
      destruct Heqves as [Hvs Hl'].
      unfold language.prim_step, wasm_lang, iris.prim_step in H ;
        destruct σ0 as [[[??]?]?] ;
        destruct H as (Hred0 & Hobs0 & Hefs0). rewrite Htail in Hred0.
      rewrite <- Hl' in Hred0. rewrite Hcl in Hlistcl.
      apply (invoke_not_enough_arguments_no_reduce_host
               _ _ _ _ _ _ _ _ _ _ Hlistcl Hred0).
      + assert (const_list ves). rewrite Hves. apply v_to_e_is_const_list.
        rewrite Hvs in H. unfold const_list in H. rewrite forallb_app in H.
        apply andb_true_iff in H. destruct H as [ _ H ] ; exact H.
      + rewrite Ht1s. assert (length vcs = length ves).
        rewrite Hves. rewrite v_to_e_length. trivial.
        rewrite Hvs in H. rewrite app_length in H. simpl in H. lia.
    }
    unfold lfilled, lfill in Hles.
    destruct k. {
      destruct lh as [bef aft|] ; [| exfalso ; false_assumption ].
      remember (const_list bef) as b eqn:Hbef.
      destruct b ; [| exfalso ; false_assumption].
      move/eqP in Hles.
      unfold lfilled, lfill in Hles'. rewrite <- Hbef in Hles'.
      move/eqP in Hles'.
      rewrite Hles in Heqves.
      destruct bef.
      { destruct ces ; first by empty_list_no_reduce.
        inversion Heqves as [[ Ha Hes ]].
        destruct aft. { subst. repeat rewrite app_nil_r.
                        repeat rewrite app_nil_r in IHreduce.
                        rewrite app_nil_r in H.
                        apply IHreduce => //=. }
        remember (to_val ces) as tv.
        destruct tv.
        { destruct v0. { apply Logic.eq_sym, to_val_const_list in Heqtv.
                         exfalso ; values_no_reduce.
                         simpl. apply andb_true_iff ; split => //=.
                         by rewrite Ha. }
          apply Logic.eq_sym, to_val_trap_is_singleton in Heqtv.
          subst => //=.
          right. exists (LH_base [] (a0 :: aft)), (LH_base [] (a0 :: aft)).
          split ; unfold lfilled, lfill => //=.
          remember [AI_basic (BI_const v) ; AI_trap] as ces.
          remember {| f_locs := l ; f_inst := i |} as f.
          remember {| f_locs := l0 ; f_inst := i0 |} as f'.
          replace [AI_basic (BI_const v) ; AI_trap] with
            ([AI_basic (BI_const v)] ++ [AI_trap]) in Heqces => //=.
          induction Hred ; try by inversion Heqces ;
            try by apply app_inj_tail in Heqces as [_ Habs] ; inversion Habs.
          { destruct H0 ; try by inversion Heqces ;
              try by apply app_inj_tail in Heqces as [_ Habs] ; inversion Habs. }
          (*       
          repeat split => //=.
          unfold lfilled, lfill => //=.
          apply r_simple, (rs_trap (lh:=LH_base [] (a0 :: aft))) => //=.
          unfold lfilled, lfill => //=. } *)
          rewrite Heqces in H0. simple_filled H0 k lh bef0 aft0 n0 ll0 ll0'.
          destruct bef0. { destruct es ; first by empty_list_no_reduce.
                           inversion H0.
                           apply Logic.eq_sym, app_eq_unit in H4 as [[Hes Haft]|[Hes Haft]].
                           subst. remember [AI_basic (BI_const v)] as ev.
                           apply Logic.eq_sym in Heqev.
                           exfalso ; no_reduce Heqev Hred.
                           unfold lfilled, lfill in H1.
                           simpl in H1. move/eqP in H1. subst.
                           rewrite app_nil_r. 
                           apply IHHred => //=. }
          inversion H0.
          apply Logic.eq_sym, app_eq_unit in H4 as [[ Hb Hes ]|[Hb Hes]].
          apply app_eq_unit in Hes as [[ Hes _ ]|[Hes _]].
          subst ; empty_list_no_reduce.
          subst ; remember [AI_trap] as ev ; apply Logic.eq_sym in Heqev ;
            exfalso ; no_reduce Heqev Hred.
          apply app_eq_nil in Hes as [ Hes _].
          subst ; empty_list_no_reduce.
          split => //.
          apply AI_trap_reduce_det in Hred.
          by inversion Hred; subst.
          { simplify_eq. exfalso. unfold to_val, iris.to_val in Heqtv.
            apply reduce_val_false in Hred;[done|].
            unfold iris.to_val => /=.
            rewrite merge_prepend.
            destruct (merge_values_list _) => //.
            inversion Heqtv => //=. }
          { simplify_eq. exfalso. unfold to_val, iris.to_val in Heqtv.
            apply reduce_val_false in Hred;[done|].
            unfold iris.to_val => /=.
            rewrite merge_prepend.
            destruct (merge_values_list _) => //.
            inversion Heqtv => //=. }
              { simplify_eq. exfalso. unfold to_val, iris.to_val in Heqtv.
            apply reduce_val_false in Hred;[done|].
            unfold iris.to_val => /=.
            rewrite merge_prepend.
            destruct (merge_values_list _) => //.
            inversion Heqtv => //=. }
        }
        rewrite <- Hes in H.
        destruct (prim_step_split_reduce_r _ _ _ _ _ _ _ (Logic.eq_sym Heqtv) H) as
          [ (es' & H1 & H2) | (n & m & lh & H1 & H2 & Hσ) ].
        { assert (reducible ces (s,l,i)).
          unfold reducible, language.reducible. exists obs0, es', σ0, efs0 => //=.
          assert (prim_step ([AI_basic (BI_const v)] ++ ces) (s,l,i) [] ces'
                            (s',l0,i0) []).
          repeat split => //=. by subst.
          assert (length ces < len) as Hlences.
          rewrite <- Hes in Hlen. rewrite app_length in Hlen. simpl in Hlen ; lia.
          destruct (IHlen v ces ces' (s,l,i) _ _ _ Hlences H0 H3) as
            [[Hdrop Hstep] | (lh & lh' & Hfill & Hfill' & Hσ) ].
          { left. subst. repeat split => //=.
            rewrite Hdrop. rewrite <- app_assoc => //=.
            replace (drop 1 (ces' ++ (a0 :: aft)%SEQ)%list) with ((drop 1 ces') ++ a0 :: aft).
            apply (r_label (es:=ces) (es':= drop 1 ces') (k:=0)
                           (lh:=LH_base [] (a0 :: aft))) => //=.
            by destruct Hstep as (? & _ & _).
            unfold lfilled, lfill => //=. unfold lfilled, lfill => //=.
            destruct ces' => //=. }
          { right. subst. unfold lfilled, lfill in Hfill, Hfill'.
            destruct lh ; last by false_assumption.
            destruct lh'; last by false_assumption.
            remember (const_list l1) as b eqn:Hl1 ; destruct b ; last by false_assumption.
            remember (const_list l3) as b eqn:Hl3 ; destruct b ; last by false_assumption.
            move/eqP in Hfill. move/eqP in Hfill'.
            exists (LH_base l1 (l2 ++ a0 :: aft)), (LH_base l3 (l4 ++ a0 :: aft)).
            split => //= ; unfold lfilled, lfill => //=.
            rewrite <- Hl1 ; rewrite Hfill ; by rewrite <- app_assoc.
            rewrite <- Hl3 ; rewrite Hfill' ; by rewrite <- app_assoc. }
        }
        right. unfold lfilled, lfill in H2.
        destruct lh as [bef0 aft0|] ; last by false_assumption.
        remember (const_list bef0) as b eqn:Hbef0 ; destruct b ; last by false_assumption.
        move/eqP in H2.
        assert (lfilled 0 (LH_base (a :: bef0) aft0) [AI_trap] (a::ces)) as Htrap.
        { subst. unfold lfilled, lfill => //=. by rewrite <- Hbef0. }
        destruct (trap_reduce _ _ (a :: ces) _ _ ces' _ Htrap Hred) as (lh' & Hfill' & Hσ').
        unfold lfilled, lfill in Hfill'. destruct lh' ; last by false_assumption.
        remember (const_list l1) as b eqn:Hl1 ; destruct b ; last by false_assumption.
        move/eqP in Hfill'.
        exists (LH_base l1 (l2 ++ a0 :: aft)), (LH_base bef0 (aft0 ++ a0 :: aft)).
        split ; unfold lfilled, lfill => //=. rewrite <- Hl1. rewrite Hles'.
        rewrite Hfill'. simpl. by rewrite <- app_assoc.
        rewrite <- Hbef0. rewrite H2. rewrite <- app_assoc. split => //.
        inversion Hσ'; subst. by inversion H4.
      }
      inversion Heqves ; subst. left. repeat split => //=.
      unfold drop.
      apply (r_label (es:=ces) (es':=ces') (k:=0) (lh:=LH_base bef aft)) ; (try done) ;
        unfold lfilled, lfill ; simpl in Hbef ; rewrite <- Hbef => //=. }
    fold lfill in Hles. destruct lh ; first by false_assumption.
    remember (const_list l1) as b ; destruct b ; last by false_assumption.
    remember (lfill k lh ces) as filled ;
      destruct filled ; last by false_assumption.
    move/eqP in Hles. unfold lfilled, lfill in Hles'. fold lfill in Hles'.
    rewrite <- Heqb in Hles'. remember (lfill k lh ces') as filled'.
    destruct filled' ; last by false_assumption.
    move/eqP in Hles'. rewrite Hles in Heqves.
    destruct l1 ; inversion Heqves as [[ Ha Hes ]].
    rewrite Hles'. rewrite Ha. simpl. unfold drop.
    left ; repeat split => //=.
    rewrite Heqf in Hred ; rewrite Heqf0 in Hred.
    simpl in Heqb ; apply Logic.eq_sym in Heqb ;
      apply andb_true_iff in Heqb ; destruct Heqb as [_ Heqb].
    apply (r_label (lh := LH_rec l1 n l2 lh l3) (k := S k) Hred) ;
      unfold lfilled, lfill ; rewrite Heqb ; fold lfill.
    rewrite <- Heqfilled ; trivial.
    rewrite <- Heqfilled' ; trivial.
  Qed.

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
        intros Hconst ; apply const_list_singleton, const_list_to_val in Hconst as [??] ;
          unfold to_val in He ; destruct He as [? | ?] ; [congruence | subst] => //.
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
        intros Hconst ; apply const_list_singleton, const_list_to_val in Hconst as [??] ;
          unfold to_val in He ; destruct He as [? | ?] ; [congruence | subst] => //.
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
        intros Hconst ; apply const_list_singleton, const_list_to_val in Hconst as [??] ;
          unfold to_val in He ; destruct He as [?|?] ; [congruence | subst] => //.
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
      intros Hconst ; apply const_list_singleton, const_list_to_val in Hconst as [??] ;
        unfold to_val in He ; destruct He as [?|?] ; [congruence | subst] => //.
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
      intros Hconst ; apply const_list_singleton, const_list_to_val in Hconst as [??] ;
        unfold to_val in He ; destruct He as [?|?] ; [congruence | subst] => //.
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
        intros Hconst ; apply const_list_singleton, const_list_to_val in Hconst as [??] ;
          unfold to_val in He ; destruct He as [?|?] ; [congruence | subst] => //.
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
        intros Hconst ; apply const_list_singleton, const_list_to_val in Hconst as [??] ;
          unfold to_val in He ; destruct He as [?|?] ; [congruence | subst] => //.
      + by const_list_app.
  Qed.

  



  (* last remaining admits for the control flow lemmas! it roughly should state the following: 
   if there is a reducible hole in some expression LI (first on its own, second within a local frame), 
   then the reduction of LI is exactly the reduction of that hole. 

   It ought to be the generalized versions of prim_step_split_reduce_r.
   *)


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
  

End split_reduce_properties.
