From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export stdpp_aux iris_reduce_properties.


Ltac solve_prim_step_split_reduce_r H objs Heqf0 :=
  left ; subst ;
  apply Logic.eq_sym, app_eq_nil in H as [? ?] ;
  exists objs ; subst ; rewrite app_nil_r ;
  repeat split => //= ; rewrite Heqf0.


Section split_reduce_properties.
  
  Let reducible := @iris.program_logic.language.reducible wasm_lang.

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
        destruct e1 => //. destruct b => //.
        destruct e1 => //. 
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
        destruct e1 => //. destruct b => //. destruct e1 => //. 
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
        destruct e1 => // ; destruct b => //. destruct e1 => //. }
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
      destruct e1 => // ; destruct b => //. destruct e1 => //. 
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
      destruct e1 => // ; destruct b => //. destruct e1 => //. 
      rewrite H1. by apply v_to_e_is_const_list. 
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
        exists [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (ssrnat.nat_of_bin n)))))].
      repeat split => //=. rewrite <- Heqf0. rewrite <- Heqf.
      by apply (r_current_memory H H0 H1).
    - apply Logic.eq_sym, app_eq_nil in H6 as [Hn1 Hn2] ; rewrite Hn1 ; rewrite Hn2.
      left ;
        exists [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (ssrnat.nat_of_bin n)))))].
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
      destruct e => //. destruct b => //. destruct e => //. 
      unfold iris.to_val => /=.
    - solve_prim_step_split_reduce_r H1 [AI_local n f' es'] Heqf0.
      by apply r_local.
  Qed.

  
  Lemma reduce_ves: forall v es es' σ σ' efs obs,
      reducible es σ ->
      prim_step ([AI_basic (BI_const v)] ++ es) σ obs es' σ' efs ->
      (es' = [AI_basic (BI_const v)] ++ drop 1 es' /\ prim_step es σ obs (drop 1 es') σ' efs)
      \/ (exists lh lh', lfilled 0 lh [AI_trap] es' /\ lfilled 0 lh' [AI_trap] es /\ σ = σ'). 
  Proof.
    cut (forall n v es es' σ σ' efs obs,
            length es < n ->
            reducible es σ ->
            prim_step ([AI_basic (BI_const v)] ++ es) σ obs es' σ' efs ->
            (es' = [AI_basic (BI_const v)] ++ drop 1 es' /\
               prim_step es σ obs (drop 1 es') σ' efs)
            \/ (exists lh lh', lfilled 0 lh [AI_trap] es' /\
                           lfilled 0 lh' [AI_trap] es /\ σ = σ')).
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

  




End split_reduce_properties.
