From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap proph_map.
Require Export stdpp_aux.
Require Export datatypes operations properties opsem.
Require Import iris_reduce_properties iris_wasm_lang_properties iris_reduction_core iris_split_reduce.



(* Knowing hypothesis "Hred : objs -> _" (with frames (locs, inst) and (locs', inst')),
   attempts to exfalso away most of the possible ways Hred could hold, leaving the user
   with only the one possible desired case. Tactic will also attempt to trivially solve
   this one case, but may give it to user if attempt fails. *)

Ltac only_one_reduction Heqes0 Hred :=
  let a := fresh "a" in
  let aft := fresh "aft" in
  let bef := fresh "bef" in
  let e := fresh "e" in
  let e' := fresh "e'" in
  let es := fresh "es" in
  let es' := fresh "es" in
  let es0 := fresh "es" in
  let es1 := fresh "es" in
  let es2 := fresh "es" in
  let f := fresh "f" in
  let f' := fresh "f" in
  let g := fresh "g" in
  let H := fresh "H" in
  let H0 := fresh "H" in
  let H1 := fresh "H" in
  let Hconst := fresh "Hconst" in
  let Heqes2 := fresh "Heqes" in
  let Heqf := fresh "Heqf" in
  let Heqf' := fresh "Heqf" in
  let Heqg := fresh "Heqg" in
  let Ht1s := fresh "Ht1s" in
  let Ht2s := fresh "Ht2s" in
  let Hvs := fresh "Hvs" in
  let Hxl1 := fresh "Hxl1" in
  let IHreduce := fresh "IHreduce" in
  let k := fresh "k" in
  let l := fresh "l" in
  let l' := fresh "l" in
  let les := fresh "les" in
  let les' := fresh "les" in
  let lh := fresh "lh" in
  let m := fresh "m" in
  let n0 := fresh "n" in
  let n' := fresh "n" in
  let s := fresh "s" in
  let s' := fresh "s'" in
  let t1s := fresh "t1s" in
  let t2s := fresh "t2s" in
  let vs := fresh "vs" in
  induction Hred as [e e' s ? H | | | | | a | a | a | | | | | | | | | | | | | | |
                      s ? es les s' f' es' les' k lh Hred IHreduce H0 H1 | ];
  (* induction on the reduction. Most cases will be trivially solved by the following
     two attemps : *)
  (try by inversion Heqes0) ;
  (try by found_intruse (AI_invoke a) Heqes0 Hxl1) ;
  (* reduce_simple case : *)
  first (destruct H as [ | | | | | | | | | | | | | | 
                         vs es n' m t1s t2s Hconst Hvs Ht1s Ht2s |
                         vs es n' m t1s t2s Hconst Hvs Ht1s Ht2s |
                       | | | | | | | | | | | | | 
                         es' lh Htrap' H0 ]  ;
         (* by case_analysis on the reduce_simple. most cases solved by just the 
            following inversion ; some cases need a little extra help *)
         inversion Heqes0 ; 
         (try by subst ; found_intruse (AI_basic (BI_block (Tf t1s t2s) es)) Heqes0 Hxl1) ;
         (try by subst ; found_intruse (AI_basic (BI_loop (Tf t1s t2s) es)) Heqes0 Hxl1) ;
         (try by subst ; filled_trap H0 Hxl1) ) ;
  (* lfilled case *)
  last (rewrite <- Heqes0 in H0 ;
        (* the simple_filled tactic unfolds lfilled, solves the case where k>0,
           and in the case k=0 leaves user with hypothesis H0 modified to now be
           les = bef ++ es ++ aft *)
        simple_filled2 H0 k lh bef aft n0 l l' ;
        first
          ( apply Logic.eq_sym in H0 ;
            remember ([] : seq.seq administrative_instruction) as g eqn:Heqg in s;
            let rec auxb H0 :=
              (* We maintain as an invariant that when auxb H0 is called,
                 H0 is the hypothesis "H0 : bef ++ es ++ aft = [some explicit sequence]" *)
              ( let b0 := fresh "b" in
                let Hb0 := fresh "Hb" in
                let H2 := fresh "H" in
                destruct bef as [| b0 bef ] ;
                [ (* case bef = []. Our invariant gives us that
                     "H0 : es ++ aft = [some explicit sequence]".
                     Recall g was defined as [] with "Heqg : g = []". *)
                  let rec auxe H0 g Heqg :=
                    (* We maintain as an invariant than when auxe H0 g Heqg is called,
                       H0 is the hypothesis "H0 : es ++ aft = [some explicit sequence]",
                       Hred is the hypothesis "Hred : (g ++ es) -> es'",
                       and Heqg is "Heqg : g = [some (other) explicit sequence]" *)
                    ( let e0 := fresh "e" in
                      let g' := fresh "g" in
                      let He0 := fresh "He" in
                      let Heqg' := fresh "Heqg" in
                      let H2 := fresh "H" in
                      destruct es as [| e0 es] ;
                      [ (* case es = []. Our invariants give us that
                           "Hred : g -> es' " with g described explicitly in Heqg.
                           Thus to conclude, we can … *)
                        rewrite <- Heqg in Hred ;
                        remember g as es2 eqn:Heqes2 in Hred ;
                        apply Logic.eq_sym in Heqes2 ;
                        rewrite Heqg in Heqes2 ;
                        (* use our induction hypothesis 
                           (case where bef = aft = []), or …  *)
                        (( by (try rewrite H0) ; simpl in H0 ; rewrite H0 in H1 ;
                           unfold lfilled, lfill in H1 ;
                           destruct (const_list []) ; [| false_assumption] ;
                           move/eqP in H1 ; rewrite H1 ; rewrite app_nil_r ;
                           apply IHreduce ; subst ; trivial) +
                           (* use no_reduce (case where bef or aft is nonempty, and thus
                              g is shorter than the original objs). Strict subsequences
                              of valid reduction sequences tend to not reduce, so this
                              will work most of the time *)
                           (exfalso ; no_reduce Heqes2 Hred) )
                      | (* case es = e0 :: es. Our invariant gives us that
                           "H0 : e0 :: es ++ aft = [some explicit sequence]". We can
                           try to conclude by inverting H0, in case the explicit sentence is
                           empty *)
                        (by inversion H0) +
                          (* else, we know the explicit sentence is nonempty. 
                             Now by inverting H0 we get 
                             "H2 : es ++ aft = [some shorter explicit sequence]"
                             The invariant also gives us
                             "Hred : (g ++ e0 :: es) -> es'", so to maintain the invariant  
                             we define g' to be g ++ [e0] and create an equation Heqg' that
                             describes g' explicitly *)
                          ( inversion H0 as [[ He0 H2 ]] ;
                            rewrite He0 in Hred ;
                            remember (g ++ [e0]) as g' eqn:Heqg' ;
                            rewrite Heqg in Heqg' ;
                            rewrite He0 in Heqg' ;
                            simpl in Heqg' ;
                            (* we can now make a recursive call to auxe. The length of the
                               explicit list in H2 has strictly decreased *)
                            auxe H2 g' Heqg'
                          )
                      ]
                    ) in auxe H0 g Heqg
                | (* case bef = b0 :: bef. Our invariant gives us that
                     "H0 : b0 :: bef ++ es ++ aft = [some explicit sequence]".
                     We can attempt to conclude by inverting H0, which will work if
                     the explicit sequence is empty *)
                  (by inversion H0 ) +
                    (* else, we know the explicit sequence is nonempty, so by inverting
                       H0, we get "H2 : bef ++ es ++ aft = [some explicit sequence]" *)
                    ( inversion H0 as [[ Hb0 H2 ]] ;
                      auxb H2 )
                ]
              ) in auxb H0
          )
       ). 

Ltac only_one objs Hred2 :=
  let es := fresh "es" in
  let Heqes := fresh "Heqes" in
  left ; remember objs as es eqn:Heqes ;
  apply Logic.eq_sym in Heqes ;
  only_one_reduction Heqes Hred2.

Section determ.
  
  Let reducible := @reducible wasm_lang.

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.

  
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

  
  Lemma invoke_native_det ws2 f2 es2 s a f f' t1s t2s ts es vcs:
    nth_error (s_funcs s) a = Some (FC_func_native (f_inst f') (Tf t1s t2s) ts es) ->
    length t1s = length vcs ->
    f_locs f' = (vcs ++ n_zeros ts) ->
    reduce s f (v_to_e_list vcs ++ [AI_invoke a]) ws2 f2 es2 ->
    (s, f, [AI_local (length t2s) f' [AI_basic (BI_block (Tf [] t2s) es)]]) = (ws2, f2, es2).
  Proof.
    remember (v_to_e_list vcs ++ [AI_invoke a])%SEQ as es0.
    move => Hnth Hlen Hflocs Hred.
    induction Hred ; try by do 4 destruct vcs => //; try by inversion Heqes0 ;
                                                try by (apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs).
    (* 3 remaining cases *)
    (* reduce_simple *)
    { destruct H ; (try by inversion Heqes0) ;
      (try by do 5 destruct vcs => //=);
      (try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs).
      rewrite Heqes0 in H0 ; filled_trap H0 Hxl1.
      apply in_app_or in Hxl1.
      destruct Hxl1; try by simpl in H1; destruct H1.
      apply const_list_In in H1 => //.
      by apply v_to_e_is_const_list. }
    (* Invoke native, the desired case *)
    { apply app_inj_tail in Heqes0 as [-> Habs]; inversion Habs; subst.
      apply v_to_e_inj in H1; subst.
      rewrite Hnth in H.
      inversion H; subst; clear H.
      do 3 f_equal. 
      destruct f', f'0. simpl in H1, H4, H8; by subst; f_equal.
    }
    { apply app_inj_tail in Heqes0 as [-> Ha].
      inversion Ha ; subst.
      rewrite Hnth in H ; done. } 
    (* r_label *)
    {
      rewrite Heqes0 in H. simple_filled H k lh bef aft nn ll ll'.
      (* es0 is either a const which can be handled by Hred, or AI_invoke
         which we can then apply the IH. *)
      - unfold lfilled, lfill in H0.
        rewrite Hvs in H0.
        move/eqP in H0.
        (* If both aft and bef are empty (trivial r_label), we can just apply the IH; this is also the only place where IH is ever needed. Otherwise, if bef is shorter, we do not have enough arguments; on the other hand, aft cannot be non-empty since AI_invoke is the last non-const instruction. *)
        destruct aft as [| ea aft]. { destruct bef as [| eb bef]. { rewrite app_nil_l app_nil_r in H0.
                                                                    subst.
                                                                    rewrite app_nil_l app_nil_r in H.
                                                                    by apply IHHred.
          }
          destruct es0 ; first by empty_list_no_reduce.
                                      exfalso.
                                      get_tail a0 es0 ys y Htail.
                                      rewrite Htail app_nil_r in H. 
                                      rewrite app_assoc in H. apply app_inj_tail in H as [Hvs' Hy].
                                      rewrite Htail in Hred. rewrite <- Hy in Hred.
                                      eapply invoke_not_enough_arguments_no_reduce_native => //=.
                                      - assert (const_list (v_to_e_list vcs)) as Hconst; first by apply v_to_e_is_const_list.           
                                        rewrite Hvs' in Hconst.
                                        unfold const_list in Hconst. rewrite forallb_app in Hconst.
                                        by apply andb_true_iff in Hconst as [_ Hys].
                                      - rewrite Hlen.
                                        replace (length vcs) with (length (v_to_e_list vcs)); last by apply v_to_e_length.
                                        rewrite Hvs' => /=.
                                        rewrite app_length.
                                        lia. }
        exfalso.
        get_tail ea aft aft' a' Htail. rewrite Htail in H.
        do 2 rewrite app_assoc in H.
        apply app_inj_tail in H as [Hvs' <-].
        values_no_reduce.
        assert (const_list (v_to_e_list vcs)) as Hconst; first by apply v_to_e_is_const_list.
        rewrite Hvs' in Hconst.
        unfold const_list in Hconst. do 2 rewrite forallb_app in Hconst.
        apply andb_true_iff in Hconst as [Hconst _].
        by apply andb_true_iff in Hconst as [_ Hconst].
      - apply in_app_or in Hxl1 as [Hxl1 | Hxl1] => /=; last by destruct Hxl1.
        apply const_list_In in Hxl1 => //.
        by apply v_to_e_is_const_list.
    }
  Qed.
  
  Lemma reduce_det: forall (ws: store_record) (f: frame) es ws1 f1 es1 ws2 f2 es2,
      reduce ws f es ws1 f1 es1 ->
      reduce ws f es ws2 f2 es2 ->
      ( (ws1, f1, es1) = (ws2, f2, es2) \/
          (exists i, first_instr es = Some (AI_basic (BI_grow_memory),i)) \/
          (exists i1 i2 i3, first_instr es = Some (AI_trap,i1) /\ first_instr es1 = Some (AI_trap,i2) /\
                         first_instr es2 = Some (AI_trap,i3) /\
                         (ws1, f1) = (ws2, f2))).
  Proof.
    intros ws f es ws1 f1 es1 ws2 f2 es2 Hred1 Hred2.
    (* we perform an (strong) induction on the length_rec of es, i.e. its number of
     instructions, counting recursively under AI_locals and AI_labels *)
    cut (forall n, length_rec es < n ->
              ((ws1, f1, es1) = (ws2, f2, es2) \/
                 (exists i, first_instr es = Some (AI_basic (BI_grow_memory),i)) \/
                 (exists i1 i2 i3, first_instr es = Some (AI_trap,i1) /\ first_instr es1 = Some (AI_trap,i2) /\
                                first_instr es2 = Some (AI_trap,i3) /\
                                (ws1, f1) = (ws2, f2)))).
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
      - (* example of a usage of [ only_one ] : in this subgoal, we know that Hred2 is
         the hypothesis [ [AI_basic (BI_const v) ; AI_basic (BI_unop t op) ] -> es2 ].
         [ only_one ] selects the left disjunct in the conclusion, meaning we wish
         to show that in this case, there was indeed determinism. Then it performs a 
         case analysis on Hred2. Most cases have a left-hand-side very different from
         [AI_basic (BI_const v) ; AI_basic (BI_unop t op)] and can thus be exfalsoed.
         Some cases, like the r_label case, require a little more effort, but the tactic
         can handle most difficulties. See the next comment for an example of when 
         [ only_one ] cannot exfalso all irrelevant cases *)
        by only_one [AI_basic (BI_const v) ; AI_basic (BI_unop t op)] Hred2.
      - (* an example where we the user need to provide some extra work because [ only_one ]
         couldn't exfalso away every possibility : here, knowing that Hred2 is
         hypothesis [ [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ; 
         AI_basic (BI_binop t op)] -> es2 ], the tactic leaves us with two (not one)
         possibilities : Hred2 holds either using rs_binop_success or rs_binop_failure.
         It is up to us to exfalso away the second case using the rest of the
         hypotheses *)
        (* Many of the following cases are handled entirely by [ only_one ], or require
         minimal work on our hand. Thus we shall only comment less trivial instances *)
        by only_one [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                     AI_basic (BI_binop t op)] Hred2 ;
        inversion Heqes ; subst ;
        rewrite H in H0 ; inversion H0 ; subst.
      - by only_one [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                     AI_basic (BI_binop t op)] Hred2 ;
        inversion Heqes ; subst ;
        rewrite H in H0 ; inversion H0 ; subst.
      - by only_one [AI_basic (BI_const (VAL_int32 c));
                     AI_basic (BI_testop T_i32 testop)] Hred2.
      - by only_one [AI_basic (BI_const (VAL_int64 c)) ;
                     AI_basic (BI_testop T_i64 testop)] Hred2.
      - by only_one [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                     AI_basic (BI_relop t op)] Hred2.
      - by only_one [AI_basic (BI_const v) ; AI_basic (BI_cvtop t2 CVO_convert t1 sx)] Hred2 ;
        inversion Heqes ; subst ; rewrite H0 in H2 ;
        inversion H2 ; subst.
      - by only_one [AI_basic (BI_const v) ; AI_basic (BI_cvtop t2 CVO_convert t1 sx)] Hred2 ;
        inversion Heqes ; subst ; rewrite H0 in H2 ;
        inversion H2 ; subst.
      - by only_one [AI_basic (BI_const v) ; AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)]
                    Hred2.
      - by only_one [AI_basic BI_unreachable] Hred2.
      - by only_one [AI_basic BI_nop] Hred2.
      - by only_one [AI_basic (BI_const v) ; AI_basic BI_drop] Hred2.
      - only_one [AI_basic (BI_const v1) ; AI_basic (BI_const v2);
                  AI_basic (BI_const (VAL_int32 n)) ; AI_basic BI_select] Hred2 ;
          [done | by inversion Heqes ; subst ].
      - only_one [AI_basic (BI_const v1); AI_basic (BI_const v2) ;
                  AI_basic (BI_const (VAL_int32 n)) ; AI_basic BI_select] Hred2 ;
          [by inversion Heqes ; subst | done].
      - (* Here, in the block case, the left-hand-side of Hred2 is
         [ vs ++ [AI_basic (BI_block (Tf t1s t2s) es)] ] which is not an explicit
         list, thus we cannot use [ only_one ]. We perform the case analysis on Hred2
         by hand. Likewise for the following case (loop) *)
        remember (vs ++ [AI_basic (BI_block (Tf t1s t2s) es)])%SEQ as es0.
        apply Logic.eq_sym in Heqes0.
        induction Hred2 ; (try by repeat ((by inversion Heqes0) +
                                            (destruct vs ; first by inversion Heqes0))) ;
          try by right ; right ; left ;
          exists a ; rewrite first_instr_const => //= ; subst ; apply v_to_e_is_const_list.
        { left ; destruct H3 ;
            try by repeat ((by inversion Heqes0) +
                             (destruct vs ; first by inversion Heqes0)). 
          apply app_inj_tail in Heqes0 as [Hvs Hbl].
          by inversion Hbl ; subst.
          apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
          rewrite <- Heqes0 in H4.
          unfold lfilled, lfill in H4. destruct lh ; last by false_assumption.
          remember (const_list l) as b eqn:Hl ;
            destruct b ; last by false_assumption.
          move/eqP in H4.
          replace [AI_basic (BI_block (Tf t1s t2s) es)] with
            (AI_basic (BI_block (Tf t1s t2s) es) :: []) in H4 => //=.
          apply first_values in H4 as (_ & Habs & _) => //= ; try by (intros [? ?]). }
        (* Invoke native appears here as well as a potential reduction, although the premise doesn't hold since we're in the block case *)
        {
          apply app_inj_tail in Heqes0 as [? Hcontra].
          by inversion Hcontra.
        }
        {
          apply app_inj_tail in Heqes0 as [? Hcontra].
          by inversion Hcontra.
        }
        simple_filled H3 k lh bef aft nn ll ll'.
        destruct aft. { destruct bef. { rewrite app_nil_l app_nil_r in H3.
                                        unfold lfilled, lfill in H4 ; simpl in H4.
                                        move/eqP in H4 ; rewrite app_nil_r in H4 ; subst.
                                        apply IHHred2 => //=. }
          destruct es0 ; first by empty_list_no_reduce.
                        get_tail a0 es0 ys y Htail.
                        rewrite Htail app_nil_r in H3. rewrite <- Heqes0 in H3.
                        rewrite app_assoc in H3. apply app_inj_tail in H3 as [Hvs' Hy].
                        rewrite Htail in Hred2. rewrite <- Hy in Hred2. exfalso.
                        apply (block_not_enough_arguments_no_reduce
                                 _ _ _ _ _ _ _ _ _ Hred2).
                        - rewrite Hvs' in H.
                          unfold const_list in H. rewrite forallb_app in H.
                          by apply andb_true_iff in H as [_ Hys].
                        - rewrite Hvs' in H0. simpl in H0. subst. rewrite app_length in H0.
                          lia. }
        get_tail a aft aft' a' Htail. rewrite Htail in H3.
        rewrite <- Heqes0 in H3. do 2 rewrite app_assoc in H3.
        apply app_inj_tail in H3 as [Hvs' _].
        exfalso ; values_no_reduce. rewrite Hvs' in H.
        unfold const_list in H. do 2 rewrite forallb_app in H.
        apply andb_true_iff in H as [H _].
        apply andb_true_iff in H as [_ H].
        done. rewrite <- Heqes0 in Hxl1. apply in_app_or in Hxl1 as [Habs | Habs].
        intruse_among_values vs Habs H. inversion Habs ; inversion H5.
      - remember (vs ++ [AI_basic (BI_loop (Tf t1s t2s) es)])%SEQ as es0.
        apply Logic.eq_sym in Heqes0.
        induction Hred2 ; (try by repeat ((by inversion Heqes0) +
                                            (destruct vs ; first by inversion Heqes0))) ;
          try by right ; right ; left ;
          exists a ; rewrite first_instr_const => //= ; subst ; apply v_to_e_is_const_list.
        { left ; destruct H3 ;
            try by repeat ((by inversion Heqes0) +
                             (destruct vs ; first by inversion Heqes0)).
          apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
          apply app_inj_tail in Heqes0 as [Hvs Hbl].
          by inversion Hbl ; subst.
          rewrite <- Heqes0 in H4.
          unfold lfilled, lfill in H4. destruct lh ; last by false_assumption.
          remember (const_list l) as b eqn:Hl ;
            destruct b ; last by false_assumption.
          move/eqP in H4.
          replace [AI_basic (BI_block (Tf t1s t2s) es)] with
            (AI_basic (BI_block (Tf t1s t2s) es) :: []) in H4 => //=.
          apply first_values in H4 as (_ & Habs & _) => //= ; try by (intros [? ?]). }
        {
          apply app_inj_tail in Heqes0 as [? Hcontra].
          by inversion Hcontra.
        }
           {
          apply app_inj_tail in Heqes0 as [? Hcontra].
          by inversion Hcontra.
        }
        simple_filled H3 k lh bef aft nn ll ll'.
        destruct aft. { destruct bef. { rewrite app_nil_l app_nil_r in H3.
                                        unfold lfilled, lfill in H4 ; simpl in H4.
                                        move/eqP in H4 ; rewrite app_nil_r in H4 ; subst.
                                        apply IHHred2 => //=. }
          destruct es0 ; first by empty_list_no_reduce.
                        get_tail a0 es0 ys y Htail.
                        rewrite Htail app_nil_r in H3. rewrite <- Heqes0 in H3.
                        rewrite app_assoc in H3. apply app_inj_tail in H3 as [Hvs' Hy].
                        rewrite Htail in Hred2. rewrite <- Hy in Hred2. exfalso.
                        apply (loop_not_enough_arguments_no_reduce
                                 _ _ _ _ _ _ _ _ _ Hred2).
                        - rewrite Hvs' in H.
                          unfold const_list in H. rewrite forallb_app in H.
                          by apply andb_true_iff in H as [_ Hys].
                        - rewrite Hvs' in H0. simpl in H0. subst. rewrite app_length in H0.
                          lia. }
        get_tail a aft aft' a' Htail. rewrite Htail in H3.
        rewrite <- Heqes0 in H3. do 2 rewrite app_assoc in H3.
        apply app_inj_tail in H3 as [Hvs' _].
        exfalso ; values_no_reduce. rewrite Hvs' in H.
        unfold const_list in H. do 2 rewrite forallb_app in H.
        apply andb_true_iff in H as [H _].
        apply andb_true_iff in H as [_ H].
        done. rewrite <- Heqes0 in Hxl1. apply in_app_or in Hxl1 as [Habs | Habs].
        intruse_among_values vs Habs H. inversion Habs ; inversion H5.
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
      - (* this is the rs_return case. It combines the difficulties of rs_br with
         the fact that, as for the previous few cases, [ only_one ] cannot be applied
         and thus all the work must be performed by hand *)
        left ; remember [AI_local n f0 es] as es0.
        rewrite <- app_nil_l in Heqes0.
        induction Hred2 ; try by inversion Heqes0 ;
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
          rewrite app_nil_r in H3. subst. apply IHHred2 => //=.
          apply app_eq_nil in Hes as [-> _] ; empty_list_no_reduce.
        + { inversion Heqes0 ; subst.
            induction Hred2 ;
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
    - (* r_label case. The proof is tedious and relies on cleverly calling the induction
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
    - (* final case : the r_local case. We perform the case analysis on Hred2 by hand *)
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
  
End determ.
