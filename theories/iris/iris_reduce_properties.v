From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap proph_map.
Require Export iris iris_locations stdpp_aux iris_wasm_lang_properties iris_lfilled_properties.
Require Export datatypes host operations properties opsem.

Ltac not_const e He :=
  let b := fresh "b" in
  destruct e as [b| | | | ] ; (try by (left + right)) ;
  destruct b ; (try by left) ;
    by exfalso ; apply He.

(* given a nonempty list x :: xs, gives user a hypothesis "Htail : x :: xs = ys ++ [y]" *)
Ltac get_tail x xs ys y Htail :=
  cut (exists ys y, x :: xs = ys ++ [y]) ;
  [ intro Htail ; destruct Htail as (ys & y & Htail) |
    exists (removelast (x :: xs)) ;
    exists (List.last (x :: xs) AI_trap) ;
    apply app_removelast_last ;
    apply not_eq_sym ; apply nil_cons ].

Import DummyHosts.

Section reduce_properties.
  
  Let reducible := @reducible wasm_lang.
  Let reduce := @reduce host_function host_instance.

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.

  (* wasm opsem related *)

  Lemma values_no_reduce hs s f vs hs' s' f' es' :
    reduce hs s f vs hs' s' f' es' -> const_list vs -> False.
  Proof.
    intros H Hvs. induction H ; try by inversion Hvs ; unfold const_list in Hvs ;
                    rewrite forallb_app in Hvs ; apply andb_true_iff in Hvs ;
                    destruct Hvs as [_ Hvs] ; inversion Hvs.
    { destruct H ; try by inversion Hvs ;
        unfold const_list in Hvs ; rewrite forallb_app in Hvs; 
        apply andb_true_iff in Hvs ; destruct Hvs as [_ Hvs] ; 
        inversion Hvs.
      - inversion Hvs. apply andb_true_iff in H1. destruct H1.
        false_assumption.
      - filled_trap H0 Hxl1. unfold const_list in Hvs. rewrite H0 in Hvs.
        rewrite forallb_app in Hvs. apply andb_true_iff in Hvs. destruct Hvs as [_ Hvs].
        inversion Hvs. 
    }
    simple_filled H0 k lh bef aft n l l' ; rewrite H0 in Hvs ; unfold const_list in Hvs ;
      rewrite forallb_app in Hvs ; apply andb_true_iff in Hvs ; destruct Hvs as [_ Hvs].
    + rewrite forallb_app in Hvs. apply andb_true_iff in Hvs. destruct Hvs as [Hvs _].
      apply (IHreduce Hvs).
    + inversion Hvs.
  Qed.

End reduce_properties.

(* Applies values_no_reduce and attempts to prove that the given arguments were indeed
   values *)
Ltac values_no_reduce :=
  eapply values_no_reduce => //=.
  

(* From hyopthesis "Heqes : [ some explicit list of instructions ] = es" and 
   "Hred : es reduces to es'", attempts to prove False. 
   Defined recursively. Examples below show how compilation time gets noticeably
   longer when there are more instructions.
   To prove lemmas reduce_ves, only length 3 is needed, which is compiled in a few
   seconds *)
Ltac no_reduce Heqes Hred :=
  let a := fresh "a" in
  let aft := fresh "aft" in
  let bef := fresh "bef" in
  let e := fresh "e" in
  let e' := fresh "e" in
  let es := fresh "es" in
  let es' := fresh "es" in
  let es0 := fresh "es" in
  let f := fresh "f" in
  let f' := fresh "f" in
  let g := fresh "g" in
  let hs := fresh "hs" in
  let hs' := fresh "hs" in
  let k := fresh "k" in
  let l := fresh "l" in
  let l' := fresh "l" in
  let les := fresh "les" in
  let les' := fresh "les'" in
  let lh := fresh "lh" in
  let m := fresh "m" in
  let n := fresh "n" in
  let n' := fresh "n" in
  let s := fresh "s" in
  let s' := fresh "s" in
  let t1s' := fresh "t1s" in
  let t2s := fresh "t2s" in
  let vs := fresh "vs" in
  let H := fresh "H" in
  let H0 := fresh "H" in
  let H1 := fresh "H" in
  let Hconst := fresh "Hconst" in
  let Heqes0 := fresh "Heqes" in
  let Heqg := fresh "Heqg" in
  let Hes := fresh "Hes" in
  let Hles' := fresh "Hles" in
  let Ht1s := fresh "Ht1s" in
  let Ht2s := fresh "Ht2s" in
  let Htrap' := fresh "Htrap" in
  let Hvs := fresh "Hvs" in
  let Hxl1 := fresh "Hxl1" in
  let IHreduce := fresh "IHreduce" in
  (* clear all unimportant hypothesis, in order to make induction hypothesis 
     created at next step as simple as possible *)
  clear - (*host_function host function_closure store_record
                      host_instance*)
                      Hred Heqes ;
  induction Hred as [e e' s f hs H | | | | | a | a | a | | | | | | | | | | | | | | | |
                      s f es les s' f' es' les' k lh hs hs' Hred IHreduce H0 _ |
    ]; (try by inversion Heqes) ; (try by found_intruse (AI_invoke a) Heqes Hxl1) ;
  [ destruct H as [ | | | | | | | | | | | | | | 
                    vs es n' m t1s' t2s Hconst Hvs Ht1s Ht2s |
                    vs es n' m t1s' t2s Hconst Hvs Ht1s Ht2s |
                  | | | | | | | | | | | | | 
                    es' lh Htrap' H0 ]; (try by inversion Heqes) ;
    first found_intruse (AI_basic (BI_block (Tf t1s' t2s) es)) Heqes Hxl1 ;
    first found_intruse (AI_basic (BI_loop (Tf t1s' t2s) es)) Heqes Hxl1 ;
    try rewrite <- Heqes in H0 ; filled_trap H0 Hxl1
  | rewrite <- Heqes in H0 ;
    (* The tactic simple_filled will destruct hypothesis "H0 : lfilled es les".
       In this case, it will completely solve the case k > 0, and for the case
       k = 0, it will transform hypothesis H0 into "H0 : objs = bef ++ es ++ aft"
       where objs is the explicit sequence from Heqes *)
    simple_filled H0 k lh bef aft n l l' ;
    apply Logic.eq_sym in H0 ;
    remember ([] : seq.seq administrative_instruction) as g eqn:Heqg in f;
    let rec auxb H0 :=
      ( (* We maintain as an invariant that when auxb H0 is called,
           H0 is the hypothesis "H0 : bef ++ es ++ aft = [some explicit sequence ]" *)
        let b0 := fresh "b" in
        let Hb0 := fresh "Hb0" in
        let H1 := fresh "H" in
        destruct bef as [| b0 bef] ;
        [ (* case bef = [] : our invariant tells us that 
             "H0 : es ++ aft = [some explicit sequence"
             recall g was defined to be [] with "Heqg : g = []" *)
          let rec auxe H0 g Heqg :=
             (* We maintain as an invariant that when auxe H0 g Heqg is called,
                 H0 is the hypothesis "H0 : es ++ aft = [some explicit sequence]"
                 Hred is the hypothesis "Hred : (g ++ es) -> es'"
                 and Heqg is "Heqg : g = [some (other) explicit sequence]" *)
            (  let e0 := fresh "e" in
              let g' := fresh "g" in
              let He0 := fresh "He" in
              let Heqg' := fresh "Heqg" in
              let H1 := fresh "H" in
              destruct es as [| e0 es ] ;
              [ (* case es = [] ; our invariant tells us that
                   "Hred : g -> es'". We can solve this case either … *)
                rewrite <- Heqg in Hred ;
                remember g as es0 eqn:Heqes0 in Hred ;
                apply Logic.eq_sym in Heqes0 ;
                rewrite Heqg in Heqes0 ;
                (* … by induction hypothesis (case where bef = aft = []), or … *)
                ((by subst ; apply IHreduce) +
                   (* … by calling recursively no_reduce (case where bef or aft is
                      nonempty, thus our recursive call is on a shorter list *)
                   no_reduce Heqes0 Hred)
              | (* case es = e0 :: es. Our invariant gives us
                   "H0 : e0 :: es ++ aft = [some explicit sequence]", so we can 
                   try to conclude by inverting H0 in case the explicit sequence is
                   empty *)
                (by inversion H0) +
                  (* else, the explicit sequence is nonempty, so by inverting H0,
                     we get "H1 : es ++ aft = [some shorter explicit sequence]".
                     Our invariant also tells us "Hred : (g ++ e0 :: es) -> es'",
                     so to maintain this invariant, we define g' to be g ++ [e0].
                     We then make sure to have a hypothesis Heqg' which gives an
                     explicit description of g' *)
                  ( inversion H0 as [[ He0 H1 ]] ;
                    rewrite He0 in Hred ;
                    remember (g ++ [e0]) as g' eqn:Heqg' ;
                    rewrite Heqg in Heqg' ;
                    rewrite He0 in Heqg' ;
                    simpl in Heqg' ;
                    (* now we can make a recursive call to auxe. The invariant 
                       is maintained, and the explicit sequence in H1 has diminished
                       in length *)
                    auxe H1 g' Heqg'
                  )
              ]
            ) in auxe H0 g Heqg
        | (* case bef = b0 :: bef. Our invariant gives us
             "H0 : b0 :: bef ++ es ++ aft = [some explicit sequence]", so we can 
             try to conclude by inverting H0 in case that explicit sequence is empty *)
          (by inversion H0) +
            (* else the explicit sequence is nonempty, so by inverting H0, we get 
               "H1 : es ++ aft = [some shorter explicit sequence]" *)
            ( inversion H0 as [[ Hb0 H1 ]] ;
              auxb H1 )
        ]
      ) in auxb H0
  ].

Section reduce_properties_lemmas.

  Let reducible := @reducible wasm_lang.
  Let reduce := @reduce host_function host_instance.

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.

  (* examples of usage of no_reduce. This first example is reused in other lemmas,
   the following ones may be removed if wanted *)
  Lemma empty_no_reduce hs s f hs' s' f' es' :
    reduce hs s f [] hs' s' f' es' -> False.
  Proof.
    intro Hred.
    remember [] as es in Hred.
    apply Logic.eq_sym in Heqes.
    no_reduce Heqes Hred.
  Qed.

  Ltac empty_list_no_reduce :=
    exfalso ; eapply empty_no_reduce => //=.

  Lemma test_no_reduce1 hs s f v hs' s' f' es' :
    reduce hs s f [AI_basic (BI_const v)] hs' s' f' es' -> False.
  Proof.
    intro Hred.
    remember [AI_basic (BI_const v)] as es in Hred.
    apply Logic.eq_sym in Heqes.
    no_reduce Heqes Hred.
  Qed.

  Lemma test_no_reduce_trap hs s f hs' s' f' es' :
    reduce hs s f [AI_trap] hs' s' f' es' -> False.
  Proof.
    intro Hred.
    remember [AI_trap] as es.
    apply Logic.eq_sym in Heqes.
    no_reduce Heqes Hred; subst => //.
  Qed.

  Lemma test_no_reduce2 hs s f v1 v2 hs' s' f' es' :
    reduce hs s f [AI_basic (BI_const v1) ; AI_basic (BI_const v2)] hs' s' f' es' -> False.
  Proof.
    intro Hred.
    remember [AI_basic (BI_const v1) ; AI_basic (BI_const v2)] as es in Hred.
    apply Logic.eq_sym in Heqes.
    no_reduce Heqes Hred.
  Qed.

  Lemma test_no_reduce3 hs s f v1 v2 v3 hs' s' f' es' :
    reduce hs s f [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ; AI_basic (BI_const v3)]
           hs' s' f' es' -> False.
  Proof.
    intro Hred.
    remember [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ; AI_basic (BI_const v3)]
      as es in Hred.
    apply Logic.eq_sym in Heqes.
    no_reduce Heqes Hred.
  Qed.
  
  Lemma reduce_load_false hs s0 f hs' s' f' es es' x0 x1 x2 x3 :
    es = [AI_basic (BI_load x0 x1 x2 x3)] ->
    reduce hs s0 f es hs' s' f' es' -> False.
  Proof.
    intros Heq Hred.
    apply Logic.eq_sym in Heq.
    no_reduce Heq Hred.
  Qed.
  
  Lemma reduce_store_false hs s0 f hs' s' f' es es' x0 x1 x2 x3 :
    es = [AI_basic (BI_store x0 x1 x2 x3)] ->
    reduce hs s0 f es hs' s' f' es' -> False.
  Proof.
    intros Heq Hred.
    apply Logic.eq_sym in Heq.
    no_reduce Heq Hred.
  Qed.
  
  Lemma reduce_store_false_2 hs s0 f hs' s' f' es es' x0 x1 x2 x3 v :
    es = [AI_basic (BI_const v); AI_basic (BI_store x0 x1 x2 x3)] ->
    reduce hs s0 f es hs' s' f' es' -> False.
  Proof.
    intros Heq Hred.
    apply Logic.eq_sym in Heq.
    no_reduce Heq Hred.
  Qed.

  Lemma reduce_val_false hs s0 f hs' s' f' es es' :
    is_Some (iris.to_val es) ->
    reduce hs s0 f es hs' s' f' es' -> False.
  Proof.
    intros Hsome Hred.
    apply val_head_stuck_reduce in Hred.
    rewrite Hred in Hsome. inversion Hsome.
    done.
  Qed.

  Lemma reduce_br_false hs s f vs0 j es es0 hs' s' f' es' :
    const_list vs0 ->
    es = vs0 ++ [AI_basic (BI_br j)] ++ es0 ->
    reduce hs s f es hs' s' f' es' -> False.
  Proof.
    intros Heqes Hred.
    eapply reduce_val_false;eauto.
    subst.
    apply const_es_exists in Heqes as [vs ->].
    rewrite to_val_br_eq. auto.
  Qed.

  Lemma reduce_ret_false hs s f vs0 es es0 hs' s' f' es' :
    const_list vs0 ->
    es = vs0 ++ [AI_basic BI_return] ++ es0 ->
    reduce hs s f es hs' s' f' es' -> False.
  Proof.
    intros Heqes Hred.
    eapply reduce_val_false;eauto.
    subst.
    apply const_es_exists in Heqes as [vs ->].
    rewrite to_val_ret_eq. auto.
  Qed.
  
End reduce_properties_lemmas.


Ltac empty_list_no_reduce :=
  exfalso ; eapply empty_no_reduce => //=.

(* Knowing hypothesis "Hin : In obj vs" and "Hvs : const_list vs", tries to prove False *)
Ltac intruse_among_values vs Hin Hvs :=
  try unfold const_list in Hvs ;
  let x := fresh "Hf" in
  destruct (forallb_forall is_const vs) as [x _] ;
  apply (x Hvs) in Hin ; inversion Hin.



(* attempts to prove that vs ++ [obj] entails false when list vs is shorter 
   than list t1s. Some subgoals may be left for user to prove *)
Ltac not_enough_arguments hs s f vs obj t1s hs' s' f' es' := 
  let Hxl1 := fresh "Hxl1" in
  let n := fresh "n" in
  let H := fresh "H" in
  let Hvs := fresh "Hvs" in
  let es := fresh "es" in
  let Heqes := fresh "Heqes" in
  let e := fresh "e" in
  let e' := fresh "e" in
  let les := fresh "les" in
  let les' := fresh "les" in
  let k := fresh "k" in
  let lh := fresh "lh" in
  let Hred := fresh "Hred" in
  let IHreduce := fresh "IHreduce" in
  let H0 := fresh "H" in
  let Habs := fresh "Habs" in
  let vs' := fresh "vs" in
  let n' := fresh "n" in
  let m := fresh "m" in
  let t1s' := fresh "t1s" in
  let t2s' := fresh "t2s" in
  let Hconst' := fresh "Hconst'" in
  let Hvs' := fresh "Hvs" in
  let Ht1s := fresh "Ht1s" in
  let Ht2s := fresh "Ht2s" in
  let Ht1s' := fresh "Ht1s" in
  let Ht2s' := fresh "Ht2s" in
  let i := fresh "i" in
  let v := fresh "v" in
  let Htrap' := fresh "Htrap" in
  let Hvs0 := fresh "Hvs" in
  let Hbl := fresh "Hbl" in
  let Hes := fresh "Hes" in
  let Hgoal := fresh "Hgoal" in
  let Hxl2 := fresh "Hxl1" in
  let Heq := fresh "Heq" in
  let l := fresh "l" in
  let l0 := fresh "l" in
  let a := fresh "a" in
  let l' := fresh "l" in
  let b := fresh "b" in
  let Htail := fresh "Htail" in
  let IHn := fresh "IHn" in
  let n0 := fresh "n" in
  let l1 := fresh "l" in
  let l3 := fresh "l" in
  cut (forall n, length vs < n ->
            reduce hs s f (vs ++ [obj]) hs' s' f' es'
            ->  const_list vs -> length vs < length t1s
            ->  False) ;
  [ intro H ; apply (H (S (length vs))) ; apply Nat.lt_succ_diag_r |] ;
  intro n ;
  generalize dependent vs;
  generalize dependent es' ;
  induction n as [| n IHn] ; [ intros es' vs Habs ; inversion Habs |] ;
  intros es' vs Hvs H Hconst Hlen ;
  remember (cat vs [obj]) as es eqn:Heqes ;
  induction H as [e e' s f hs H | | | | | | | | | | | | | | | | | | | | | | |
                      s f es les s' f' es' les' k lh hs hs' Hred IHreduce H0 _ |
    ]; (try by found_intruse obj Heqes Hxl1);
  ( try by apply app_inj_tail in Heqes ; destruct Heqes as [ _ Habs ] ;
    inversion Habs ) ;
  (try 
     (destruct H as [ | | | | | | | | | | | | | | 
                      vs' es n' m t1s' t2s' Hconst' Hvs' Ht1s' Ht2s' |
                      vs' es n' m t1s' t2s' Hconst' Hvs' Ht1s' Ht2s' |
                    | | | | | | | | | | | | i v | 
                      es' lh Htrap' H0 ]; try by found_intruse obj Heqes Hxl1 ;
      try by apply app_inj_tail in Heqes ; destruct Heqes as [ _ Habs ] ; inversion Habs ;
      try by apply app_inj_tail in Heqes ; destruct Heqes as [ Hvs0 Hbl ] ;
      inversion Hbl as [[ Ht1s Ht2s Hes ]] ; rewrite Ht1s in Ht1s' ;
      rewrite Ht1s' in Hlen ; rewrite Hvs0 in Hvs' ;
      rewrite Hvs' in Hlen ; apply Nat.lt_neq in Hlen ;
      apply Hlen ; trivial ;
      try by cut ([ v ; AI_basic (BI_tee_local i)] = [v] ++ [AI_basic (BI_tee_local i)]) ;
      [| simpl ; trivial ] ; intro Heq ; rewrite Heq in Heqes ;
      apply app_inj_tail in Heqes ; destruct Heqes as [ _ Habs ] ; inversion Habs ;
      try by rewrite Heqes in H0 ; filled_trap H0 Hxl1 ; apply in_app_or in Hxl1 ;
      destruct Hxl1 as [Hxl1 | Hxl1] ; [ intruse_among_values vs Hxl1 Hconst |] ;
      destruct Hxl1 as [Hxl1 | Hxl1] ; [inversion Hxl1 | exact Hxl1 ] 
  )) ;
  (try (rewrite Heqes in H0 ;
        simple_filled H0 k lh l0 l n0 l1 l3 ;
        [ apply Logic.eq_sym in H0 ;
          destruct l ;
          [ rewrite app_nil_r in H0 ;
            destruct es as [| a es] ;
            [ empty_list_no_reduce |] ;
            get_tail a es l' b Htail ;
            rewrite Htail in H0 ;
            rewrite app_assoc in H0 ;
            apply app_inj_tail in H0 ; destruct H0 as [Hll Hb] ;
            destruct l0 ;
            [ simpl in Hll ; rewrite Htail in IHreduce ;
              rewrite Hll in IHreduce ; rewrite Hb in IHreduce ;
              apply IHreduce; [assumption | trivial]  |] ;
            apply (IHn es' l') ;
            [ rewrite <- Hll in Hvs ;
              rewrite app_length in Hvs ; simpl in Hvs ;
              apply lt_S_n in Hvs ; lia 
            | rewrite Htail in Hred ; rewrite Hb in Hred ;
              exact Hred 
            | rewrite <- Hll in Hconst ; unfold const_list in Hconst ;
              rewrite forallb_app in Hconst ;
              apply andb_true_iff in Hconst ;
              destruct Hconst as [_ Hgoal] ; exact Hgoal 
            | rewrite <- Hll in Hlen ;
              rewrite app_length in Hlen ; lia
            ]
          | get_tail a l l' b Htail;
            rewrite Htail in H0 ;
            rewrite app_assoc in H0 ; rewrite app_assoc in H0 ;
            apply app_inj_tail in H0 ; destruct H0 as [ Hes _ ] ;
            values_no_reduce ;
(*            apply (values_no_reduce _ _ _ _ _ _ _ _ Hred) ; *)
            rewrite <- Hes in Hconst ; unfold const_list in Hconst ;
            rewrite forallb_app in Hconst ;
            apply andb_true_iff in Hconst ;
            destruct Hconst as [Hconst _ ] ;
            rewrite forallb_app in Hconst ;
            apply andb_true_iff in Hconst ;
            destruct Hconst as [ _ Hconst ] ;
            exact Hconst
          ]
        | found_intruse (AI_label n0 l1 l3) H0 Hxl2 ;
          apply in_app_or in Hxl2 ; destruct Hxl2 as [Hxl2 | Hxl2] ;
          [ intruse_among_values vs Hxl2 Hconst 
          | destruct Hxl2 as [Hxl2 | Hxl2] ; [inversion Hxl2 | assumption]
          ]
        ]
  )).

Section reduce_properties_lemmas.
  Let reducible := @reducible wasm_lang.
  Let reduce := @reduce host_function host_instance.

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.

  Lemma block_not_enough_arguments_no_reduce hs s f (vs : seq.seq administrative_instruction)
        t1s t2s esb hs' s' f' es'  :
    reduce hs s f (vs ++ [AI_basic (BI_block (Tf t1s t2s) esb)]) hs' s' f' es' ->
    const_list vs ->
    length vs < length t1s ->
    False.
  Proof.
    not_enough_arguments hs s f vs (AI_basic (BI_block (Tf t1s t2s) esb)) t1s hs' s' f' es'.
    - apply app_inj_tail in Heqes. destruct Heqes as [Hvs' Hbl].
      inversion Hbl as [[ Ht1s Ht2s Hes ]]. rewrite Hvs' in Hvs0.
      rewrite Hvs0 in Hlen. rewrite <- Ht1s0 in Hlen. rewrite Ht1s in Hlen. lia.
    - assert ([v;AI_basic (BI_tee_local i)] = [v] ++ [AI_basic (BI_tee_local i)]).
      simpl ; trivial. rewrite H0 in Heqes ; apply app_inj_tail in Heqes.
      destruct Heqes as [_ Habs] ; inversion Habs.
    - filled_trap H0 Hxl1. rewrite H0 in Heqes. apply Logic.eq_sym in Heqes.
      found_intruse AI_trap Heqes Hxl2. apply in_app_or in Hxl2.
      destruct Hxl2 as [Hxl2 | Hxl2].
      intruse_among_values vs Hxl2 Hconst.
      destruct Hxl2 as [Hxl2 | Hxl2] ; inversion Hxl2.
  Qed. 

  
  Lemma loop_not_enough_arguments_no_reduce hs s f (vs : seq.seq administrative_instruction)
        t1s t2s esb hs' s' f' es'  :
    reduce hs s f (vs ++ [AI_basic (BI_loop (Tf t1s t2s) esb)]) hs' s' f' es' ->
    const_list vs ->
    length vs < length t1s ->
    False.
  Proof.
    not_enough_arguments hs s f vs (AI_basic (BI_loop (Tf t1s t2s) esb)) t1s hs' s' f'
                         es'.
    - apply app_inj_tail in Heqes. destruct Heqes as [Hvs' Hlp].
      inversion Hlp as [[ Ht1s Ht2s Hes ]].
      rewrite Ht1s in Ht1s0. rewrite Ht1s0 in Hlen. rewrite Hvs' in Hvs0.
      lia.
    - assert ([v;AI_basic (BI_tee_local i)] = [v] ++ [AI_basic (BI_tee_local i)]).
      simpl ; trivial. rewrite H0 in Heqes. apply app_inj_tail in Heqes.
      destruct Heqes as [ _ Habs ] ; inversion Habs.
    - filled_trap H0 Hxl1. rewrite H0 in Heqes. apply Logic.eq_sym in Heqes.
      found_intruse AI_trap Heqes Hxl2. apply in_app_or in Hxl2.
      destruct Hxl2 as [Hxl2 | Hxl2].
      intruse_among_values vs Hxl2 Hconst. destruct Hxl2 as [Hxl2 | Hxl2].
      inversion Hxl2. inversion Hxl2.
  Qed.

  Lemma v_to_e_length: forall vs,
      length (v_to_e_list vs) = length vs.
  Proof.
    move => vs. elim: vs => //=.
    - move => a l IH. by f_equal.
  Qed.

  Lemma invoke_not_enough_arguments_no_reduce_native
        hs s f vs a0 hs' s' f' es' i' t1s t2s ts es'' :
    nth_error (s_funcs s) a0 = Some (FC_func_native i' (Tf t1s t2s) ts es'') ->
    reduce hs s f (vs ++ [AI_invoke a0]) hs' s' f' es' ->
    const_list vs ->
    length vs < length t1s ->
    False.
  Proof.
    intro Hs.
  not_enough_arguments hs s f vs (AI_invoke a0) t1s hs' s' f' es'.
  - assert ([v ; AI_basic (BI_tee_local i)] = [v] ++ [AI_basic (BI_tee_local i)]).
    trivial. rewrite H0 in Heqes ; apply app_inj_tail in Heqes.
    destruct Heqes as [_ Habs] ; inversion Habs.
  - filled_trap H0 Hxl1. rewrite H0 in Heqes. apply Logic.eq_sym in Heqes.
    found_intruse AI_trap Heqes Hxl2. apply in_app_or in Hxl2.
    destruct Hxl2 as [Hxl2 | Hxl2] ;
      [ intruse_among_values vs Hxl2 Hconst |
        destruct Hxl2 as [Hxl2 | Hxl2] ; inversion Hxl2 ].
  - apply app_inj_tail in Heqes. destruct Heqes as [Hves  Hinvoke ].
    inversion Hinvoke as [Ha]. rewrite Ha in H.
    rewrite H in Hs. rewrite H0 in Hs. inversion Hs as [[ Hi Ht1s Ht2s Hts Hes ]].
    rewrite Ht1s in H4. rewrite H4 in Hlen.
    rewrite <- Hves in Hlen. rewrite H1 in Hlen. rewrite v_to_e_length in Hlen. lia.
 (* - apply app_inj_tail in Heqes. destruct Heqes as [Hves Hinvoke].
    inversion Hinvoke as [Ha]. rewrite Ha in H. rewrite H in Hs.
    rewrite H0 in Hs. inversion Hs.
  - apply app_inj_tail in Heqes. destruct Heqes as [Hves Hinvoke].
    inversion Hinvoke as [Ha]. rewrite Ha in H. rewrite H in Hs.
    rewrite H0 in Hs. inversion Hs.*)
  - simple_filled H0 k lh bef aft n0 l l'.
    destruct aft.
    { destruct es. { empty_list_no_reduce. }
      get_tail a es b l' Htail.
      rewrite Htail in H0. rewrite app_assoc in H0. rewrite app_nil_r in H0.
      rewrite app_assoc in H0. rewrite H0 in Heqes. apply app_inj_tail in Heqes.
      destruct Heqes as [Hb Hl'].
      rewrite Htail in Hred. rewrite Hl' in Hred.
      destruct bef. { simpl in Hb. rewrite Hb in Hred. rewrite Hb in Htail.
                      rewrite Hl' in Htail. apply IHreduce ; assumption. }
      apply (IHn es' b).
      + rewrite <- Hb in Hvs. rewrite app_length in Hvs. simpl in Hvs. lia.
      + exact Hred.
      + rewrite <- Hb in Hconst. unfold const_list in Hconst.
        rewrite forallb_app in Hconst. apply andb_true_iff in Hconst.
        destruct Hconst as [_ Hconst] ; exact Hconst.
      + rewrite <- Hb in Hlen. rewrite app_length in Hlen. lia.
    } get_tail a aft b l' Htail.
    rewrite Htail in H0. rewrite H0 in Heqes. do 2 rewrite app_assoc in Heqes.
    apply app_inj_tail in Heqes. destruct Heqes as [Heqes _].
    values_no_reduce. rewrite <- Heqes in Hconst.
    unfold const_list in Hconst. rewrite forallb_app in Hconst.
    apply andb_true_iff in Hconst. destruct Hconst as [Hconst _].
    rewrite forallb_app in Hconst. apply andb_true_iff in Hconst.
    destruct Hconst as [_ Hconst]. exact Hconst.
    rewrite Heqes in Hxl1. apply in_app_or in Hxl1.
    destruct Hxl1 as [ Hxl1 | Hxl1 ] ;
      [ intruse_among_values vs Hxl1 Hconst |
        destruct Hxl1 as [ Hxl1 | Hxl1 ] ; inversion Hxl1 ].
  Qed.


  Lemma invoke_not_enough_arguments_no_reduce_host
        hs s f vs a0 hs' s' f' es' t1s t2s h :
    nth_error (s_funcs s) a0 = Some (FC_func_host (Tf t1s t2s) h) ->
    reduce hs s f (vs ++ [AI_invoke a0]) hs' s' f' es' ->
    const_list vs ->
    length vs < length t1s ->
    False.
  Proof.
    intro Hs.
    not_enough_arguments hs s f vs (AI_invoke a0) t1s hs' s' f' es'.
    - assert ([v ; AI_basic (BI_tee_local i)] = [v] ++ [AI_basic (BI_tee_local i)]).
      trivial. rewrite H0 in Heqes ; apply app_inj_tail in Heqes.
      destruct Heqes as [_ Habs] ; inversion Habs.
    - filled_trap H0 Hxl1. rewrite H0 in Heqes. apply Logic.eq_sym in Heqes.
      found_intruse AI_trap Heqes Hxl2. apply in_app_or in Hxl2.
      destruct Hxl2 as [Hxl2 | Hxl2] ;
        [ intruse_among_values vs Hxl2 Hconst |
          destruct Hxl2 as [Hxl2 | Hxl2] ; inversion Hxl2 ].
    - apply app_inj_tail in Heqes. destruct Heqes as [Hves Hinvoke].
      inversion Hinvoke as [Ha]. rewrite Ha in H. rewrite H in Hs.
      rewrite H0 in Hs. inversion Hs. (*
  - apply app_inj_tail in Heqes. destruct Heqes as [Hves  Hinvoke ].
    inversion Hinvoke as [Ha]. rewrite Ha in H.
    rewrite H in Hs. rewrite H0 in Hs. inversion Hs as [[ Ht1s Ht2s Hh ]].
    rewrite Ht1s in H3. rewrite H3 in Hlen.
    rewrite <- Hves in Hlen. rewrite H1 in Hlen. rewrite v_to_e_length in Hlen. lia.
  - apply app_inj_tail in Heqes. destruct Heqes as [Hves  Hinvoke ].
    inversion Hinvoke as [Ha]. rewrite Ha in H.
    rewrite H in Hs. rewrite H0 in Hs. inversion Hs as [[ Ht1s Ht2s Hh ]].
    rewrite Ht1s in H3. rewrite H3 in Hlen.
    rewrite <- Hves in Hlen. rewrite H1 in Hlen. rewrite v_to_e_length in Hlen. lia. *)
    - simple_filled H0 k lh bef aft n0 l l'.
      destruct aft.
      { destruct es. { empty_list_no_reduce. }
        get_tail a es b l' Htail.
        rewrite Htail in H0. rewrite app_assoc in H0. rewrite app_nil_r in H0.
        rewrite app_assoc in H0. rewrite H0 in Heqes. apply app_inj_tail in Heqes.
        destruct Heqes as [Hb Hl'].
        rewrite Htail in Hred. rewrite Hl' in Hred.
        destruct bef. { simpl in Hb. rewrite Hb in Hred. rewrite Hb in Htail.
                        rewrite Hl' in Htail. apply IHreduce ; assumption. }
        apply (IHn es' b).
        + rewrite <- Hb in Hvs. rewrite app_length in Hvs. simpl in Hvs. lia.
        + exact Hred.
        + rewrite <- Hb in Hconst. unfold const_list in Hconst.
          rewrite forallb_app in Hconst. apply andb_true_iff in Hconst.
          destruct Hconst as [_ Hconst] ; exact Hconst.
        + rewrite <- Hb in Hlen. rewrite app_length in Hlen. lia.
      } get_tail a aft b l' Htail.
      rewrite Htail in H0. rewrite H0 in Heqes. do 2 rewrite app_assoc in Heqes.
      apply app_inj_tail in Heqes. destruct Heqes as [Heqes _].
      values_no_reduce. rewrite <- Heqes in Hconst.
      unfold const_list in Hconst. rewrite forallb_app in Hconst.
      apply andb_true_iff in Hconst. destruct Hconst as [Hconst _].
      rewrite forallb_app in Hconst. apply andb_true_iff in Hconst.
      destruct Hconst as [_ Hconst]. exact Hconst.
      rewrite Heqes in Hxl1. apply in_app_or in Hxl1.
      destruct Hxl1 as [ Hxl1 | Hxl1 ] ;
        [ intruse_among_values vs Hxl1 Hconst |
          destruct Hxl1 as [ Hxl1 | Hxl1 ] ; inversion Hxl1 ].
  Qed.

  Lemma prim_step_obs_efs_empty es es' σ σ' obs efs:
    prim_step es σ obs es' σ' efs ->
    (obs, efs) = ([], []).
  Proof.
    unfold prim_step, iris.prim_step.
    destruct σ as [[[??]?]?].
    destruct σ' as [[[??]?]?].
    by move => [_ [-> ->]].
  Qed.

  Lemma append_reducible (es1 es2: list administrative_instruction) σ:
    iris.to_val es1 = None ->
    reducible es1 σ ->
    reducible (es1 ++ es2) σ.
  Proof.
    unfold reducible => /=.
    move => Htv [κ [es' [σ' [efs HStep]]]].
    exists κ, (es' ++ es2), σ', efs.
    unfold iris.prim_step in * => //=.
    destruct σ as [[[hs ws] locs] inst].
    destruct σ' as [[[hs' ws'] locs'] inst'].
    destruct HStep as [HStep [-> ->]].
    repeat split => //.
    by apply r_elimr.
  Qed.

  Lemma AI_trap_reducible es2 σ :
    es2 ≠ [] -> 
    reducible ([AI_trap] ++ es2) σ.
  Proof.
    elim: es2;[done|].
    move => a l IH _.
    unfold reducible => /=.
    unfold language.reducible.
    exists [],[AI_trap],σ,[].
    simpl. unfold iris.prim_step.
    destruct σ as [[[hs ws] locs] inst].
    repeat split;auto.
    constructor. econstructor. auto.
    instantiate (1:=LH_base [] (a :: l)).
    unfold lfilled, lfill => //=.
  Qed.

  Lemma AI_trap_reducible_2 es1 σ :
    es1 ≠ [] ->
    const_list es1 ->
    reducible (es1 ++ [AI_trap]) σ.
  Proof.
    move => H H'.
    unfold reducible => /=.
    unfold language.reducible.
    exists [],[AI_trap],σ,[].
    simpl. unfold iris.prim_step.
    destruct σ as [[[hs ws] locs] inst].
    repeat split;auto.
    constructor. econstructor.
    destruct es1;auto.
    intros Hcontr. inversion Hcontr.
    destruct es1 => //=.
    instantiate (1:=LH_base (es1) []).
    unfold lfilled, lfill => //=.
    by rewrite H'.
  Qed.

  Lemma AI_trap_irreducible hs ws f hs' ws' f' es':
    reduce hs ws f [AI_trap] hs' ws' f' es' ->
    False.
  Proof.
    move => HReduce.
    remember ([AI_trap]) as e.
    induction HReduce => //=; subst; try by do 2 destruct vcs => //=.
    - subst. inversion H; subst; clear H => //; by do 3 destruct vs => //=.
    - move/lfilledP in H.
      move/lfilledP in H0.
      inversion H => //; subst; clear H; last by do 3 destruct vs => //=.
      inversion H0; subst; clear H0.
      destruct vs => /=; last by destruct vs, es, es'0 => //; inversion H1; subst.
      destruct es => /=; first by apply empty_no_reduce in HReduce.
      by destruct es, es'0 => //.
  Qed.
    
  Lemma AI_trap_reduce_det v hs ws f hs' ws' f' es':
    reduce hs ws f ([AI_basic (BI_const v); AI_trap]) hs' ws' f' es' ->
    (hs', ws', f', es') = (hs, ws, f, [AI_trap]).
  Proof.
    move => HReduce.
    remember ([AI_basic (BI_const v); AI_trap]) as es0.
    induction HReduce => //=; subst; try by do 3 destruct vcs => //=.
    - inversion H; subst; clear H => //; by do 3 destruct vs => //=.
    - move/lfilledP in H.
      move/lfilledP in H0.
      inversion H => //; subst; clear H; last by do 3 destruct vs => //=.
      inversion H0; subst; clear H0.
      destruct vs => /=.
      + destruct es => /=; first by apply empty_no_reduce in HReduce.
        destruct es => /=; simpl in H1; inversion H1; subst; clear H1; first by apply test_no_reduce1 in HReduce.
        destruct es, es'0 => //=.
        rewrite cats0.
        by apply IHHReduce.
      + destruct vs => /=; last by destruct vs, es, es'0 => //; inversion H1; subst.
        inversion H1; subst; clear H1.
        destruct es => /=; first by apply empty_no_reduce in HReduce.
        destruct es, es'0 => //.
        inversion H2; subst.
        by apply AI_trap_irreducible in HReduce.
  Qed.

  
  Lemma prepend_reducible (es1 es2: list administrative_instruction) vs σ :
    (∀ n (vh: valid_holed n), vs ≠ brV vh) ->
    (∀ sh, vs ≠ retV sh) ->
    iris.to_val es1 = Some vs ->
    reducible es2 σ ->
    reducible (es1 ++ es2) σ.
  Proof.
    intros Hne1 Hne2.
    destruct vs.
    { unfold reducible => /=.
      move => Htv [κ [es' [σ' [efs HStep]]]].
      exists κ, (es1 ++ es'), σ', efs.
      unfold iris.prim_step in * => //=.
      destruct σ as [[[hs ws] locs] inst].
      destruct σ' as [[[hs' ws'] locs'] inst'].
      destruct HStep as [HStep [-> ->]].
      repeat split => //.
      apply r_eliml => //.
      eapply to_val_const_list; eauto. }
    { move => Ht [κ [es' [σ' [efs HStep]]]].
      pose proof (to_val_trap_is_singleton Ht) as ->.
      apply AI_trap_reducible.
      rewrite /= /iris.prim_step in HStep.
      destruct σ as [[[hs ws] locs] inst].
      destruct σ' as [[[hs' ws'] locs'] inst'].
      destruct HStep as [HStep [-> ->]].
      by pose proof (reduce_not_nil HStep). }
    { congruence. }
    { congruence. }
  Qed.

  Lemma first_non_value_reduce hs s f es hs' s' f' es' :
    reduce hs s f es hs' s' f' es' ->
    exists vs e es'', const_list vs /\ (to_val [e] = None \/ e = AI_trap) /\ es = vs ++ e :: es''.
  Proof.
    intros Hes.
    remember (to_val es) as tv. apply Logic.eq_sym in Heqtv. destruct tv;simplify_eq.
    { destruct v. { apply to_val_const_list in Heqtv.
                    exfalso ; values_no_reduce. }
      apply to_val_trap_is_singleton in Heqtv. subst.
      exfalso ; by apply (AI_trap_irreducible _ _ _ _ _ _ _ Hes).
      { apply reduce_val_false in Hes;try done. }
      { apply reduce_val_false in Hes;try done. }
    }
      by apply first_non_value.
  Qed.

  Lemma trap_reduce_length hs s f es hs' s' f' es' vs1 es2 :
    lfilled 0 (LH_base vs1 es2) [AI_trap] es -> reduce hs s f es hs' s' f' es' ->
    exists n1 n2, (n1 + (length es2 - n2) < length vs1 + length es2 ∧ n1 <= length vs1 ∧ n2 <= length es2) ∧
               lfilled 0 (LH_base (take n1 vs1) (drop n2 es2)) [AI_trap] es' /\ (hs, s, f) = (hs', s', f').
  Proof.
    intros Hfill%lfilled_Ind_Equivalent Hred.
    revert vs1 es2 Hfill.
    generalize dependent es.
    induction 1;intros vs1 es2 Hfill;[|inversion Hfill;simplify_eq..].
    all: try do 2 destruct vs1 =>//.
    all: try do 3 destruct vs1 =>//.
    2: try by apply first_values in H11 as [?[? ?]];auto;[|apply v_to_e_is_const_list].
    { revert vs1 es2 Hfill.
      generalize dependent e.
      induction 1;intros vs1 es2 Hfill;inversion Hfill;simplify_eq.
      all: try do 2 destruct vs1 =>//.
      all: try do 3 destruct vs1 =>//.
      all: try by apply first_values in H5 as [?[? ?]];auto.
      destruct vs1 =>//. do 2 destruct es2 =>//. by inversion H2;simplify_eq.
      do 2 destruct vs1 =>//.
      (* base case *)
      apply lfilled_Ind_Equivalent in H0.
      inversion H0;simplify_eq.
      apply first_values in H1;auto.
      destruct H1 as [-> [_ ->]].
      exists 0,(length es2). split.
      { split;try lia. destruct vs1,es2 =>//.
        all: simpl;lia. }
      rewrite take_0 drop_all. split;auto. }
    { apply lfilled_Ind_Equivalent in H.
      inversion H;simplify_eq; [|by eapply first_values in H1 as [?[? ?]];auto].
      apply lfilled_Ind_Equivalent in H0. inversion H0;simplify_eq.
      apply val_head_stuck_reduce in Hred as Hnv.
      apply const_list_snoc_eq3 in H1;auto.
      2: destruct es =>//.
      2: intros [? Hcontr]%const_list_to_val;congruence.
      2: intros ->;done.
      destruct H1 as [? [? [? [? [? ?]]]]];simplify_eq.
      assert (lfilledInd 0 (LH_base x x0) [AI_trap] (x ++ [AI_trap] ++ x0)%list) as HH;[by constructor|].
      apply IHHred in HH as [n1 [n2 [Hlt [Hlh' Heq]]]].
      apply lfilled_Ind_Equivalent in Hlh'.
      inversion Hlh';simplify_eq.
      exists (length vs + n1),n2.
      split. { rewrite !app_length. lia. }
      split;auto.
      rewrite take_plus_app//.
      rewrite drop_app_le;[|lia].
      apply lfilled_Ind_Equivalent.
      repeat erewrite app_assoc.
      erewrite <- app_assoc.
      erewrite <- (app_assoc _ _ (drop n2 x0 ++ es'0)).
      constructor. apply const_list_app;auto. }
  Qed.

  Lemma trap_reduce hs s f es hs' s' f' es' lh :
    lfilled 0 lh [AI_trap] es -> reduce hs s f es hs' s' f' es' ->
    exists lh', lfilled 0 lh' [AI_trap] es' /\ (hs, s, f) = (hs', s', f').
  Proof.
    intros Hfill Hred.
    destruct lh;try done.
    eapply trap_reduce_length in Hfill;eauto.
    destruct Hfill as [? [? [? ?]]].
    eexists;eauto.
  Qed.

  Lemma lfilled_reducible i lh e LI σ :
    lfilled i lh e LI ->
    reducible e σ ->
    reducible LI σ.
  Proof.
    intros Hfill [obs [e' [σ' [efs Hred]]]].
    unfold reducible, language.reducible.
    specialize (lfilled_swap e' Hfill) as [LI' HLI'].
    exists [], LI', σ', [].
    destruct σ as [[[? ?] ?] ?].
    destruct σ' as [[[? ?] ?] ?].
    rewrite /= /iris.prim_step in Hred.
    destruct Hred as [Hred [-> ->]].
    split;auto.
    by eapply r_label => //.
  Qed.

  Lemma local_frame_reducible n e hi s v i v' i' :
    reducible e (hi,s,v,i) ->
    reducible [AI_local n (Build_frame v i) e] (hi,s,v',i').
  Proof.
    intros [obs [e' [σ' [efs Hred]]]].
    unfold reducible, language.reducible.
    destruct σ' as [[[? ?] ?] ?].
    exists [], [AI_local n (Build_frame l i0) e'], (s0,s1,v',i'), [].
    rewrite /= /iris.prim_step in Hred.
    destruct Hred as [Hred [-> ->]]. eauto.
    split;auto.
    eapply r_local => //.
  Qed.

  Lemma local_frame_lfilled_reducible j lh LI n e hi s v i v' i' :
    lfilled j lh e LI ->
    reducible e (hi,s,v,i) ->
    reducible [AI_local n (Build_frame v i) LI] (hi,s,v',i').
  Proof.
    intros Hfill Hred.
    apply lfilled_reducible with (i:=j) (lh:=lh) (LI:=LI) in Hred;auto.
    apply local_frame_reducible. auto.
  Qed.

  
  Lemma reduce_focus hs s f es hs' s' f' es':
    reduce hs s f es hs' s' f' es' ->
    (exists k lh vs e es'', const_list vs /\ (is_const e -> False) /\
                         reduce hs s f (vs ++ [e]) hs' s' f' es''  /\
                         lfilled k lh (vs ++ [e]) es /\ 
                         lfilled k lh es'' es')
    \/
      (exists k lh bef aft, const_list bef /\ (bef ++ aft = [] -> False) /\
                         lfilled k lh (bef ++ [AI_trap] ++ aft) es /\
                         lfilled k lh [AI_trap] es' /\
                         (hs, s, f) = (hs', s', f')).
  Proof.
    intro Hred.
    induction Hred ;
      (try by left ; eexists 0, (LH_base [] []), [] , _, _ ;
       repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
       (try by rewrite app_nil_r) ; constructor ) ;  
      (try by left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _)] , _, _ ;
       repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
       (try by rewrite app_nil_r) ; constructor) ; 
      (try by left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _) ;
                                                  AI_basic (BI_const _) ] , _, _ ;
       repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
       (try by rewrite app_nil_r) ; constructor ).
    { destruct H ;
        last (by right ; unfold lfilled, lfill in H0 ;
              destruct lh as [bef aft|] ; last (by false_assumption) ;
              remember (const_list bef) as b eqn:Hbef ; destruct b ;
              last (by false_assumption) ;
              move/eqP in H0 ;
              exists 0, (LH_base [] []), bef, aft ; repeat split ; (try by simpl) ;
              [ intro Habs ; apply app_eq_nil in Habs as [-> ->] ;
                rewrite app_nil_l app_nil_r in H0 ; by apply H
              | unfold lfilled, lfill ; simpl ; subst ; rewrite app_nil_r]) ;
        (try by left ; eexists 0, (LH_base [] []), [] , _, _ ;
         repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ; 
         (try by rewrite app_nil_r) ; constructor ;
         ((by apply (rs_br _ H H0 H1)) +
            (by apply (rs_return _ H H0 H1)) +
            constructor)
        ) ;
        (try by left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _)] , _, _ ;
         repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
         (try by rewrite app_nil_r) ; constructor ; constructor
        ); 
        (try by left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _) ;
                                                    AI_basic (BI_const _) ] , _, _ ;
         repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
         (try by rewrite app_nil_r) ; constructor ; constructor
        );
        (try by left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _) ;
                                                    AI_basic (BI_const _) ;
                                                    AI_basic (BI_const _) ] , _, _ ;
         repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
         (try by rewrite app_nil_r) ; constructor ; constructor
        ) ;
        left ; eexists 0, (LH_base [] []), _, _, _ ;
        repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r) ;
        try  constructor.
      done. apply (rs_block _ H H0 H1 H2). done. apply (rs_loop _ H H0 H1 H2).
      instantiate (1 := [v]) => //=. by rewrite H.
      instantiate (1 := AI_basic (BI_tee_local i)) => //=.
      by constructor. by rewrite app_nil_r. }
    left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _)], _, _.
    repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
      (try by rewrite app_nil_r). 
    apply (r_call_indirect_success _ H H0 H1).
    left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _)], _, _.
    repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
      (try by rewrite app_nil_r). 
    apply (r_call_indirect_failure1 _ H H0 H1).
    left ; eexists 0, (LH_base [] []), _, _, _ ; repeat split ;
      (try unfold lfilled, lfill => //=) ; (try done) ; (try by rewrite app_nil_r).
    rewrite H1 ; by apply v_to_e_is_const_list. done.
    apply (r_invoke_native _ _ H H0 H1 H2 H3 H4 H5 H6 H7 H8).
    (* left ; eexists 0, (LH_base [] []), _, _, _ ; repeat split ;
    (try unfold lfilled, lfill => //=) ; (try done) ; (try by rewrite app_nil_r).
  rewrite H1 ; by apply v_to_e_is_const_list. done.
  apply (r_invoke_host_success _ H H0 H1 H2 H3 H4 H5).
  left ; eexists 0, (LH_base [] []), _, _, _ ; repeat split ;
    (try unfold lfilled, lfill => //=) ; (try done) ; (try by rewrite app_nil_r).
  rewrite H1 ; by apply v_to_e_is_const_list. done.
  apply (r_invoke_host_diverge _ H H0 H1 H2 H3 H4 H5).*)
    left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _)], _, _.
    repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
      (try by rewrite app_nil_r). 
    apply (r_set_local _ _ H H0 H1).
    left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _)], _, _.
    repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
      (try by rewrite app_nil_r). 
    apply (r_load_success _ _ H H0 H1).
    left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _)], _, _.
    repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
      (try by rewrite app_nil_r). 
    apply (r_load_failure _ _ H H0 H1).
    left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _)], _, _.
    repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
      (try by rewrite app_nil_r). 
    apply (r_load_packed_success _ _ H H0 H1).
    left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _)], _, _.
    repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
      (try by rewrite app_nil_r). 
    apply (r_load_packed_failure _ _ H H0 H1).
    left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _) ;
                                        AI_basic (BI_const _)], _, _.
    repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
      (try by rewrite app_nil_r). 
    apply (r_store_success _ _ H H0 H1 H2).
    left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _) ;
                                        AI_basic (BI_const _)], _, _.
    repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
      (try by rewrite app_nil_r). 
    apply (r_store_failure _ _ H H0 H1 H2).
    left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _) ;
                                        AI_basic (BI_const _)], _, _.
    repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
      (try by rewrite app_nil_r). 
    apply (r_store_packed_success _ _ H H0 H1 H2).
    left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _) ;
                                        AI_basic (BI_const _)], _, _.
    repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
      (try by rewrite app_nil_r). 
    apply (r_store_packed_failure _ _ H H0 H1 H2).
    left ; eexists 0, (LH_base [] []), [], _, _.
    repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
      (try by rewrite app_nil_r). 
    apply (r_current_memory _ H H0 H1).
    left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _)], _, _.
    repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
      (try by rewrite app_nil_r). 
    apply (r_grow_memory_success _ H H0 H1 H2).
    left ; eexists 0, (LH_base [] []), [AI_basic (BI_const _)], _, _.
    repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
      (try by rewrite app_nil_r). 
    apply (r_grow_memory_failure _ _ H H0 H1).
    destruct IHHred as [ (k0 & lh0 & vs & e & es'' & Hvs & He & Hred' & Hes & Hes')
                       | (k0 & lh0 & bef & aft & Hbef & Hba & Hfill & Hfill' & Hσ) ].
    destruct (lfilled_trans2 _ _ _ _ _ _ _ _ _ _ Hes Hes' H H0) as (lh' & Hfill1 & Hfill2).
    left ; exists (k0 + k), lh', vs, e, es'' => //=.  
    destruct (lfilled_trans2 _ _ _ _ _ _ _ _ _ _ Hfill Hfill' H H0)
      as (lh' & Hfill1 & Hfill2).
    right ; exists (k0 + k), lh', bef, aft => //=.
    Unshelve.
    exact AI_trap.
    exact [AI_trap].
    exact AI_trap.
    exact [].
    (* A few uninstantiated variables left on shelf, due to host being replaced by a dummy now *)
  Qed.

  
  Lemma reduce_append: forall e es es' σ σ' efs obs,
      reducible es σ ->
      prim_step (es ++ [e]) σ obs es' σ' efs ->
      (es' = take (length es' - 1) es' ++ [e] /\
         prim_step es σ obs (take (length es' - 1) es') σ' efs)
      \/ (exists lh lh', lfilled 0 lh [AI_trap] es' /\ lfilled 0 lh' [AI_trap] es /\ σ = σ'). (* prim_step es σ obs [AI_trap] σ' efs). *)
  Proof.
    destruct σ as [[[??]?]?].
    destruct σ' as [[[??]?]?].
    intros efs obs Hred Hstep.
    destruct Hstep as (Hstep & -> & ->).
    destruct Hred as (obs & es1 & [[[??]?]?] & efs & (Hred & -> & ->)).
    destruct (reduce_focus _ _ _ _ _ _ _ _ Hstep) as [ (k & lh & vs & e0 & es'' &
                                                          Hvs & He & Hred' & Hes & Hes')
                                                     | (k & lh & bef & aft & Hbef & Hba &
                                                          Hfill & Hfill' & Hσ)].
    { destruct k.
      { unfold lfilled, lfill in Hes. destruct lh as [bef aft|]; last by false_assumption.
        remember (const_list bef) as b eqn:Hbef ; destruct b ; last by false_assumption.
        move/eqP in Hes.
        destruct aft. { rewrite app_nil_r in Hes. rewrite app_assoc in Hes.
                        apply app_inj_tail in Hes as [Hes _].
                        exfalso ; eapply values_no_reduce ; first exact Hred. rewrite Hes.
                        unfold const_list ; rewrite forallb_app.
                        unfold const_list in Hvs ; rewrite Hvs.
                        unfold const_list in Hbef ; rewrite <- Hbef.
                        done. }
        get_tail a aft ys y Htail. rewrite Htail in Hes. repeat rewrite app_assoc in Hes.
        apply app_inj_tail in Hes as [Hes Hy]. left.
        unfold lfilled, lfill in Hes'. rewrite <- Hbef in Hes'. move/eqP in Hes'.
        rewrite Htail in Hes'. rewrite Hes'. repeat rewrite app_assoc.
        rewrite app_length. simpl. rewrite Nat.add_sub.
        rewrite take_app. repeat split => //=. by subst. subst.
        apply (r_label (k:=0) (lh:=LH_base bef ys) (es:=vs++[e0]) (es':=es'')) ; (try done) ;
          unfold lfilled, lfill ; rewrite <- Hbef ; repeat rewrite <- app_assoc => //=. }
      unfold lfilled, lfill in Hes ; fold lfill in Hes.
      destruct lh ; first by false_assumption.
      remember (const_list l2) as b eqn:Hl2 ; destruct b ; last by false_assumption.
      remember (lfill _ _ _) as fill ; destruct fill ; last by false_assumption.
      move/eqP in Hes.
      destruct l4. { apply app_inj_tail in Hes as [Hes _].
                     exfalso ; eapply values_no_reduce ; first exact Hred. by subst. }
      get_tail a l4 ys y Htail. rewrite Htail in Hes. rewrite app_comm_cons in Hes.
      repeat rewrite app_assoc in Hes.
      apply app_inj_tail in Hes as [Hes Hy]. left.
      unfold lfilled, lfill in Hes' ; fold lfill in Hes'.
      rewrite <- Hl2 in Hes'.
      remember (lfill _ _ es'') as fill' ; destruct fill' ; last by false_assumption.
      move/eqP in Hes'.
      rewrite Htail in Hes'. rewrite Hes'. rewrite app_comm_cons. repeat rewrite app_assoc.
      rewrite app_length. simpl. rewrite Nat.add_sub.
      rewrite take_app. repeat split => //=. by subst. subst.
      apply (r_label (k:=S k) (lh:=LH_rec l2 n l3 lh ys) (es:=vs++[e0]) (es':=es'')) ;
        (try done) ;
        unfold lfilled, lfill ; fold lfill ; rewrite <- Hl2.
      by rewrite <- Heqfill.
      by rewrite <- Heqfill'. }
    destruct k. { unfold lfilled, lfill in Hfill.
                  destruct lh as [bef0 aft0 |]; last by false_assumption.
                  remember (const_list bef0) as b eqn:Hbef0 ; destruct b ;
                    last by false_assumption.
                  move/eqP in Hfill. destruct aft0. destruct aft.
                  { rewrite app_nil_r in Hfill. repeat rewrite app_assoc in Hfill.
                    replace ([AI_trap] ++ [])%SEQ with ([AI_trap] ++ [])%list in Hfill => //=.
                    rewrite app_nil_r in Hfill.                    
                    apply app_inj_tail in Hfill as [Hes _].
                    subst ; exfalso ; values_no_reduce.
                    unfold const_list ; rewrite forallb_app.
                    unfold const_list in Hbef ; unfold const_list in Hbef0.
                    by rewrite Hbef ; rewrite <- Hbef0. }
                  rewrite app_nil_r in Hfill.
                  replace (bef ++ [AI_trap] ++ a :: aft)%SEQ with
                    (bef ++ [AI_trap] ++ a :: aft)%list in Hfill => //=.
                  get_tail a aft ys y Htail.
                  rewrite Htail in Hfill.
                  repeat rewrite app_assoc in Hfill.
                  apply app_inj_tail in Hfill as [Hes Hy].
                  right ; exists (LH_base bef0 []), (LH_base (bef0 ++ bef) ys) ;
                    repeat split => //=.
                  unfold lfilled, lfill, const_list. rewrite forallb_app.
                  unfold const_list in Hbef0 ; unfold const_list in Hbef.
                  rewrite <- Hbef0 ; rewrite Hbef => //=. rewrite Hes.
                  rewrite <- app_assoc => //=.
                  by inversion Hσ.
                  get_tail a aft0 ys y Htail.
                  rewrite Htail in Hfill.
                  repeat rewrite app_assoc in Hfill.
                  apply app_inj_tail in Hfill as [Hes Hy].
                  right ; exists (LH_base bef0 (a :: aft0)), (LH_base (bef0 ++ bef) (aft ++ ys)) ;
                    repeat split => //=.
                  unfold lfilled, lfill, const_list. rewrite forallb_app.
                  unfold const_list in Hbef0 ; unfold const_list in Hbef.
                  rewrite <- Hbef0 ; rewrite Hbef => //=. rewrite Hes.
                  rewrite <- app_assoc => //=.
                  by inversion Hσ.
    }
    unfold lfilled, lfill in Hfill ; fold lfill in Hfill.
    destruct lh ; first by false_assumption.
    remember (const_list l2) as b eqn:Hl2 ; destruct b ; last by false_assumption.
    remember (lfill _ _ _) as fill ; destruct fill ; last by false_assumption.
    move/eqP in Hfill. destruct l4. { apply app_inj_tail in Hfill as [Hes _].
                                      exfalso ; eapply values_no_reduce ;
                                        first exact Hred. by subst. }
    get_tail a l4 ys y Htail. rewrite Htail in Hfill. rewrite app_comm_cons in Hfill.
    repeat rewrite app_assoc in Hfill.
    apply app_inj_tail in Hfill as [Hes Hy]. left.
    unfold lfilled, lfill in Hfill' ; fold lfill in Hfill'.
    rewrite <- Hl2 in Hfill'.
    remember (lfill _ _ [AI_trap]) as fill' ; destruct fill' ; last by false_assumption.
    move/eqP in Hfill'.
    rewrite Htail in Hfill'. rewrite Hfill'. rewrite app_comm_cons. repeat rewrite app_assoc.
    rewrite app_length. simpl. rewrite Nat.add_sub.
    rewrite take_app. repeat split => //=. by subst. subst.
    apply (r_label (k:=S k) (lh:=LH_rec l2 n l3 lh ys) (es:=bef ++ [AI_trap] ++ aft)
                   (es':=[AI_trap])) ;
      unfold lfilled, lfill ; fold lfill.
    inversion Hσ ; subst ; constructor.
    apply (rs_trap (lh := LH_base bef aft)) ; unfold lfilled, lfill.
    intro Habs ; apply app_eq_unit in Habs as [[-> Habs] | [_ Habs]] ; last by inversion Habs.
    apply app_eq_unit in Habs as [[ Habs _] | [_ ->]] ; first by inversion Habs.
    by apply Hba.
    by rewrite Hbef.
    rewrite <- Hl2. by rewrite <- Heqfill.
    rewrite <- Hl2. by rewrite <- Heqfill'.
  Qed.

  
  Lemma br_no_reduce hs s f lh i es hs' s' f' es' :
    lfilled 0 lh [AI_basic (BI_br i)] es ->
    reduce hs s f es hs' s' f' es' -> False.
  Proof.
    cut (forall n, length es < n -> lfilled 0 lh [AI_basic (BI_br i)] es ->
              reduce hs s f es hs' s' f' es' -> False).
    { intro Hn ; apply (Hn (S (length es))) ; lia. }
    intro n. generalize dependent es. generalize dependent lh. generalize dependent es'.
    induction n ; intros es' lh es Hlen Hfill Hred ; first by inversion Hlen.
    unfold lfilled, lfill in Hfill. destruct lh as [vs esf|] ; last by false_assumption.
    remember (const_list vs) as b eqn:Hvs ; destruct b ; last by false_assumption.
    move/eqP in Hfill.
    induction Hred ; try by found_intruse (AI_basic (BI_br i)) Hfill Hxl1.
    { destruct H ; try by found_intruse (AI_basic (BI_br i)) Hfill Hxl1.
      - found_intruse (AI_basic (BI_br i)) Hfill Hxl1.
        apply in_app_or in Hxl1 as [Habs | Habs].
        intruse_among_values vs0 Habs H. inversion Habs ; inversion H3.
      - found_intruse (AI_basic (BI_br i)) Hfill Hxl1.
        apply in_app_or in Hxl1 as [Habs | Habs].
        intruse_among_values vs0 Habs H. inversion Habs ; inversion H3.
      - found_intruse (AI_basic (BI_br i)) Hfill Hxl1.
        rewrite Hxl1 in H ; inversion H.
      - rewrite Hfill in H0. unfold lfilled, lfill in H0.
        destruct lh ; last by false_assumption.
        remember (const_list l) as b eqn:Hl ; destruct b ; last by false_assumption.
        move/eqP in H0. apply first_values in H0 as (_ & Habs & _) ;
                          (try done) ; try by intros [? ?]. }
    - found_intruse (AI_basic (BI_br i)) Hfill Hxl1.
      apply in_app_or in Hxl1 as [Habs | Habs].
      assert (const_list ves) as Hconst ; last by intruse_among_values ves Habs Hconst.
      rewrite H1 ; by apply v_to_e_is_const_list. inversion Habs ; inversion H9.
    - rewrite Hfill in H. unfold lfilled, lfill in H.
      destruct k. { destruct lh ; last by false_assumption.
                    remember (const_list l) as b eqn:Hl ; destruct b ;
                      last by false_assumption.
                    move/eqP in H.
                    destruct l. { destruct l0. { rewrite app_nil_l app_nil_r in H. 
                                                 unfold lfilled, lfill in H0.
                                                 simpl in H0. move/eqP in H0.
                                                 rewrite app_nil_r in H0. subst.
                                                 apply IHHred => //=. }
          destruct (first_non_value_reduce _ _ _ _ _ _ _ _ Hred) as
            (vs0 & e0 & es0 & Hvs0 & He0 & Hes). rewrite Hfill H in Hlen.
                                  rewrite Hes in H. simpl in H.
                                  rewrite <- app_assoc in H. rewrite <- app_comm_cons in H.
                                  apply first_values in H as (_ & He0' & _) ;
                                    (try done) ; (try by intros Hconst ; apply const_list_singleton, const_list_to_val in Hconst as [??] ; unfold to_val in He0 ; destruct He0 as [?|?] ; [congruence | subst]).
                                  apply (IHn es' (LH_base vs0 es0) es) => //=.
                                  simpl in Hlen. rewrite app_length in Hlen. simpl in Hlen.
                                  lia. unfold lfilled, lfill ; rewrite Hvs0 ; by subst. }
        destruct (first_non_value_reduce _ _ _ _ _ _ _ _ Hred) as
          (vs0 & e0 & es0 & Hvs0 & He0 & Hes). rewrite Hfill H in Hlen.
                    rewrite Hes in H. simpl in H.
                    rewrite <- app_assoc in H. rewrite app_comm_cons in H.
                    rewrite <- (app_comm_cons es0) in H. rewrite app_assoc in H.
                    apply first_values in H as (_ & He0' & _) ;
                      (try done) ; (try by (intros [? ?])).
                    apply (IHn es' (LH_base vs0 es0) es) => //=.
                    do 2 rewrite app_length in Hlen. simpl in Hlen.
                    lia. unfold lfilled, lfill ; rewrite Hvs0 ; by subst.
                    destruct e0 => // ; destruct b => //.
                    unfold to_val, iris.to_val in He0 ; simpl in He0.
                    destruct He0 as [? | ?] => //.
                    by const_list_app. }
      fold lfill in H. destruct lh ; first by false_assumption.
      remember (const_list l) as b eqn:Hl ; destruct b ; last by false_assumption.
      destruct (lfill _ _ _) ; last by false_assumption. move/eqP in H.
      apply first_values in H as (_ & Habs & _) ; (try done) ; try by intros [? ?].
  Qed.

  Lemma lfilled_first_non_value hs s f es hs' s' f' es' k lh les les':
    reduce hs s f es hs' s' f' es' ->
    lfilled k lh es les ->
    lfilled k lh es' les' ->
    exists vs e esf es' k0 lh0,
      const_list vs /\
        (forall n es LI, e = AI_label n es LI ->
                    (hs, s, f) = (hs', s', f') /\
                      (const_list LI \/ LI = [AI_trap] \/
                         exists k lh vs i, lfilled k lh (vs ++ [AI_basic (BI_br i)]) LI)) /\
        (is_const e -> False) /\ 
        reduce hs s f (vs ++ e :: esf) hs' s' f' es' /\
        lfilled k0 lh0 (vs ++ e :: esf) les /\
        lfilled k0 lh0 es' les'.
  Proof.
    intros Hred Hfill Hfill'.
    generalize dependent k ; generalize dependent lh.
    induction Hred as [ | | | | |
                        ? ? ? ? ? ? ? ? ? ? k0
                      | | | | | | |
                        ? ? ? ? ? k0
                      |
                        ? ? ? ? k0
                      |
                        ? ? ? ? ? k0
                      |
                        ? ? ? ? ? k0
                      |
                        ? ? ? ? ? ? k0
                      |
                        ? ? ? ? ? ? k0
                      |
                        ? ? ? ? ? ? k0
                      |
                        ? ? ? ? ? ? k0
                      | | | |
                        ? ? ? ? ? ? ? ? k0 lh0 ? ? ? ? ? ? | ];
      intros lh k Hfill Hfill'.
    { destruct H.
      - exists [AI_basic (BI_const v)], (AI_basic (BI_unop t op)), [],
          [AI_basic (BI_const (app_unop op v))], k, lh ; repeat split => //=.
        by apply r_simple, rs_unop.
      - exists [AI_basic (BI_const v1); AI_basic (BI_const v2)], (AI_basic (BI_binop t op)),
          [], [AI_basic (BI_const v)], k, lh ; repeat split => //=.
        by apply r_simple, rs_binop_success.
      - exists [AI_basic (BI_const v1); AI_basic (BI_const v2)], (AI_basic (BI_binop t op)),
          [], [AI_trap], k, lh ; repeat split => //=.
        by apply r_simple, rs_binop_failure.
      - exists [AI_basic (BI_const (VAL_int32 c))], (AI_basic (BI_testop T_i32 testop)), [],
          [AI_basic (BI_const (VAL_int32 (wasm_bool (app_testop_i (e:=i32t) testop c))))],
          k, lh ; repeat split => //=.
        by apply r_simple, rs_testop_i32.
      - exists [AI_basic (BI_const (VAL_int64 c))], (AI_basic (BI_testop T_i64 testop)), [],
          [AI_basic (BI_const (VAL_int32 (wasm_bool (app_testop_i (e:=i64t) testop c))))],
          k, lh ; repeat split => //=.
        by apply r_simple, rs_testop_i64.
      - exists [AI_basic (BI_const v1) ; AI_basic (BI_const v2)], (AI_basic (BI_relop t op)), [],
          [AI_basic (BI_const (VAL_int32 (wasm_bool (app_relop op v1 v2))))], k, lh ;
          repeat split => //=. by apply r_simple, rs_relop.
      - exists [AI_basic (BI_const v)], (AI_basic (BI_cvtop t2 CVO_convert t1 sx)), [],
          [AI_basic (BI_const v')], k, lh ; repeat split => //=.
        by apply r_simple, rs_convert_success.
      - exists [AI_basic (BI_const v)], (AI_basic (BI_cvtop t2 CVO_convert t1 sx)), [],
          [AI_trap], k, lh ; repeat split => //=.
        by apply r_simple, rs_convert_failure.
      - exists [AI_basic (BI_const v)], (AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)), [],
          [AI_basic (BI_const (wasm_deserialise (bits v) t2))], k, lh ; repeat split => //=.
        by apply r_simple, rs_reinterpret.
      - exists [], (AI_basic BI_unreachable), [], [AI_trap], k, lh ; repeat split => //=.
        by apply r_simple, rs_unreachable.
      - exists [], (AI_basic (BI_nop)), [], [], k, lh ; repeat split => //=.
        by apply r_simple, rs_nop.
      - exists [AI_basic (BI_const v)], (AI_basic BI_drop), [], [], k, lh ; repeat split => //=.
        by apply r_simple, rs_drop.
      - exists [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
           AI_basic (BI_const (VAL_int32 n))], (AI_basic BI_select), [],
          [AI_basic (BI_const v2)], k, lh ; repeat split => //=.
        by apply r_simple, rs_select_false.
      - exists [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
           AI_basic (BI_const (VAL_int32 n))], (AI_basic BI_select), [],
          [AI_basic (BI_const v1)], k, lh ; repeat split => //=.
        by apply r_simple, rs_select_true.
      - exists vs, (AI_basic (BI_block (Tf t1s t2s) es)), [],
          [AI_label m [] (vs ++ to_e_list es)], k, lh ; repeat split => //=.
        by apply r_simple, (rs_block _ H H0 H1 H2).
      - exists vs, (AI_basic (BI_loop (Tf t1s t2s) es)), [],
          [AI_label n [AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)],
          k, lh ; repeat split => //=.
        by apply r_simple, (rs_loop _ H H0 H1 H2).
      - exists [AI_basic (BI_const (VAL_int32 n))], (AI_basic (BI_if tf e1s e2s)), [],
          [AI_basic (BI_block tf e2s)], k, lh ; repeat split => //=.
        by apply r_simple, rs_if_false.
      - exists [AI_basic (BI_const (VAL_int32 n))], (AI_basic (BI_if tf e1s e2s)), [],
          [AI_basic (BI_block tf e1s)], k, lh ; repeat split => //=.
        by apply r_simple, rs_if_true.
      - exists [], (AI_label n es vs), [], vs, k, lh ; repeat split => //=.
        by inversion H0 ; subst ; left.
        by apply r_simple, rs_label_const.
      - exists [], (AI_label n es [AI_trap]), [], [AI_trap], k, lh ; repeat split => //=.
        by inversion H ; right ; left.
        by apply r_simple, rs_label_trap.
      - exists [], (AI_label n es LI), [], (vs ++ es), k, lh ; repeat split => //=.
        right ; right. inversion H2 ; subst. by exists i, lh0, vs, i.
      by apply r_simple, (rs_br _ H H0 H1).
      - exists [AI_basic (BI_const (VAL_int32 n))], (AI_basic (BI_br_if i)), [],
          [], k, lh ; repeat split => //=.
        by apply r_simple, rs_br_if_false.
      - exists [AI_basic (BI_const (VAL_int32 n))], (AI_basic (BI_br_if i)), [],
          [AI_basic (BI_br i)], k, lh ; repeat split => //=.
        by apply r_simple, rs_br_if_true.
      - exists [AI_basic (BI_const (VAL_int32 c))], (AI_basic (BI_br_table iss i)),
          [], [AI_basic (BI_br j)], k, lh ; repeat split => //=.
        by apply r_simple, rs_br_table.
      - exists [AI_basic (BI_const (VAL_int32 c))], (AI_basic (BI_br_table iss i)),
          [], [AI_basic (BI_br i)], k, lh ; repeat split => //=.
        by apply r_simple, rs_br_table_length.
      - exists [], (AI_local n f0 es), [], es, k, lh ; repeat split => //=.
        by apply r_simple, rs_local_const.
      - exists [], (AI_local n f0 [AI_trap]), [], [AI_trap], k, lh ; repeat split => //=.
        by apply r_simple, rs_local_trap.
      - exists [], (AI_local n f0 es), [], vs, k, lh ; repeat split => //=.
        by apply r_simple, (rs_return _ H H0 H1).
      - exists [v], (AI_basic (BI_tee_local i)), [], [v ; v; AI_basic (BI_set_local i)],
          k, lh ; repeat split => //=. apply andb_true_iff ; split => //=.
        by apply r_simple, rs_tee_local.
      - unfold lfilled, lfill in H0. destruct lh0 as [bef aft|] ; last by false_assumption.
        remember (const_list bef) as b eqn:Hbef ; destruct b ; last by false_assumption.
        move/eqP in H0. subst.
        exists bef, (AI_trap), aft, [AI_trap], k, lh ; repeat split => //=.
        apply r_simple, (rs_trap (lh := (LH_base bef aft))) => //=.
        unfold lfilled, lfill ; by rewrite <- Hbef. }
    - exists [], (AI_basic (BI_call i)), [], [AI_invoke a], k, lh ; repeat split => //=.
      by apply r_call.
    - exists [AI_basic (BI_const (VAL_int32 c))], (AI_basic (BI_call_indirect i)), [],
        [AI_invoke a], k, lh ; repeat split => //=.
      by apply (r_call_indirect_success _ H H0 H1).
    - exists [AI_basic (BI_const (VAL_int32 c))], (AI_basic (BI_call_indirect i)), [],
        [AI_trap], k, lh ; repeat split => //=.
      by apply (r_call_indirect_failure1 _ H H0 H1).
    - exists [AI_basic (BI_const (VAL_int32 c))], (AI_basic (BI_call_indirect i)), [],
        [AI_trap], k, lh ; repeat split => //=.
      by apply (r_call_indirect_failure2 _ _ H).
    - exists ves, (AI_invoke a), [], [AI_local m f' [AI_basic (BI_block (Tf [] t2s) es)]],
        k, lh ; repeat split => //=.
      rewrite H1 ; by apply v_to_e_is_const_list.
      by apply (r_invoke_native _ _ H H0 H1 H2 H3 H4 H5 H6 H7 H8).
    - exists ves, (AI_invoke a), [], (result_to_stack r),
        k, lh ; repeat split => //=.
    (*  rewrite H1 ; by apply v_to_e_is_const_list.
    by apply (r_invoke_host_success _ H H0 H1 H2 H3 H4 H5).*)
    - exists ves, (AI_invoke a), [], (ves ++ [AI_invoke a]),
      k, lh ; repeat split => //=.
    (* rewrite H1 ; by apply v_to_e_is_const_list.
    by apply (r_invoke_host_diverge _ H H0 H1 H2 H3 H4 H5).*)
    - exists [], (AI_basic (BI_get_local j)), [], [AI_basic (BI_const v)], k, lh ;
      repeat split => //=.
      by apply r_get_local.
    - exists [AI_basic (BI_const v)], (AI_basic (BI_set_local i)), [], [], k, lh ;
        repeat split => //=.
      by apply (r_set_local _ _ H H0 H1).
    - exists [], (AI_basic (BI_get_global i)), [], [AI_basic (BI_const v)], k, lh ;
        repeat split => //=.
      by apply r_get_global.
    - exists [AI_basic (BI_const v)], (AI_basic (BI_set_global i)), [], [], k, lh ;
        repeat split => //=.
      by apply r_set_global.
    - exists [AI_basic (BI_const (VAL_int32 k0))], (AI_basic (BI_load t None a off)),
        [], [AI_basic (BI_const (wasm_deserialise bs t))], k, lh ; repeat split => //=.
      by apply (r_load_success _ _ H H0 H1).
    - exists [AI_basic (BI_const (VAL_int32 k0))], (AI_basic (BI_load t None a off)),
        [], [AI_trap], k, lh ; repeat split => //=.
      by apply (r_load_failure _ _ H H0 H1).
    - exists [AI_basic (BI_const (VAL_int32 k0))], (AI_basic (BI_load t (Some (tp, sx)) a off)),
        [], [AI_basic (BI_const (wasm_deserialise bs t))], k, lh ; repeat split => //=.
      by apply (r_load_packed_success _ _ H H0 H1).
    - exists [AI_basic (BI_const (VAL_int32 k0))], (AI_basic (BI_load t (Some (tp, sx)) a off)),
        [], [AI_trap], k, lh ; repeat split => //=.
      by apply (r_load_packed_failure _ _ H H0 H1).
    - exists [AI_basic (BI_const (VAL_int32 k0)); AI_basic (BI_const v)],
        (AI_basic (BI_store t None a off)), [], [], k, lh ; repeat split => //=.
      by apply (r_store_success _ _ H H0 H1 H2).
    - exists [AI_basic (BI_const (VAL_int32 k0)); AI_basic (BI_const v)],
        (AI_basic (BI_store t None a off)), [], [AI_trap], k, lh ; repeat split => //=.
      by apply (r_store_failure _ _ H H0 H1 H2).
    - exists [AI_basic (BI_const (VAL_int32 k0)); AI_basic (BI_const v)],
        (AI_basic (BI_store t (Some tp) a off)), [], [], k, lh ; repeat split => //=.
      by apply (r_store_packed_success _ _ H H0 H1 H2).
    - exists [AI_basic (BI_const (VAL_int32 k0)); AI_basic (BI_const v)],
        (AI_basic (BI_store t (Some tp) a off)), [], [AI_trap], k, lh ; repeat split => //=.
      by apply (r_store_packed_failure _ _ H H0 H1 H2).
    - exists [], (AI_basic BI_current_memory), [],
        [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin n))))],
        k, lh ; repeat split => //=.
      by apply (r_current_memory _ H H0 H1).
    - exists [AI_basic (BI_const (VAL_int32 c))], (AI_basic BI_grow_memory), [],
        [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin n))))],
        k, lh ; repeat split => //=.
      by apply (r_grow_memory_success _ H H0 H1 H2).
    - exists [AI_basic (BI_const (VAL_int32 c))], (AI_basic BI_grow_memory), [],
        [AI_basic (BI_const (VAL_int32 int32_minus_one))],
        k, lh ; repeat split => //=.
      by apply (r_grow_memory_failure _ _ H H0 H1).
    - destruct (lfilled_trans2 _ _ _ _ _ _ _ _ _ _ H H0 Hfill Hfill')
        as (lh1 & Hfill1 & Hfill2).
      apply (IHHred lh1 (k0 + k)) => //=.
    - exists [], (AI_local n f es), [], [AI_local n f' es'], k, lh ; repeat split => //=.
      by apply r_local.
  Qed.

  Lemma reduce_return_trap_label es hs' s' f' vs n es'0 es'' es' :
    reduce hs' s' f' es hs' s' f' es' ->
    const_list vs ->
    es = (vs ++ [AI_label n es'0 [AI_trap]] ++ es'') ->
    ∃ lh', lfilled 0 lh' [AI_trap] es'.
  Proof.
    intros Hred.
    revert vs es''. induction Hred;[|intros vs es'' Hconst Heq..].
    { induction H; intros vs' es'' Hconst Heq;subst.
      all: try (do 2 destruct vs' =>//).
      all: try (do 3 destruct vs' =>//).
      all: try (apply const_list_concat_inv in Heq as [? [? ?]];auto; done).
      destruct vs',es'' =>//.
      rewrite app_nil_r app_nil_l in Heq. simplify_eq.
      exists (LH_base [] []). by cbn.
      1,2: destruct vs' =>//.
      destruct vs',es'' =>//.
      exists (LH_base [] []). by cbn.
      1,2: destruct vs' =>//.
      destruct vs'=>//;[|destruct vs'=>//].
      destruct es''=>//.
      { apply lfilled_Ind_Equivalent in H1. inversion H1;subst.
        inversion Heq;subst.
        do 3 (destruct vs0 || destruct vs || destruct es'0 || destruct es') =>//.
        inversion Heq;subst.
        do 2 destruct vs0 =>//. }
      { destruct vs',es'' =>//. destruct es'' =>//.
        rewrite app_nil_l in Heq. inversion Heq;subst. done.
        1,2: do 2 destruct vs' =>//. }
      { apply lfilled_Ind_Equivalent in H0. inversion H0;subst.
        apply const_list_concat_inv in H1 as [? [? ?]];auto; done. }
    }
    all: try (subst; do 2 destruct vs =>//).
    all: try (subst; do 3 destruct vs =>//).
    subst. apply const_list_concat_inv in Heq as [? [? ?]];auto. done. apply v_to_e_is_const_list.
    subst.
    apply lfilled_one_depth_trap in H as Hk;auto.
    destruct Hk as [-> | ->].
    { apply lfilled_Ind_Equivalent in H. inversion H;subst.
      apply const_list_snoc_eq3 in H1;auto.
      2: eapply reduce_not_nil;eauto.
      2: eapply values_no_reduce => //.
      2: intros -> ; eapply AI_trap_irreducible => //.
      destruct H1 as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst2]]]]].
      subst.
      edestruct IHHred as [lh' Hlh'];eauto.
      apply lfilled_Ind_Equivalent in Hlh'.
      inversion Hlh';subst.
      apply lfilled_Ind_Equivalent in H0.
      inversion H0;subst.
      exists (LH_base (vs0 ++ vs) (es'2 ++ es'1)).
      assert (vs0 ++ (vs ++ [AI_trap] ++ es'2) ++ es'1 = (vs0 ++ vs) ++ [AI_trap] ++ (es'2 ++ es'1))%SEQ as Heq.
      { repeat erewrite app_assoc. auto. }
      erewrite Heq. apply lfilled_Ind_Equivalent. constructor.
      apply const_list_app. auto.
    }
    { apply lfilled_Ind_Equivalent in H.
      inversion H;subst.
      apply first_values in H2 as [Heq1 [Heq2 Heq3]];auto.
      simplify_eq. apply lfilled_Ind_Equivalent in H6.
      apply filled_singleton in H6 as [? [? ?]].
      3: eapply reduce_not_nil;eauto.
      2: intros;done.
      subst.
      apply val_head_stuck_reduce in Hred.
      done. all: by intros [? ?].
    }
  Qed.

  Lemma reduce_focus_one es1 hs s f hs' s' f' vs n es'0 LI es'' es' :
    reduce hs s f es1 hs' s' f' es' ->
    es1 = (vs ++ [AI_label n es'0 LI] ++ es'') ->
    const_list vs ->
    iris.to_val LI = None ->
    (∀ i j lh vs0, const_list vs0 -> lfilled i lh (vs0 ++ [AI_basic (BI_br j)]) LI -> False) ->
    ∃ LI', reduce hs s f LI hs' s' f' LI'.
  Proof.
    intros Hred.
    revert vs n es'0 LI es''.
    induction Hred;intros vs n' es'0 LI es'' Heq Hconst HLI Hnbr.
    all: try (subst; do 2 destruct vs =>//).
    all: try (subst; do 3 destruct vs =>//).
    { induction H;subst.
      all: try (do 2 destruct vs =>//).
      all: try (do 3 destruct vs =>//).
      all: try (apply const_list_concat_inv in Heq as [? [? ?]];auto; done).
      { destruct vs,es'' =>//.
        2: destruct vs =>//.
        2: destruct vs,es'' =>//.
        rewrite app_nil_l app_nil_r in Heq.
        simplify_eq.
        exfalso. apply const_list_to_val in H as [? ?].
        congruence. }
      { destruct vs,es'' =>//.
        2: destruct vs =>//.
        2: destruct vs,es'' =>//.
        rewrite app_nil_l app_nil_r in Heq.
        simplify_eq. }
      { destruct vs,es'' =>//.
        2: destruct vs =>//.
        2: destruct vs,es'' =>//.
        rewrite app_nil_l app_nil_r in Heq.
        simplify_eq. 
        apply Hnbr in H1. done. auto.
      }
      { destruct vs =>//.
        { inversion Heq;subst. done. }
        destruct vs =>//.
        { inversion Heq;subst. simpl in Hconst.
          apply andb_true_iff in Hconst as [? ?]. done. }
      }
      { apply lfilled_Ind_Equivalent in H0; inversion H0;subst.
        apply first_values in H1 as [? [? ?]];auto. done. all: by intros [? ?].
      }      
    }
    { subst. symmetry in Heq.
      apply const_list_snoc_eq in Heq as [-> [vs2 [? [? ?]]]];auto;subst.
      do 2 destruct vs2 =>//.
      apply v_to_e_is_const_list.
      unfold to_val, iris.to_val => /=.
      unfold iris.to_val in HLI.
      destruct (merge_values_list _) => //.
    }
    { subst.
      apply reduce_not_nil in Hred as Hnil.
      apply val_head_stuck_reduce in Hred as Hnval.
      apply lfilled_Ind_Equivalent in H.
      inversion H;subst.
      { apply const_list_snoc_eq3 in H1 as [? [? [? [? [? ?]]]]];auto;subst.
        eapply IHHred;eauto. by eapply values_no_reduce.
        by intros -> ; eapply AI_trap_irreducible. }
      { apply first_values in H1 as [? [? ?]];auto. simplify_eq.
        apply lfilled_Ind_Equivalent in H6.
        apply lfilled_swap with (es':=es') in H6 as Hfill'.
        destruct Hfill' as [LI' Hfill'].
        exists LI'. eapply r_label;eauto.
      }
    }
  Qed.

  Lemma trap_reduce_state_eq i lh es hs s f hs' s' f' es' :
    reduce hs s f es hs' s' f' es' ->
    lfilled i lh [AI_trap] es -> 
    (hs,s,f) = (hs',s',f').
  Proof.
    intros Hred. 
    revert i lh.
    induction Hred;auto.
    { subst. intros i lh Hfill%lfilled_Ind_Equivalent.
      inversion Hfill.
      all: subst.
      all: apply first_values in H0 as [? [? ?]];auto.
      all: done. }
    { subst. intros i lh Hfill%lfilled_Ind_Equivalent.
      inversion Hfill.
      all: subst.
      all: apply first_values in H0 as [? [? ?]];auto.
      all: done. }
    { subst. intros i' lh Hfill%lfilled_Ind_Equivalent.
      inversion Hfill.
      all: do 3 destruct vs =>//. }
    { subst. intros i' lh Hfill%lfilled_Ind_Equivalent.
      inversion Hfill.
      all: do 3 destruct vs =>//. }
    { subst. intros i' lh Hfill%lfilled_Ind_Equivalent.
      inversion Hfill.
      all: do 4 destruct vs =>//. }
    { subst. intros i' lh Hfill%lfilled_Ind_Equivalent.
      inversion Hfill.
      all: do 4 destruct vs =>//. }
    { subst. intros i' lh Hfill%lfilled_Ind_Equivalent.
      inversion Hfill.
      all: do 3 destruct vs =>//. }
    { intros i lh' Hlh'.
      eapply lfilled_singleton in Hlh' as [? [? ?]];[..|apply H];auto.
      eapply IHHred. apply H1.
      eapply reduce_not_nil;eauto.
      eapply values_no_reduce => //.
      intros -> ; eapply AI_trap_irreducible => //.
    }
    { intros i lh Hfill%lfilled_Ind_Equivalent.
      inversion Hfill;subst.
      all: do 2 destruct vs =>//. }
  Qed.

  Lemma trap_reduce_lfilled i lh es hs s f hs' s' f' es' :
    reduce hs s f es hs' s' f' es' ->
    lfilled i lh [AI_trap] es -> 
    exists lh' j, lfilled j lh' [AI_trap] es' ∧ j <= i.
  Proof.
    intros Hred.
    revert i lh.
    induction Hred;[|intros i' lh' Hfill%lfilled_Ind_Equivalent..].
    2-25: inversion Hfill;
    try done;
    try by destruct vs =>//;
    try by do 2 destruct vs =>//;
    try by do 3 destruct vs =>//;
    try by do 4 destruct vs =>//.
    { induction H;intros i' lh' Hfill%lfilled_Ind_Equivalent.
      all: inversion Hfill;
        try by destruct vs =>//;
        try by do 2 destruct vs =>//;
        try by do 3 destruct vs =>//.
      all: try apply first_values in H3 as [? [? ?]];auto;try done.
      all: try by do 2 destruct vs0 =>//.
      all: try by intros [? ?].
      { simplify_eq.
        destruct vs0,es'' =>//.
        erewrite app_nil_l in H0. simplify_eq.
        inversion H5;subst.
        apply const_list_app in H as [_ [H _]%const_list_app];done.
        2,3: destruct vs0 =>//.
        exists (LH_rec vs0 n0 es' lh' es''),(S k0). split;[|lia].
        apply lfilled_Ind_Equivalent;constructor;auto. }
      { simplify_eq.
        destruct vs,es'' =>//.
        erewrite app_nil_l in H. simplify_eq.
        inversion H4;subst.
        destruct vs,es' =>//.
        all: try by destruct vs =>//.
        exists (LH_base [] []),0. split;[|lia]. by cbn.
        do 2 destruct vs =>//. }
      { exfalso. simplify_eq.
        destruct vs0,es'' =>//.
        2,3: try by destruct vs0 =>//.
        erewrite app_nil_l in H2. simplify_eq.
        apply lfilled_Ind_Equivalent in H7.
        eapply lfilled_singleton in H7 ;[..|apply H1];auto.
        2: destruct vs =>//.
        destruct H7 as [? [? [Hcontr ?]]].
        apply lfilled_Ind_Equivalent in Hcontr.
        inversion Hcontr.
        1,2: apply first_values in H2 as [? [? ?]];auto;try by intros [? ?]. done. done.
        unfold const_list. rewrite forallb_app.
        intros [??]%andb_true_iff. done.
        do 2 destruct vs => //. }
      { destruct vs =>//;[|do 2 destruct vs =>//].
        inversion H0;subst. done. }
      { destruct vs =>//;[|do 2 destruct vs =>//].
        inversion H0;subst. done. }
      { exists (LH_base [] []),0. by cbn. }
      { exists (LH_base [] []),0. split;[|lia]. by cbn. }
      
    }
    { apply first_values in H9 as [? [? ?]];auto. done.
      subst. apply v_to_e_is_const_list. }
    { apply first_values in H9 as [? [? ?]];auto. done.
      subst. simplify_eq. apply v_to_e_is_const_list. }
    { subst.
      apply lfilled_Ind_Equivalent in H.
      inversion H.
      { subst.
        apply lfilled_Ind_Equivalent in H0.
        inversion H0;subst.
        apply const_list_snoc_eq3 in H2 as [? [? [? [? [? ?]]]]];auto.
        2: eapply reduce_not_nil;eauto.
        2: eapply values_no_reduce => //.
        2: intros -> ; eapply AI_trap_irreducible => //.
        subst.
        assert (lfilled 0 (LH_base x x0) [AI_trap] (x ++ [AI_trap] ++ x0)) as Hf%IHHred.
        { apply lfilled_Ind_Equivalent. constructor. auto. }
        destruct Hf as [lh' [j [Hfill'%lfilled_Ind_Equivalent Hle]]].
        inversion Hfill';subst.
        { exists (LH_base (vs0++vs) (es'0 ++ es'1)),0.
          assert (vs0 ++ (vs ++ [AI_trap] ++ es'0) ++ es'1 =
                    (vs0 ++ vs) ++ [AI_trap] ++ (es'0 ++ es'1))%SEQ as Heq.
          { repeat erewrite app_assoc. auto. }
          rewrite Heq. split;[|lia]. apply lfilled_Ind_Equivalent. constructor.
          apply const_list_app. auto. }
        { exists (LH_rec (vs0 ++ vs) n es'0 lh'0 (es'' ++ es'1)),(S k).
          assert (vs0 ++ (vs ++ [AI_label n es'0 LI] ++ es'') ++ es'1 =
                 (vs0 ++ vs) ++ [AI_label n es'0 LI] ++ (es'' ++ es'1))%SEQ as ->.
          { repeat erewrite app_assoc. auto. } inversion Hle.
          (* apply lfilled_Ind_Equivalent. constructor;auto. *)
          (* apply const_list_app;auto. *)
        }
      }
      { apply first_values in H2 as [? [? ?]];auto. done. }
    }
    { subst.
      apply lfilled_Ind_Equivalent in H.
      apply lfilled_Ind_Equivalent in H0.
      inversion H;subst.
      { apply const_list_snoc_eq3 in H3 as [? [? [? [? [? ?]]]]];auto.
        2: eapply reduce_not_nil;eauto.
        2: eapply values_no_reduce => //.
        2: intros -> ; eapply AI_trap_irreducible => //.
        subst.
        inversion H0;subst.
        destruct IHHred with (i := S k0) (lh:=LH_rec x n es'0 lh'0 x0) as [lh' [j [Hfill'%lfilled_Ind_Equivalent Hle]]].
        { apply lfilled_Ind_Equivalent. constructor;auto. }
        inversion Hfill';subst.
        { exists (LH_base (vs0 ++ vs) (es'2 ++ es'1)),0.
          assert (vs0 ++ (vs ++ [AI_trap] ++ es'2) ++ es'1 =
                    (vs0 ++ vs) ++ [AI_trap] ++ (es'2 ++ es'1))%SEQ as Heq.
          { repeat erewrite app_assoc. auto. }
          rewrite Heq. split;[|lia]. apply lfilled_Ind_Equivalent. constructor.
          apply const_list_app. auto. }
        { exists (LH_rec (vs0 ++ vs) n0 es'2 lh'1 (es'' ++ es'1)),(S k).
          assert (vs0 ++ (vs ++ [AI_label n0 es'2 LI0] ++ es'') ++ es'1 =
                 (vs0 ++ vs) ++ [AI_label n0 es'2 LI0] ++ (es'' ++ es'1))%SEQ as ->.
          { repeat erewrite app_assoc. auto. }
          split;[|lia].
          apply lfilled_Ind_Equivalent. constructor;auto.
          apply const_list_app;auto.
        }
      }
      { apply first_values in H3 as [? [? ?]];simplify_eq;auto.
        apply lfilled_Ind_Equivalent in H2.
        apply lfilled_Ind_Equivalent in H8.
        eapply lfilled_singleton in H2 as [? [? [HH%IHHred Heq]]];[..|apply H8];auto.
        2: eapply reduce_not_nil;eauto.
        2: eapply values_no_reduce => //.
        2: intros -> ; eapply AI_trap_irreducible => //.
        inversion H0;subst.
        destruct HH as [lh2 [j2 [Hlh2 Hle2]]].
        apply lfilled_Ind_Equivalent in H13.
        eapply lfilled_trans in H13 as [? ?];[|apply Hlh2].
        exists (LH_rec vs n es'0 x1 es''),(S (j2 + k1)). split;[|lia].
        apply lfilled_Ind_Equivalent;constructor;auto.
        apply lfilled_Ind_Equivalent;auto.
      }
    }
  Qed.
    
  Lemma trap_reduce_nested hs s f es hs' s' f' es' lh i :
    lfilled i lh [AI_trap] es -> reduce hs s f es hs' s' f' es' ->
    (exists lh' j, lfilled j lh' [AI_trap] es' ∧ j <= i) ∧ (hs,s,f) = (hs',s',f').
  Proof.
    intros Hfill Hred.
    eapply trap_reduce_state_eq in Hred as Heq;eauto.
    eapply trap_reduce_lfilled in Hred as Hf;eauto.
  Qed.

  Lemma trap_context_reduce hs locs s LI lh k :
    lfilled (S k) lh [AI_trap] LI ->
    ∃ e', reduce hs locs s LI hs locs s e'.
  Proof.
    revert LI lh.
    induction k;intros LI lh Hfill%lfilled_Ind_Equivalent.
    { inversion Hfill;simplify_eq. inversion H1;simplify_eq.
      destruct (decide (vs0 ++ [AI_trap] ++ es'0 = [AI_trap])).
      { destruct vs0,es'0 =>//.
        2: destruct vs0 =>//.
        2: destruct vs0,es'0 =>//.
        erewrite app_nil_l, app_nil_r.
        exists (vs ++ [AI_trap] ++ es'').
        eapply r_label.
        2: instantiate (3:=0).
        2,3: apply lfilled_Ind_Equivalent;constructor;auto.
        apply r_simple. apply rs_label_trap. }
      { exists (vs ++ [AI_label n es' ([AI_trap])] ++ es'').
        eapply r_label.
        2: instantiate (3:=1).
        2,3: apply lfilled_Ind_Equivalent;constructor;auto.
        2: instantiate (2:=LH_base [] []).
        2,3: apply lfilled_Ind_Equivalent.
        2,3: cbn;rewrite app_nil_r; by apply/eqseqP.
        apply r_simple. eapply rs_trap. auto.
        apply lfilled_Ind_Equivalent. eauto.
      }
    }
    { inversion Hfill;simplify_eq.
      apply lfilled_Ind_Equivalent in H1.
      eapply IHk in H1 as Hred.
      destruct Hred as [e' Hred].
      eexists.
      eapply r_label;[eauto|..].
      instantiate (2:=1).
      all: apply lfilled_Ind_Equivalent;constructor;auto.
      all: apply lfilled_Ind_Equivalent.
      instantiate (1:=LH_base [] []).
      all: cbn;rewrite app_nil_r;by apply/eqseqP.
    }
  Qed.

  Lemma to_val_trapV_lfilled_None es k lh LI :
    iris.to_val es = Some trapV ->
    lfilled (S k) lh es LI ->
    iris.to_val LI = None.
  Proof.
    intros Hes Hfill.
    apply to_val_trap_is_singleton in Hes as ->.
    eapply trap_context_reduce in Hfill as [e' Hred].
    eapply val_head_stuck_reduce;eauto.
    Unshelve.
    done.
    apply (Build_store_record [] [] [] []).
    apply (Build_frame [] (Build_instance [] [] [] [] [])).
  Qed.

  Lemma lfilled_to_val_0 i lh e es v :
    iris.to_val e = Some trapV ->
    lfilled i lh e es ->
    iris.to_val es = Some v ->
    i = 0.
  Proof.
    intros He Hfill Hes.
    destruct i;auto.
    exfalso.
    apply to_val_trapV_lfilled_None in Hfill;auto.
    unfold to_val in Hfill.
    congruence.
  Qed.

  Lemma reduce_det_local hs ws f hs' ws' f' es1 es2 n f0 :
    iris.to_val es1 = None ->
    opsem.reduce (host_instance:=DummyHosts.host_instance) hs ws f [AI_local n f0 es1] hs' ws' f' es2 ->
    ∃ es2' f1, es2 = [AI_local n f1 es2'] ∧ f = f' ∧
                 opsem.reduce (host_instance:=DummyHosts.host_instance) hs ws f0 es1 hs' ws' f1 es2'.
  Proof.
    intros Hes1.
    remember [AI_local n f0 es1] as es.
    revert es2. induction 1;simplify_eq.
    all: try destruct vcs =>//.
    { remember [AI_local n f0 es1] as es.
      revert e' H;induction 1;simplify_eq.
      all: try do 2 destruct vs =>//.
      { apply const_list_to_val in H as [? ?]. congruence. }
      { apply const_es_exists in H as [? ?]. simplify_eq. 
        apply lfilled_to_sfill in H1 as [sh Hsh].
        rewrite -sfill_sh_pull_const_r in Hsh.
        rewrite Hsh in Hes1.
        assert (iris.of_val (retV (sh_pull_const_r sh x)) = es1);[rewrite Hsh;auto|].
        rewrite Hsh in H. rewrite -H in Hes1.
        rewrite to_of_val in Hes1. done. }
      { apply lfilled_Ind_Equivalent in H0. inversion H0. do 2 destruct vs =>//. }
    }
    { apply lfilled_Ind_Equivalent in H0.
      inversion H0;simplify_eq.
      rewrite -(app_nil_l [AI_local n f0 es1]) in H2.
      apply val_head_stuck_reduce in H as Hstuck.
      apply const_list_snoc_eq3 in H2;auto.
      2,4: intros ->;done.
      2: intros [? ?]%const_list_to_val;congruence.
      destruct H2 as [? [? [? [? [? ?]]]]].
      simplify_eq. destruct vs,x,x0,es'0 =>//.
      apply lfilled_Ind_Equivalent in H1.
      inversion H1;simplify_eq. erewrite app_nil_l, app_nil_r.
      apply IHreduce. auto.
      rewrite -(app_nil_l [AI_local n f0 es1]) in H2.
      apply first_values in H2 as [?[? ?]];auto. done. }
    { eauto. }
  Qed.

  Lemma reduce_det_label hs ws f hs' ws' f' es1 n es es'' es2 :
    opsem.reduce (host_instance:=DummyHosts.host_instance) hs ws f es'' hs' ws' f' es2 ->
    ∀ l1 l2, es'' = (l1 ++ [AI_label n es es1] ++ l2) ->
    const_list l1 ->
    iris.to_val es1 = None ->
    ∃ es2', es2 = l1 ++ [AI_label n es es2'] ++ l2 ∧
              opsem.reduce (host_instance:=DummyHosts.host_instance) hs ws f es1 hs' ws' f' es2'.
  Proof.
    revert es2. induction 1.
    2-25:intros l1 l2 Heqes'' Hconst Hes1; simplify_eq.
    all: try by destruct l1 =>//.
    all: try by do 2 destruct l1 =>//.
    all: try by do 3 destruct l1 =>//.
    { revert e' H;induction 1;simplify_eq;intros l1 l2 Heqes'' Hconst Hes1; simplify_eq.
      all: try do 2 destruct l1 =>//.
      all: try do 3 destruct l1 =>//.
      all: try by apply first_values in Heqes'' as (?&?&?);auto.
      { destruct l1 =>//;[|destruct l1 =>//].
        destruct l2 =>//. erewrite app_nil_l, app_nil_r in Heqes''. simplify_eq.
        apply const_list_to_val in H as [? ?]. congruence. }
      { destruct l1 =>//;[|destruct l1 =>//].
        destruct l2 =>//. erewrite app_nil_l, app_nil_r in Heqes''. simplify_eq. }
      { destruct l1 =>//;[|destruct l1 =>//].
        destruct l2 =>//. erewrite app_nil_l, app_nil_r in Heqes''. simplify_eq.
        apply const_es_exists in H as [? ?]. simplify_eq.
        apply lh_pull_const_r_app in H1 as [lh' Hlh'].        
        apply lfilled_to_vfill with (i:=i) in Hlh';[|lia].
        destruct Hlh' as [vh [Heq Hvh]].
        assert (iris.of_val (brV vh) = es1);[auto|].
        rewrite -H in Hes1.
        rewrite to_of_val in Hes1. done. }
      { assert ([v;AI_basic (BI_tee_local i)] = [v] ++ [AI_basic (BI_tee_local i)]) as Heq;[auto|].
        rewrite Heq in Heqes''.
        apply first_values in Heqes'' as (?&?&?);auto;[done|]. simpl. rewrite H;auto. }
      { apply lfilled_Ind_Equivalent in H0. inversion H0.
        apply first_values in H1 as (?&?&?);auto. done. }
    }
    { apply first_values in Heqes'' as (?&?&?);auto;[done|]; apply v_to_e_is_const_list. }
    { erewrite <-(take_drop 2 [_;_;_]) in Heqes'';simpl take in Heqes'';simpl drop in Heqes''.
      apply first_values in Heqes'' as (?&?&?);auto. done. }
    all: try (erewrite <-(take_drop 2 [_;_;_]) in Heqes'';simpl take in Heqes'';simpl drop in Heqes'').
    all: try by (apply first_values in Heqes'' as (?&?&?);auto).
    { apply lfilled_Ind_Equivalent in H0.
      inversion H0;simplify_eq.
      { apply val_head_stuck_reduce in H as Hstuck.
        apply const_list_snoc_eq3 in H2;auto.
        2,4: intros ->;done.
        2: intros [? ?]%const_list_to_val;congruence.
        destruct H2 as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst']]]]].
        apply IHreduce in Heq2;auto.
        simplify_eq.
        apply lfilled_Ind_Equivalent in H1. inversion H1. simplify_eq.
        destruct Heq2 as [es2' [-> Hstep]].
        repeat erewrite <- app_assoc;erewrite app_assoc.
        eexists. split;eauto. }
      { apply first_values in H2 as (?&?&?);auto. simplify_eq.
        apply lfilled_Ind_Equivalent in H1. inversion H1. simplify_eq.
        eexists. split;eauto.
        apply lfilled_Ind_Equivalent in H7.
        apply lfilled_Ind_Equivalent in H13.
        eapply r_label;eauto. 
      }
    }
  Qed.

  Lemma reduce_det_label_nil hs ws f hs' ws' f' es1 es2 n es :
    iris.to_val es1 = None ->
    opsem.reduce (host_instance:=DummyHosts.host_instance) hs ws f [AI_label n es es1] hs' ws' f' es2 ->
    ∃ es2', es2 = [AI_label n es es2'] ∧
              opsem.reduce (host_instance:=DummyHosts.host_instance) hs ws f es1 hs' ws' f' es2'.
  Proof.
    intros Hes1.
    remember [AI_label n es es1] as es''.
    erewrite <-(app_nil_l [_]),<-(app_nil_r [_]) in Heqes''.
    intros Hred.
    eapply reduce_det_label in Heqes'';eauto.
  Qed.

  
End reduce_properties_lemmas.
