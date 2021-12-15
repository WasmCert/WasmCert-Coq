From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap proph_map.
Require Export iris iris_locations stdpp_aux.
Require Export datatypes host operations properties opsem.

Ltac false_assumption := exfalso ; apply ssrbool.not_false_is_true ; assumption.

(* given a nonempty list x :: xs, gives user a hypothesis "Htail : x :: xs = ys ++ [y]" *)
Ltac get_tail x xs ys y Htail :=
  cut (exists ys y, x :: xs = ys ++ [y]) ;
  [ intro Htail ; destruct Htail as (ys & y & Htail) |
    exists (removelast (x :: xs)) ;
    exists (List.last (x :: xs) AI_trap) ;
    apply app_removelast_last ;
    apply not_eq_sym ; apply nil_cons ].


Lemma b2p: forall {T:eqType} (a b:T), a==b -> a=b.
Proof. move => T a b Hb. by move/eqP in Hb. Qed.

Lemma found_intruse l1 l2 (x : administrative_instruction) :
  l1 = l2 -> (In x l1 -> False) -> In x l2 -> False.
Proof.
  intros. rewrite H in H0. apply H0 ; exact H1.
Qed.

(* If H is a hypothesis that states the equality between 2 lists, attempts to prove
   False by showing object x is in the rhs of H, but not in the lhs.
   If attempt fails, user is given a hypothesis Hxl1 to end proof manually *)
Ltac found_intruse x H Hxl1 :=
  exfalso ; 
  apply (found_intruse _ _ x H) ;
  [intro Hxl1 ; repeat ((destruct Hxl1 as [Hxl1 | Hxl1] ; [ inversion Hxl1 |]) +
                          assumption  ) |
    try by (apply in_or_app ; right ; left ; trivial) ].



(* Attempts to prove False from hypothesis H, which states that an lholed is filled
   with AI_trap. If attempt fails, user is given a hypothesis Hxl1 to end proof manually *)
Ltac filled_trap H Hxl1 :=
  exfalso ;
  unfold lfilled, lfill in H ;
  destruct (_:lholed) in H ; [|false_assumption] ;
  destruct (const_list _) in H ; [|false_assumption] ;
  apply b2p in H ; found_intruse AI_trap H Hxl1.

(* Given hypothesis H, which states that an lholed lh is filled at level k, 
   unfolds the definition of lfilled. Attempts to prove a contradiction when k > 0.
   If attempts fail, user is given that filled expression is 
   vs ++ (AI_label n l1 l3) :: l0 *)
Ltac simple_filled H k lh vs l0 n l1 l3 :=
  let l2 := fresh "l" in
  let lh' := fresh "lh" in
  let Hxl1 := fresh "Hxl1" in
  let les := fresh "les" in
  unfold lfilled, lfill in H ;
  destruct k ;
  [ destruct lh as [vs l0|] ; [| false_assumption] ;
    destruct (const_list vs) ; [| false_assumption] ; apply b2p in H |
    fold lfill in H ; destruct lh as [|vs n l1 lh' l2] ; [false_assumption |] ;
    destruct (const_list vs) ; [| false_assumption ] ;
    remember (lfill k lh' _) as les ;
    destruct les as [l3|] ; [| false_assumption ] ;
    apply b2p in H ; found_intruse (AI_label n l1 l3) H Hxl1].

(* Like simple_filled, but does not attempt to solve case k > 0 *)
Ltac simple_filled2 H k lh vs l0 n l1 l3 :=
  let l2 := fresh "l" in
  let lh' := fresh "lh" in
  let Hxl1 := fresh "Hxl1" in
  let les := fresh "les" in
  unfold lfilled, lfill in H ;
  destruct k ;
  [ destruct lh as [vs l0|] ; [| false_assumption] ;
    destruct (const_list vs) ; [| false_assumption] ; apply b2p in H |
    fold lfill in H ; destruct lh as [|vs n l1 lh' l2] ; [false_assumption |] ;
    destruct (const_list vs) ; [| false_assumption ] ;
    remember (lfill k lh' _) as les ;
    destruct les as [l3|] ; [| false_assumption ] ;
    apply b2p in H ; try by found_intruse (AI_label n l1 l3) H Hxl1].


Section Host.

Variable host_function : eqType.

Let host := host.host host_function.
Let function_closure := function_closure host_function.
Let store_record := store_record host_function.

Variable host_instance : host.

Let reduce := @reduce host_function host_instance.

Let prim_step := @iris.prim_step host_function host_instance.

Let wasm_mixin : LanguageMixin _ _ _ := wasm_mixin host_instance.

Canonical Structure wasm_lang := Language wasm_mixin.

Let reducible := @reducible wasm_lang.


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

(* Applies values_no_reduce and attempts to prove that the given arguments were indeed
   values *)
Ltac values_no_reduce Hred :=
  apply (values_no_reduce _ _ _ _ _ _ _ _ Hred) ;
  simpl ; trivial.

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
  let t1s := fresh "t1s" in
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
  clear - host_function host function_closure store_record
                      host_instance reduce
                      Hred Heqes ;
  induction Hred as [e e' s f hs H | | | | | a | a | a | | | | | | | | | | | | | | | |
                      s f es les s' f' es' les' k lh hs hs' Hred IHreduce H0 _ |
    ]; (try by inversion Heqes) ; (try by found_intruse (AI_invoke a) Heqes Hxl1) ;
  [ destruct H as [ | | | | | | | | | | | | | | 
                    vs es n' m t1s t2s Hconst Hvs Ht1s Ht2s |
                    vs es n' m t1s t2s Hconst Hvs Ht1s Ht2s |
                  | | | | | | | | | | | | | 
                    es' lh Htrap' H0 ]; (try by inversion Heqes) ;
    first found_intruse (AI_basic (BI_block (Tf t1s t2s) es)) Heqes Hxl1 ;
    first found_intruse (AI_basic (BI_loop (Tf t1s t2s) es)) Heqes Hxl1 ;
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
(* examples of usage of no_reduce. This first example is reused in other lemmas,
   the following ones may be removed if wanted *)
Lemma test_no_reduce0 hs s f hs' s' f' es' :
  reduce hs s f [] hs' s' f' es' -> False.
Proof.
  intro Hred.
  remember [] as es in Hred.
  apply Logic.eq_sym in Heqes.
  no_reduce Heqes Hred.
Qed.

Ltac empty_list_no_reduce Hred :=
  exfalso ; apply (test_no_reduce0 _ _ _ _ _ _ _ Hred).

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
            [ empty_list_no_reduce Hred |] ;
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
            apply (values_no_reduce _ _ _ _ _ _ _ _ Hred) ;
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
  - apply app_inj_tail in Heqes. destruct Heqes as [Hves Hinvoke].
    inversion Hinvoke as [Ha]. rewrite Ha in H. rewrite H in Hs.
    rewrite H0 in Hs. inversion Hs.
  - apply app_inj_tail in Heqes. destruct Heqes as [Hves Hinvoke].
    inversion Hinvoke as [Ha]. rewrite Ha in H. rewrite H in Hs.
    rewrite H0 in Hs. inversion Hs.
  - simple_filled H0 k lh bef aft n0 l l'.
    destruct aft.
    { destruct es. { empty_list_no_reduce Hred. }
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
    values_no_reduce Hred. rewrite <- Heqes in Hconst.
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
    rewrite H0 in Hs. inversion Hs.
  - apply app_inj_tail in Heqes. destruct Heqes as [Hves  Hinvoke ].
    inversion Hinvoke as [Ha]. rewrite Ha in H.
    rewrite H in Hs. rewrite H0 in Hs. inversion Hs as [[ Ht1s Ht2s Hh ]].
    rewrite Ht1s in H3. rewrite H3 in Hlen.
    rewrite <- Hves in Hlen. rewrite H1 in Hlen. rewrite v_to_e_length in Hlen. lia.
  - apply app_inj_tail in Heqes. destruct Heqes as [Hves  Hinvoke ].
    inversion Hinvoke as [Ha]. rewrite Ha in H.
    rewrite H in Hs. rewrite H0 in Hs. inversion Hs as [[ Ht1s Ht2s Hh ]].
    rewrite Ht1s in H3. rewrite H3 in Hlen.
    rewrite <- Hves in Hlen. rewrite H1 in Hlen. rewrite v_to_e_length in Hlen. lia.
  - simple_filled H0 k lh bef aft n0 l l'.
    destruct aft.
    { destruct es. { empty_list_no_reduce Hred. }
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
    values_no_reduce Hred. rewrite <- Heqes in Hconst.
    unfold const_list in Hconst. rewrite forallb_app in Hconst.
    apply andb_true_iff in Hconst. destruct Hconst as [Hconst _].
    rewrite forallb_app in Hconst. apply andb_true_iff in Hconst.
    destruct Hconst as [_ Hconst]. exact Hconst.
    rewrite Heqes in Hxl1. apply in_app_or in Hxl1.
    destruct Hxl1 as [ Hxl1 | Hxl1 ] ;
      [ intruse_among_values vs Hxl1 Hconst |
        destruct Hxl1 as [ Hxl1 | Hxl1 ] ; inversion Hxl1 ].
Qed.




(* iris related *)



Lemma reduce_val_false hs s0 f hs' s' f' es es' :
  is_Some (iris.to_val es) ->
  reduce hs s0 f es hs' s' f' es' -> False.
Proof.
  intros Hsome Hred.
  apply val_head_stuck_reduce in Hred.
  rewrite Hred in Hsome. inversion Hsome.
  done.
Qed.

Lemma to_val_const_list: forall es vs,
  iris.to_val es = Some (immV vs) ->
  const_list es.
Proof.
  move => es. 
  elim: es => [|e es'] //=.
  move => IH vs.
  destruct e => //=.
  destruct b => //=.
  move => H.
  destruct (iris.to_val es') eqn:HConst => //=.
  destruct v0 => //=.
  inversion H; subst; clear H.
  by eapply IH; eauto.
  case es' => //.
Qed.

Lemma to_val_cat (es1 es2: list administrative_instruction) (vs: list value) :
  iris.to_val (es1 ++ es2) = Some (immV vs) ->
  iris.to_val es1 = Some (immV (take (length es1) vs)) /\
  iris.to_val es2 = Some (immV ((drop (length es1) vs))).
Proof.
  move => H.
  apply iris.of_to_val in H.
  apply fmap_split in H; destruct H as [H1 H2].
  remember (length es1) as n1.
  remember (length es2) as n2.
  rewrite - H1.
  rewrite - H2.
  rewrite !of_val_imm.
  by repeat rewrite iris.to_of_val.
Qed.

Lemma to_val_cat_inv (es1 es2: list administrative_instruction) (vs1 vs2: list value) :
  iris.to_val es1 = Some (immV vs1) ->
  iris.to_val es2 = Some (immV vs2) ->
  iris.to_val (es1 ++ es2) = Some (immV (vs1 ++ vs2)).
Proof.
  revert vs1 vs2 es2.
  induction es1;intros vs1' vs2' es2' He1 He2.
  destruct vs1' =>//=.
  simpl in *.
  destruct a =>//=.
  destruct b =>//=.
  destruct (iris.to_val es1) eqn:Hsome =>//=.
  destruct v0 =>//=.
  destruct vs1';inversion He1;subst.
  erewrite IHes1=>//=.
  destruct es1=>//=.
Qed.

Lemma to_val_cat_None1 (es1 es2: list administrative_instruction) :
  iris.to_val es1 = None ->
  iris.to_val (es1 ++ es2) = None.
Proof.
  move => H.
  destruct (iris.to_val (es1 ++ es2)) eqn: HContra => //.
  case: v HContra.
  { move => l HContra.
    apply to_val_cat in HContra as [H1 _].
    rewrite H1 in H.
    by inversion H. }
  { move => Hcontra.
    pose proof (to_val_trap_is_singleton Hcontra) as Heq.
    destruct es1;[done|].
    destruct es1, es2;try done.
    inversion Heq. subst. done. }
Qed.

Lemma to_val_cat_None2 (es1 es2: list administrative_instruction) :
  iris.to_val es2 = None ->
  iris.to_val (es1 ++ es2) = None.
Proof.
  move => H.
  destruct (iris.to_val (es1 ++ es2)) eqn: HContra => //.
  case: v HContra => //=.
  { move => l HContra. apply to_val_cat in HContra as [_ H1].
    rewrite H1 in H.
    by inversion H. }
  { move => Hcontra.
    pose proof (to_val_trap_is_singleton Hcontra) as Heq.
    destruct es2;[done|].
    case: es1 Hcontra Heq.
    move => Hcontra Heq.
    rewrite app_nil_l in Heq.
    destruct es2;try done.
    inversion Heq;subst;done.
    move => a0 l Hcontra Heq.
    assert (length [AI_trap] = 1) as Hl;auto.
    revert Hl. rewrite -Heq -Permutation_middle =>Hl //=. }
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

(* Note : the following lemma exists already in Coq's standard library, and 
   is called app_eq_unit *)
Lemma app_eq_singleton: ∀ T (l1 l2 : list T) (a : T),
    l1 ++ l2 = [a] ->
    (l1 = [a] ∧ l2 = []) ∨ (l1 = [] ∧ l2 = [a]).
Proof.
  move =>T.
  elim.
  move => l2 a Heq. right. by rewrite app_nil_l in Heq.
  move => a l l2 a0 a1 Heq. inversion Heq;subst.
  left. split. f_equiv.
  all: destruct l, a0;try done.
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

Lemma rcons_eq (T: Type) (es1: list T) e1 es2 e2:
  es1 ++ [e1] = es2 ++ [e2] ->
  es1 = es2 /\ e1 = e2.
Proof.
  move: es2.
  induction es1 => //; move => es2 H.
  - destruct es2 => //=; first simpl in H; inversion H => //.
    by destruct es2.
  - destruct es2 => //=; first by destruct es1 => //.
    inversion H; subst; clear H.
    apply IHes1 in H2 as [-> ->].
    split => //.
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
    destruct es => /=; first by apply test_no_reduce0 in HReduce.
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
    + destruct es => /=; first by apply test_no_reduce0 in HReduce.
      destruct es => /=; simpl in H1; inversion H1; subst; clear H1; first by apply test_no_reduce1 in HReduce.
      destruct es, es'0 => //=.
      rewrite cats0.
      by apply IHHReduce.
    + destruct vs => /=; last by destruct vs, es, es'0 => //; inversion H1; subst.
      inversion H1; subst; clear H1.
      destruct es => /=; first by apply test_no_reduce0 in HReduce.
      destruct es, es'0 => //.
      inversion H2; subst.
      by apply AI_trap_irreducible in HReduce.
Qed.
      
Lemma prepend_reducible (es1 es2: list administrative_instruction) vs σ:
  iris.to_val es1 = Some vs ->
  reducible es2 σ ->
  reducible (es1 ++ es2) σ.
Proof.
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
Qed.

Lemma first_non_value es :
  iris.to_val es = None ->
  exists vs e es', const_list vs /\ (to_val [e] = None \/ e = AI_trap) /\ es = vs ++ e :: es'.
Proof.
  intros Hes.
  induction es ; first by inversion Hes.
  remember a as a'.
  destruct a ; try by exists [], a', es ; repeat split => //= ; left ; rewrite Heqa'.
  { subst ; remember b as b'.
    destruct b ;
      try by exists [], (AI_basic b'), es ; repeat split => //= ; left ; rewrite Heqb'.
    subst. simpl in Hes. remember (iris.to_val es) as tv.
    destruct tv. { destruct v0. { inversion Hes. }
      exists [AI_basic (BI_const v)], AI_trap, []. repeat split => //=. by right.
                   by rewrite (to_val_trap_is_singleton (Logic.eq_sym Heqtv)). }
    destruct (IHes Hes) as (vs & e & es' & Hvs & He & Hes').
    exists (AI_basic (BI_const v) :: vs), e, es'.
    repeat split => //=. by rewrite Hes'. }
  subst. exists [], AI_trap, es. repeat split => //=. by right.
Qed.

Lemma first_non_value_reduce hs s f es hs' s' f' es' :
  reduce hs s f es hs' s' f' es' ->
  exists vs e es'', const_list vs /\ (to_val [e] = None \/ e = AI_trap) /\ es = vs ++ e :: es''.
Proof.
  intros Hes.
  remember (to_val es) as tv. apply Logic.eq_sym in Heqtv. destruct tv.
  { destruct v. { apply to_val_const_list in Heqtv.
                  exfalso ; values_no_reduce Hes. }
    apply to_val_trap_is_singleton in Heqtv. subst.
    exfalso ; by apply (AI_trap_irreducible _ _ _ _ _ _ _ Hes). }
  by apply first_non_value.
Qed.

Lemma const_list_is_val vs :
  const_list vs -> ∃ v, to_val vs = Some (immV v).
Proof.
  induction vs.
  eauto.
  simpl. intros [Hconst Hvs]%andb_prop.
  specialize (IHvs Hvs) as [v Hv].
  destruct a;inversion Hconst.
  destruct b;inversion Hconst.
  exists (v0::v). rewrite Hv. eauto.
Qed.


Lemma first_values vs1 e1 es1 vs2 e2 es2 :
  (to_val [e1] = None \/ e1 = AI_trap) ->
  (to_val [e2] = None \/ e2 = AI_trap) ->
  const_list vs1 ->
  const_list vs2 ->
  vs1 ++ e1 :: es1 = vs2 ++ e2 :: es2 ->
  vs1 = vs2 /\ e1 = e2 /\ es1 = es2.
Proof.
  intros He1 He2 Hvs1 Hvs2 Heq.
  generalize dependent vs2; induction vs1 ; intros.
  { destruct vs2 ; inversion Heq => //=. rewrite <- H0 in Hvs2.
    simpl in Hvs2. apply andb_true_iff in Hvs2 as [ Habs _ ].
    assert (const_list [e1]) ; first by apply andb_true_iff.
    apply const_list_is_val in H.
    destruct He1 as [He1 | He1] ;
      rewrite He1 in H ; destruct H as [v H] ; inversion H. }
  destruct vs2 ; inversion Heq.
  { rewrite H0 in Hvs1.
    simpl in Hvs1. apply andb_true_iff in Hvs1 as [ Habs _ ].
    assert (const_list [e2]) ; first by apply andb_true_iff.
    apply const_list_is_val in H.
    destruct He2 as [He2 | He2] ;
      rewrite He2 in H ; destruct H as [ v H] ; inversion H. }
  assert (vs1 = vs2 /\ e1 = e2 /\ es1 = es2) as H ; last by destruct H ; subst.
  apply IHvs1 => //=.
  - by apply andb_true_iff in Hvs1 as [ _ Hvs1 ].
  - by apply andb_true_iff in Hvs2 as [ _ Hvs2 ].  
Qed.


Ltac solve_prim_step_split_reduce_r H objs Heqf0 :=
  (* this code has to be written so many times in the following proof, with just
     minor changes, so I wrote a tactic. *)
  left ; subst ;
  apply Logic.eq_sym, app_eq_nil in H as [? ?] ;
  exists objs ; subst ; rewrite app_nil_r ;
  repeat split => //= ; rewrite Heqf0.


Lemma prim_step_split_reduce_r (es1 es2 es' : list administrative_instruction) σ σ' obs efs :
  iris.to_val es1 = None -> 
  prim_step (es1 ++ es2) σ obs es' σ' efs ->
  (exists es'', es' = es'' ++ es2 /\ prim_step es1 σ obs es'' σ' efs) \/
    (exists n m lh, lfilled 0 (LH_base (take n es1)
                               (drop m (es1 ++ es2)))
                       [AI_trap] es' /\ lfilled 0 lh [AI_trap] es1 ∧ σ' = σ). 
(*                  σ' = σ /\
              prim_step es1 σ obs [AI_trap] σ efs). *)
Proof.
  intros Hes1 Hstep. 
  cut (forall n, length es' < n ->
            (exists es'', es' = es'' ++ es2 /\ prim_step es1 σ obs es'' σ' efs) \/
              (exists n m lh, n <= length es1 /\ m <= length (es1 ++ es2) /\
                        lfilled 0 (LH_base (take n es1)
                                         (drop m (es1 ++ es2)))
                                [AI_trap] es' /\ lfilled 0 lh [AI_trap] es1 ∧ σ'=σ)). (* σ' = σ /\
                        exists lh, lfilled 0 lh [AI_trap] es1)). *)
  { intro Hn ; assert (length es' < S (length es')) as Hlen ; first lia.
    destruct (Hn (S (length es')) Hlen) as [ Hl | (n0 & m & lh & _ & _ & ? & ? & ?) ].
    by left. right ; exists n0, m, lh. 
    repeat split => //=. } (* apply r_simple, (rs_trap (lh:=x)) => //=.
    intro Habs ; rewrite Habs in Hes1 ; inversion Hes1. 
  } *)
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
  induction Hstep ; repeat (destruct es1 ; first (by inversion Heqes ; subst ;
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
      apply first_values in Heqes as (Hvs & He & Hnil) => //=.
      apply Logic.eq_sym, app_eq_nil in Hnil as [Hn1 Hn2].
      exists [AI_label m [] (vs ++ to_e_list es)].
      repeat (split => //= ; try by subst). rewrite Hes'1. rewrite <- Hvs.
      rewrite <- He. rewrite <- Heqf. rewrite <- Heqf0. rewrite Hn1.
      apply r_simple. apply (rs_block es H H1 H2 H3). by left.
    - left ; destruct (first_non_value _ Hes1) as (vs1 & e1 & es'1 & Hvs1 & He1 & Hes'1).
      rewrite Hes'1 in Heqes. rewrite <- app_assoc in Heqes.
      rewrite <- app_comm_cons in Heqes.
      apply first_values in Heqes as (Hvs & He & Hnil) => //=.
      apply Logic.eq_sym, app_eq_nil in Hnil as [Hn1 Hn2].
      exists [AI_label n [AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)].
      repeat (split => //= ; try by subst). rewrite Hes'1. rewrite <- Hvs.
      rewrite <- He. rewrite <- Heqf. rewrite <- Heqf0. rewrite Hn1.
      apply r_simple. apply (rs_loop es H H1 H2 H3). by left.
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
      apply b2p in H1. rewrite H1 in Heqes.
      rewrite <- app_assoc in Heqes. rewrite <- app_comm_cons in Heqes.
      apply first_values in Heqes as (Hvs & He & Hnil) => //= ; try by right.
      rewrite <- He in Hes'1. rewrite Hes'1.
      exists (LH_base vs1 es'1). repeat (split => //=). lia.
      by unfold lfilled, lfill ; rewrite Hvs1. }
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
    apply first_values in Heqes as (Hvs & He & Hnil) => //=.
    apply Logic.eq_sym, app_eq_nil in Hnil as [Hn1 Hn2].
    exists [AI_local m f' [AI_basic (BI_block (Tf [] t2s) es)]].
    rewrite Hn2.
    repeat split => //=. rewrite <- Heqf0. rewrite <- Heqf. rewrite Hes'1.
    rewrite Hn1. rewrite <- He. rewrite <- Hvs.
    by apply (r_invoke_native f _ H H0 H1 H2 H3 H4 H5 H6).
    by left. rewrite H1. by apply v_to_e_is_const_list.
  - left ; destruct (first_non_value _ Hes1) as (vs1 & e1 & es'1 & Hvs1 & He1 & Hes'1).
    rewrite Hes'1 in Heqes. rewrite <- app_assoc in Heqes.
    rewrite <- app_comm_cons in Heqes.
    apply first_values in Heqes as (Hvs & He & Hnil) => //=.
    apply Logic.eq_sym, app_eq_nil in Hnil as [Hn1 Hn2].
    exists (result_to_stack r). rewrite Hn2. rewrite app_nil_r.
    repeat split => //=. rewrite <- Heqf0. rewrite <- Heqf. rewrite Hes'1.
    rewrite Hn1. rewrite <- He. rewrite <- Hvs.
    by apply (r_invoke_host_success f H H0 H1 H2 H3 H4 H5).
    by left. rewrite H1. by apply v_to_e_is_const_list.
  - left ; destruct (first_non_value _ Hes1) as (vs1 & e1 & es'1 & Hvs1 & He1 & Hes'1).
    rewrite Hes'1 in Heqes. rewrite <- app_assoc in Heqes.
    rewrite <- app_comm_cons in Heqes.
    apply first_values in Heqes as (Hvs & He & Hnil) => //=.
    apply Logic.eq_sym, app_eq_nil in Hnil as [Hn1 Hn2].
    exists (ves ++ [AI_invoke a]). rewrite Hn2. rewrite app_nil_r.
    repeat split => //=. rewrite <- Heqf0. rewrite <- Heqf. rewrite Hes'1.
    rewrite Hn1. rewrite <- He. rewrite <- Hvs.
    by apply (r_invoke_host_diverge f H H0 H1 H2 H3 H4 H5).
    by left. rewrite H1. by apply v_to_e_is_const_list.
  - solve_prim_step_split_reduce_r H2 [AI_basic (BI_const v)] Heqf0.
    apply r_get_local. by rewrite <- Heqf0.
  - apply Logic.eq_sym, app_eq_nil in H5 as [Hn1 Hn2] ; rewrite Hn1 ; rewrite Hn2.
    left ; exists []. repeat split => //=. subst.
    by apply (r_set_local s _ H H0 H1).
  - solve_prim_step_split_reduce_r H2 [AI_basic (BI_const v)] Heqf0.
    apply r_get_global. by rewrite <- Heqf0.
  - solve_prim_step_split_reduce_r H3 ([] : seq.seq administrative_instruction)
                                   Heqf0.
    by apply r_set_global ; rewrite <- Heqf0.
  - solve_prim_step_split_reduce_r H5 [AI_basic (BI_const (wasm_deserialise bs t))]
                                   Heqf0.
    rewrite <- Heqf0.
    by apply (r_load_success a _ H H0).
  - solve_prim_step_split_reduce_r H5 [AI_trap] Heqf0.
    rewrite <- Heqf0.
    by apply (r_load_failure a _ H H0).
  - solve_prim_step_split_reduce_r H5 [AI_basic (BI_const (wasm_deserialise bs t))]
                                   Heqf0.
    rewrite <- Heqf0 ;
      by apply (r_load_packed_success a _ H H0).
  - solve_prim_step_split_reduce_r H5 [AI_trap] Heqf0 ;
      rewrite <- Heqf0 ; by apply (r_load_packed_failure a _ H H0).
  - solve_prim_step_split_reduce_r H7 ([] : seq.seq administrative_instruction) Heqf0.
    by rewrite <- Heqf0 ; apply (r_store_success a _ H H0 H1 H2).
  - solve_prim_step_split_reduce_r H7 [AI_trap] Heqf0 ;
      by rewrite <- Heqf0 ; apply (r_store_failure a _ H H0 H1 H2).
  - solve_prim_step_split_reduce_r H7 ([] : seq.seq administrative_instruction) Heqf0 ;
      by rewrite <- Heqf0 ; apply (r_store_packed_success a _ H H0 H1 H2).
  - solve_prim_step_split_reduce_r H7 [AI_trap] Heqf0 ;
      by rewrite <- Heqf0 ; apply (r_store_packed_failure a _ H H0 H1 H2).
  - apply Logic.eq_sym, app_eq_nil in H4 as [Hn1 Hn2] ; rewrite Hn1 ; rewrite Hn2.
    left ;
      exists [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin n))))].
    repeat split => //=. rewrite <- Heqf0. rewrite <- Heqf.
    by apply (r_current_memory _ H H0 H1).
  - apply Logic.eq_sym, app_eq_nil in H6 as [Hn1 Hn2] ; rewrite Hn1 ; rewrite Hn2.
    left ;
      exists [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin n))))].
    repeat split => //=. rewrite <- Heqf0. rewrite <- Heqf.
    by apply (r_grow_memory_success _ H H0 H1).
  - apply Logic.eq_sym, app_eq_nil in H5 as [Hn1 Hn2] ; rewrite Hn1 ; rewrite Hn2.
    left ; exists [AI_basic (BI_const (VAL_int32 int32_minus_one))].
    repeat split => //=. rewrite <- Heqf0. rewrite <- Heqf.
    by apply (r_grow_memory_failure (n := n) _ _ H H0).
  - unfold lfilled, lfill in H.
    destruct k.
    { destruct lh as [bef aft|] ; last by false_assumption.
      remember (const_list bef) as b eqn:Hbef ; destruct b ; last by false_assumption.
      apply b2p in H. rewrite H in Heqes.
      unfold lfilled, lfill in H0. rewrite <- Hbef in H0. apply b2p in H0.
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
        assert (prim_step ((a :: es1) ++ es2') (hs,s,l,i) [] (es' ++ aft')
                          (hs',s',l0,i0) []) as Hstep'.
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
          apply b2p in Hfill ; rewrite app_assoc Hfill.
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
        simpl in Hes1. rewrite <- Heqtv in Hes1.
        destruct v ; first by inversion Hes1.
        apply Logic.eq_sym in Heqtv. apply to_val_trap_is_singleton in Heqtv.
        rewrite Heqtv in H4.
        destruct bef ; last by inversion H4 as [[ Hhd Htl ]] ;
          simpl in Hbef ; apply andb_true_iff in Hbef as [Htrap _] ;
          rewrite Hhd in Htrap ; inversion Htrap.
        destruct es ; first by empty_list_no_reduce Hstep.
        inversion H4. rewrite H5 in Hstep.
        right.
        remember (AI_trap :: es) as es0. clear IHHstep IHlen.
        rewrite Heqtv. exists 1. simpl.
        cut (forall n, (length es0 < n ->
                   exists m, 1 <= 2
                        /\ m <= S (S (length (es ++ aft)%list))
                        /\ lfilled 0
                                  (LH_base [AI_basic (BI_const v0)]
                                           (drop m ([AI_basic (BI_const v0) ; AI_trap]
                                                      ++ (es ++ aft))))
                                    [AI_trap] (AI_basic (BI_const v0) :: (es' ++ aft)%list)
                        /\ (hs', s', l0, i0) = (hs, s, l, i)
                        /\ opsem.reduce (host_instance:=host_instance) hs s
                                       {| f_locs := l ; f_inst := i |}
                                       [AI_basic (BI_const v0); AI_trap] hs s
                                       {| f_locs := l ; f_inst := i |} [AI_trap] /\
                          ([] : seq.seq administrative_instruction) = [] /\
                          ([] : seq.seq administrative_instruction) = [])).
        { intro Hn. assert (length es0 < S (length es0)) ; first lia.
          destruct (Hn _ H2) as (m & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7).
          exists m. repeat split => //=. exists (LH_base [AI_basic (BI_const v0)] []).
          unfold lfilled, lfill => //=. }
        intros len' Hlen'. 
        generalize dependent es0. clear H H0 H4 H6 Heqes. generalize dependent es.
        generalize dependent es'. generalize dependent aft.
        induction len' ; intros aft es' es es0 Heqes0 Hstep Hlen' ; first lia.
        induction Hstep ; try by inversion Heqes0.
        { destruct H ; try by inversion Heqes0.
          destruct vs ; inversion Heqes0.
          rewrite H7 in H. simpl in H ; false_assumption.
          destruct vs ; inversion Heqes0.
          rewrite H7 in H ; simpl in H ; false_assumption.
          inversion Heqes0. rewrite H2 in H ; simpl in H ; false_assumption.
          exists (2 + length es).
          repeat split => //=. lia. rewrite app_length. lia.
          unfold lfilled, lfill. simpl. by rewrite drop_app.
          rewrite Heqf in Heqf0 ; by inversion Heqf0.
          apply r_simple. apply (rs_trap (lh := LH_base [AI_basic (BI_const v0)] [])).
          intro Habs ; inversion Habs. unfold lfilled, lfill => //=. }
        destruct ves ; inversion Heqes0.
        rewrite H13 in H2. cut (const_list (AI_trap :: ves) = true).
        intro Habs ; simpl in Habs ; false_assumption.
        rewrite H2 ; by apply v_to_e_is_const_list.
        destruct ves ; inversion Heqes0.
        rewrite H10 in H2. cut (const_list (AI_trap :: ves) = true).
        intro Habs ; simpl in Habs ; false_assumption.
        rewrite H2 ; by apply v_to_e_is_const_list.
        destruct ves ; inversion Heqes0.
        rewrite H10 in H2. cut (const_list (AI_trap :: ves) = true).
        intro Habs ; simpl in Habs ; false_assumption.
        rewrite H2 ; by apply v_to_e_is_const_list.
        unfold lfilled, lfill in H.
        destruct k.
        { destruct lh as [bef0 aft0 |] ; last by false_assumption.
          remember (const_list bef0) as b eqn:Hbef0 ; destruct b ; last by false_assumption.
          apply b2p in H. rewrite Heqes0 in H.
          unfold lfilled, lfill in H0. rewrite <- Hbef0 in H0.
          apply b2p in H0. rewrite H0.
          destruct bef0. {
            destruct aft0. {
              rewrite app_nil_l app_nil_r in H. subst.
              rewrite app_nil_l app_nil_r.
              apply IHHstep => //=. }
            clear IHHstep. destruct es.
            { destruct es0 ; first by empty_list_no_reduce Hstep.
              inversion H. apply Logic.eq_sym, app_eq_nil in H6 as [_ Habs].
              inversion Habs. }
            rewrite H in Heqes0.
            get_tail a2 es ys y Hy. rewrite Hy in H.
            get_tail a1 aft0 zs z Hz ; rewrite Hz in H.
            rewrite app_comm_cons in H. do 2 rewrite app_assoc in H.
            apply app_inj_tail in H as [Heq Hyz]. simpl in Heq.
            assert (reduce hs s f (es0 ++ zs) hs' s' f' (es' ++ zs)).
            apply (r_label (es:=es0) (es':=es') (k:=0) (lh:=LH_base [] zs)) ;
              try done ;
              by unfold lfilled, lfill => //=.
            assert (length (es0 ++ zs) < len').
            rewrite Heqes0 in Hlen'. rewrite Hz in Hlen'. simpl in Hlen'.
            rewrite app_assoc in Hlen'. rewrite app_length in Hlen'. simpl in Hlen'.
            rewrite Nat.add_1_r in Hlen'. by apply lt_S_n.
            destruct (IHlen' (z :: aft) _ ys (es0 ++ zs) (Logic.eq_sym Heq) H H2) as
              (m & Hn & Hm & Hfill & Hσ & Hred & _ & _).
            unfold lfilled, lfill in Hfill. simpl in Hfill.
            apply b2p in Hfill. simpl. rewrite (app_comm_cons es) Hy Hz Hyz.
            exists m. repeat split => //=.
            { replace (ys ++ (z :: aft)) with ((ys ++ [z]) ++ aft) in Hm ;
                last by rewrite <- app_assoc.
              rewrite <- Hyz in Hm. rewrite <- Hy in Hm. simpl in Hm. lia. }
            unfold lfilled, lfill => //=. do 2 rewrite <- app_assoc => //=.
            rewrite app_assoc. rewrite Hfill. rewrite <- app_assoc => //=. }
          inversion H.
          rewrite <- H4 in Hbef0 ; simpl in Hbef0 ; inversion Hbef0. }
        fold lfill in H. destruct lh ; first by false_assumption.
        remember (const_list l1) as b eqn:Hl1 ; destruct b ; last by false_assumption.
        remember (lfill k lh es0) as lfilledk ;
          destruct lfilledk ; last by false_assumption.
        apply b2p in H.
        rewrite Heqes0 in H. destruct l1 ; inversion H.
        rewrite <- H4 in Hl1 ; simpl in Hl1 ; inversion Hl1. }
      clear IHHstep.
      simpl in Hbef ; apply Logic.eq_sym, andb_true_iff in Hbef as [Ha Hbef].
      assert (prim_step (es1 ++ es2) (hs, s, l, i) [] (bef ++ es' ++ aft)
                        (hs', s', l0, i0) []).
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
        simpl. apply b2p in Hfill.
        unfold lfilled, lfill in Hcontext.
        destruct lh ; last by false_assumption.
        exists (LH_base (a :: l1) l2).
        repeat split => //= ; try lia. by rewrite Hfill. unfold lfilled, lfill.
        simpl ; subst ; rewrite Ha. destruct (const_list l1) ; last by false_assumption.
        simpl. apply b2p in Hcontext ; by rewrite Hcontext. }
    }          
    clear IHHstep. fold lfill in H. destruct lh ; first by false_assumption.
    remember (const_list l1) as b eqn:Hl1 ; destruct b ; last by false_assumption.
    remember (lfill k lh es) as lfilledk ;
      destruct lfilledk ; last by false_assumption.
    apply b2p in H. rewrite H1 in H.
    destruct (first_non_value _ Hes1) as (vs & e & ult & Hvs & He & Hult).
    rewrite Hult in H. rewrite <- app_assoc in H. rewrite <- app_comm_cons in H.
    apply first_values in H as (Hvsl1 & Hlab & Hlast) => //= ; try by left.
    unfold lfilled, lfill in H0 ; fold lfill in H0.
    rewrite <- Hl1 in H0.
    remember (lfill k lh es') as lfilledk' ;
      destruct lfilledk' ; last by false_assumption.
    apply b2p in H0.
    left ; exists (l1 ++ AI_label n l2 l5 :: ult).
    repeat split => //=.
    rewrite <- app_assoc. rewrite <- app_comm_cons. by rewrite Hlast.
    rewrite Hult. rewrite Hlab. rewrite Hvsl1.
    apply (r_label (es:=es) (es':=es') (k:=S k) (lh:=LH_rec l1 n l2 lh ult)) ;
      first (by subst) ;
      unfold lfilled, lfill ; fold lfill ; rewrite <- Hl1.
    by rewrite <- Heqlfilledk.
    by rewrite <- Heqlfilledk'.
  - solve_prim_step_split_reduce_r H1 [AI_local n f' es'] Heqf0.
    by apply r_local.
Qed.


  


Lemma trap_reduce hs s f es hs' s' f' es' lh :
  lfilled 0 lh [AI_trap] es -> reduce hs s f es hs' s' f' es' ->
  exists lh', lfilled 0 lh' [AI_trap] es' /\ (hs, s, f) = (hs', s', f').
Proof.
  cut (forall n, length es < n -> lfilled 0 lh [AI_trap] es -> reduce hs s f es hs' s' f' es'
            -> exists lh', lfilled 0 lh' [AI_trap] es' /\ (hs, s, f) = (hs', s', f')).
  { intro Hn ; apply (Hn (S (length es))) ; lia. }
  intro n. generalize dependent es. generalize dependent es'. generalize dependent lh.
  induction n ; intros lh es' es Hlen Hfill Hred. inversion Hlen.
  unfold lfilled, lfill in Hfill. destruct lh as [bef aft|] ; last by false_assumption.
  remember (const_list bef) as b eqn:Hbef ; destruct b ; last by false_assumption.
  apply b2p in Hfill.
  induction Hred ; (try by inversion Hfill) ;
    try by found_intruse AI_trap Hfill Hxl1 ;
    try (apply in_app_or in Hxl1 as [Habs | Habs] ;
         [ assert (const_list ves) as Hconst ;
           [ by rewrite H1 ; apply v_to_e_is_const_list |
             intruse_among_values ves Habs Hconst ] |
           simpl in Habs ; destruct Habs as [Habs | Habs] ; inversion Habs ]).
  { destruct H ; (try by inversion Hfill) ;
          try by found_intruse AI_trap Hfill Hxl1 ;
          try (apply in_app_or in Hxl1 as [Habs | Habs] ;
               [ intruse_among_values vs Habs H
               | simpl in Habs ;
                 destruct Habs as [Habs | Habs] ; inversion Habs]).
        found_intruse AI_trap Hfill Hxl1.
        rewrite Hxl1 in H ; inversion H.
        exists (LH_base [] []).
    unfold lfilled, lfill => //=. }
  unfold lfilled, lfill in H. destruct k.
  { destruct lh as [bef1 aft1 |] ; last by false_assumption.
    remember (const_list bef1) as b eqn:Hbef1 ; destruct b ; last by false_assumption.
    unfold lfilled, lfill in H0. rewrite <- Hbef1 in H0.
    apply b2p in H, H0.
    destruct bef1. { destruct aft1. { rewrite app_nil_l app_nil_r in H.
                                      rewrite app_nil_l app_nil_r in H0.
                                      subst.
                                      apply IHHred => //=. }
      remember (iris.to_val es) as tv.
                     destruct tv.
                     { destruct v. { apply Logic.eq_sym, to_val_const_list in Heqtv.
                                     exfalso ; values_no_reduce Hred. }
                       apply Logic.eq_sym, to_val_trap_is_singleton in Heqtv.
                       apply Logic.eq_sym in Heqtv.
                       exfalso ; no_reduce Heqtv Hred. }
                     { destruct (first_non_value _ (Logic.eq_sym Heqtv)) as
                       (vs & e & es'' & Hvs & He & Hes).
                       rewrite H in Hlen.
                       rewrite Hes in H. rewrite Hfill in H. simpl in H.
                       rewrite <- app_assoc in H.
                       rewrite <- app_comm_cons in H.
                       apply first_values in H as (Hbefvs & Hetrap & _) => //= ;
                                                                          try by right.
                       assert (length es < n) as Hlenes.
                       { simpl in Hlen. rewrite app_length in Hlen. simpl in Hlen. lia. }
                       assert (lfilled 0 (LH_base vs es'') [AI_trap] es) as Htrap.
                       { unfold lfilled, lfill ;
                           rewrite Hvs Hes ; rewrite <- Hetrap ; done. }
                       destruct (IHn (LH_base vs es'') es' es Hlenes Htrap Hred)
                         as (lh' & Hfill' & Hσ).
                       unfold lfilled, lfill in Hfill'.
                       destruct lh' ; last by false_assumption.
                       remember (const_list l) as b eqn:Hl ; destruct b ;
                         last by false_assumption.
                       apply b2p in Hfill'. exists (LH_base l (l0 ++ a :: aft1)).
                       unfold lfilled, lfill ; rewrite <- Hl ; rewrite H0.
                       rewrite Hfill' => //=. by rewrite <- app_assoc. } }
    rewrite H in Hlen, Hfill. destruct bef ; inversion Hfill.
    rewrite H2 in Hbef1. inversion Hbef1.
    assert (length (bef1 ++ es ++ aft1) < n) as Hlen'.
    { simpl in Hlen. by apply lt_S_n. }
    assert (lfilled 0 (LH_base bef aft) [AI_trap] (bef1 ++ es ++ aft1)%list) as Hfill'.
    { rewrite H3. unfold lfilled, lfill ; simpl in Hbef ;
                    apply Logic.eq_sym, andb_true_iff in Hbef as [_ Hbef] ;
                    by rewrite Hbef. }
    assert (reduce hs s f (bef1 ++ es ++ aft1) hs' s' f' (bef1 ++ es' ++ aft1)) as Hred'.
    { apply (r_label (es:=es) (es':=es') (k:=0) (lh:=LH_base bef1 aft1)) ; (try done) ;
        unfold lfilled, lfill ; simpl in Hbef1 ;
        apply Logic.eq_sym, andb_true_iff in Hbef1 as [_ Hbef1] ; rewrite Hbef1 => //=. }
    destruct (IHn _ (bef1 ++ es' ++ aft1) (bef1 ++ es ++ aft1) Hlen' Hfill' Hred') as
      (lh' & Htrap & Hσ). unfold lfilled, lfill in Htrap.
    destruct lh' ; last by false_assumption.
    remember (const_list l) as b eqn:Hl ; destruct b ; last by false_assumption.
    apply b2p in Htrap. exists (LH_base (a :: l) l0).
    unfold lfilled, lfill => //=.
    simpl in Hbef1 ; apply Logic.eq_sym, andb_true_iff in Hbef1 as [Ha _] ; rewrite Ha.
    rewrite <- Hl => //=. rewrite H0. rewrite <- app_comm_cons. by rewrite Htrap. }
  fold lfill in H. destruct lh ; first by false_assumption.
  remember (const_list l) as b eqn:Hl ;
    destruct b ; last by false_assumption.
  destruct (lfill k lh es) ; last by false_assumption.
  apply b2p in H. rewrite Hfill in H.
  apply first_values in H as (_ & Habs & _) => //=. by right. by left.
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
  induction Hred as [e e' s f hs Hredsimpl | | | | |
                     a cl t1s t2s ts es' ves vcs n m k zs s f f' i' hs Hlistcl Hcl Hves
                       Hvcs Hts Ht1s Ht2s Hzts Hinst Hlocs |
                     a cl h t1s t2s ves vcs m n s s' r f hs hs' Hlistcl Hcl Hves Hvcs
                       Ht1s Ht2s Hhost |
                     a cl t1s t2s h ves vcs n m s f hs hs' Hlistcl Hcl Hves Hvcs Ht1s
                       Ht2s Hhost |
                     | | | | | | | | | | | | | | | 
                     s f ces les s' f' ces' les' k lh hs hs' Hred IHreduce Hles Hles' | ] ;
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
      apply (block_not_enough_arguments_no_reduce _ _ _ _ _ _ _ _ _ _ _ Hred0).
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
      apply (loop_not_enough_arguments_no_reduce _ _ _ _ _ _ _ _ _ _ _ Hred0).
      - rewrite Hvs in Hconst ; unfold const_list in Hconst ;
        rewrite forallb_app in Hconst ; apply andb_true_iff in Hconst ;
        destruct Hconst as [_ Hconst] ; exact Hconst.
      - rewrite Hvs in Hlenvs ; simpl in Hlenvs ; lia.
    }
    { right. exists (LH_base [] []).
      unfold lfilled, lfill in H0. destruct lh ; last by false_assumption.
      remember (const_list l2) as b eqn:Hl2.
      destruct b ; last by false_assumption.
      apply b2p in H0.
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
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hlistcl Hred0).
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
             _ _ _ _ _ _ _ _ _ _ _ _ Hlistcl Hred0).
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
    apply b2p in Hles.
    unfold lfilled, lfill in Hles'. rewrite <- Hbef in Hles'.
    apply b2p in Hles'.
    rewrite Hles in Heqves.
    destruct bef.
    { destruct ces ; first by empty_list_no_reduce Hred.
      inversion Heqves as [[ Ha Hes ]].
      destruct aft. { subst. repeat rewrite app_nil_r.
                      repeat rewrite app_nil_r in IHreduce.
                      rewrite app_nil_r in H.
                      apply IHreduce => //=. }
      remember (to_val ces) as tv.
      destruct tv.
      { destruct v0. { apply Logic.eq_sym, to_val_const_list in Heqtv.
                       exfalso ; apply ( values_no_reduce _ _ _ _ _ _ _ _ Hred).
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
        destruct bef0. { destruct es ; first by empty_list_no_reduce Hred.
                         inversion H0.
                         apply Logic.eq_sym, app_eq_unit in H4 as [[Hes Haft]|[Hes Haft]].
                         subst. remember [AI_basic (BI_const v)] as ev.
                         apply Logic.eq_sym in Heqev.
                         exfalso ; no_reduce Heqev Hred.
                         unfold lfilled, lfill in H1.
                         simpl in H1. apply b2p in H1. subst.
                         rewrite app_nil_r. 
                         apply IHHred => //=. }
        inversion H0.
        apply Logic.eq_sym, app_eq_unit in H4 as [[ Hb Hes ]|[Hb Hes]].
        apply app_eq_unit in Hes as [[ Hes _ ]|[Hes _]].
        subst ; empty_list_no_reduce Hred.
        subst ; remember [AI_trap] as ev ; apply Logic.eq_sym in Heqev ;
          exfalso ; no_reduce Heqev Hred.
        apply app_eq_nil in Hes as [ Hes _].
        subst ; empty_list_no_reduce Hred.
        split => //.
        apply AI_trap_reduce_det in Hred.
        by inversion Hred; subst.
      }
      rewrite <- Hes in H.
      destruct (prim_step_split_reduce_r _ _ _ _ _ _ _ (Logic.eq_sym Heqtv) H) as
        [ (es' & H1 & H2) | (n & m & lh & H1 & H2 & Hσ) ].
      { assert (reducible ces (hs,s,l,i)).
        unfold reducible, language.reducible. exists obs0, es', σ0, efs0 => //=.
        assert (prim_step ([AI_basic (BI_const v)] ++ ces) (hs,s,l,i) [] ces'
                          (hs',s',l0,i0) []).
        repeat split => //=. by subst.
        assert (length ces < len) as Hlences.
        rewrite <- Hes in Hlen. rewrite app_length in Hlen. simpl in Hlen ; lia.
        destruct (IHlen v ces ces' (hs,s,l,i) _ _ _ Hlences H0 H3) as
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
          apply b2p in Hfill. apply b2p in Hfill'.
          exists (LH_base l1 (l2 ++ a0 :: aft)), (LH_base l3 (l4 ++ a0 :: aft)).
          split => //= ; unfold lfilled, lfill => //=.
          rewrite <- Hl1 ; rewrite Hfill ; by rewrite <- app_assoc.
          rewrite <- Hl3 ; rewrite Hfill' ; by rewrite <- app_assoc. }
      }
      right. unfold lfilled, lfill in H2.
      destruct lh as [bef0 aft0|] ; last by false_assumption.
      remember (const_list bef0) as b eqn:Hbef0 ; destruct b ; last by false_assumption.
      apply b2p in H2.
      assert (lfilled 0 (LH_base (a :: bef0) aft0) [AI_trap] (a::ces)) as Htrap.
      { subst. unfold lfilled, lfill => //=. by rewrite <- Hbef0. }
      destruct (trap_reduce _ _ _ (a :: ces) _ _ _ ces' _ Htrap Hred) as (lh' & Hfill' & Hσ').
      unfold lfilled, lfill in Hfill'. destruct lh' ; last by false_assumption.
      remember (const_list l1) as b eqn:Hl1 ; destruct b ; last by false_assumption.
      apply b2p in Hfill'.
      exists (LH_base l1 (l2 ++ a0 :: aft)), (LH_base bef0 (aft0 ++ a0 :: aft)).
      split ; unfold lfilled, lfill => //=. rewrite <- Hl1. rewrite Hles'.
      rewrite Hfill'. simpl. by rewrite <- app_assoc.
      rewrite <- Hbef0. rewrite H2. rewrite <- app_assoc. split => //.
      by inversion Hσ'; subst; inversion H5.
    }
    inversion Heqves ; subst. left. repeat split => //=.
    unfold drop.
    apply (r_label (es:=ces) (es':=ces') (k:=0) (lh:=LH_base bef aft)) ; (try done) ;
      unfold lfilled, lfill ; simpl in Hbef ; rewrite <- Hbef => //=. }
  fold lfill in Hles. destruct lh ; first by false_assumption.
  remember (const_list l1) as b ; destruct b ; last by false_assumption.
  remember (lfill k lh ces) as filled ;
    destruct filled ; last by false_assumption.
  apply b2p in Hles. unfold lfilled, lfill in Hles'. fold lfill in Hles'.
  rewrite <- Heqb in Hles'. remember (lfill k lh ces') as filled'.
  destruct filled' ; last by false_assumption.
  apply b2p in Hles'. rewrite Hles in Heqves.
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

    


Lemma filled_is_val_imm : ∀ i lh es LI vals,
  iris.to_val LI = Some (immV vals) ->
  lfilled i lh es LI ->
  ∃ vs es', i = 0 ∧ lh = LH_base vs es' ∧ const_list vs ∧ const_list es'.
Proof.
  intros i.
  destruct i;
    intros lh es LI vals Hval Hfill%lfilled_Ind_Equivalent.
  { inversion Hfill;subst.
    apply to_val_cat in Hval as [Hval1 Hval2].
    apply to_val_cat in Hval2 as [Hval21 Hval22].
    eexists _,_. repeat split;eauto.
    eapply to_val_const_list. eauto. }
  { exfalso. inversion Hfill;subst.
    apply to_val_cat in Hval as [Hval1 Hval2].
    apply to_val_cat in Hval2 as [Hval21 Hval22].
    rewrite /= in Hval21. done. }
Qed.
Lemma filled_is_val_trap : ∀ i lh es LI,
  iris.to_val LI = Some trapV ->
  lfilled i lh es LI ->
  es ≠ [] ->
  i = 0 ∧ lh = LH_base [] [].
Proof.
  intros i.
  destruct i;
    intros lh es LI Hval Hfill%lfilled_Ind_Equivalent Hne.
  { inversion Hfill;subst.
    apply to_val_trap_is_singleton in Hval.
    destruct es,vs,es' =>//=.
    destruct es =>//=.
    destruct vs =>//=.
    destruct vs =>//=. }
  { inversion Hfill;subst.
    apply to_val_trap_is_singleton in Hval.
    repeat destruct vs =>//=. }
Qed.
Lemma filled_is_val_trap_nil : ∀ i lh LI,
  iris.to_val LI = Some trapV ->
  lfilled i lh [] LI ->
  ∃ vs es, i = 0 ∧ lh = LH_base vs es ∧
             ((vs = [] ∧ es = [::AI_trap])
              ∨ (es = [] ∧ vs = [::AI_trap])).
Proof.
  intros i.
  destruct i;
    intros lh LI Hval Hfill%lfilled_Ind_Equivalent.
  { inversion Hfill;subst.
    apply to_val_trap_is_singleton in Hval.
    destruct vs,es' =>//=.
    repeat destruct es' =>//=.
    repeat erewrite app_nil_l in Hval. simplify_eq.
    eexists _,_. eauto.
    repeat destruct vs =>//=.
    repeat erewrite app_nil_r in Hval. simplify_eq.
    eexists _,_. eauto.
    repeat destruct vs =>//=. }
  { exfalso. inversion Hfill;subst.
    apply to_val_trap_is_singleton in Hval.
    repeat destruct vs =>//=. }
Qed.

Lemma to_val_nil : ∀ e,
    iris.to_val e = Some (immV []) -> e = [].
Proof.
  intros e He. destruct e;auto. inversion He.
  destruct a=>//=.
  destruct b=>//=.
  destruct (iris.to_val e) eqn:HH =>//=.
  destruct v0=>//=.
  destruct e=>//=.
Qed.

Lemma fill_val : ∀ l LI v1 v2 vs es' es,
  lfilled 0 (LH_base vs es') es LI ->
  iris.to_val LI = Some (immV l) ->
  iris.to_val vs = Some (immV v1) ->
  iris.to_val es' = Some (immV v2) ->
  ∃ vs, iris.to_val es = Some (immV vs) ∧ l = v1 ++ vs ++ v2.
Proof.
  intros l LI v1 v2 vs es' es
         Hfill%lfilled_Ind_Equivalent
         HLI Hvs Hes'.
  destruct (iris.to_val es) eqn:Hsome.
  2: { apply (to_val_cat_None2 vs) in Hsome.
       apply (to_val_cat_None1 _ es') in Hsome.
       rewrite -app_assoc in Hsome.
       inversion Hfill;subst. by rewrite HLI in Hsome. }
  destruct v.
  2: { apply to_val_trap_is_singleton in Hsome as ->.
       inversion Hfill;subst.
       destruct vs, es' =>//=.
       rewrite to_val_not_trap_interweave in HLI=>//=. by left.
       rewrite to_val_not_trap_interweave in HLI=>//=. by left. }
  pose proof (to_val_cat_inv _ _ _ _ Hsome Hes') as Hi.
  pose proof (to_val_cat_inv _ _ _ _ Hvs Hi) as Hl.
  inversion Hfill;subst. rewrite Hl in HLI. simplify_eq. eauto.
Qed.

Lemma lfilled_reducible i lh e LI σ :
  lfilled i lh e LI ->
  reducible e σ ->
  reducible LI σ.
Proof.
  intros Hfill [obs [e' [σ' [efs Hred]]]].
  unfold reducible, language.reducible.
  Print lfilled_swap.
  specialize (lfilled_swap e' Hfill) as [LI' HLI'].
  exists [], LI', σ', [].
  destruct σ as [[[? ?] ?] ?].
  destruct σ' as [[[? ?] ?] ?].
  rewrite /= /iris.prim_step in Hred.
  destruct Hred as [Hred [-> ->]].
  split;auto.
  by eapply r_label => //.
Qed.

(* last remaining admit for the control flow lemmas! it roughly should state the following: 
   if there is a reducible hole in some expression LI, than the reduction of LI is 
   exactly the reduction of that hole. It ought to be the generalized version of 
   prim_step_split_reduce_r *)
Lemma lfilled_prim_step_split_reduce_r i lh es1 es2 σ LI e2 σ2 obs2 efs2 :
  lfilled i lh (es1 ++ es2)%list LI ->
  reducible es1 σ ->
  prim_step LI σ obs2 e2 σ2 efs2 ->
  ∃ e', prim_step es1 σ obs2 e' σ2 efs2 ∧ lfilled i lh (e' ++ es2) e2.
Proof.
Admitted.

(* Knowing hypothesis "Hred : objs -> _" (with frames (locs, inst) and (locs', inst')),
   attempts to exfalso away most of the possible ways Hred could hold, leaving the user
   with only the one possible desired case. Tactic will also attempt to trivially solve
   this one case, but may give it to user if attempt fails. *)


Ltac only_one_reduction Heqes0 Hred := (*objs locs inst locs' inst' :=*)
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
  let hs := fresh "hs" in
  let hs' := fresh "hs" in
  let H := fresh "H" in
  let H0 := fresh "H" in
  let H1 := fresh "H" in
  let Hconst := fresh "Hconst" in
(*  let Heqes0 := fresh "Heqes" in *)
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
 (*  remember objs as es0 eqn:Heqes0 ;
  remember {| f_locs := locs ; f_inst := inst |} as f eqn:Heqf ;
  remember {| f_locs := locs' ; f_inst := inst' |} as f' eqn:Heqf' ;
  apply Logic.eq_sym in Heqes0 ; *)
  induction Hred as [e e' s ? hs H | | | | | a | a | a | | | | | | | | | | | | | | | |
                      s ? es les s' f' es' les' k lh hs hs' Hred IHreduce H0 H1 | ];
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
                           apply b2p in H1 ; rewrite H1 ; rewrite app_nil_r ;
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
  (* at this point, only one case should be remaining.
     we attempt to solve this case too trivially, as the following line is often
     what user would be going to do next anyway *)
  (* try by inversion Heqes0 ; subst ; inversion Heqf' ; subst ; iFrame. *)

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
  apply b2p in Hfill.
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
      apply b2p in H0. apply first_values in H0 as (_ & Habs & _) ;
                         (try done) ; try by (left + right). }
  - found_intruse (AI_basic (BI_br i)) Hfill Hxl1.
    apply in_app_or in Hxl1 as [Habs | Habs].
    assert (const_list ves) as Hconst ; last by intruse_among_values ves Habs Hconst.
    rewrite H1 ; by apply v_to_e_is_const_list. inversion Habs ; inversion H9.
  - found_intruse (AI_basic (BI_br i)) Hfill Hxl1.
    apply in_app_or in Hxl1 as [Habs | Habs].
    assert (const_list ves) as Hconst ; last by intruse_among_values ves Habs Hconst.
    rewrite H1 ; by apply v_to_e_is_const_list. inversion Habs ; inversion H6.
  - found_intruse (AI_basic (BI_br i)) Hfill Hxl1.
    apply in_app_or in Hxl1 as [Habs | Habs].
    assert (const_list ves) as Hconst ; last by intruse_among_values ves Habs Hconst.
    rewrite H1 ; by apply v_to_e_is_const_list. inversion Habs ; inversion H6.
     - rewrite Hfill in H. unfold lfilled, lfill in H.
    destruct k. { destruct lh ; last by false_assumption.
                  remember (const_list l) as b eqn:Hl ; destruct b ;
                    last by false_assumption.
                  apply b2p in H.
                  destruct l. { destruct l0. { rewrite app_nil_l app_nil_r in H. 
                                               unfold lfilled, lfill in H0.
                                               simpl in H0. apply b2p in H0.
                                               rewrite app_nil_r in H0. subst.
                                               apply IHHred => //=. }
        destruct (first_non_value_reduce _ _ _ _ _ _ _ _ Hred) as
          (vs0 & e0 & es0 & Hvs0 & He0 & Hes). rewrite Hfill H in Hlen.
                                rewrite Hes in H. simpl in H.
                                rewrite <- app_assoc in H. rewrite <- app_comm_cons in H.
                                apply first_values in H as (_ & He0' & _) ;
                                  (try done) ; (try by (left + right)).
                                apply (IHn es' (LH_base vs0 es0) es) => //=.
                                simpl in Hlen. rewrite app_length in Hlen. simpl in Hlen.
                                lia. unfold lfilled, lfill ; rewrite Hvs0 ; by subst. }
         destruct (first_non_value_reduce _ _ _ _ _ _ _ _ Hred) as
           (vs0 & e0 & es0 & Hvs0 & He0 & Hes). rewrite Hfill H in Hlen.
                  rewrite Hes in H. simpl in H.
                  rewrite <- app_assoc in H. rewrite app_comm_cons in H.
                  rewrite <- (app_comm_cons es0) in H. rewrite app_assoc in H.
                  apply first_values in H as (_ & He0' & _) ;
                    (try done) ; (try by (left + right)).
                  apply (IHn es' (LH_base vs0 es0) es) => //=.
                  do 2 rewrite app_length in Hlen. simpl in Hlen.
                  lia. unfold lfilled, lfill ; rewrite Hvs0 ; by subst.
                  unfold const_list ; rewrite forallb_app ; apply andb_true_iff ;
                    split => //=. }
       fold lfill in H. destruct lh ; first by false_assumption.
       remember (const_list l) as b eqn:Hl ; destruct b ; last by false_assumption.
       destruct (lfill _ _ _) ; last by false_assumption. apply b2p in H.
       apply first_values in H as (_ & Habs & _) ; (try done) ; try by (left + right).
Qed.
 



Fixpoint size_of_instruction e :=
  match e with
  | AI_label _ _ LI => S (list_sum (map size_of_instruction LI))
  | AI_local _ _ LI => S (list_sum (map size_of_instruction LI))
  | _ => 1
  end .
Definition length_rec es := list_sum (map size_of_instruction es).

Lemma cons_length_rec a es :
  length_rec (a :: es) > 0.
Proof.
  unfold length_rec => //=. destruct a => //= ; lia.
Qed.


Lemma app_length_rec l1 l2 :
  length_rec (app l1 l2) = length_rec l1 + length_rec l2.
Proof.
  unfold length_rec. rewrite map_app. rewrite list_sum_app. done.  
Qed.

Lemma lfilled_length_rec k lh es les :
  lfilled k lh es les -> length_rec es <= length_rec les.
Proof.
  generalize dependent lh ; generalize dependent les.
  induction k ; intros les lh Hfill ; unfold lfilled, lfill in Hfill.
  { destruct lh ; last by false_assumption.
    destruct (const_list l) ; last by false_assumption.
    apply b2p in Hfill. rewrite Hfill. do 2 rewrite app_length_rec. lia. }
  fold lfill in Hfill. destruct lh ; first by false_assumption.
  destruct (const_list l) ; last by false_assumption.
  remember (lfill _ _ _ ) as fill ; destruct fill ; last by false_assumption.
  apply b2p in Hfill. assert (lfilled k lh es l2) as Hfill'.
  { unfold lfilled ; by rewrite <- Heqfill. }
  apply IHk in Hfill'.
  replace (AI_label n l0 l2 :: l1) with ([AI_label n l0 l2] ++ l1) in Hfill => //=.
  rewrite Hfill. do 2 rewrite app_length_rec.
  assert (length_rec l2 <= length_rec [AI_label n l0 l2]) ; last lia.
  unfold length_rec => //=. lia.
Qed.


  

Ltac not_const e He :=
  let b := fresh "b" in
  destruct e as [b| | | | ] ; (try by (left + right)) ;
  destruct b ; (try by left) ;
    by exfalso ; apply He.
(*
Lemma filled_first_values i lh vs e i' lh' vs' e' LI :
  lfilled i lh (vs ++ [e]) LI ->
  lfilled i' lh' (vs' ++ [e']) LI ->
  const_list vs -> const_list vs' ->
  (is_const e -> False) -> (is_const e' -> False) ->
  (forall n es LI, e = AI_label n es LI ->
              ( const_list LI \/ LI = [AI_trap] \/
                  exists k lh vs i, lfilled k lh (vs ++ [AI_basic (BI_br i)]) LI))
  -> (forall n es LI, e' = AI_label n es LI ->
                (const_list LI \/ LI = [AI_trap] \/
                   exists k lh vs i, lfilled k lh (vs ++ [AI_basic (BI_br i)]) LI))
  -> e = e'.
Proof.
  cut (forall n,
          amount_of_labels LI < n ->
          lfilled i lh (vs ++ [e]) LI ->
          lfilled i' lh' (vs' ++ [e']) LI ->
          const_list vs -> const_list vs' ->
          (is_const e -> False) -> (is_const e' -> False) ->
          (forall n es LI, e = AI_label n es LI ->
                      ( const_list LI \/ LI = [AI_trap] \/ 
                          exists k lh vs i, lfilled k lh (vs ++ [AI_basic (BI_br i)]) LI))
          -> (forall n es LI, e' = AI_label n es LI ->
                        (const_list LI \/ LI = [AI_trap] \/
                           exists k lh vs i, lfilled k lh (vs ++ [AI_basic (BI_br i)]) LI))
            ->  e = e').
  { intro Hn ; apply (Hn (S (amount_of_labels LI))) ; lia. }
  intro n. generalize dependent LI. generalize dependent e'.
  generalize dependent vs'. generalize dependent lh'. generalize dependent i'.
  generalize dependent e. generalize dependent vs. generalize dependent lh.
  generalize dependent i.
  induction n ;
    intros i lh vs e i' lh' vs' e' LI Hlab Hfill Hfill' Hvs Hvs' He He' Hlabe Hlabe' ;
    first by inversion Hlab.
  unfold lfilled, lfill in Hfill. destruct i.
  { destruct lh as [bef aft|] ; last by false_assumption.
    remember (const_list bef) as b eqn:Hbef ; destruct b ; last by false_assumption.
    apply b2p in Hfill.
    unfold lfilled, lfill in Hfill' ; destruct i'.
    { destruct lh' as [bef' aft'|] ; last by false_assumption.
      remember (const_list bef') as b0 eqn:Hbef' ; destruct b0 ; last by false_assumption.
      apply b2p in Hfill'.
      rewrite Hfill in Hfill'. do 2 rewrite <- app_assoc in Hfill'.
      rewrite app_assoc in Hfill'. rewrite (app_assoc bef' _ _) in Hfill'.
      apply first_values in Hfill' as (_ & Hee & _) ; (try done) ; (try by left) ;
        try by unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
      not_const e He. not_const e' He'. }
    fold lfill in Hfill'. destruct lh' ; first by false_assumption.
    remember (const_list l) as b ; destruct b ; last by false_assumption.
    remember (lfill i' lh' _) as fill ; destruct fill ; last by false_assumption.
    apply b2p in Hfill'. rewrite Hfill in Hfill'.
    rewrite <- app_assoc in Hfill'. rewrite app_assoc in Hfill'.
    apply first_values in Hfill' as ( _ & Hee & _ ) ; (try done) ; try by left.
    destruct (Hlabe n0 l0 l2 Hee) as [ HLI | [ HLI | HLI ]].
    - destruct i' ; unfold lfill in Heqfill.
      { destruct lh' as [bef' aft'|] ; last by inversion Heqfill.
        destruct (const_list bef') ; inversion Heqfill.
        rewrite H0 in HLI. unfold const_list in HLI. do 3 rewrite forallb_app in HLI.
        apply andb_true_iff in HLI as [_ Habs].
        apply andb_true_iff in Habs as [Habs _].
        apply andb_true_iff in Habs as [_ Habs]. simpl in Habs.
        apply andb_true_iff in Habs as [Habs _].
        exfalso ; by apply He'. }
      fold lfill in Heqfill. destruct lh' ; first by inversion Heqfill.
      destruct (const_list l3) ; last by inversion Heqfill.
      destruct (lfill i' _ _) ; inversion Heqfill.
      rewrite H0 in HLI. unfold const_list in HLI ; rewrite forallb_app in HLI.
      apply andb_true_iff in HLI as [_ Habs]. simpl in Habs. false_assumption.
    - rewrite HLI in Heqfill. destruct i' ; unfold lfill in Heqfill.
      { destruct lh' as [bef' aft' |] ; last by inversion Heqfill.
        destruct (const_list bef') ; inversion Heqfill.
        apply Logic.eq_sym, app_eq_unit in H0 as [[_ 
    by exfalso ; apply (Hlabe n0 l0 l2).
    not_const e He.
    unfold const_list ; rewrite forallb_app ; by apply andb_true_iff. }
  fold lfill in Hfill. 
  destruct lh as [| bef n' l lh aft] ; first by false_assumption.
  remember (const_list bef) as b ; destruct b ; last by false_assumption.
  remember (lfill i lh (vs ++ [e])) as les ; destruct les ; last by false_assumption.
  apply b2p in Hfill.
  unfold lfilled, lfill in Hfill' ; destruct i'.
  { destruct lh' as [bef' aft' |] ; last by false_assumption.
    remember (const_list bef') as b ; destruct b ; last by false_assumption.
    apply b2p in Hfill'. rewrite Hfill in Hfill'.
    rewrite <- app_assoc in Hfill'. rewrite app_assoc in Hfill'.
    apply first_values in Hfill' as ( _ & Habs & _ ) => //= ; try by left.
    by exfalso ; apply (Hlabe' n' l l0). not_const e' He'.
    unfold const_list ; rewrite forallb_app ; by apply andb_true_iff. }
  fold lfill in Hfill'.
  destruct lh' as [| bef' n'' l' lh' aft'] ; first by false_assumption.
  remember (const_list bef') as b ; destruct b ; last by false_assumption.
  remember (lfill i' lh' (vs' ++ [e'])) as les0 ; destruct les0 ; last by false_assumption.
  apply b2p in Hfill'. rewrite Hfill in Hfill'.
  apply first_values in Hfill' as ( Hl & Hlab' & _ ) => //= ; try by left.
  inversion Hlab' ; subst.
  apply (IHn i lh vs e i' lh' vs' e' l1) => //=.
  rewrite amount_of_labels_app in Hlab.
  replace (AI_label n'' l' l1 :: aft) with ([AI_label n'' l' l1] ++ aft) in Hlab => //=.
  rewrite amount_of_labels_app in Hlab. simpl in Hlab.
  rewrite Nat.add_0_r in Hlab. rewrite <- Nat.add_succ_l in Hlab.
  fold (amount_of_labels l1) in Hlab. lia.
  unfold lfilled ; rewrite <- Heqles ; done.
  unfold lfilled ; rewrite <- Heqles0 ; done.
Qed.        *)



Lemma lfilled_first_values i lh vs e i' lh' vs' e' LI :
  lfilled i lh (vs ++ [e]) LI ->
  lfilled i' lh' (vs' ++ [e']) LI ->
  const_list vs -> const_list vs' ->
  (is_const e -> False) -> (is_const e' -> False) ->
  (forall n es LI, e <> AI_label n es LI) -> (forall n es LI, e' <> AI_label n es LI) ->
  e = e' /\ i = i' /\ (length vs = length vs' -> vs = vs').
Proof.
  cut (forall n,
          length_rec LI < n ->
          lfilled i lh (vs ++ [e]) LI ->
          lfilled i' lh' (vs' ++ [e']) LI ->
          const_list vs -> const_list vs' ->
          (is_const e -> False) -> (is_const e' -> False) ->
          (forall n es LI, e <> AI_label n es LI) -> (forall n es LI, e' <> AI_label n es LI) ->
          e = e' /\ i = i' /\ (length vs = length vs' -> vs = vs')).
  { intro Hn ; apply (Hn (S (length_rec LI))) ; lia. }
  intro n. generalize dependent LI. generalize dependent e'.
  generalize dependent vs'. generalize dependent lh'. generalize dependent i'.
  generalize dependent e. generalize dependent vs. generalize dependent lh.
  generalize dependent i.
  induction n ;
    intros i lh vs e i' lh' vs' e' LI Hlab Hfill Hfill' Hvs Hvs' He He' Hlabe Hlabe' ;
    first by inversion Hlab.
  unfold lfilled, lfill in Hfill. destruct i.
  { destruct lh as [bef aft|] ; last by false_assumption.
    remember (const_list bef) as b eqn:Hbef ; destruct b ; last by false_assumption.
    apply b2p in Hfill.
    unfold lfilled, lfill in Hfill' ; destruct i'.
    { destruct lh' as [bef' aft'|] ; last by false_assumption.
      remember (const_list bef') as b0 eqn:Hbef' ; destruct b0 ; last by false_assumption.
      apply b2p in Hfill'.
      rewrite Hfill in Hfill'. do 2 rewrite <- app_assoc in Hfill'.
      rewrite app_assoc in Hfill'. rewrite (app_assoc bef' _ _) in Hfill'.
      apply first_values in Hfill' as (Hvvs & Hee & _) ; (try done) ; (try by left) ;
        try by unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
      repeat split => //=. intro Hlen. apply (app_inj_2 _ _ _ _ Hlen Hvvs).
      not_const e He. not_const e' He'. }
    fold lfill in Hfill'. destruct lh' ; first by false_assumption.
    remember (const_list l) as b ; destruct b ; last by false_assumption.
    destruct (lfill i' lh' _) ; last by false_assumption.
    apply b2p in Hfill'. rewrite Hfill in Hfill'.
    rewrite <- app_assoc in Hfill'. rewrite app_assoc in Hfill'.
    apply first_values in Hfill' as ( _ & Habs & _ ) ; (try done) ; try by left.
    by exfalso ; apply (Hlabe n0 l0 l2).
    not_const e He.
    unfold const_list ; rewrite forallb_app ; by apply andb_true_iff. }
  fold lfill in Hfill. 
  destruct lh as [| bef n' l lh aft] ; first by false_assumption.
  remember (const_list bef) as b ; destruct b ; last by false_assumption.
  remember (lfill i lh (vs ++ [e])) as les ; destruct les ; last by false_assumption.
  apply b2p in Hfill.
  unfold lfilled, lfill in Hfill' ; destruct i'.
  { destruct lh' as [bef' aft' |] ; last by false_assumption.
    remember (const_list bef') as b ; destruct b ; last by false_assumption.
    apply b2p in Hfill'. rewrite Hfill in Hfill'.
    rewrite <- app_assoc in Hfill'. rewrite app_assoc in Hfill'.
    apply first_values in Hfill' as ( _ & Habs & _ ) => //= ; try by left.
    by exfalso ; apply (Hlabe' n' l l0). not_const e' He'.
    unfold const_list ; rewrite forallb_app ; by apply andb_true_iff. }
  fold lfill in Hfill'.
  destruct lh' as [| bef' n'' l' lh' aft'] ; first by false_assumption.
  remember (const_list bef') as b ; destruct b ; last by false_assumption.
  remember (lfill i' lh' (vs' ++ [e'])) as les0 ; destruct les0 ; last by false_assumption.
  apply b2p in Hfill'. rewrite Hfill in Hfill'.
  apply first_values in Hfill' as ( Hl & Hlab' & _ ) => //= ; try by left.
  inversion Hlab' ; subst.
  assert (e = e' /\ i = i' /\ (length vs = length vs' -> vs = vs')) as (? & ? & ?).
  apply (IHn i lh vs e i' lh' vs' e' l1) => //=.
  rewrite app_length_rec in Hlab.
  replace (AI_label n'' l' l1 :: aft) with ([AI_label n'' l' l1] ++ aft) in Hlab => //=.
  rewrite app_length_rec in Hlab. simpl in Hlab.
  rewrite Nat.add_0_r in Hlab. rewrite <- Nat.add_succ_l in Hlab.
  fold (length_rec l1) in Hlab. lia.
  unfold lfilled ; rewrite <- Heqles ; done.
  unfold lfilled ; rewrite <- Heqles0 ; done.
  repeat split => //=. lia.
Qed.        


 Lemma lfilled_all_values i lh vs e i' lh' n0 es vs' LI :
  lfilled i lh (vs ++ [e]) LI ->
  lfilled i' lh' [AI_label n0 es vs'] LI ->
  const_list vs -> is_Some (to_val vs') ->
  (to_val [e]) = None ->
  (forall n es LI, e <> AI_label n es LI) ->
  False.
Proof.
  cut (forall n,
          length_rec LI < n ->
          lfilled i lh (vs ++ [e]) LI ->
          lfilled i' lh' [AI_label n0 es vs'] LI ->
          const_list vs -> (is_Some (to_val vs')) ->
          (to_val [e]) = None ->
          (forall n es LI, e <> AI_label n es LI) ->
          False).
  { intro Hn ; apply (Hn (S (length_rec LI))) ; lia. }
  intro n. generalize dependent LI. generalize dependent es. generalize dependent n0.
  generalize dependent vs'. generalize dependent lh'. generalize dependent i'.
  generalize dependent e. generalize dependent vs. generalize dependent lh.
  generalize dependent i.
  induction n ;
    intros i lh vs e i' lh' vs' n0 es LI Hlab Hfill Hfill' Hvs Hvs' He Hlabe ;
    first by inversion Hlab.
  unfold lfilled, lfill in Hfill. destruct i.
  { destruct lh as [bef aft|] ; last by false_assumption.
    remember (const_list bef) as b eqn:Hbef ; destruct b ; last by false_assumption.
    apply b2p in Hfill.
    unfold lfilled, lfill in Hfill' ; destruct i'.
    { destruct lh' as [bef' aft'|] ; last by false_assumption.
      remember (const_list bef') as b0 eqn:Hbef' ; destruct b0 ; last by false_assumption.
      apply b2p in Hfill'.
      rewrite Hfill in Hfill'. rewrite <- app_assoc in Hfill'.
      rewrite app_assoc in Hfill'. 
      apply first_values in Hfill' as (_ & Hee & _) ; (try done) ; (try by left) ;
        try by unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
      apply (Hlabe _ _ _ Hee). } 
    fold lfill in Hfill'. destruct lh' ; first by false_assumption.
    remember (const_list l) as b ; destruct b ; last by false_assumption.
    destruct (lfill i' lh' _) ; last by false_assumption.
    apply b2p in Hfill'. rewrite Hfill in Hfill'.
    rewrite <- app_assoc in Hfill'. rewrite app_assoc in Hfill'.
    apply first_values in Hfill' as ( _ & Habs & _ ) ; (try done) ; try by left.
    apply (Hlabe _ _ _ Habs).
    unfold const_list ; rewrite forallb_app ; by apply andb_true_iff. }
  fold lfill in Hfill. 
  destruct lh as [| bef n' l lh aft] ; first by false_assumption.
  remember (const_list bef) as b ; destruct b ; last by false_assumption.
  remember (lfill i lh (vs ++ [e])) as les ; destruct les ; last by false_assumption.
  apply b2p in Hfill.
  unfold lfilled, lfill in Hfill' ; destruct i'.
  { destruct lh' as [bef' aft' |] ; last by false_assumption.
    remember (const_list bef') as b ; destruct b ; last by false_assumption.
    apply b2p in Hfill'. rewrite Hfill in Hfill'.
    apply first_values in Hfill' as ( _ & Habs & _ ) => //= ; try by left.
    inversion Habs ; subst ; clear Habs.
    destruct i. { unfold lfill in Heqles. destruct lh ; last by inversion Heqles.
                  destruct (const_list l) ; inversion Heqles. rewrite H0 in Hvs'.
                  remember (to_val (l ++ _)) as tv.
                  destruct tv ; try by inversion Hvs'.
                  destruct v.
                  { apply Logic.eq_sym, to_val_const_list in Heqtv.
                    unfold const_list in Heqtv ;
                      do 3 rewrite forallb_app in Heqtv.
                    apply andb_true_iff in Heqtv as [_ Habs].
                    apply andb_true_iff in Habs as [Habs _].
                    apply andb_true_iff in Habs as [_ Habs].
                    apply andb_true_iff in Habs as [Habs _].
                    destruct e ; try by inversion Habs.
                    destruct b ; try by inversion Habs. }
                  apply Logic.eq_sym, to_val_trap_is_singleton in Heqtv.
                  apply app_eq_unit in Heqtv as [[_ Habs] | [_ Habs]].
                  apply app_eq_unit in Habs as [[Habs _] | [Habs _]].
                  by apply app_eq_nil in Habs as [_ Habs].
                  apply app_eq_unit in Habs as [[_ Habs] | [_ Habs]].
                  by inversion Habs ; subst.
                  by inversion Habs.
                  apply app_eq_nil in Habs as [Habs _].
                  apply app_eq_nil in Habs as [_ Habs].
                  by inversion Habs. }
    unfold lfill in Heqles ; fold lfill in Heqles.
    destruct lh ; first by inversion Heqles.
    destruct (const_list l) ; last by inversion Heqles.
    destruct (lfill i _ _) ; inversion Heqles.
    rewrite H0 in Hvs'.
    assert (to_val (l ++ (AI_label n1 l0 l2 :: l1)) = None) as Htv ;
      last by rewrite Htv in Hvs' ; inversion Hvs'.
    apply to_val_cat_None2 => //=. }
  fold lfill in Hfill'.
  destruct lh' as [| bef' n'' l' lh' aft'] ; first by false_assumption.
  remember (const_list bef') as b ; destruct b ; last by false_assumption.
  remember (lfill i' lh' _) as les0 ; destruct les0 ; last by false_assumption.
  apply b2p in Hfill'. rewrite Hfill in Hfill'.
  apply first_values in Hfill' as ( Hl & Hlab' & _ ) => //= ; try by left.
  inversion Hlab' ; subst.
  apply (IHn i lh vs e i' lh' vs' n0 es l1) => //=.
  rewrite app_length_rec in Hlab.
  replace (AI_label n'' l' l1 :: aft) with ([AI_label n'' l' l1] ++ aft) in Hlab => //=.
  rewrite app_length_rec in Hlab. simpl in Hlab.
  rewrite Nat.add_0_r in Hlab. rewrite <- Nat.add_succ_l in Hlab.
  fold (length_rec l1) in Hlab. lia.
  unfold lfilled ; rewrite <- Heqles ; done.
  unfold lfilled ; rewrite <- Heqles0 ; done.
Qed.


Lemma lfilled_trans : forall k lh es1 es2 k' lh' es3,
    lfilled k lh es1 es2 -> lfilled k' lh' es2 es3 -> exists lh'', lfilled (k+k') lh'' es1 es3.
Proof.
  intros k lh es1 es2 k' ; generalize dependent es2 ; generalize dependent es1 ;
    generalize dependent lh ; generalize dependent k ; induction k' ;
    intros k lh es1 es2 lh' es3 Hfill2 Hfill3.
  { unfold lfilled, lfill in Hfill3.
    destruct lh' as [ bef' aft' |] ; last by false_assumption.
    remember (const_list bef') as b eqn:Hbef' ; destruct b ; last by false_assumption.
    apply b2p in Hfill3.
    unfold lfilled, lfill in Hfill2.
    destruct k. { destruct lh as [bef aft |] ; last by false_assumption.
                  remember (const_list bef) as b eqn:Hbef ; destruct b ;
                    last by false_assumption.
                  apply b2p in Hfill2 ; subst.
                  exists (LH_base (bef' ++ bef) (aft ++ aft')). simpl.
                  unfold lfilled, lfill, const_list.
                  rewrite forallb_app. unfold const_list in Hbef ; rewrite <- Hbef.
                  unfold const_list in Hbef' ; rewrite <- Hbef' => //=.
                  by repeat rewrite app_assoc. }
    fold lfill in Hfill2. destruct lh as [| bef n es lh aft ] ; first by false_assumption.
    remember (const_list bef) as b eqn:Hbef ; destruct b ; last by false_assumption.
    remember (lfill k lh es1) as fill ; destruct fill ; last by false_assumption.
    apply b2p in Hfill2 ; subst.
    exists (LH_rec (bef' ++ bef) n es lh (aft ++ aft')). rewrite <- plus_n_O.
    unfold lfilled, lfill ; fold lfill ; unfold const_list.
    rewrite forallb_app. unfold const_list in Hbef ; rewrite <- Hbef.
    unfold const_list in Hbef' ; rewrite <- Hbef' => //=.
    rewrite <- Heqfill. repeat rewrite app_assoc. by rewrite <- app_assoc. }
  unfold lfilled, lfill in Hfill3 ; fold lfill in Hfill3.
  destruct lh' as [| bef' n' es' lh' aft' ] ; first by false_assumption.
  remember (const_list bef') as b eqn:Hbef' ; destruct b ; last by false_assumption.
  remember (lfill k' lh' es2) as fill' ; destruct fill' ; last by false_assumption.
  apply b2p in Hfill3. assert (lfilled k' lh' es2 l) as Hfill.
  by unfold lfilled ; rewrite <- Heqfill'.
  destruct (IHk' _ _ _ _ _ _ Hfill2 Hfill) as (lh'' & Hfill').
  exists (LH_rec bef' n' es' lh'' aft'). rewrite plus_comm => //=. rewrite plus_comm.
  unfold lfilled, lfill ; fold lfill. rewrite <- Hbef'. unfold lfilled in Hfill'.
  destruct (lfill (k + k') lh'' es1) ; last by false_assumption.
  apply b2p in Hfill' ; by subst.
Qed.

Lemma lfilled_trans2 : forall k lh es1 es1' es2 es2' k' lh' es3 es3',
    lfilled k lh es1 es2 -> lfilled k lh es1' es2' -> 
    lfilled k' lh' es2 es3 -> lfilled k' lh' es2' es3' ->
    exists lh'', lfilled (k+k') lh'' es1 es3 /\ lfilled (k+k') lh'' es1' es3'.
Proof.
  intros k lh es1 es1' es2 es2' k' ; generalize dependent es2' ;
    generalize dependent es2 ; generalize dependent es1' ; generalize dependent es1 ;
    generalize dependent lh ; generalize dependent k ; induction k' ;
    intros k lh es1 es1' es2 es2' lh' es3 es3' Hfill2 Hfill2' Hfill3 Hfill3'.
  { unfold lfilled, lfill in Hfill3. unfold lfilled, lfill in Hfill3'.
    destruct lh' as [ bef' aft' |] ; last by false_assumption.
    remember (const_list bef') as b eqn:Hbef' ; destruct b ; last by false_assumption.
    apply b2p in Hfill3. apply b2p in Hfill3'.
    unfold lfilled, lfill in Hfill2. unfold lfilled, lfill in Hfill2'.
    destruct k. { destruct lh as [bef aft |] ; last by false_assumption.
                  remember (const_list bef) as b eqn:Hbef ; destruct b ;
                    last by false_assumption.
                  apply b2p in Hfill2 ; apply b2p in Hfill2' ; subst.
                  exists (LH_base (bef' ++ bef) (aft ++ aft')) => //=.
                  split ; unfold lfilled, lfill, const_list ;
                    rewrite forallb_app ; unfold const_list in Hbef ; rewrite <- Hbef ;
                    unfold const_list in Hbef' ; rewrite <- Hbef' ; simpl ;
                    by repeat rewrite app_assoc. }
    fold lfill in Hfill2. fold lfill in Hfill2'.
    destruct lh as [| bef n es lh aft ] ; first by false_assumption.
    remember (const_list bef) as b eqn:Hbef ; destruct b ; last by false_assumption.
    remember (lfill k lh es1) as fill ; destruct fill ; last by false_assumption.
    remember (lfill k lh es1') as fill' ; destruct fill' ; last by false_assumption.
    apply b2p in Hfill2 ; apply b2p in Hfill2' ; subst.
    exists (LH_rec (bef' ++ bef) n es lh (aft ++ aft')) ; rewrite <- plus_n_O.
    unfold lfilled, lfill ; fold lfill ; unfold const_list.
    rewrite forallb_app. unfold const_list in Hbef ; rewrite <- Hbef.
    unfold const_list in Hbef' ; rewrite <- Hbef' => //=.
    rewrite <- Heqfill. rewrite <- Heqfill'.
    repeat rewrite app_assoc. split ; by rewrite <- app_assoc. }
  unfold lfilled, lfill in Hfill3 ; fold lfill in Hfill3.
  unfold lfilled, lfill in Hfill3' ; fold lfill in Hfill3'.
  destruct lh' as [| bef' n' es' lh' aft' ] ; first by false_assumption.
  remember (const_list bef') as b eqn:Hbef' ; destruct b ; last by false_assumption.
  remember (lfill k' lh' es2) as fill' ; destruct fill' ; last by false_assumption.
  remember (lfill k' lh' es2') as fill'' ; destruct fill'' ; last by false_assumption.
  apply b2p in Hfill3.  apply b2p in Hfill3'. assert (lfilled k' lh' es2 l) as Hfill.
  by unfold lfilled ; rewrite <- Heqfill'.
  assert (lfilled k' lh' es2' l0) as Hfill'.
  by unfold lfilled ; rewrite <- Heqfill''.
  destruct (IHk' _ _ _ _ _ _ _ _ _ Hfill2 Hfill2' Hfill Hfill')
    as (lh'' & Hfilln & Hfilln').
  exists (LH_rec bef' n' es' lh'' aft'). rewrite plus_comm => //=.  rewrite plus_comm.
  unfold lfilled, lfill ; fold lfill. rewrite <- Hbef'. unfold lfilled in Hfilln.
  destruct (lfill (k + k') lh'' es1) ; last by false_assumption.
  unfold lfilled in Hfilln'. destruct (lfill (k+k') lh'' es1') ; last by false_assumption.
  apply b2p in Hfilln ; apply b2p in Hfilln' ; by subst.
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
      apply b2p in H0. subst.
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
    rewrite H1 ; by apply v_to_e_is_const_list.
    by apply (r_invoke_host_success _ H H0 H1 H2 H3 H4 H5).
  - exists ves, (AI_invoke a), [], (ves ++ [AI_invoke a]),
      k, lh ; repeat split => //=.
    rewrite H1 ; by apply v_to_e_is_const_list.
    by apply (r_invoke_host_diverge _ H H0 H1 H2 H3 H4 H5).
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
            apply b2p in H0 ;
            exists 0, (LH_base [] []), bef, aft ; repeat split ; (try by simpl) ;
            [ intro Habs ; apply app_eq_nil in Habs as [-> ->] ;
                        rewrite app_nil_l app_nil_r in H0 ; by apply H
                      | unfold lfilled, lfill ; simpl ; subst ; rewrite app_nil_r]);
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
  left ; eexists 0, (LH_base [] []), _, _, _ ; repeat split ;
    (try unfold lfilled, lfill => //=) ; (try done) ; (try by rewrite app_nil_r).
  rewrite H1 ; by apply v_to_e_is_const_list. done.
  apply (r_invoke_host_success _ H H0 H1 H2 H3 H4 H5).
  left ; eexists 0, (LH_base [] []), _, _, _ ; repeat split ;
    (try unfold lfilled, lfill => //=) ; (try done) ; (try by rewrite app_nil_r).
  rewrite H1 ; by apply v_to_e_is_const_list. done.
  apply (r_invoke_host_diverge _ H H0 H1 H2 H3 H4 H5).
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
      apply b2p in Hes.
      destruct aft. { rewrite app_nil_r in Hes. rewrite app_assoc in Hes.
                      apply app_inj_tail in Hes as [Hes _].
                      exfalso ; values_no_reduce Hred. rewrite Hes.
                      unfold const_list ; rewrite forallb_app.
                      unfold const_list in Hvs ; rewrite Hvs.
                      unfold const_list in Hbef ; rewrite <- Hbef.
                      done. }
      get_tail a aft ys y Htail. rewrite Htail in Hes. repeat rewrite app_assoc in Hes.
      apply app_inj_tail in Hes as [Hes Hy]. left.
      unfold lfilled, lfill in Hes'. rewrite <- Hbef in Hes'. apply b2p in Hes'.
      rewrite Htail in Hes'. rewrite Hes'. repeat rewrite app_assoc.
      rewrite app_length. simpl. rewrite Nat.add_sub.
      rewrite take_app. repeat split => //=. by subst. subst.
      apply (r_label (k:=0) (lh:=LH_base bef ys) (es:=vs++[e0]) (es':=es'')) ; (try done) ;
        unfold lfilled, lfill ; rewrite <- Hbef ; repeat rewrite <- app_assoc => //=. }
    unfold lfilled, lfill in Hes ; fold lfill in Hes.
    destruct lh ; first by false_assumption.
    remember (const_list l2) as b eqn:Hl2 ; destruct b ; last by false_assumption.
    remember (lfill _ _ _) as fill ; destruct fill ; last by false_assumption.
    apply b2p in Hes.
    destruct l4. { apply app_inj_tail in Hes as [Hes _].
                   exfalso ; values_no_reduce Hred. by subst. }
    get_tail a l4 ys y Htail. rewrite Htail in Hes. rewrite app_comm_cons in Hes.
    repeat rewrite app_assoc in Hes.
    apply app_inj_tail in Hes as [Hes Hy]. left.
    unfold lfilled, lfill in Hes' ; fold lfill in Hes'.
    rewrite <- Hl2 in Hes'.
    remember (lfill _ _ es'') as fill' ; destruct fill' ; last by false_assumption.
    apply b2p in Hes'.
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
                apply b2p in Hfill. destruct aft0. destruct aft.
                { rewrite app_nil_r in Hfill. repeat rewrite app_assoc in Hfill.
                  replace ([AI_trap] ++ [])%SEQ with ([AI_trap] ++ [])%list in Hfill => //=.
                  rewrite app_nil_r in Hfill.                    
                  apply app_inj_tail in Hfill as [Hes _].
                  subst ; exfalso ; values_no_reduce Hred.
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
  apply b2p in Hfill. destruct l4. { apply app_inj_tail in Hfill as [Hes _].
                                     exfalso ; values_no_reduce Hred. by subst. }
  get_tail a l4 ys y Htail. rewrite Htail in Hfill. rewrite app_comm_cons in Hfill.
  repeat rewrite app_assoc in Hfill.
  apply app_inj_tail in Hfill as [Hes Hy]. left.
  unfold lfilled, lfill in Hfill' ; fold lfill in Hfill'.
  rewrite <- Hl2 in Hfill'.
  remember (lfill _ _ [AI_trap]) as fill' ; destruct fill' ; last by false_assumption.
  apply b2p in Hfill'.
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



Lemma lfilled_br_and_reduce hs s f es LI hs' s' f' es' i lh vs k lh' :
  reduce hs s f es hs' s' f' es' ->
  const_list vs ->
  lfilled i lh (vs ++ [AI_basic (BI_br i)]) LI ->
  lfilled k lh' es LI ->
  False.
Proof.
  intros Hred Hvs H1 Hes.
  cut (forall n, length_rec es < n -> False).
  { intro Hn ; apply (Hn (S (length_rec es))) ; lia. }
  intro n0. 
  generalize dependent es. generalize dependent es'.  generalize dependent k.
  generalize dependent lh'.
  induction n0 ; intros lh1 k es' es1 Hred2 Hfill Hlab ; first by lia.
  induction Hred2.
  { destruct H.
    - replace [AI_basic (BI_const v) ; AI_basic (BI_unop t op)] with
        ([AI_basic (BI_const v)] ++ [AI_basic (BI_unop t op)])%SEQ
        in Hfill ; last done.
      assert (AI_basic (BI_br i) = AI_basic (BI_unop t op)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
               AI_basic (BI_binop t op)] with
        ([AI_basic (BI_const v1) ; AI_basic (BI_const v2)]
           ++ [AI_basic (BI_binop t op)])%SEQ in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic (BI_binop t op)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
               AI_basic (BI_binop t op)] with
        ([AI_basic (BI_const v1) ; AI_basic (BI_const v2)]
           ++ [AI_basic (BI_binop t op)])%SEQ in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic (BI_binop t op)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const (VAL_int32 c)) ;
               AI_basic (BI_testop T_i32 testop)] with
        ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic (BI_testop T_i32 testop)]
        )%SEQ in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic (BI_testop T_i32 testop)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const (VAL_int64 c)) ;
               AI_basic (BI_testop T_i64 testop)] with
        ([AI_basic (BI_const (VAL_int64 c))] ++ [AI_basic (BI_testop T_i64 testop)]
        )%SEQ in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic (BI_testop T_i64 testop)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v1); AI_basic (BI_const v2) ;
               AI_basic (BI_relop t op)] with
        ([AI_basic (BI_const v1) ; AI_basic (BI_const v2)]
           ++ [AI_basic (BI_relop t op)])%SEQ in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic (BI_relop t op)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)]
        with ([AI_basic (BI_const v)]
                ++ [AI_basic (BI_cvtop t2 CVO_convert t1 sx)])%SEQ
        in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic (BI_cvtop t2 CVO_convert t1 sx)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)]
        with ([AI_basic (BI_const v)]
                ++ [AI_basic (BI_cvtop t2 CVO_convert t1 sx)])%SEQ
        in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic (BI_cvtop t2 CVO_convert t1 sx)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)]
        with ([AI_basic (BI_const v)]
                ++ [AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)])%SEQ
        in Hfill => //=.
      assert (AI_basic (BI_br i) =
                AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic BI_unreachable] with ([] ++ [AI_basic BI_unreachable])%SEQ
        in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic BI_unreachable) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic BI_nop] with ([] ++ [AI_basic BI_nop])%SEQ in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic BI_nop) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v) ; AI_basic BI_drop] with
        ([AI_basic (BI_const v)] ++ [AI_basic BI_drop])%SEQ in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic BI_drop) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
               AI_basic (BI_const (VAL_int32 n)) ; AI_basic BI_select] with
        ([AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
          AI_basic (BI_const (VAL_int32 n))] ++ [AI_basic BI_select])%SEQ
        in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic BI_select) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
               AI_basic (BI_const (VAL_int32 n)) ; AI_basic BI_select] with
        ([AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
          AI_basic (BI_const (VAL_int32 n))] ++ [AI_basic BI_select])%SEQ
        in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic BI_select) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - assert (AI_basic (BI_br i) = AI_basic (BI_block (Tf t1s t2s) es)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - assert (AI_basic (BI_br i) = AI_basic (BI_loop (Tf t1s t2s) es)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf e1s e2s)]
        with ([AI_basic (BI_const (VAL_int32 n))]
                ++ [AI_basic (BI_if tf e1s e2s)])%SEQ in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic (BI_if tf e1s e2s)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf e1s e2s)]
        with ([AI_basic (BI_const (VAL_int32 n))]
                ++ [AI_basic (BI_if tf e1s e2s)])%SEQ in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic (BI_if tf e1s e2s)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - exfalso ; apply (lfilled_all_values _ _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
      unfold is_Some.
      destruct (const_list_is_val vs0) as [v Hv] => //= ; exists (immV v). exact Hv.
    - exfalso ; apply (lfilled_all_values _ _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
      unfold is_Some ; exists trapV. done.
    - assert (lfilled (S i0) (LH_rec [] n es lh0 []) (vs0 ++ [AI_basic (BI_br i0)])
                      [AI_label n es LI0]) as Hfill'.
      unfold lfilled, lfill ; fold lfill => //=.
      unfold lfilled in H2. destruct (lfill i0 _ _) ; last by false_assumption.
      apply b2p in H2 ; by subst.
      destruct (lfilled_trans _ _ _ _ _ _ _ Hfill' Hfill) as [lh' Hfillbr].
      assert (AI_basic (BI_br i) = AI_basic (BI_br i0) /\ (i = S i0 + k)
              /\ (length vs = length vs0 -> vs = vs0)) as (? & ? & ?).
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfillbr) => //=.
      inversion H3 ; subst. lia.
    - replace [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_br_if i0)] with
        ([AI_basic (BI_const (VAL_int32 n))] ++ [AI_basic (BI_br_if i0)])%SEQ
        in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic (BI_br_if i0)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_br_if i0)] with
        ([AI_basic (BI_const (VAL_int32 n))] ++ [AI_basic (BI_br_if i0)])%SEQ
        in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic (BI_br_if i0)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_br_table iss i0)]
        with
        ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic (BI_br_table iss i0)])%SEQ
        in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic (BI_br_table iss i0)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_br_table iss i0)]
        with
        ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic (BI_br_table iss i0)])%SEQ
        in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic (BI_br_table iss i0)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_local n f0 es] with ([] ++ [AI_local n f0 es])%SEQ in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_local n f0 es) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_local n f0 [AI_trap]] with
        ([] ++ [AI_local n f0 [AI_trap]])%SEQ in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_local n f0 [AI_trap]) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_local n f0 es] with ([] ++ [AI_local n f0 es])%SEQ in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_local n f0 es) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [v ; AI_basic (BI_tee_local i0)] with
        ([v] ++ [AI_basic (BI_tee_local i0)])%SEQ in Hfill => //=.
      assert (AI_basic (BI_br i) = AI_basic (BI_tee_local i0)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
      by rewrite H.
    - destruct (lfilled_trans _ _ _ _ _ _ _ H0 Hfill) as [lh' Hfill'].
      replace [AI_trap] with ([] ++ [AI_trap])%SEQ in Hfill' => //=.
      assert (AI_basic (BI_br i) = AI_trap) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill') => //=. }
  * replace [AI_basic (BI_call i0)] with ([] ++ [AI_basic (BI_call i0)])%SEQ
    in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic (BI_call i0)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i0)]
      with ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic (BI_call_indirect i0)]
           )%SEQ in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic (BI_call_indirect i0)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i0)]
      with ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic (BI_call_indirect i0)]
           )%SEQ in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic (BI_call_indirect i0)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i0)]
      with ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic (BI_call_indirect i0)]
           )%SEQ in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic (BI_call_indirect i0)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * assert (AI_basic (BI_br i) = AI_invoke a) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    rewrite H2 ; by apply v_to_e_is_const_list.
  * assert (AI_basic (BI_br i) = AI_invoke a) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    rewrite H2 ; by apply v_to_e_is_const_list.
  * assert (AI_basic (BI_br i) = AI_invoke a) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    rewrite H2 ; by apply v_to_e_is_const_list.
  * replace [AI_basic (BI_get_local j)] with
      ([] ++ [AI_basic (BI_get_local j)])%SEQ in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic (BI_get_local j)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const v); AI_basic (BI_set_local i0)] with
      ([AI_basic (BI_const v)] ++ [AI_basic (BI_set_local i0)])%SEQ in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic (BI_set_local i0)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_get_global i0)] with
      ([] ++ [AI_basic (BI_get_global i0)])%SEQ in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic (BI_get_global i0)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const v); AI_basic (BI_set_global i0)] with
      ([AI_basic (BI_const v)] ++ [AI_basic (BI_set_global i0)])%SEQ in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic (BI_set_global i0)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_load t None a off)]
      with ([AI_basic (BI_const (VAL_int32 k0))]
              ++ [AI_basic (BI_load t None a off)])%SEQ in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic (BI_load t None a off)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_load t None a off)]
      with ([AI_basic (BI_const (VAL_int32 k0))]
              ++ [AI_basic (BI_load t None a off)])%SEQ in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic (BI_load t None a off)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 k0)) ;
             AI_basic (BI_load t (Some (tp, sx)) a off)]
      with ([AI_basic (BI_const (VAL_int32 k0))]
              ++ [AI_basic (BI_load t (Some (tp, sx)) a off)])%SEQ in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic (BI_load t (Some (tp, sx)) a off)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 k0)) ;
             AI_basic (BI_load t (Some (tp, sx)) a off)]
      with ([AI_basic (BI_const (VAL_int32 k0))]
              ++ [AI_basic (BI_load t (Some (tp, sx)) a off)])%SEQ in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic (BI_load t (Some (tp, sx)) a off)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_const v);
             AI_basic (BI_store t None a off)] with
      ([AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_const v)]
         ++ [AI_basic (BI_store t None a off)])%SEQ in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic (BI_store t None a off)) => //=.
    apply  (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_const v);
             AI_basic (BI_store t None a off)] with
      ([AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_const v)]
         ++ [AI_basic (BI_store t None a off)])%SEQ in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic (BI_store t None a off)) => //=.
    apply  (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_const v);
             AI_basic (BI_store t (Some tp) a off)] with
      ([AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_const v)]
         ++ [AI_basic (BI_store t (Some tp) a off)])%SEQ in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic (BI_store t (Some tp) a off)) => //=.
    apply  (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_const v);
             AI_basic (BI_store t (Some tp) a off)] with
      ([AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_const v)]
         ++ [AI_basic (BI_store t (Some tp) a off)])%SEQ in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic (BI_store t (Some tp) a off)) => //=.
    apply  (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic BI_current_memory] with ([] ++ [AI_basic BI_current_memory])%SEQ
      in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic BI_current_memory) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 c)) ; AI_basic BI_grow_memory] with
      ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic BI_grow_memory])%SEQ
      in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic BI_grow_memory) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 c)) ; AI_basic BI_grow_memory] with
      ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic BI_grow_memory])%SEQ
      in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_basic BI_grow_memory) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfill'].
    apply (IHn0 _ _ _ _ Hred2 Hfill').
    unfold lfilled, lfill in H ; destruct k0.
    { destruct lh0 ; last by false_assumption.
      destruct (const_list l) ; last by false_assumption.
      apply b2p in H.
      destruct l. { destruct l0. { unfold lfilled, lfill in H0 ; simpl in H0.
                                    apply b2p in H0. simpl in H.
                                    rewrite app_nil_r in H.
                                    rewrite app_nil_r in H0. subst.
                                    exfalso ; apply IHHred2 => //=. }
        simpl in H. rewrite H in Hlab.
                     rewrite app_length_rec in Hlab.
                     assert (length_rec (a :: l0) > 0) ; first by apply cons_length_rec.
                     lia. }
      rewrite H in Hlab. do 2 rewrite app_length_rec in Hlab.
      assert (length_rec (a :: l) > 0) ; first by apply cons_length_rec.
      lia. }
    fold lfill in H. destruct lh0 ; first by false_assumption.
    destruct (const_list l) ; last by false_assumption.
    remember (lfill _ _ _) as fill ; destruct fill ; last by false_assumption.
    apply b2p in H. rewrite H in Hlab.
    replace (AI_label n l0 l2 :: l1) with ([AI_label n l0 l2] ++ l1) in Hlab => //=.
    do 2 rewrite app_length_rec in Hlab.
    unfold length_rec in Hlab. simpl in Hlab.
    rewrite <- (Nat.add_0_r (S n0)) in Hlab. rewrite plus_comm in Hlab.
    apply Nat.le_lt_add_lt in Hlab ; try lia. 
    apply lt_S_n in Hlab. rewrite Nat.add_0_r in Hlab.
    assert (lfilled k0 lh0 es l2) as Hfill''.
    { unfold lfilled ; by rewrite <- Heqfill. }
    apply lfilled_length_rec in Hfill''. unfold length_rec.
    unfold length_rec in Hfill''. lia.
  * replace [AI_local n f es] with ([] ++ [AI_local n f es])%SEQ in Hfill => //=.
    assert (AI_basic (BI_br i) = AI_local n f es) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
Qed.

Lemma lfilled_return_and_reduce hs s f es LI hs' s' f' es' i lh vs k lh' :
  reduce hs s f es hs' s' f' es' ->
  const_list vs ->
  lfilled i lh (vs ++ [AI_basic BI_return]) LI ->
  lfilled k lh' es LI ->
  False.
Proof.
  intros Hred Hvs H1 Hes.
  cut (forall n, length_rec es < n -> False).
  { intro Hn ; apply (Hn (S (length_rec es))) ; lia. }
  intro n0. 
  generalize dependent es. generalize dependent es'. generalize dependent k.
  generalize dependent lh'.
  induction n0 ; intros lh1 k es' es1 Hred2 Hfill Hlab ; first by lia.
  induction Hred2.
  { destruct H.
    - replace [AI_basic (BI_const v) ; AI_basic (BI_unop t op)] with
        ([AI_basic (BI_const v)] ++ [AI_basic (BI_unop t op)])%SEQ
        in Hfill ; last done.
      assert (AI_basic BI_return = AI_basic (BI_unop t op)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
               AI_basic (BI_binop t op)] with
        ([AI_basic (BI_const v1) ; AI_basic (BI_const v2)]
           ++ [AI_basic (BI_binop t op)])%SEQ in Hfill => //=.
      assert (AI_basic BI_return = AI_basic (BI_binop t op)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
               AI_basic (BI_binop t op)] with
        ([AI_basic (BI_const v1) ; AI_basic (BI_const v2)]
           ++ [AI_basic (BI_binop t op)])%SEQ in Hfill => //=.
      assert (AI_basic BI_return = AI_basic (BI_binop t op)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const (VAL_int32 c)) ;
               AI_basic (BI_testop T_i32 testop)] with
        ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic (BI_testop T_i32 testop)]
        )%SEQ in Hfill => //=.
      assert (AI_basic BI_return = AI_basic (BI_testop T_i32 testop)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const (VAL_int64 c)) ;
               AI_basic (BI_testop T_i64 testop)] with
        ([AI_basic (BI_const (VAL_int64 c))] ++ [AI_basic (BI_testop T_i64 testop)]
        )%SEQ in Hfill => //=.
      assert (AI_basic BI_return = AI_basic (BI_testop T_i64 testop)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v1); AI_basic (BI_const v2) ;
               AI_basic (BI_relop t op)] with
        ([AI_basic (BI_const v1) ; AI_basic (BI_const v2)]
           ++ [AI_basic (BI_relop t op)])%SEQ in Hfill => //=.
      assert (AI_basic BI_return = AI_basic (BI_relop t op)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)]
        with ([AI_basic (BI_const v)]
                ++ [AI_basic (BI_cvtop t2 CVO_convert t1 sx)])%SEQ
        in Hfill => //=.
      assert (AI_basic BI_return = AI_basic (BI_cvtop t2 CVO_convert t1 sx)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)]
        with ([AI_basic (BI_const v)]
                ++ [AI_basic (BI_cvtop t2 CVO_convert t1 sx)])%SEQ
        in Hfill => //=.
      assert (AI_basic BI_return = AI_basic (BI_cvtop t2 CVO_convert t1 sx)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)]
        with ([AI_basic (BI_const v)]
                ++ [AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)])%SEQ
        in Hfill => //=.
      assert (AI_basic BI_return =
                AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic BI_unreachable] with ([] ++ [AI_basic BI_unreachable])%SEQ
        in Hfill => //=.
      assert (AI_basic BI_return = AI_basic BI_unreachable) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic BI_nop] with ([] ++ [AI_basic BI_nop])%SEQ in Hfill => //=.
      assert (AI_basic BI_return = AI_basic BI_nop) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v) ; AI_basic BI_drop] with
        ([AI_basic (BI_const v)] ++ [AI_basic BI_drop])%SEQ in Hfill => //=.
      assert (AI_basic BI_return = AI_basic BI_drop) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
               AI_basic (BI_const (VAL_int32 n)) ; AI_basic BI_select] with
        ([AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
          AI_basic (BI_const (VAL_int32 n))] ++ [AI_basic BI_select])%SEQ
        in Hfill => //=.
      assert (AI_basic BI_return = AI_basic BI_select) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
               AI_basic (BI_const (VAL_int32 n)) ; AI_basic BI_select] with
        ([AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
          AI_basic (BI_const (VAL_int32 n))] ++ [AI_basic BI_select])%SEQ
        in Hfill => //=.
      assert (AI_basic BI_return = AI_basic BI_select) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - assert (AI_basic BI_return = AI_basic (BI_block (Tf t1s t2s) es)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - assert (AI_basic BI_return = AI_basic (BI_loop (Tf t1s t2s) es)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf e1s e2s)]
        with ([AI_basic (BI_const (VAL_int32 n))]
                ++ [AI_basic (BI_if tf e1s e2s)])%SEQ in Hfill => //=.
      assert (AI_basic BI_return = AI_basic (BI_if tf e1s e2s)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf e1s e2s)]
        with ([AI_basic (BI_const (VAL_int32 n))]
                ++ [AI_basic (BI_if tf e1s e2s)])%SEQ in Hfill => //=.
      assert (AI_basic BI_return = AI_basic (BI_if tf e1s e2s)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - exfalso ; apply (lfilled_all_values _ _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
      unfold is_Some.
      destruct (const_list_is_val vs0) as [v Hv] => //= ; exists (immV v). exact Hv.
    - exfalso ; apply (lfilled_all_values _ _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
      unfold is_Some ; exists trapV. done.
    - assert (lfilled (S i0) (LH_rec [] n es lh0 []) (vs0 ++ [AI_basic (BI_br i0)])
                      [AI_label n es LI0]) as Hfill'.
      unfold lfilled, lfill ; fold lfill => //=.
      unfold lfilled in H2. destruct (lfill i0 _ _) ; last by false_assumption.
      apply b2p in H2 ; by subst.
      destruct (lfilled_trans _ _ _ _ _ _ _ Hfill' Hfill) as [lh' Hfillbr].
      assert (AI_basic BI_return = AI_basic (BI_br i0) /\ (i = S i0 + k)
              /\ (length vs = length vs0 -> vs = vs0)) as (? & ? & ?).
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfillbr) => //=.
      inversion H3.
    - replace [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_br_if i0)] with
        ([AI_basic (BI_const (VAL_int32 n))] ++ [AI_basic (BI_br_if i0)])%SEQ
        in Hfill => //=.
      assert (AI_basic BI_return = AI_basic (BI_br_if i0)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_br_if i0)] with
        ([AI_basic (BI_const (VAL_int32 n))] ++ [AI_basic (BI_br_if i0)])%SEQ
        in Hfill => //=.
      assert (AI_basic BI_return = AI_basic (BI_br_if i0)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_br_table iss i0)]
        with
        ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic (BI_br_table iss i0)])%SEQ
        in Hfill => //=.
      assert (AI_basic BI_return = AI_basic (BI_br_table iss i0)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_br_table iss i0)]
        with
        ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic (BI_br_table iss i0)])%SEQ
        in Hfill => //=.
      assert (AI_basic BI_return = AI_basic (BI_br_table iss i0)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_local n f0 es] with ([] ++ [AI_local n f0 es])%SEQ in Hfill => //=.
      assert (AI_basic BI_return = AI_local n f0 es) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_local n f0 [AI_trap]] with
        ([] ++ [AI_local n f0 [AI_trap]])%SEQ in Hfill => //=.
      assert (AI_basic BI_return = AI_local n f0 [AI_trap]) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [AI_local n f0 es] with ([] ++ [AI_local n f0 es])%SEQ in Hfill => //=.
      assert (AI_basic BI_return = AI_local n f0 es) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    - replace [v ; AI_basic (BI_tee_local i0)] with
        ([v] ++ [AI_basic (BI_tee_local i0)])%SEQ in Hfill => //=.
      assert (AI_basic BI_return = AI_basic (BI_tee_local i0)) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
      by rewrite H.
    - destruct (lfilled_trans _ _ _ _ _ _ _ H0 Hfill) as [lh' Hfill'].
      replace [AI_trap] with ([] ++ [AI_trap])%SEQ in Hfill' => //=.
      assert (AI_basic BI_return = AI_trap) => //=.
      apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill') => //=. }
  * replace [AI_basic (BI_call i0)] with ([] ++ [AI_basic (BI_call i0)])%SEQ
    in Hfill => //=.
    assert (AI_basic BI_return = AI_basic (BI_call i0)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i0)]
      with ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic (BI_call_indirect i0)]
           )%SEQ in Hfill => //=.
    assert (AI_basic BI_return = AI_basic (BI_call_indirect i0)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i0)]
      with ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic (BI_call_indirect i0)]
           )%SEQ in Hfill => //=.
    assert (AI_basic BI_return = AI_basic (BI_call_indirect i0)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i0)]
      with ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic (BI_call_indirect i0)]
           )%SEQ in Hfill => //=.
    assert (AI_basic BI_return = AI_basic (BI_call_indirect i0)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * assert (AI_basic BI_return = AI_invoke a) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    rewrite H2 ; by apply v_to_e_is_const_list.
  * assert (AI_basic BI_return = AI_invoke a) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    rewrite H2 ; by apply v_to_e_is_const_list.
  * assert (AI_basic BI_return = AI_invoke a) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
    rewrite H2 ; by apply v_to_e_is_const_list.
  * replace [AI_basic (BI_get_local j)] with
      ([] ++ [AI_basic (BI_get_local j)])%SEQ in Hfill => //=.
    assert (AI_basic BI_return = AI_basic (BI_get_local j)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const v); AI_basic (BI_set_local i0)] with
      ([AI_basic (BI_const v)] ++ [AI_basic (BI_set_local i0)])%SEQ in Hfill => //=.
    assert (AI_basic BI_return = AI_basic (BI_set_local i0)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_get_global i0)] with
      ([] ++ [AI_basic (BI_get_global i0)])%SEQ in Hfill => //=.
    assert (AI_basic BI_return = AI_basic (BI_get_global i0)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const v); AI_basic (BI_set_global i0)] with
      ([AI_basic (BI_const v)] ++ [AI_basic (BI_set_global i0)])%SEQ in Hfill => //=.
    assert (AI_basic BI_return = AI_basic (BI_set_global i0)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_load t None a off)]
      with ([AI_basic (BI_const (VAL_int32 k0))]
              ++ [AI_basic (BI_load t None a off)])%SEQ in Hfill => //=.
    assert (AI_basic BI_return = AI_basic (BI_load t None a off)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_load t None a off)]
      with ([AI_basic (BI_const (VAL_int32 k0))]
              ++ [AI_basic (BI_load t None a off)])%SEQ in Hfill => //=.
    assert (AI_basic BI_return = AI_basic (BI_load t None a off)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 k0)) ;
             AI_basic (BI_load t (Some (tp, sx)) a off)]
      with ([AI_basic (BI_const (VAL_int32 k0))]
              ++ [AI_basic (BI_load t (Some (tp, sx)) a off)])%SEQ in Hfill => //=.
    assert (AI_basic BI_return = AI_basic (BI_load t (Some (tp, sx)) a off)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 k0)) ;
             AI_basic (BI_load t (Some (tp, sx)) a off)]
      with ([AI_basic (BI_const (VAL_int32 k0))]
              ++ [AI_basic (BI_load t (Some (tp, sx)) a off)])%SEQ in Hfill => //=.
    assert (AI_basic BI_return = AI_basic (BI_load t (Some (tp, sx)) a off)) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_const v);
             AI_basic (BI_store t None a off)] with
      ([AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_const v)]
         ++ [AI_basic (BI_store t None a off)])%SEQ in Hfill => //=.
    assert (AI_basic BI_return = AI_basic (BI_store t None a off)) => //=.
    apply  (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_const v);
             AI_basic (BI_store t None a off)] with
      ([AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_const v)]
         ++ [AI_basic (BI_store t None a off)])%SEQ in Hfill => //=.
    assert (AI_basic BI_return = AI_basic (BI_store t None a off)) => //=.
    apply  (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_const v);
             AI_basic (BI_store t (Some tp) a off)] with
      ([AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_const v)]
         ++ [AI_basic (BI_store t (Some tp) a off)])%SEQ in Hfill => //=.
    assert (AI_basic BI_return = AI_basic (BI_store t (Some tp) a off)) => //=.
    apply  (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_const v);
             AI_basic (BI_store t (Some tp) a off)] with
      ([AI_basic (BI_const (VAL_int32 k0)) ; AI_basic (BI_const v)]
         ++ [AI_basic (BI_store t (Some tp) a off)])%SEQ in Hfill => //=.
    assert (AI_basic BI_return = AI_basic (BI_store t (Some tp) a off)) => //=.
    apply  (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic BI_current_memory] with ([] ++ [AI_basic BI_current_memory])%SEQ
      in Hfill => //=.
    assert (AI_basic BI_return = AI_basic BI_current_memory) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 c)) ; AI_basic BI_grow_memory] with
      ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic BI_grow_memory])%SEQ
      in Hfill => //=.
    assert (AI_basic BI_return = AI_basic BI_grow_memory) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * replace [AI_basic (BI_const (VAL_int32 c)) ; AI_basic BI_grow_memory] with
      ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic BI_grow_memory])%SEQ
      in Hfill => //=.
    assert (AI_basic BI_return = AI_basic BI_grow_memory) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
  * destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfill'].
    apply (IHn0 _ _ _ _ Hred2 Hfill').
    unfold lfilled, lfill in H ; destruct k0.
    { destruct lh0 ; last by false_assumption.
      destruct (const_list l) ; last by false_assumption.
      apply b2p in H.
      destruct l. { destruct l0. { unfold lfilled, lfill in H0 ; simpl in H0.
                                   apply b2p in H0. simpl in H.
                                   rewrite app_nil_r in H0.
                                   rewrite app_nil_r in H. subst.
                                   exfalso ; apply IHHred2 => //=. }
        simpl in H. rewrite H in Hlab.
                    rewrite app_length_rec in Hlab. 
                    destruct (cons_length_rec a l0) as [? | ?]. lia. lia. }
      rewrite H in Hlab. do 2 rewrite app_length_rec in Hlab.
      destruct (cons_length_rec a l) as [? | ?] ; lia. }
    fold lfill in H. destruct lh0 ; first by false_assumption.
    destruct (const_list l) ; last by false_assumption.
    remember (lfill _ _ _) as fill ; destruct fill ; last by false_assumption.
    apply b2p in H. rewrite H in Hlab.
    replace (AI_label n l0 l2 :: l1) with ([AI_label n l0 l2] ++ l1) in Hlab => //=.
    do 2 rewrite app_length_rec in Hlab.
    unfold length_rec in Hlab. simpl in Hlab.
    rewrite <- (Nat.add_0_r (S n0)) in Hlab. rewrite plus_comm in Hlab.
    apply Nat.le_lt_add_lt in Hlab ; try lia. 
    apply lt_S_n in Hlab. rewrite Nat.add_0_r in Hlab.
    assert (lfilled k0 lh0 es l2) as Hfill''.
    { unfold lfilled ; by rewrite <- Heqfill. }
    apply lfilled_length_rec in Hfill''. unfold length_rec.
    unfold length_rec in Hfill''. lia.
  * replace [AI_local n f es] with ([] ++ [AI_local n f es])%SEQ in Hfill => //=.
    assert (AI_basic BI_return = AI_local n f es) => //=.
    apply (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 Hfill) => //=.
Qed.

Inductive starts_with : administrative_instruction -> seq.seq administrative_instruction
                        -> Prop :=
| start_label : forall vs n es LI es' e, const_list vs -> starts_with e LI ->
                                    starts_with e (vs ++ [AI_label n es LI] ++ es')
| start_local : forall vs n es LI es' e, const_list vs -> starts_with e LI ->
                                    starts_with e (vs ++ [AI_local n es LI] ++ es')
| start_basic : forall vs a es, const_list vs -> (is_const (AI_basic a) -> False) ->
                           starts_with (AI_basic a) (vs ++ [AI_basic a] ++ es)
| start_invoke : forall vs a es, const_list vs -> starts_with (AI_invoke a)
                                                        (vs ++ [AI_invoke a] ++ es)
| start_trap : forall vs es, const_list vs -> starts_with AI_trap (vs ++ [AI_trap] ++ es).

Lemma start_is_unique e1 e2 es :
  starts_with e1 es -> starts_with e2 es -> e1 = e2.
Proof.
  intros H1 H2. induction H1.
  - remember (vs ++ [AI_label n es LI] ++ es')%SEQ as es1. destruct H2.
    + apply IHstarts_with.
      apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
      inversion Hlab. by subst.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
      destruct a ; try by left. exfalso ; by apply H2.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
      by right.
  - remember (vs ++ [AI_local n es LI] ++ es')%SEQ as es1. destruct H2.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
    + apply IHstarts_with.
      apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
      inversion Hlab ; by subst.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
      destruct a ; try by left. exfalso ; by apply H2.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.      
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
      by right.
  - remember (vs ++ [AI_basic a] ++ es)%SEQ as es1. destruct H2.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
      destruct a ; try by left. exfalso ; by apply H0.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
      destruct a ; try by left. exfalso ; by apply H0.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
      destruct a0 ; try by left. exfalso ; by apply H2.
      destruct a ; try by left. exfalso ; by apply H0.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
      destruct a ; try by left. exfalso ; by apply H0.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
      by right. destruct a ; try by left. exfalso ; by apply H0.
  - remember (vs ++ [AI_invoke a] ++ es)%SEQ as es1. destruct H2.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
      destruct a0 ; try by left. exfalso ; by apply H1.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.      
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by left.
      by right.
  - remember (vs ++ [AI_trap] ++ es)%SEQ as es1. destruct H2.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by (left + right).
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by (left + right).
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by (left + right).
      destruct a ; try by left. exfalso ; by apply H1.
    + apply first_values in Heqes1 as (_ & Hlab & _) => //= ; try by (left + right).
    + done.
Qed.

      
Lemma starts_with_lfilled e es k lh les :
  starts_with e es ->
  lfilled k lh es les ->
  starts_with e les.
Proof.
  generalize dependent es. generalize dependent lh. generalize dependent les.
  induction k ; intros les lh es Hstart Hfill ; unfold lfilled, lfill in Hfill.
  { destruct lh ; last by false_assumption.
    remember (const_list l) as b eqn:Hl ; destruct b ; last by false_assumption.
    apply b2p in Hfill.
    destruct Hstart ; subst ; repeat rewrite app_assoc ;
      repeat rewrite <- (app_assoc (l ++ vs)) ; constructor ; (try done) ;
      unfold const_list ; rewrite forallb_app ; apply andb_true_iff ; split => //=. } 
  fold lfill in Hfill. destruct lh ; first by false_assumption.
  remember (const_list l) as b eqn:Hl ; destruct b ; last by false_assumption.
  remember (lfill k lh es) as fill ; destruct fill ; last by false_assumption.
  apply b2p in Hfill.
  assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite <- Heqfill.
  subst. apply start_label => //=. by eapply IHk.
Qed.


Lemma lfilled_implies_starts k lh e es :
  (forall n es' LI, e <> AI_label n es' LI) ->
  (forall n es' LI, e <> AI_local n es' LI) ->
  (is_const e -> False) ->
  lfilled k lh [e] es ->
  starts_with e es.
Proof.
  generalize dependent es. generalize dependent lh.
  induction k ; intros lh es Hlabel Hlocal Hconst Hfill ; unfold lfilled, lfill in Hfill ;
    destruct lh ; (try by false_assumption) ; remember (const_list l) as b eqn:Hl ;
    destruct b ; try by false_assumption.
  { apply b2p in Hfill. destruct e ; try by subst ; constructor.
    by exfalso ; eapply Hlabel. by exfalso ; eapply Hlocal. }
  fold lfill in Hfill.
  remember (lfill _ _ _) as fill ; destruct fill ; last by false_assumption.
  apply b2p in Hfill. subst ; constructor => //=. eapply IHk => //=.
  unfold lfilled ; by rewrite <- Heqfill.
Qed.
    

  
Ltac only_one objs Hred2 :=
  let es := fresh "es" in
  let Heqes := fresh "Heqes" in
  left ; remember objs as es eqn:Heqes ;
  apply Logic.eq_sym in Heqes ;
  only_one_reduction Heqes Hred2.

Lemma reduce_det: forall hs f ws es hs1 f1 ws1 es1 hs2 f2 ws2 es2,
  reduce hs f ws es hs1 f1 ws1 es1 ->
  reduce hs f ws es hs2 f2 ws2 es2 ->
  ( (hs1, f1, ws1, es1) = (hs2, f2, ws2, es2) \/
      starts_with (AI_basic BI_grow_memory) es \/
      (exists a, starts_with (AI_invoke a) es) \/
      (starts_with AI_trap es /\ starts_with AI_trap es1 /\ starts_with AI_trap es2 /\
         (hs1, f1, ws1) = (hs2, f2, ws2))).
(*      (exists k lh lh1 lh2, lfilled k lh [AI_trap] es /\
                         lfilled k lh1 [AI_trap] es1 /\ lfilled k lh2 [AI_trap] es2 /\
                         (hs1, f1, ws1) = (hs2, f2, ws2))). *)
(*      (exists k lh, lfilled k lh [AI_basic BI_grow_memory] es) \/
      (exists k lh a, lfilled k lh [AI_invoke a] es) \/
      (exists k lh lh1 lh2, lfilled k lh [AI_trap] es /\
                         lfilled k lh1 [AI_trap] es1 /\ lfilled k lh2 [AI_trap] es2 /\
                         (hs1, f1, ws1) = (hs2, f2, ws2)) \/
      (exists k lh n es0 es0', lfilled k lh [AI_basic BI_grow_memory] es0 /\
                          es = [AI_local n es0' es0])
                          ). *)
Proof.
  intros hs f ws es hs1 f1 ws1 es1 hs2 f2 ws2 es2 Hred1 Hred2.
  (* we perform an (strong) induction on the length_rec of es, i.e. its number of
     instructions, counting recursively under AI_locals and AI_labels *)
  cut (forall n, length_rec es < n ->
            ((hs1, f1, ws1, es1) = (hs2, f2, ws2, es2) \/
               starts_with (AI_basic BI_grow_memory) es \/
               (exists a, starts_with (AI_invoke a) es) \/
                  (starts_with AI_trap es /\ starts_with AI_trap es1 /\ starts_with AI_trap es2 /\
         (hs1, f1, ws1) = (hs2, f2, ws2)))).
     (* (exists k lh lh1 lh2, lfilled k lh [AI_trap] es /\
                         lfilled k lh1 [AI_trap] es1 /\ lfilled k lh2 [AI_trap] es2 /\
                         (hs1, f1, ws1) = (hs2, f2, ws2)))). *)
(*               (exists k lh, lfilled k lh [AI_basic BI_grow_memory] es) \/
               (exists k lh a, lfilled k lh [AI_invoke a] es) \/
               (exists k lh lh1 lh2, lfilled k lh [AI_trap] es /\
                                  lfilled k lh1 [AI_trap] es1 /\
                                  lfilled k lh2 [AI_trap] es2 /\
                                  (hs1, f1, ws1) = (hs2, f2, ws2)) \/
      (exists k lh n es0 es0', lfilled k lh [AI_basic BI_grow_memory] es0 /\
                          es = [AI_local n es0' es0])
      )). *)
  (* the next few lines simply help put the induction into place *)
  { intro Hn ; apply (Hn (S (length_rec es))) ; lia. }
  intro nnn. generalize dependent es. generalize dependent es1.
  generalize dependent es2. generalize dependent ws1. generalize dependent ws2.
  generalize dependent ws.
  induction nnn ; intros ws ws2 ws1 es2 es1 es Hred1 Hred2 Hlen ; first lia.
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
        exists a ; apply start_invoke ; subst ; apply v_to_e_is_const_list.
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
        apply b2p in H4.
        replace [AI_basic (BI_block (Tf t1s t2s) es)] with
          (AI_basic (BI_block (Tf t1s t2s) es) :: []) in H4 => //=.
        apply first_values in H4 as (_ & Habs & _) => //= ; try by (left + right). }
      simple_filled H3 k lh bef aft nn ll ll'.
      destruct aft. { destruct bef. { rewrite app_nil_l app_nil_r in H3.
                                      unfold lfilled, lfill in H4 ; simpl in H4.
                                      apply b2p in H4 ; rewrite app_nil_r in H4 ; subst.
                                      apply IHHred2 => //=. }
        destruct es0 ; first by empty_list_no_reduce Hred2.
                      get_tail a0 es0 ys y Htail.
                      rewrite Htail app_nil_r in H3. rewrite <- Heqes0 in H3.
                      rewrite app_assoc in H3. apply app_inj_tail in H3 as [Hvs Hy].
                      rewrite Htail in Hred2. rewrite <- Hy in Hred2. exfalso.
                      apply (block_not_enough_arguments_no_reduce
                               _ _ _ _ _ _ _ _ _ _ _ Hred2).
                      - rewrite Hvs in H.
                        unfold const_list in H. rewrite forallb_app in H.
                        by apply andb_true_iff in H as [_ Hys].
                      - rewrite Hvs in H0. simpl in H0. subst. rewrite app_length in H0.
                        lia. }
      get_tail a aft aft' a' Htail. rewrite Htail in H3.
      rewrite <- Heqes0 in H3. do 2 rewrite app_assoc in H3.
      apply app_inj_tail in H3 as [Hvs _].
      exfalso ; values_no_reduce Hred2. rewrite Hvs in H.
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
        exists a ; apply start_invoke ; subst ; apply v_to_e_is_const_list.
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
        apply b2p in H4.
        replace [AI_basic (BI_block (Tf t1s t2s) es)] with
          (AI_basic (BI_block (Tf t1s t2s) es) :: []) in H4 => //=.
        apply first_values in H4 as (_ & Habs & _) => //= ; try by (left + right). }
      simple_filled H3 k lh bef aft nn ll ll'.
      destruct aft. { destruct bef. { rewrite app_nil_l app_nil_r in H3.
                                      unfold lfilled, lfill in H4 ; simpl in H4.
                                      apply b2p in H4 ; rewrite app_nil_r in H4 ; subst.
                                      apply IHHred2 => //=. }
        destruct es0 ; first by empty_list_no_reduce Hred2.
                      get_tail a0 es0 ys y Htail.
                      rewrite Htail app_nil_r in H3. rewrite <- Heqes0 in H3.
                      rewrite app_assoc in H3. apply app_inj_tail in H3 as [Hvs Hy].
                      rewrite Htail in Hred2. rewrite <- Hy in Hred2. exfalso.
                      apply (loop_not_enough_arguments_no_reduce
                               _ _ _ _ _ _ _ _ _ _ _ Hred2).
                      - rewrite Hvs in H.
                        unfold const_list in H. rewrite forallb_app in H.
                        by apply andb_true_iff in H as [_ Hys].
                      - rewrite Hvs in H0. simpl in H0. subst. rewrite app_length in H0.
                        lia. }
      get_tail a aft aft' a' Htail. rewrite Htail in H3.
      rewrite <- Heqes0 in H3. do 2 rewrite app_assoc in H3.
      apply app_inj_tail in H3 as [Hvs _].
      exfalso ; values_no_reduce Hred2. rewrite Hvs in H.
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
                      apply b2p in H2. subst.
                      unfold const_list in H.
                      do 3 rewrite forallb_app in H.
                      apply andb_true_iff in H as [_ H].
                      apply andb_true_iff in H as [H _].
                      apply andb_true_iff in H as [_ H].
                      inversion H. }
        fold lfill in H2. destruct lh ; first by false_assumption.
        destruct (const_list l) ; last by false_assumption.
        destruct (lfill _ _ _) ; last by false_assumption.
        apply b2p in H2. subst. unfold const_list in H.
        rewrite forallb_app in H. apply andb_true_iff in H as [_ Habs].
        inversion Habs.
      + destruct bef ; inversion H1.
        exfalso ; values_no_reduce Hred2.
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
                      apply b2p in H1. found_intruse (AI_basic (BI_br 0)) H1 Hxl1.
                      apply in_or_app. right.
                      apply in_or_app. left.
                      apply in_or_app. right => //=. by left. }
        fold lfill in H1. destruct lh ; first by false_assumption.
        destruct (const_list l) ; last by false_assumption.
        destruct (lfill _ _ _) ; last by false_assumption.
        apply b2p in H1. found_intruse (AI_label n1 l0 l2) H1 Hxl1.
      + destruct bef ; inversion H0. rewrite <- H4 in Heqles1.
        unfold lfill in Heqles1. destruct k. { destruct lh0 ; last by false_assumption.
                                               destruct (const_list l2) ;
                                                 inversion Heqles1.
                                               destruct l2.
                                               { destruct es1 ;
                                                   first by empty_list_no_reduce Hred2.
                                                 inversion H6.
                                                 apply Logic.eq_sym,
                                                   app_eq_nil in H8 as [Hes1 _].
                                                 subst.
                                                 exfalso ;
                                                   apply (AI_trap_irreducible
                                                            _ _ _ _ _ _ _ Hred2). }
                                               inversion H6.
                                               apply Logic.eq_sym,
                                                 app_eq_nil in H8 as [_ Hes1].
                                               apply app_eq_nil in Hes1 as [Hes1 _].
                                               subst ; empty_list_no_reduce Hred2. }
        fold lfill in Heqles1. destruct lh0 ; first by false_assumption.
        destruct (const_list l2) ; last by inversion Heqles1.
        destruct (lfill _ _ _) ; inversion Heqles1.
        subst. found_intruse (AI_label n1 l3 l5) H6 Hxl1. 
        apply Logic.eq_sym, app_eq_nil in H3 as [_ Habs] ; inversion Habs.
    - only_one [AI_label n es LI] Hred2.
      + subst. unfold lfilled, lfill in H1. destruct i.
        { destruct lh ; last by false_assumption.
          destruct (const_list l) ; last by false_assumption.
          apply b2p in H1. rewrite H1 in H2.
          unfold const_list in H2. do 3 rewrite forallb_app in H2.
          apply andb_true_iff in H2 as [_ Habs].
          apply andb_true_iff in Habs as [Habs _].
          apply andb_true_iff in Habs as [_ Habs].
          inversion Habs. }
        fold lfill in H1. destruct lh ; first by false_assumption.
        destruct (const_list l) ; last by false_assumption.
        destruct (lfill _ _ _) ; last by false_assumption.
        apply b2p in H1. rewrite H1 in H2. unfold const_list in H2.
        rewrite forallb_app in H2. apply andb_true_iff in H2 as [_ Habs].
        inversion Habs.
      + subst. unfold lfilled, lfill in H1. destruct i.
        { destruct lh ; last by false_assumption.
          destruct (const_list l) ; last by false_assumption.
          apply b2p in H1. found_intruse (AI_basic (BI_br 0)) H1 Hxl1.
          apply in_or_app. right. apply in_or_app. left.
          apply in_or_app. right. by left. } 
        fold lfill in H1. destruct lh ; first by false_assumption.
        destruct (const_list l) ; last by false_assumption.
        destruct (lfill _ _ _) ; last by false_assumption.
        apply b2p in H1. found_intruse (AI_label n l0 l2) H1 Hxl1.
      + subst.
        destruct (lfilled_first_values _ _ _ _ _ _ _ _ _ H4 H1) as (? & ? & ?) => //=.
        by rewrite (H5 (Logic.eq_sym H6)).
      + destruct bef ; last by inversion H3 as [[ Hhd Htl ]];
          apply Logic.eq_sym, app_eq_nil in Htl as [_ Habs] ;
          inversion Habs.
        inversion H3 ; subst ; clear H3. 
        assert (lfilled k lh1 es1 l0) as Hfill ;
          first by unfold lfilled ; rewrite <- Heqles1. exfalso.
        eapply lfilled_br_and_reduce => //=.
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
            apply b2p in H3. rewrite H3 in H.
            unfold const_list in H ; do 3 rewrite forallb_app in H.
            apply andb_true_iff in H as [_ Habs].
            apply andb_true_iff in Habs as [Habs _].
            apply andb_true_iff in Habs as [_ Habs].
            apply andb_true_iff in Habs as [Habs _].
            inversion Habs. }
          fold lfill in H3. destruct lh ; first by false_assumption.
          destruct (const_list l) ; last by false_assumption.
          destruct (lfill _ _ _) ; last by false_assumption.
          apply b2p in H3. rewrite H3 in H. unfold const_list in H.
          rewrite forallb_app in H. apply andb_true_iff in H as [_ Habs].
          simpl in Habs. false_assumption.
        - rewrite Heqes0 in H2. filled_trap H2 Hxl1. }
      + rewrite Heqes0 in H1. simple_filled H1 k lh bef aft nn ll ll'.
        simpl in H1. apply Logic.eq_sym, app_eq_unit in H1 as [[-> Hes] | [_ Hes]].
        apply app_eq_unit in Hes as [[-> _]|[Hes ->]].
        empty_list_no_reduce Hred2.
        unfold lfilled, lfill in H2. simpl in H2. apply b2p in H2.
        rewrite app_nil_r in H2. subst. apply IHHred2 => //=.
        apply app_eq_nil in Hes as [-> _] ; empty_list_no_reduce Hred2.
      + inversion Heqes0 ; subst. exfalso ; values_no_reduce Hred2.
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
            apply b2p in H1. found_intruse (AI_basic (BI_return)) H1 Hxl1.
            apply in_or_app ; right.
            apply in_or_app ; left.
            apply in_or_app ; right. by left. }
          fold lfill in H1. destruct lh ; first by false_assumption.
          destruct (const_list l) ; last by false_assumption.
          destruct (lfill _ _ _) ; last by false_assumption.
          apply b2p in H1. found_intruse (AI_label n l0 l2) H1 Hxl1. }
      + rewrite Heqes0 in H. simple_filled H k lh bef aft nn ll ll'.
        simpl in H. apply Logic.eq_sym, app_eq_unit in H as [[-> Hes] | [_ Hes]].
        apply app_eq_unit in Hes as [[-> _]|[Hes ->]].
        empty_list_no_reduce Hred2.
        unfold lfilled, lfill in H0. simpl in H0. apply b2p in H0.
        rewrite app_nil_r in H0. subst. apply IHHred2 => //=.
        apply app_eq_nil in Hes as [-> _] ; empty_list_no_reduce Hred2.
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
            apply b2p in H1. rewrite H1 in H2.
            unfold const_list in H2 ; do 3 rewrite forallb_app in H2.
            apply andb_true_iff in H2 as [_ Habs].
            apply andb_true_iff in Habs as [Habs _].
            apply andb_true_iff in Habs as [_ Habs].
            apply andb_true_iff in Habs as [Habs _].
            inversion Habs. }
          fold lfill in H1. destruct lh ; first by false_assumption.
          destruct (const_list l) ; last by false_assumption.
          destruct (lfill _ _ _) ; last by false_assumption.
          apply b2p in H1. rewrite H1 in H2. unfold const_list in H2.
          rewrite forallb_app in H2. apply andb_true_iff in H2 as [_ Habs].
          simpl in Habs. false_assumption.
        - inversion Heqes0. rewrite <- H5 in H1.
          destruct i ; unfold lfilled, lfill in H1.
          { destruct lh ; last by false_assumption.
            destruct (const_list l) ; last by false_assumption. apply b2p in H1.
            found_intruse (AI_basic BI_return) H1 Hxl1.
            apply in_or_app ; right. apply in_or_app ; left.
            apply in_or_app ; right. by left. }
          fold lfill in H1. destruct lh ; first by false_assumption.
          destruct (const_list l) ; last by false_assumption.
          destruct (lfill _ _ _) ; last by false_assumption.
          apply b2p in H1. found_intruse (AI_label n1 l0 l2) H1 Hxl1.
        - inversion Heqes0 ; subst.
          destruct (lfilled_first_values _ _ _ _ _ _ _ _ _ H1 H4) as (_ & _ & Hvs) => //=.
          by rewrite (Hvs (Logic.eq_sym H6)).
        - rewrite Heqes0 in H3. filled_trap H3 Hxl1. }
      + rewrite Heqes0 in H2. simple_filled H2 k lh0 bef aft nn ll ll'.
        simpl in H2. apply Logic.eq_sym, app_eq_unit in H2 as [[-> Hes] | [_ Hes]].
        apply app_eq_unit in Hes as [[-> _]|[Hes ->]].
        empty_list_no_reduce Hred2.
        unfold lfilled, lfill in H3. simpl in H3. apply b2p in H3.
        rewrite app_nil_r in H3. subst. apply IHHred2 => //=.
        apply app_eq_nil in Hes as [-> _] ; empty_list_no_reduce Hred2.
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
              destruct (lfilled_trans _ _ _ _ _ _ _ H3 H4) as [lh' Hfill].
              destruct (lfilled_first_values _ _ _ _ _ _ _ _ _ Hfill H1) as (Habs & _ & _);
                try done.
            - simple_filled H1 i lh bef aft nn ll ll'.
              found_intruse (AI_basic BI_return) H1 Hxl1.
              rewrite Hxl1 in H0. inversion H0.
              apply in_or_app ; right ; apply in_or_app ; left ;
                apply in_or_app ; right ; by left.
              rewrite Hxl1 in H0 ; inversion H0.
            - replace [AI_trap] with ([] ++ [AI_trap])%SEQ in H2 => //=.
              destruct (lfilled_first_values _ _ _ _ _ _ _ _ _ H2 H1)
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
      destruct bef. { destruct es ; first by empty_list_no_reduce Hred2.
                      inversion H0. apply Logic.eq_sym, app_eq_unit in H4
                                        as [[ -> _ ]|[ -> -> ]].
                      subst ; exfalso ; values_no_reduce Hred2.
                      apply andb_true_iff ; split => //=.
                      unfold lfilled, lfill in H1 ; simpl in H1.
                      apply b2p in H1. rewrite app_nil_r in H1 ; subst.
                      apply IHHred2 => //=. }
      inversion H0. apply Logic.eq_sym, app_eq_unit in H4 as [[ _ Hes ]|[ _ Hes]].
      apply app_eq_unit in Hes as [[ -> _ ]|[ Hes _]].
      empty_list_no_reduce Hred2.
      apply Logic.eq_sym in Hes ; exfalso ; no_reduce Hes Hred2.
      apply app_eq_nil in Hes as [-> _]. empty_list_no_reduce Hred2.
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
      + filled_trap H0 Hxl1. apply in_app_or in Hxl1 as [Habs | Habs].
        assert (const_list ves) as Hconst ;
          first by rewrite H3 ; apply v_to_e_is_const_list.
        intruse_among_values ves Habs Hconst. destruct Habs => //=.
      + do 3 right. (* in this case, we might not have determinism, but the last 
                       disjunct of the conclusion holds *)
        unfold lfilled, lfill in H0. destruct lh as [bef aft|] ; last by false_assumption.
        remember (const_list bef) as b eqn:Hbef ; destruct b ; last by false_assumption.
        apply b2p in H0. rewrite H0 in H1.
        unfold lfilled, lfill in H1 ; destruct k.
        { destruct lh0 ; last by false_assumption.
          remember (const_list l) as b eqn:Hl ; destruct b ; last by false_assumption.
          apply b2p in H1. 
          destruct (first_non_value_reduce _ _ _ _ _ _ _ _ Hred2)
            as (vs & e & esf & Hvs & He & Hes).
          rewrite Hes in H1. do 3 rewrite app_assoc in H1.
          rewrite <- (app_assoc (l ++ vs)) in H1. rewrite <- app_assoc in H1.
          rewrite <- (app_comm_cons esf) in H1.
          apply first_values in H1 as (Hbefvs & Htrap & Hesf) => //= ; try by right.
          assert (lfilled 0 (LH_base vs esf) [AI_trap] es).
          { unfold lfilled, lfill ; rewrite Hvs. rewrite Hes => //=. by rewrite <- Htrap. }
          destruct (trap_reduce _ _ _ _ _ _ _ _ _ H1 Hred2) as (lh' & Hfill & Hσ).
          apply (lfilled_trans _ _ _ _ _ _ _ Hfill) in H2 as [lh'' Hfill'].
          simpl in Hfill'. subst.
          repeat split => //=. constructor. 
          unfold const_list ; rewrite forallb_app ; apply andb_true_iff ; split => //=.
          rewrite <- app_nil_r ; rewrite <- app_nil_l. by constructor.
          by eapply lfilled_implies_starts. unfold const_list ; rewrite forallb_app.
          apply andb_true_iff ; split => //=.
        }
        fold lfill in H1. destruct lh0 ; first by false_assumption.
        remember (const_list l) as b eqn:Hl ; destruct b ; last by false_assumption.
        destruct (lfill _ _ _) ; last by false_assumption.
        apply b2p in H1. apply first_values in H1 as (_ & Habs & _) ; (try done) ;
                           (try by (left + right)). }
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
    (* The following 3 cases are the r_invoke cases. We do not guarantee determinism in
       these cases, but the third disjunct of the conclusion holds *)
  - right ; right ; left. exists a. apply start_invoke. subst. by apply v_to_e_is_const_list.
  - right ; right ; left. exists a ; apply start_invoke ; subst ; by apply v_to_e_is_const_list.
  - right ; right ; left. exists a ; apply start_invoke ; subst ; by apply v_to_e_is_const_list.
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
    replace [AI_basic (BI_const (VAL_int32 c)); AI_basic BI_grow_memory] with
      ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic BI_grow_memory] ++ []).
    constructor => //=. by rewrite app_nil_r.
  - right ; left.
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
      apply b2p in H.
      (* in this case, Hred1 was [ les -> les1 ] with [ les = bef ++ es ++ aft ],
         [ les1 = bef ++ es1 ++ aft ] and [ es -> es1 ]. 
         Hred2 is hypothesis [ les -> es2 ] with nothing known of [ es2 ]. *)
      unfold lfilled, lfill in H0. rewrite <- Hbef in H0. apply b2p in H0.
      destruct bef.
      { destruct aft. { (*  If bef and aft are both empty, induction hypothesis 
                            IHHred1 can be used. *)
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
        assert (reducible (es ++ ys) (hs, s, f_locs f, f_inst f)) as Hred.
        { exists [], (es' ++ ys), (hs', s', f_locs f', f_inst f'), [].
          repeat split => //=.
          apply (r_label (k:=0) (lh:=LH_base [] ys) (es:=es) (es':=es')) ;
                unfold lfilled, lfill => //=.
          destruct f ; destruct f' => //=. }
        assert (prim_step ((es ++ ys) ++ [y]) (hs, s, f_locs f, f_inst f)
                          [] es2 (hs2, f2, f_locs ws2, f_inst ws2) []) as Hstep.
        { repeat split => //=. rewrite <- H. by destruct f ; destruct ws2. }
        destruct (reduce_append _ _ _ _ _ _ _ Hred Hstep) as [[ Hes2y Htakestep ]|
                                                               (lh & lh' & Htrap &
                                                                  Htrap' & Hσ)].
        { assert (reduce hs s f (es ++ ys) hs' s' f' (es' ++ ys)).
          { apply (r_label (k:=0) (lh:=LH_base [] ys) (es:=es) (es':=es')) ;
              (try done) ; by unfold lfilled, lfill => //=. }
          destruct Htakestep as (H2 & _ & _).
          destruct f ; destruct ws2.
          assert (length_rec (es ++ ys) < nnn).
          { rewrite H in Hlen. rewrite app_length_rec in Hlen.
            assert (length_rec [y] > 0) ; first by apply cons_length_rec.
            replace (es ++ ys)%list with (es ++ ys)%SEQ in Hlen => //=.
            lia. }
          destruct (IHnnn _ _ _ _ _ _ H1 H2 H3) as [Hσ | [Hstart |
                                                     [ [a0 Hstart] |
                                                       (Hstart1 & Hstart2 & Hstart3 & Hσ)
            ]]].
          - left. rewrite H0. inversion Hσ ; subst.
            replace (es' ++ ys)%SEQ with (es' ++ ys)%list in H8 => //=.
            rewrite H8. by rewrite <- Hes2y.
          - right ; left. assert (lfilled 0 (LH_base [] [y]) (es ++ ys) les).
            unfold lfilled, lfill => //=. by subst.
            eapply starts_with_lfilled => //=.
          - right ; right ; left. assert (lfilled 0 (LH_base [] [y]) (es ++ ys) les).
            unfold lfilled, lfill => //= ; by subst. exists a0.
            eapply starts_with_lfilled => //=.
          - do 3 right. repeat split => //=.
            assert (lfilled 0 (LH_base [] [y]) (es ++ ys) les).
            unfold lfilled, lfill => //= ; by subst.
            apply (starts_with_lfilled _ _ _ _ _ Hstart1 H4) => //=.
            assert (lfilled 0 (LH_base [] [y]) (es' ++ ys) les').
            unfold lfilled, lfill => //= ; by subst.
            apply (starts_with_lfilled _ _ _ _ _ Hstart2 H4) => //=.
            assert (lfilled 0 (LH_base [] [y])
                            (take (length es2 - 1) es2) es2).
            unfold lfilled, lfill => //=. by rewrite <- Hes2y.
            apply (starts_with_lfilled _ _ _ _ _ Hstart3 H4) => //=. }
        do 3 right. assert (lfilled 0 (LH_base [] [y]) (es ++ ys) les) as Hfill.
        { unfold lfilled, lfill => //=. by subst. }
        destruct (lfilled_trans _ _ _ _ _ _ _ Htrap' Hfill) as [lh'' ?]. simpl in H1.
        assert (reduce hs s f (es ++ ys) hs' s' f' (es' ++ ys)) as Hles.
        { apply (r_label (k:=0) (lh:=LH_base [] ys) (es:=es) (es':=es')) => //=.
          unfold lfilled, lfill => //=.
          unfold lfilled, lfill => //=. }
        destruct (trap_reduce _ _ _ _ _ _ _ _ _ Htrap' Hles) as (lh''' & ? & Hσ').
        assert (lfilled 0 (LH_base [] [y]) (es' ++ ys) les') as Hfill'.
        { unfold lfilled, lfill => //=. rewrite H0 => //=. }
        destruct (lfilled_trans _ _ _ _ _ _ _ H2 Hfill') as [lh0 ?]. simpl in H3.
        repeat split => //= ; try by eapply lfilled_implies_starts.
        rewrite <- Hσ'. inversion Hσ ; subst.
        destruct f ; destruct ws2 ; simpl in H7 ; simpl in H8 ; by subst. }
      (* if bef is nonempty, then we proceed like before, but on the left side.
         Calling v the first value in bef, we know that [ les = v :: bef' ++ es ++ aft ]
         r_label gives us [ bef' ++ es ++ aft -> bef' ++ es1 ++ aft ] and we still
         have Hred2 telling [ les -> es2 ]. Using reduce_ves, we know that es2 starts
         with v and that [ bef' ++ es ++ aft -> drop 1 es2 ]. We can thus apply
         induction hypothesis on [ bef' ++ es ++ aft ], which is indeed shorter than
         les since we removed v *)
      unfold const_list in Hbef.
      simpl in Hbef. apply Logic.eq_sym, andb_true_iff in Hbef as [Ha Hbef].
      assert (reduce hs s f (bef ++ es ++ aft) hs' s' f' (bef ++ es' ++ aft)) as Hles.
      { apply (r_label (k:=0) (lh:=LH_base bef aft) (es:=es) (es':=es')) => //=.
        unfold lfilled, lfill, const_list ; by rewrite Hbef. 
        unfold lfilled, lfill, const_list ; by rewrite Hbef. }
      assert (reducible (bef ++ es ++ aft) (hs, s, f.(f_locs), f.(f_inst))) as Hred.
      { exists [], (bef ++ es' ++ aft), (hs', s', f_locs f', f_inst f'), [].
        repeat split => //=. destruct f ; destruct f' => //=. } 
      destruct a ; try by inversion Ha.
      destruct b ; try by inversion Ha.
      assert (prim_step ([AI_basic (BI_const v)] ++ bef ++ es ++ aft)
                        (hs, s, f_locs f, f_inst f) [] es2
                        (hs2, f2, f_locs ws2, f_inst ws2) []) as Hstep.
      { repeat split => //=. rewrite <- app_comm_cons in H. rewrite <- H.
        by destruct f ; destruct ws2. } 
      destruct (reduce_ves _ _ _ _ _ _ _ Hred Hstep) as [[ Hves2 Hdropstep] |
                                                          ( lh & lh' & Htrap & Htrap' &
                                                              Hσ )].
      { assert (reduce hs s f (bef ++ es ++ aft) hs' s' f' (bef ++ es' ++ aft)).
        { apply (r_label (k:=0) (lh:=LH_base bef aft) (es:=es) (es':=es'))
          ; (try done) ; by unfold lfilled, lfill, const_list ; rewrite Hbef. }
        destruct Hdropstep as (H2 & _ & _).
        replace (bef ++ es ++ aft)%list with (bef ++ es ++ aft)%SEQ in H2 => //=.
        destruct f ; simpl in H2. destruct ws2 ; simpl in H2.
        assert (length_rec (bef ++ es ++ aft) < nnn).
        { rewrite H in Hlen. rewrite <- app_comm_cons in Hlen.
          replace (AI_basic (BI_const v) :: (bef ++ es ++ aft)) with
            ([AI_basic (BI_const v)] ++ (bef ++ es ++ aft)) in Hlen => //=.
          rewrite app_length_rec in Hlen. simpl in Hlen. 
          by apply lt_S_n. }
        destruct (IHnnn _ _ _ _ _ _ H1 H2 H3) as [Hσ | [Hstart |
                                                   [ [a Hstart] |
                                                     (Hstart1 & Hstart2 & Hstart3 & Hσ)
          ]]].
        - left. rewrite H0. rewrite <- app_comm_cons.
          inversion Hσ ; subst.
          replace (bef ++ es' ++ aft)%SEQ with (bef ++ es' ++ aft)%list in H8 => //=.
          rewrite H8. by rewrite Hves2.
        - right ; left. assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                                        (bef ++ es ++ aft) les).
          unfold lfilled, lfill => //=. by subst ; rewrite app_nil_r.
          eapply starts_with_lfilled => //=.
        - right ; right ; left. assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                                                   (bef ++ es ++ aft) les).
          unfold lfilled, lfill => //=. by subst ; rewrite app_nil_r.
          exists a ; eapply starts_with_lfilled => //=.
        - repeat right. repeat split => //=.
          assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                                                   (bef ++ es ++ aft) les).
          unfold lfilled, lfill => //=. by subst ; rewrite app_nil_r.
          by apply (starts_with_lfilled _ _ _ _ _ Hstart1 H4).
          assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                                                   (bef ++ es' ++ aft) les').
          unfold lfilled, lfill => //=. by subst ; rewrite app_nil_r.
          by apply (starts_with_lfilled _ _ _ _ _ Hstart2 H4).
          destruct es2 ; simpl in Hstart3 ; first by inversion Hves2.
          unfold drop in Hstart3. inversion Hves2 ; subst.
          assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                          es2 (AI_basic (BI_const v) :: es2)).
          unfold lfilled, lfill => //= ; by rewrite app_nil_r.
          by apply (starts_with_lfilled _ _ _ _ _ Hstart3 H). } 
      do 3 right.
      assert (lfilled 0 (LH_base [AI_basic (BI_const v)] []) (bef ++ es ++ aft) les)
        as Hfill.
      { unfold lfilled, lfill => //=. rewrite H.
        by rewrite app_comm_cons app_nil_r. } 
      destruct (lfilled_trans _ _ _ _ _ _ _ Htrap' Hfill) as [lh'' ?]. simpl in H1.
      destruct (trap_reduce _ _ _ _ _ _ _ _ _ Htrap' Hles) as (lh''' & ? & Hσ').
      assert (lfilled 0 (LH_base [AI_basic (BI_const v)] []) (bef ++ es' ++ aft) les')
        as Hfill'.
      { unfold lfilled, lfill => //=. rewrite H0.
        by rewrite app_comm_cons app_nil_r. }
      destruct (lfilled_trans _ _ _ _ _ _ _ H2 Hfill') as [lh0 ?]. simpl in H3.
      repeat split => //= ; try by eapply lfilled_implies_starts.
      rewrite <- Hσ'. inversion Hσ ; subst.
      destruct f ; destruct ws2 ; simpl in H7 ; simpl in H8 ; by subst. }
    (* in this case, Hred1 was [ les -> les1 ] with 
       [ les = bef ++ AI_label n es0 l :: aft ], [ les1 = bef ++ AI_label n es0 l1 :: aft ],
       [ lfilled k lh es l ], [ lfilled k lh es1 l1 ] and [ es -> es1 ]. We still have
       Hred2 being [ les -> es2 ] with nothing known of es2. *)
    fold lfill in H. destruct lh as [|bef n es0 lh aft] ; first by false_assumption.
    remember (const_list bef) as b eqn:Hbef ; destruct b ; last by false_assumption.
    remember (lfill _ _ _) as fill ; destruct fill ; last by false_assumption.
    apply b2p in H.
    { unfold lfilled, lfill in H0 ; fold lfill in H0. rewrite <- Hbef in H0.
      remember (lfill _ _ es') as fill ; destruct fill ; last by false_assumption.
      apply b2p in H0. destruct bef.
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
                exfalso ; values_no_reduce Hred1.
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
                empty_list_no_reduce Hred1.
                exfalso ; by eapply test_no_reduce_trap.
                apply app_eq_nil in Hes as [-> _] ; empty_list_no_reduce Hred1. } 
              fold lfill in Heqfill. destruct lh ; first by inversion Heqfill.
              destruct (const_list l) ; last by inversion Heqfill.
              destruct (lfill _ _ _) ; inversion Heqfill.
              found_intruse (AI_label n0 l1 l3) H1 Hxl1.
            - inversion H ; subst.
              assert (lfilled k lh es l) as Hfill ;
                first by unfold lfilled ; rewrite <- Heqfill. exfalso.
              eapply lfilled_br_and_reduce => //=.
            - rewrite H in H2. filled_trap H2 Hxl1. }
          rewrite H in H1.
          destruct k0 ; unfold lfilled, lfill in H1.
          { destruct lh0 ; last by false_assumption.
            destruct (const_list l1) ; last by false_assumption.
            apply b2p in H1. simpl in H1.
            apply Logic.eq_sym, app_eq_unit in H1 as [[ ->  Hes1 ] | [ _ Hes1]].
            apply app_eq_unit in Hes1 as [[ -> _ ] | [ -> -> ]].
            empty_list_no_reduce Hred2.
            unfold lfilled, lfill in H2 ; simpl in H2 ; apply b2p in H2.
            rewrite app_nil_r in H2. subst. apply IHHred2 => //=.
            apply app_eq_nil in Hes1 as [-> _ ] ; empty_list_no_reduce Hred2. }
          fold lfill in H1. clear IHHred1 IHHred2.
          destruct lh0 ; first by false_assumption.
          destruct (const_list l1) ; last by false_assumption.
          remember (lfill k0 _ _) as fill ; destruct fill ; last by false_assumption.
          apply b2p in H1.
          destruct l1 ; last by inversion H1 ; found_intruse (AI_label n0 l2 l4) H5 Hxl1.
          inversion H1 ; subst.
          assert (reduce hs s f l4 hs' s' f' l0).
          { eapply r_label. exact Hred1. unfold lfilled. by rewrite <- Heqfill.
            unfold lfilled ; by rewrite <- Heqfill0. }
          unfold lfilled, lfill in H2 ; fold lfill in H2. simpl in H2.
          remember (lfill k0 lh0 es'0) as fill ; destruct fill ; last by false_assumption.
          assert (reduce hs s f l4 hs'0 s'0 f'0 l).
          { eapply r_label. exact Hred2. unfold lfilled ; by rewrite <- Heqfill1.
            unfold lfilled. by rewrite <- Heqfill2. }
          assert (length_rec l4 < nnn).
          { simpl in Hlen. unfold length_rec in Hlen. simpl in Hlen. unfold length_rec.
            lia. }
          assert (lfilled 1 (LH_rec [] n0 l2 (LH_base [] []) []) l4
                                          [AI_label n0 l2 l4]).
          unfold lfilled, lfill => //=. by rewrite app_nil_r.
          destruct (IHnnn _ _ _ _ _ _ H H0 H3)
            as [ Hσ | [ Hstart | [ [a Hstart] | (Hstart1 & Hstart2 & Hstart3 & Hσ) ]]].
          - left. apply b2p in H2. inversion Hσ ; by subst.
          - right ; left.
            eapply starts_with_lfilled => //=.
          - right ; right ; left.
            exists a ; eapply starts_with_lfilled => //=.
          - do 3 right. repeat split => //=.
            replace [AI_label n0 l2 l4] with ([] ++ [AI_label n0 l2 l4] ++ [])%SEQ.
            constructor => //=.
            assert (lfilled 1 (LH_rec [] n0 l2 (LH_base [] []) []) l0
                            [AI_label n0 l2 l0]).
            unfold lfilled, lfill => //= ; by rewrite app_nil_r.
            apply (starts_with_lfilled _ _ _ _ _ Hstart2 H5) => //=.                  
            apply b2p in H2.
            assert (lfilled 1 (LH_rec [] n0 l2 (LH_base [] []) []) l les'0).
            unfold lfilled, lfill => //= ; by subst ; rewrite app_nil_r.
            apply (starts_with_lfilled _ _ _ _ _ Hstart3 H5) => //=. }
        (* in the cases where aft is nonempty or bef is nonempty, we proceed exactly
           like in the corresponding cases when k was 0 *)
          get_tail a aft ys y Htail.
          rewrite Htail in H. rewrite Htail in H0. simpl in H. simpl in H0.
          rewrite app_comm_cons in H. rewrite app_comm_cons in H0.
          assert (reducible (AI_label n es0 l :: ys) (hs, s, f_locs f, f_inst f)) as Hred.
          { exists [], (AI_label n es0 l0 :: ys), (hs', s', f_locs f', f_inst f'), [].
            repeat split => //=.
            apply (r_label (k:=S k) (lh:=LH_rec [] n es0 lh ys) (es:=es) (es':=es')) ;
              unfold lfilled, lfill ; fold lfill => //=.
            destruct f ; destruct f' => //=.
            rewrite <- Heqfill => //=.
            rewrite <- Heqfill0 => //=.
          }
          assert (prim_step ((AI_label n es0 l :: ys) ++ [y]) (hs, s, f_locs f, f_inst f)
                            [] es2 (hs2, f2, f_locs ws2, f_inst ws2) []) as Hstep.
        { repeat split => //=. simpl in H ; rewrite <- H. by destruct f ; destruct ws2. }
        destruct (reduce_append _ _ _ _ _ _ _ Hred Hstep) as [[ Hes2y Htakestep ]|
                                                               (lh0 & lh' & Htrap &
                                                                  Htrap' & Hσ)].
        { assert (reduce hs s f (AI_label n es0 l :: ys) hs' s' f'
                         (AI_label n es0 l0 :: ys)).
          { apply (r_label (k:=S k) (lh:=LH_rec [] n es0 lh ys) (es:=es) (es':=es')) ;
              (try done) ; unfold lfilled, lfill ; fold lfill => //=.
          rewrite <- Heqfill => //=. rewrite <- Heqfill0 => //=. }
          destruct Htakestep as (H2 & _ & _).
          destruct f ; destruct ws2.
          assert (length_rec (AI_label n es0 l :: ys) < nnn).
          { rewrite H in Hlen. rewrite app_length_rec in Hlen.
            assert (length_rec [y] > 0) ; first by apply cons_length_rec.
            replace (es ++ ys)%list with (es ++ ys)%SEQ in Hlen => //=.
            lia. }
          destruct (IHnnn _ _ _ _ _ _ H1 H2 H3) as [Hσ | [ Hstart |
                                                     [ [a0 Hstart] |
                                                       (Hstart1 & Hstart2 & Hstart3 & Hσ)
            ]]].
          - left. rewrite H0. inversion Hσ ; subst.
            replace (AI_label n es0 l0 :: ys)%SEQ with
              (AI_label n es0 l0 :: ys)%list in H8 => //=.
            rewrite app_comm_cons H8. by rewrite <- Hes2y.
          - right ; left. assert (lfilled 0 (LH_base [] [y]) (AI_label n es0 l ::  ys) les).
            unfold lfilled, lfill => //=. by subst.
            eapply starts_with_lfilled => //=.
          - right ; right ; left.
            assert (lfilled 0 (LH_base [] [y]) (AI_label n es0 l :: ys) les).
            unfold lfilled, lfill => //= ; by subst.
            exists a0 ; eapply starts_with_lfilled => //=.
          - repeat right. repeat split => //=.
            assert (lfilled 0 (LH_base [] [y]) (AI_label n es0 l :: ys) les).
            unfold lfilled, lfill => //= ; by subst.
            by apply (starts_with_lfilled _ _ _ _ _ Hstart1 H4).
            assert (lfilled 0 (LH_base [] [y]) (AI_label n es0 l0 :: ys) les').
            unfold lfilled, lfill => //= ; by subst.
            by apply (starts_with_lfilled _ _ _ _ _ Hstart2 H4).
            assert (lfilled 0 (LH_base [] [y])
                            (take (length es2 - 1) es2) es2).
            unfold lfilled, lfill => //=. by rewrite <- Hes2y.
            by apply (starts_with_lfilled _ _ _ _ _ Hstart3 H4). }
        repeat right.
        assert (lfilled 0 (LH_base [] [y]) (AI_label n es0 l :: ys) les) as Hfill.
        { unfold lfilled, lfill => //=. by subst. }
        destruct (lfilled_trans _ _ _ _ _ _ _ Htrap' Hfill) as [lh'' ?]. simpl in H1.
        assert (reduce hs s f (AI_label n es0 l :: ys) hs' s' f'
                       (AI_label n es0 l0 :: ys)) as Hles.
        { apply (r_label (k:=S k) (lh:=LH_rec [] n es0 lh ys) (es:=es) (es':=es')) => //=.
          unfold lfilled, lfill ; fold lfill => //=. rewrite <- Heqfill => //=.
          unfold lfilled, lfill ; fold lfill => //=. rewrite <- Heqfill0 => //=. }
        destruct (trap_reduce _ _ _ _ _ _ _ _ _ Htrap' Hles) as (lh''' & ? & Hσ').
        assert (lfilled 0 (LH_base [] [y]) (AI_label n es0 l0 :: ys) les') as Hfill'.
        { unfold lfilled, lfill => //=. rewrite H0 => //=. }
        destruct (lfilled_trans _ _ _ _ _ _ _ H2 Hfill') as [lh0' ?]. simpl in H3.
        repeat split => //= ; try by eapply lfilled_implies_starts.
        rewrite <- Hσ'. inversion Hσ ; subst.
        destruct f ; destruct ws2 ; simpl in H7 ; simpl in H8 ; by subst. } 
      unfold const_list in Hbef.
      simpl in Hbef. apply Logic.eq_sym, andb_true_iff in Hbef as [Ha Hbef].
      assert (reduce hs s f (bef ++ AI_label n es0 l :: aft) hs' s' f'
                     (bef ++ AI_label n es0 l0 :: aft)) as Hles.
      { apply (r_label (k:=S k) (lh:=LH_rec bef n es0 lh aft) (es:=es) (es':=es')) => //=.
        unfold lfilled, lfill ; fold lfill. unfold const_list ; rewrite Hbef.
        rewrite <- Heqfill => //=.
        unfold lfilled, lfill ; fold lfill ; unfold  const_list ; rewrite Hbef.
        rewrite <- Heqfill0 => //=. }
      assert (reducible (bef ++ AI_label n es0 l :: aft)
                        (hs, s, f.(f_locs), f.(f_inst))) as Hred.
      { exists [], (bef ++ AI_label n es0 l0 :: aft), (hs', s', f_locs f', f_inst f'), [].
        repeat split => //=. destruct f ; destruct f' => //=. } 
      destruct a ; try by inversion Ha.
      destruct b ; try by inversion Ha.
      assert (prim_step ([AI_basic (BI_const v)] ++ bef ++ AI_label n es0 l :: aft)
                        (hs, s, f_locs f, f_inst f) [] es2
                        (hs2, f2, f_locs ws2, f_inst ws2) []) as Hstep.
      { repeat split => //=. rewrite <- app_comm_cons in H. rewrite <- H.
        by destruct f ; destruct ws2. } 
      destruct (reduce_ves _ _ _ _ _ _ _ Hred Hstep) as [[ Hves2 Hdropstep] |
                                                          ( lh0 & lh' & Htrap & Htrap' &
                                                              Hσ )].
      { destruct Hdropstep as (H2 & _ & _).
        replace (bef ++ AI_label n es0 l :: aft)%list with
          (bef ++ AI_label n es0 l :: aft)%SEQ in H2 => //=.
        destruct f ; simpl in H2. destruct ws2 ; simpl in H2.
        assert (length_rec (bef ++ AI_label n es0 l :: aft) < nnn).
        { rewrite H in Hlen. rewrite <- app_comm_cons in Hlen.
          replace (AI_basic (BI_const v) :: (bef ++ AI_label n es0 l :: aft)) with
            ([AI_basic (BI_const v)] ++ (bef ++ AI_label n es0 l :: aft)) in Hlen => //=.
          rewrite app_length_rec in Hlen. simpl in Hlen. 
          by apply lt_S_n. }          
        destruct (IHnnn _ _ _ _ _ _ Hles H2 H1) as [Hσ | [ Hstart |
                                                   [ [ a Hstart ] |
                                                     (Hstart1 & Hstart2 & Hstart3 & Hσ)
          ]]].
        - left. rewrite H0. rewrite <- app_comm_cons.
          inversion Hσ ; subst.
          replace (bef ++ AI_label n es0 l0 :: aft)%SEQ with
            (bef ++ AI_label n es0 l0 :: aft)%list in H7 => //=.
          rewrite H7. by rewrite Hves2.
        - right ; left. assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                                                   (bef ++ AI_label n es0 l :: aft) les).
          unfold lfilled, lfill => //=. by subst ; rewrite app_nil_r.
          eapply starts_with_lfilled => //=.
        - right ; right ; left. assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                                                   (bef ++ AI_label n es0 l :: aft) les).
          unfold lfilled, lfill => //=. by subst ; rewrite app_nil_r.
          exists a ; eapply starts_with_lfilled => //=.
        - repeat right. repeat split => //=.
          assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                                                   (bef ++ AI_label n es0 l :: aft) les).
          unfold lfilled, lfill => //=. by subst ; rewrite app_nil_r.
          by apply (starts_with_lfilled _ _ _ _ _ Hstart1 H3).
          assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                                                   (bef ++ AI_label n es0 l0 :: aft) les').
          unfold lfilled, lfill => //=. by subst ; rewrite app_nil_r.
          by apply (starts_with_lfilled _ _ _ _ _ Hstart2 H3).
          destruct es2 ; simpl in Hstart3 ; first by inversion Hves2.
          unfold drop in Hstart3. inversion Hves2 ; subst.
          assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                          es2 (AI_basic (BI_const v) :: es2)).
          unfold lfilled, lfill => //= ; by rewrite app_nil_r.
          by apply (starts_with_lfilled _ _ _ _ _ Hstart3 H). } 
      repeat right.
      assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                      (bef ++ AI_label n es0 l :: aft) les) as Hfill.
      { unfold lfilled, lfill => //=. rewrite H.
        by rewrite app_comm_cons app_nil_r. }
      destruct (lfilled_trans _ _ _ _ _ _ _ Htrap' Hfill) as [lh'' ?]. simpl in H1.
      destruct (trap_reduce _ _ _ _ _ _ _ _ _ Htrap' Hles) as (lh''' & ? & Hσ').
      assert (lfilled 0 (LH_base [AI_basic (BI_const v)] [])
                      (bef ++ AI_label n es0 l0 :: aft) les') as Hfill'.
      { unfold lfilled, lfill => //=. rewrite H0.
        by rewrite app_comm_cons app_nil_r. }
      destruct (lfilled_trans _ _ _ _ _ _ _ H2 Hfill') as [lh0' ?]. simpl in H3.
      repeat split => //= ; try by eapply lfilled_implies_starts.
      rewrite <- Hσ'. inversion Hσ ; subst.
      destruct f ; destruct ws2 ; simpl in H7 ; simpl in H8 ; by subst. }
  - (* final case : the r_local case. We perform the case analysis on Hred2 by hand *)
    clear IHHred1. remember [AI_local n f es] as es0.
    rewrite <- (app_nil_l [AI_local n f es]) in Heqes0.
    induction Hred2 ; (try by inversion Heqes0) ;
      try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
    { destruct H ; (try by inversion Heqes0) ;
        try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
      - inversion Heqes0 ; subst. exfalso ; values_no_reduce Hred1.
      - inversion Heqes0 ; subst.
        exfalso ; by apply (test_no_reduce_trap _ _ _ _ _ _ _ Hred1).
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
              destruct (lfilled_trans _ _ _ _ _ _ _ H3 H4) as [lh' Hfill].
              destruct (lfilled_first_values _ _ _ _ _ _ _ _ _ Hfill H1) as (Habs & _ & _);
                try done.
            - simple_filled H1 i lh bef aft nn ll ll'.
              found_intruse (AI_basic BI_return) H1 Hxl1.
              rewrite Hxl1 in H0. inversion H0.
              apply in_or_app ; right ; apply in_or_app ; left ;
                apply in_or_app ; right ; by left.
              rewrite Hxl1 in H0 ; inversion H0.
            - replace [AI_trap] with ([] ++ [AI_trap])%SEQ in H2 => //=.
              destruct (lfilled_first_values _ _ _ _ _ _ _ _ _ H2 H1)
                as (Habs & _ & _) => //=. } 
          * exfalso. eapply lfilled_return_and_reduce => //=. } 
      - rewrite Heqes0 in H0. filled_trap H0 Hxl1. }
    + rewrite Heqes0 in H. simple_filled H k lh bef aft nn ll ll'.
      simpl in H. apply Logic.eq_sym, app_eq_unit in H as [[ -> Hes] | [_ Hes]].
      apply app_eq_unit in Hes as [[ -> _ ] | [-> ->]].
      empty_list_no_reduce Hred2.
      unfold lfilled, lfill in H0 ; simpl in H0 ; rewrite app_nil_r in H0 ;
        apply b2p in H0 ; subst.
      by apply IHHred2.
      apply app_eq_nil in Hes as [-> _ ] ; empty_list_no_reduce Hred2.
    + (* In case Hred2 was also proved using r_local, we make use of the induction
         hypothesis IHnnn *)
      inversion Heqes0 ; subst. clear IHHred2.
      assert (length_rec es < nnn).
      unfold length_rec in Hlen ; simpl in Hlen.
      unfold length_rec ; lia.
      destruct (IHnnn _ _ _ _ _ _ Hred1 Hred2 H)
        as [Hσ | [ Hstart | [ [a Hstart] | (Hstart1 & Hstart2 & Hstart3 & Hσ) ]]].
      * left. by inversion Hσ ; subst.
      * right ; left. rewrite <- app_nil_r. rewrite <- app_nil_l. constructor => //=.
      * right ; right ; left. exists a. rewrite <- app_nil_r ; rewrite <- app_nil_l.
        constructor => //=.
      * repeat right. repeat split => //=.
        rewrite <- app_nil_r. rewrite <- app_nil_l. constructor => //=.
        rewrite <- app_nil_r. rewrite <- app_nil_l. constructor => //=.
        rewrite <- app_nil_r. rewrite <- app_nil_l. constructor => //=.
        by inversion Hσ ; subst.
Qed.      

 
            
            
                                   
                                       
      
      


End Host.
