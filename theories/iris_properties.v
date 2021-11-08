From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre lifting.
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
                       [AI_trap] es' /\ lfilled 0 lh [AI_trap] es1). 
(*                  σ' = σ /\
              prim_step es1 σ obs [AI_trap] σ efs). *)
Proof.
  intros Hes1 Hstep. 
  cut (forall n, length es' < n ->
            (exists es'', es' = es'' ++ es2 /\ prim_step es1 σ obs es'' σ' efs) \/
              (exists n m lh, n <= length es1 /\ m <= length (es1 ++ es2) /\
                        lfilled 0 (LH_base (take n es1)
                                         (drop m (es1 ++ es2)))
                                [AI_trap] es' /\ lfilled 0 lh [AI_trap] es1)). (* σ' = σ /\
                        exists lh, lfilled 0 lh [AI_trap] es1)). *)
  { intro Hn ; assert (length es' < S (length es')) as Hlen ; first lia.
    destruct (Hn (S (length es')) Hlen) as [ Hl | (n0 & m & lh & _ & _ & ? & ?) ].
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
  - apply Logic.eq_sym, app_eq_nil in H4 as [Hn1 Hn2] ; rewrite Hn1 ; rewrite Hn2.
    left ; exists []. repeat split => //=. subst.
    by apply (r_set_local s _ H H0).
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
        as [(es'' & Heq & Hred) | (n & m & lh & Hn & Hm & Hfill & Hcontext)].
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
        [ (es' & H1 & H2) | (n & m & lh & H1 & H2) ].
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
      destruct (trap_reduce _ _ _ (a :: ces) _ _ _ ces' _ Htrap Hred) as (lh' & Hfill' & Hσ).
      unfold lfilled, lfill in Hfill'. destruct lh' ; last by false_assumption.
      remember (const_list l1) as b eqn:Hl1 ; destruct b ; last by false_assumption.
      apply b2p in Hfill'.
      exists (LH_base l1 (l2 ++ a0 :: aft)), (LH_base bef0 (aft0 ++ a0 :: aft)).
      split ; unfold lfilled, lfill => //=. rewrite <- Hl1. rewrite Hles'.
      rewrite Hfill'. simpl. by rewrite <- app_assoc.
      rewrite <- Hbef0. rewrite H2. rewrite <- app_assoc. split => //.
      by inversion Hσ; subst; inversion H5.
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


End Host.
