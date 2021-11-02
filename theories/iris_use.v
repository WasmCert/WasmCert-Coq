(** Example of Iris usage **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre lifting.
From iris.base_logic Require Export gen_heap proph_map.
Require Export iris iris_locations iris_monotone.
Require Export datatypes host operations opsem properties.
Require Import Coq.Program.Equality.

Set Default Proof Using "Type". (* what is this? *)

Close Scope byte_scope.

Section Host.

Variable host_function : eqType.

Let host := host.host host_function.
Let function_closure := function_closure host_function.
Let store_record := store_record host_function.
(* Let expr := expr host_function. *)

Variable host_instance : host.

Let reduce := @reduce host_function host_instance.

Let wasm_mixin : LanguageMixin _ _ _ := wasm_mixin host_instance.

Canonical Structure wasm_lang := Language wasm_mixin.

Let expr := iris.expr.
Let val := iris.val.
Let to_val := iris.to_val.

Let reducible := @reducible wasm_lang.

Class wfuncG Σ := WFuncG {
  func_invG : invG Σ;
  func_gen_hsG :> gen_heapG N function_closure Σ;
}.

Class wtabG Σ := WTabG {
  tab_invG : invG Σ;
  tab_gen_hsG :> gen_heapG (N*N) funcelem Σ;
}.

Class wmemG Σ := WMemG {
  mem_invG : invG Σ;
  mem_gen_hsG :> gen_heapG (N*N) byte Σ;
}.

Class wmemsizeG Σ := WMemsizeG {
  memsize_invG : invG Σ;
  memsize_gen_hsG :> gen_heapG N N Σ;
}.

Class wglobG Σ := WGlobG {
  glob_invG : invG Σ;
  glob_gen_hsG :> gen_heapG N global Σ;
}.

Class wlocsG Σ := WLocsG {
  locs_invG : invG Σ;
  locs_gen_hsG :> gen_heapG N value Σ;
}.

Class winstG Σ := WInstG {
  inst_invG: invG Σ;
  inst_gen_hsG :> gen_heapG unit instance Σ;
}.

Notation "n ↦[wf]{ q } v" := (mapsto (L:=N) (V:=function_closure) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wf]{ q } v") : bi_scope.
Notation "n ↦[wf] v" := (mapsto (L:=N) (V:=function_closure) n (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wf] v") : bi_scope.
Notation "n ↦[wt]{ q } [ i ] v" := (mapsto (L:=N*N) (V:=funcelem) (n, i) q v%V)
                           (at level 20, q at level 5, format "n ↦[wt]{ q } [ i ] v") : bi_scope.
Notation "n ↦[wt][ i ] v" := (mapsto (L:=N*N) (V:=funcelem) (n, i) (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wt][ i ] v") : bi_scope.
Notation "n ↦[wm]{ q } [ i ] v" := (mapsto (L:=N*N) (V:=byte) (n, i) q v%V)
                           (at level 20, q at level 5, format "n ↦[wm]{ q } [ i ] v") : bi_scope.
Notation "n ↦[wm][ i ] v" := (mapsto (L:=N*N) (V:=byte) (n, i) (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wm][ i ] v") : bi_scope.
Notation "n ↦[wmlength] v" := (mapsto (L:=N) (V:=N) n (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wmlength] v") : bi_scope.
Notation "n ↦[wg]{ q } v" := (mapsto (L:=N) (V:=global) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wg]{ q } v") : bi_scope.
Notation "n ↦[wg] v" := (mapsto (L:=N) (V:=global) n (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wg] v") : bi_scope.

Notation "n ↦[wl]{ q } v" := (mapsto (L:=N) (V:=value) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wl]{ q } v") : bi_scope.
Notation "n ↦[wl] v" := (mapsto (L:=N) (V:=value) n (DfracOwn 1) v%V)
                           (at level 20, format "n ↦[wl] v") : bi_scope.
Notation " ↦[wi] v" := (mapsto (L:=unit) (V:=instance) tt (DfracOwn 1) v%V)
                         (at level 20, format " ↦[wi] v") : bi_scope.
(* We also somehow need a predicate to indicate the size of a memory. But
   how should it be done? *)

Definition proph_id := positive. (* ??? *)


(*
(* Memory size predicate using Monotone? *)
Definition R : relation N := fun x y => (x<y)%N.

Class MemsizeG Σ := memsizeG {
    MemsizeIG_monauth :> inG Σ (authUR (monotoneUR R));
}.

Definition MemsizeΣ := #[GFunctor (authUR (monotoneUR R))].

Instance subG_MonRefIGΣ {Σ} : subG MemsizeΣ Σ → MemsizeG Σ.
Proof. solve_inG. Qed.

Context `{!MemsizeG Σ}.

Definition mem_size_exact (γ: gname) sz := (own γ (● (principal R sz)))%I.

(* This should not be necessary *)
Definition mem_size_at_least (γ: gname) sz := (own γ (◯ (principal R sz)))%I.

(* Have to convert to 1-indexed, since Iris ghost names only allow positive. *)
Definition gen_mem_size (l: list memory) :=
  ([∗ list] i ↦ m ∈ l, mem_size_exact (Pos.of_succ_nat i) (mem_size m))%I.


Print gen_heap_interp.
*)

Instance heapG_irisG `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, wmemsizeG Σ, !wglobG Σ, !wlocsG Σ, !winstG Σ} : irisG wasm_lang Σ := {
  iris_invG := func_invG; (* Check: do we actually need this? *)
  state_interp σ _ κs _ :=
    let: (_, s, locs, inst) := σ in
     ((gen_heap_interp (gmap_of_list s.(s_funcs))) ∗
      (gen_heap_interp (gmap_of_table s.(s_tables))) ∗
      (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
      (gen_heap_interp (gmap_of_list s.(s_globals)) ∗
      (gen_heap_interp (gmap_of_list locs)) ∗
      (gen_heap_interp (<[tt := inst]> ∅)) ∗
      (gen_heap_interp (gmap_of_list (fmap mem_length s.(s_mems))))
      )
    )%I;
    (* (gen_heap_ctx σ.(heap) ∗ proph_map_ctx κs σ.(used_proph_id))%I *)
    num_laters_per_step _ := 0;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := fupd_intro _ _
}.

(* TODO: this tactic is currently useless *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : iris.prim_step ?e _ _ _ _ _ |- _ =>
     inversion H; subst; clear H
  | H : _ = [] /\ _ = [] |- _ => (* this is to resolve the resulting equalities from head_step. *) 
     destruct H
         end.

Let empty_instance := Build_instance [] [] [] [] [].

Let prim_step := @iris.prim_step host_function host_instance.

Definition xx i := (VAL_int32 (Wasm_int.int_of_Z i32m i)).
Definition xb b := (VAL_int32 (wasm_bool b)).


(* The following atomicity definition will be useful for opening invariants *)
Definition is_atomic (e : expr) : Prop :=
  match e with
  | [::AI_basic (BI_const (VAL_int32 _)); AI_basic (BI_load _ _ _ _)] => True
  | [::AI_basic (BI_const (VAL_int32 _)); AI_basic (BI_const _); AI_basic (BI_store _ _ _ _)] => True
  | [::AI_trap] => True
  | _ => False
  end.

Ltac destruct_match_goal :=
  let x := fresh "x" in 
  match goal with
                | _ : _ |- (match ?x with | _ => _ end -> _) => case: x => x //=
  end.
Lemma is_atomic_eq (e : expr) :
  is_atomic e ->
  (∃ k x1 x2 x3 x4, e = [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load x1 x2 x3 x4)]) ∨
  (∃ k v x1 x2 x3 x4, e = [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store x1 x2 x3 x4)]) ∨
  (e = [::AI_trap]).
Proof.
  intros He.
  do 2 (destruct e;try done).
  { destruct a;try done.
    destruct b;try done; destruct v;try done.
    right. by right. }
  do 1 (destruct e;try done).
  { revert He. cbn. repeat destruct_match_goal.
    move => *.
    left. repeat eexists. } 
  { destruct e.
    2: { exfalso. cbn in He. revert He.
         repeat destruct_match_goal. }
    revert He. cbn. repeat destruct_match_goal.
    move => *. right;left. repeat eexists. }
Qed.

Lemma b2p: forall {T:eqType} (a b:T), a==b -> a=b.
Proof. move => T a b Hb. by move/eqP in Hb. Qed.


Ltac false_assumption := exfalso ; apply ssrbool.not_false_is_true ; assumption.


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
                      host_instance reduce wasm_mixin expr val
                      reducible empty_instance prim_step to_val 
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
  no_reduce Heqes Hred.
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


Lemma reduce_val_false hs s0 f hs' s' f' es es' :
  is_Some (iris.to_val es) ->
  reduce hs s0 f es hs' s' f' es' -> False.
Proof.
  intros Hsome Hred.
  apply val_head_stuck_reduce in Hred.
  rewrite Hred in Hsome. inversion Hsome.
  done.
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


Lemma atomic_no_hole_load hs s0 f es hs' s' f' es' k lh k0 x0 x1 x2 x3 :
  reduce hs s0 f es hs' s' f' es' -> 
  lfilled k lh es [::AI_basic (BI_const (VAL_int32 k0)); AI_basic (BI_load x0 x1 x2 x3)] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.  
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 2 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_load_false;eauto. }
Qed.
    
Lemma atomic_no_hole_store hs s0 f es hs' s' f' es' k lh k0 v x0 x1 x2 x3 :
  reduce hs s0 f es hs' s' f' es' -> 
  lfilled k lh es [::AI_basic (BI_const (VAL_int32 k0)); AI_basic (BI_const v); AI_basic (BI_store x0 x1 x2 x3)] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 3 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_store_false_2;eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_store_false;eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
Qed.

Lemma atomic_no_hole_trap hs s0 f es hs' s' f' es' k lh :
  reduce hs s0 f es hs' s' f' es' -> 
  lfilled k lh es [::AI_trap] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 2 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
Qed.  
  
Global Instance is_atomic_correct s e : is_atomic e → Atomic s e.
Proof.
  intros Ha; apply strongly_atomic_atomic.
  move => σ e' K σ' e'' /= Hstep.
  unfold iris.prim_step in Hstep.
  destruct σ as [[[hs ws] locs] inst].
  destruct σ' as [[[hs' ws'] locs'] inst'].
  destruct Hstep as [Hstep [-> ->]].
  induction Hstep using reduce_ind.
  all: apply is_atomic_eq in Ha as Heq.
  all: destruct Heq as [(?&?&?&?&?&?)|[(?&?&?&?&?&?&?)|?]];simplify_eq; eauto.
  all: try by (do 2 (destruct vcs;try done)).
  all: try by (do 3 (destruct vcs;try done)).
  { inversion H;subst;eauto.
    1,2: do 3 (destruct vs;try done). }
  { inversion H;subst;eauto.
    1,2: do 4 (destruct vs;try done). }
  { inversion H;simpl;eauto; subst; exfalso.
    - do 2 (destruct vs;inversion H0;try done).
    - do 2 (destruct vs;inversion H0;try done). }
  { eapply atomic_no_hole_load in Hstep as HH;eauto. destruct HH as [Hlh Hk];eauto. subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }
  { edestruct atomic_no_hole_store as [Hlh Hk];eauto.
    subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }
  { edestruct atomic_no_hole_trap as [Hlh Hk];eauto.
    subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }
Qed.

(* Auxiliary lemmas *)

Lemma app_app (es1 es2 es3 es4: list administrative_instruction) :
  es1 ++ es2 = es3 ++ es4 ->
  length es1 = length es3 ->
  (es1, es2) = (es3, es4).
Proof.
  move: es2 es3 es4.
  elim: es1; destruct es3 => //=; move => es4 H2 Hlen; try by subst.
  inversion H2; subst; clear H2.
  inversion Hlen; clear Hlen.
  apply H in H3 => //.
  by inversion H3 => //; subst.
Qed.

Lemma fmap_split: forall {X Y:Type} (f: X -> Y) vs es1 es2,
  fmap f vs = es1 ++ es2 ->
  fmap f (take (length es1) vs) = es1 /\ fmap f (drop (length es1) vs) = es2.
Proof.
  move => X Y f vs es1.
  move : f vs.
  elim: es1; destruct vs => //=.
  move => es2 Hmap.
  inversion Hmap; subst; clear Hmap.
  apply H in H2. destruct H2; subst.
  split => //=.
  by f_equal.
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

(* given a nonempty list x :: xs, gives user a hypothesis "Htail : x :: xs = ys ++ [y]" *)
Ltac get_tail x xs ys y Htail :=
  cut (exists ys y, x :: xs = ys ++ [y]) ;
  [ intro Htail ; destruct Htail as (ys & y & Htail) |
    exists (removelast (x :: xs)) ;
    exists (List.last (x :: xs) AI_trap) ;
    apply app_removelast_last ;
    apply not_eq_sym ; apply nil_cons ].


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
    (exists n m, lfilled 0 (LH_base (take n es1)
                               (drop m (es1 ++ es2)))
                    [AI_trap] es' /\ σ' = σ /\ prim_step es1 σ obs [AI_trap] σ efs).
Proof.
  intros Hes1 Hstep.
  cut (forall n, length es' < n ->
            (exists es'', es' = es'' ++ es2 /\ prim_step es1 σ obs es'' σ' efs) \/
              (exists n m, n <= length es1 /\ m <= length (es1 ++ es2) /\
                        lfilled 0 (LH_base (take n es1)
                                         (drop m (es1 ++ es2)))
                              [AI_trap] es' /\ σ' = σ /\
                        prim_step es1 σ obs [AI_trap] σ efs)).
  { intro Hn ; assert (length es' < S (length es')) as Hlen ; first lia.
    destruct (Hn (S (length es')) Hlen) as [ Hl | (n0 & m & _ & _ & ? & ?) ].
    by left. by right ; exists n0, m. } 
  intros len Hlen.
  generalize dependent es' ; generalize dependent es1 ; generalize dependent es2.
  induction len ; intros es2 es1 Hes1 es' Hstep Hlen ; first lia.
  unfold prim_step, iris.prim_step in Hstep.
  destruct σ as [[[??]?]?].
  destruct σ' as [[[??]?]?].
  destruct Hstep as (Hstep & -> & ->).
  remember (es1 ++ es2) as es.
  remember {| f_locs := l ; f_inst := i |} as f.
  remember {| f_locs := l0 ; f_inst := i0 |} as f0.
  (* destruct es2 as [| e2 es2'].
  { left. exists es'. rewrite app_nil_r. repeat split => //=. rewrite app_nil_r in Heqes.
    by subst. }
  remember (e2 :: es2') as es2. *)
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
      rewrite Heqf in Heqf0 ; inversion Heqf0. repeat (split => //=). lia.
      destruct (first_non_value _ Hes1) as (vs1 & e1 & es'1 & Hvs1 & He1 & Hes'1).
      rewrite Hes'1 in Heqes. unfold lfilled, lfill in H1.
      destruct lh ; last by false_assumption.
      remember (const_list l1) as b eqn:Hl1. destruct b ; last by false_assumption.
      apply b2p in H1. rewrite H1 in Heqes.
      rewrite <- app_assoc in Heqes. rewrite <- app_comm_cons in Heqes.
      apply first_values in Heqes as (Hvs & He & Hnil) => //= ; try by right.
      rewrite <- He in Hes'1. rewrite Hes'1.
      apply r_simple. apply (rs_trap (lh :=LH_base vs1 es'1)).
      fold (app (A := administrative_instruction)) in Hnil. simpl in Hnil.
      subst. rewrite Hes'1 in Hes1. intro Htrap ; rewrite Htrap in Hes1.
      inversion Hes1.
      unfold lfilled, lfill. by rewrite Hvs1. }
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
          as [(es'' & Heq & Hred) | (n & m & Hn & Hm & Hfill & Hcontext & Hred)].
        { left. rewrite Hult. rewrite Hult'. rewrite Hults.
          exists es''. repeat split => //=. rewrite app_assoc ; rewrite Heq.
          by rewrite app_assoc. }
        { right. rewrite Hult. rewrite Hult'. exists n, m.
          repeat split => //=. do 2 rewrite app_length. simpl in Hm.
          rewrite app_length in Hm. lia.
          unfold lfilled, lfill. unfold lfilled, lfill in Hfill.
          destruct (const_list (take n (a :: es1))) ; last by false_assumption.
          apply b2p in Hfill ; rewrite app_assoc Hfill.
          rewrite <- app_assoc. rewrite <- (app_assoc [AI_trap]).
          rewrite Hults.
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
      Check (IHlen es2 es1).
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
        induction Hstep ; try by inversion Heqes0.
        { destruct H2 ; try by inversion Heqes0.
          destruct vs ; inversion Heqes0.
          rewrite H11 in H2. simpl in H2. false_assumption.
          destruct vs ; inversion Heqes0.
          rewrite H11 in H2 ; simpl in H2 ; false_assumption.
          inversion Heqes0. rewrite H8 in H2 ; simpl in H2 ; false_assumption.
          rewrite Heqtv. exists 1, (2 + length es).
          repeat split => //=. lia. rewrite app_length. lia.
          unfold lfilled, lfill. simpl. by rewrite drop_app.
          rewrite Heqf in Heqf0 ; by inversion Heqf0.
          apply r_simple. apply (rs_trap (lh := LH_base [AI_basic (BI_const v0)] [])).
          intro Habs ; inversion Habs. unfold lfilled, lfill => //=. }
        destruct ves ; inversion Heqes0.
        rewrite H17 in H8. cut (const_list (AI_trap :: ves) = true).
        intro Habs ; simpl in Habs ; false_assumption.
        rewrite H8 ; by apply v_to_e_is_const_list.
        destruct ves ; inversion Heqes0.
        rewrite H14 in H8. cut (const_list (AI_trap :: ves) = true).
        intro Habs ; simpl in Habs ; false_assumption.
        rewrite H8 ; by apply v_to_e_is_const_list.
        destruct ves ; inversion Heqes0.
        rewrite H14 in H8. cut (const_list (AI_trap :: ves) = true).
        intro Habs ; simpl in Habs ; false_assumption.
        rewrite H8 ; by apply v_to_e_is_const_list.
        unfold lfilled, lfill in H2.
        destruct k.
        { destruct lh as [bef0 aft0 |] ; last by false_assumption.
          remember (const_list bef0) as b eqn:Hbef0 ; destruct b ; last by false_assumption.
          apply b2p in H2. rewrite Heqes0 in H2.
          destruct bef0. {
            destruct es0 ; first by empty_list_no_reduce Hstep.
            inversion H2. rewrite H10 in IHHstep.
            Admitted. (* Rest of proof, work in progress
            apply IHHstep.
            
            unfold lfilled, lfill in H7. simpl in H7.
            apply b2p in H7. rewrite H7.
            
        

        
        subst.
        unfold iris.to_val in Hes1.
      assert (iris.to_val es1 = None) as Hes1'.
      { rewrite H3 in Hbef. simpl in Hbef.
        apply Logic.eq_sym, andb_true_iff in Hbef as [Ha Hbef].
        unfold iris.to_val in Hes1.
        destruct a ; try by inversion Ha.
        destruct b ; try by inversion Ha.
        fold iris.to_val in Hes1.
        destruct (iris.to_val es1).
          
          
          

          
          
        apply IHlen. repeat split => //=.
        rewrite H.
        apply (r_label (es:=es) (es':=es') (k:=0) (lh:=LH_base [] (a0 :: aft))) ;
          try by unfold lfilled, lfill ; simpl.
        by subst. rewrite H0 in Hlen. lia.
        
          
      
    
      
Qed. *)
  
(* Incorrect version of the lemma : to be removed soon 
(* The following few auxiliary lemmas are intuitive, but tedious to prove. *)
Lemma prim_step_split_reduce_r (es1 es2 es' : list administrative_instruction) σ σ' obs efs :
  iris.to_val es1 = None ->
  prim_step (es1 ++ es2) σ obs es' σ' efs ->
  exists es'', es' = es'' ++ es2 /\ prim_step es1 σ obs es'' σ' efs.
Proof.
  intros Hes1 Hstep.
  unfold prim_step, iris.prim_step in Hstep.
  destruct σ as [[[??]?]?].
  destruct σ' as [[[??]?]?].
  destruct Hstep as (Hstep & -> & ->).
  remember (es1 ++ es2) as es.
  remember {| f_locs := l ; f_inst := i |} as f.
  remember {| f_locs := l0 ; f_inst := i0 |} as f0.
  induction Hstep.
  { destruct H ;
      repeat (destruct es1 ; first (by inversion Heqes ; subst ; inversion Hes1)) ;
      inversion Heqes.
    - solve_prim_step_split_reduce_r H2 [AI_basic (BI_const (app_unop op v))]
                                     Heqf0 rs_unop.
    - solve_prim_step_split_reduce_r H4 [AI_basic (BI_const v)] Heqf0 rs_binop_success.
    - solve_prim_step_split_reduce_r H4 [AI_trap] Heqf0 rs_binop_failure.
    - solve_prim_step_split_reduce_r
        H2 [AI_basic (BI_const (VAL_int32 (wasm_bool (app_testop_i (e:=i32t) testop c))))]
        Heqf0 rs_testop_i32.
    - solve_prim_step_split_reduce_r
        H2 [AI_basic (BI_const (VAL_int32 (wasm_bool (app_testop_i (e:=i64t) testop c))))]
        Heqf0 rs_testop_i64.
    - solve_prim_step_split_reduce_r
        H3 [AI_basic (BI_const (VAL_int32 (wasm_bool (app_relop op v1 v2))))]
        Heqf0 rs_relop.
    - solve_prim_step_split_reduce_r H4 [AI_basic (BI_const v')] Heqf0 rs_convert_success.
    - solve_prim_step_split_reduce_r H4 [AI_trap] Heqf0 rs_convert_failure.
    - solve_prim_step_split_reduce_r
        H3 [AI_basic (BI_const (wasm_deserialise (bits v) t2))] Heqf0 rs_reinterpret.
    - solve_prim_step_split_reduce_r H1 [AI_trap] Heqf0 rs_unreachable.
    - solve_prim_step_split_reduce_r H1 ([] : seq.seq administrative_instruction)
                                     Heqf0 rs_nop.
    - solve_prim_step_split_reduce_r H2 ([] : seq.seq administrative_instruction)
                                     Heqf0 rs_drop.
    - solve_prim_step_split_reduce_r H5 [AI_basic (BI_const v2)] Heqf0 rs_select_false.
    - solve_prim_step_split_reduce_r H5 [AI_basic (BI_const v1)] Heqf0 rs_select_true.
    - destruct (first_non_value _ Hes1) as (vs1 & e1 & es'1 & Hvs1 & He1 & Hes'1).
      rewrite Hes'1 in Heqes. rewrite <- app_assoc in Heqes.
      rewrite <- app_comm_cons in Heqes.
      apply first_values in Heqes as (Hvs & He & Hnil) => //=.
      apply Logic.eq_sym, app_eq_nil in Hnil as [Hn1 Hn2].
      exists [AI_label m [] (vs ++ to_e_list es)].
      repeat (split => //= ; try by subst). rewrite Hes'1. rewrite <- Hvs.
      rewrite <- He. rewrite <- Heqf. rewrite <- Heqf0. rewrite Hn1.
      apply r_simple. apply (rs_block es H H0 H1 H2). by left.
    - destruct (first_non_value _ Hes1) as (vs1 & e1 & es'1 & Hvs1 & He1 & Hes'1).
      rewrite Hes'1 in Heqes. rewrite <- app_assoc in Heqes.
      rewrite <- app_comm_cons in Heqes.
      apply first_values in Heqes as (Hvs & He & Hnil) => //=.
      apply Logic.eq_sym, app_eq_nil in Hnil as [Hn1 Hn2].
      exists [AI_label n [AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)].
      repeat (split => //= ; try by subst). rewrite Hes'1. rewrite <- Hvs.
      rewrite <- He. rewrite <- Heqf. rewrite <- Heqf0. rewrite Hn1.
      apply r_simple. apply (rs_loop es H H0 H1 H2). by left.
    - solve_prim_step_split_reduce_r H3 [AI_basic (BI_block tf e2s)] Heqf0 rs_if_false.
    - solve_prim_step_split_reduce_r H3 [AI_basic (BI_block tf e1s)] Heqf0 rs_if_true.
    - solve_prim_step_split_reduce_r H2 vs Heqf0 rs_label_const.
    - solve_prim_step_split_reduce_r H1 [AI_trap] Heqf0 rs_label_trap.
    - apply Logic.eq_sym, app_eq_nil in H4 as [Hn1 Hn2].
      exists (vs ++ es). repeat ( split => //= ; try by subst ; rewrite app_nil_r).
      rewrite <- Heqf. rewrite <- Heqf0. apply r_simple. rewrite Hn1.
      apply (rs_br es H H0 H1).
    - solve_prim_step_split_reduce_r H3 ([] : seq.seq administrative_instruction)
                                     Heqf0 rs_br_if_false.
    - solve_prim_step_split_reduce_r H3 [AI_basic (BI_br i1)] Heqf0 rs_br_if_true.
    - solve_prim_step_split_reduce_r H4 [AI_basic (BI_br j)] Heqf0 rs_br_table.
    - solve_prim_step_split_reduce_r H3 [AI_basic (BI_br i1)] Heqf0 rs_br_table_length.
    - solve_prim_step_split_reduce_r H3 es Heqf0 rs_local_const.
    - solve_prim_step_split_reduce_r H1 [AI_trap] Heqf0 rs_local_trap.
    - apply Logic.eq_sym, app_eq_nil in H4 as [Hn1 Hn2].
      exists vs. repeat (split => //= ; try by subst ; rewrite app_nil_r).
      rewrite <- Heqf. rewrite Heqf0. apply r_simple. rewrite Hn1.
      apply (rs_return f0 H H0 H1).
    - destruct es1. subst. destruct a ; try by inversion H.
      destruct b ; try by inversion H. inveirson H2.
        
      
        
                                                               


    
  move: es2 es' σ σ' obs efs.
  elim: es1 => //=.
  - move => e es0 IH es2 es' σ σ' obs efs HConst HStep.
    unfold prim_step, iris.prim_step in HStep.
    specialize IH with es2 es' σ σ' [] [].
    destruct σ as [[[hs ws] locs] inst].
    destruct σ' as [[[hs' ws'] locs'] inst'].
    destruct HStep as [HStep [-> ->]].
Admitted.
*)





(* Context lemmas -- could be very tedious to prove *)





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
  generalize dependent vs ;
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


(* 
Lemma reduce_ves1: forall v es es' σ σ' efs obs,
    reducible es σ ->
    prim_step ([AI_basic (BI_const v)] ++ es) σ obs es' σ' efs ->
    (In AI_trap es -> False) -> 
    es' = [AI_basic (BI_const v)] ++ drop 1 es'.
Proof.
  cut (forall n v es es' σ σ' efs obs,
          length es < n ->
          reducible es σ ->
          prim_step ([AI_basic (BI_const v)] ++ es) σ obs es' σ' efs ->
          (In AI_trap es -> False) ->
          es' = [AI_basic (BI_const v)] ++ drop 1 es').
  { intros H v es es' σ σ' efs obs. apply (H (S (length es)) v es). lia. }
  intro len. induction len.
  { intros v es es' σ σ' efs obs Habs ; inversion Habs. }
  intros v es es' σ σ' efs obs Hlen Hes Hves Htrap.
  destruct Hes as (obs0 & es0 & σ0 & efs0 & H).
  unfold prim_step, iris.prim_step in Hves.
  destruct σ as [[[??]?]?].
  destruct σ' as [[[??]?]?]. 
  destruct Hves as (Hred & Hobs & Hefs).
  remember ([AI_basic (BI_const v)] ++ es)%list as ves.
  remember {| f_locs := l ; f_inst := i |} as f.
  induction Hred as [e e' s f hs Hredsimpl | | | | |
                     a cl t1s t2s ts es' ves vcs n m k zs s f f' i' hs Hlistcl Hcl Hves
                       Hvcs Hts Ht1s Ht2s Hzts Hinst Hlocs |
                     a cl h t1s t2s ves vcs m n s s' r f hs hs' Hlistcl Hcl Hves Hvcs
                       Ht1s Ht2s Hhost |
                     a cl t1s t2s h ves vcs n m s f hs hs' Hlistcl Hcl Hves Hvcs Ht1s
                       Ht2s Hhost |
                     | | | | | | | | | | | | | | | 
                     s f es' les s' f' es'' les' k lh hs hs' Hred IHreduce Hles Hles' | ] ;
    (try by inversion Heqves );
    (try by exfalso ; unfold language.prim_step, wasm_lang, iris.prim_step in H ;
     destruct σ0 as [[[??]?]?] ; destruct H as (Hred0 & Hobs0 & Hefs0) ;
     inversion Heqves as [[ Hhd Htl ]] ; no_reduce Htl Hred0 ).
  {  unfold language.prim_step, wasm_lang, iris.prim_step in H ;
     destruct σ0 as [[[??]?]?] ; destruct H as (Hred0 & Hobs0 & Hefs0).
    destruct Hredsimpl as [ | | | | | | | | | | | | | |
                            vs es' n m t1s t2s Hconst Hlenvs Ht1s Ht2s |
                            vs es' n m t1s t2s Hconst Hlenvs Ht1s Ht2s |
                          | | | | | | | | | | | | | ] ; exfalso ;
       inversion Heqves as [[ Hhd Htl ]] ;
      (try by no_reduce Htl Hred0).
    { destruct es. { rewrite app_nil_r in Heqves ;
                       rewrite <- app_nil_l in Heqves ; apply app_inj_tail in Heqves ;
                       destruct Heqves as [_ Habs] ; inversion Habs. }
      get_tail a es b l' Htail ; rewrite Htail in Heqves ;
        rewrite app_assoc in Heqves ; apply app_inj_tail in Heqves ;
        destruct Heqves as [Hvs Hl'] ; rewrite Htail in Hred0 ;
        rewrite <- Hl' in Hred0.
      remember {| f_locs := l0 ; f_inst := i0 |} as f'.
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
      rewrite <- Hl' in Hred0 ;
      apply (loop_not_enough_arguments_no_reduce _ _ _ _ _ _ _ _ _ _ _ Hred0).
      - rewrite Hvs in Hconst ; unfold const_list in Hconst ;
        rewrite forallb_app in Hconst ; apply andb_true_iff in Hconst ;
        destruct Hconst as [_ Hconst] ; exact Hconst.
      - rewrite Hvs in Hlenvs ; simpl in Hlenvs ; lia.
    }
    { filled_trap H0 Hxl1. rewrite Hhd in Hxl1. apply in_app_or in Hxl1.
      destruct Hxl1 as [Hxl1 | Hxl1 ] ; [ destruct Hxl1 as [ Hxl1 | Hxl1 ] ;
                                          inversion Hxl1 |].
      apply (Htrap Hxl1). }
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
  destruct k. { destruct lh ; [| exfalso ; false_assumption ].
                remember (const_list l1) as b.
                destruct b ; [| exfalso ; false_assumption].
                apply b2p in Hles.
                unfold lfilled, lfill in Hles'. rewrite <- Heqb in Hles'.
                apply b2p in Hles'.
                rewrite Hles in Heqves.
                destruct l1. { destruct es'.
                               { empty_list_no_reduce Hred. }
                               inversion Heqves as [[ Ha Hes ]].
                               rewrite Hles'. simpl.
                               destruct l2. { rewrite app_nil_r.
                                              rewrite app_nil_r in Hes.
                                              rewrite Hes in IHreduce.
                                              rewrite Ha in IHreduce.
                                              apply IHreduce ; auto. }
      assert (const_list es' -> False).
                               intro Hconst. apply (values_no_reduce _ _ _ _ _ _ _ _ Hred).
                               simpl. apply andb_true_iff. split.
                               rewrite Ha ; trivial. exact Hconst.
                               rewrite <- Hes in H.
                               assert (iris.to_val es' = None).
                               remember (iris.to_val es') as tv.
                               destruct tv ; [trivial |].
                               exfalso ; apply H0.
                               destruct v0.
                               apply (to_val_const_list _ l1 (Logic.eq_sym Heqtv)).
                               rewrite (to_val_trap_is_singleton (Logic.eq_sym Heqtv))
                                 in Hes.
                               rewrite <- Hes in Htrap. exfalso ; apply Htrap.
                               simpl. left ; reflexivity. reflexivity.
                               apply (prim_step_split_reduce_r _ _ _ _ _ _ _ H1) in H.
                               destruct H as (es1 & Hes0 & Hes').
                               assert (es'' = [AI_basic (BI_const v)] ++ drop 1 es'').
                               { destruct f'.
                                 apply (IHlen v es' es'' (hs, s, l, i)
                                              (hs', s', f_locs, f_inst) [] []).
                                 + rewrite <- Hes in Hlen.
                                   rewrite app_length in Hlen. simpl in Hlen.
                                   lia.
                                 + unfold reducible, language.reducible.
                                   exists obs0, es1, σ0, efs0 ; exact Hes'.
                                 + unfold prim_step, iris.prim_step.
                                   split. rewrite Ha in Hred. simpl.
                                   rewrite Heqf in Hred. exact Hred.
                                   split ; trivial.
                                 + intro ; apply Htrap. rewrite <- Hes.
                                   apply in_or_app. left ; assumption. }
                               destruct es''.
                               { exfalso. simpl in H. inversion H. }
                               simpl. unfold drop. simpl in H. unfold drop in H.
                               do 2 rewrite app_comm_cons. rewrite H. trivial. }
    rewrite Hles'. simpl. unfold drop. inversion Heqves as [[ Ha Htl ]]. trivial. }
  fold lfill in Hles. destruct lh ; [ exfalso ; false_assumption |].
  remember (const_list l1) as b. destruct b ; [| exfalso ; false_assumption].
  remember (lfill k lh es') as filled.
  destruct filled ; [| exfalso ; false_assumption ].
  apply b2p in Hles. unfold lfilled, lfill in Hles'. fold lfill in Hles'.
  rewrite <- Heqb in Hles'. remember (lfill k lh es'') as filled'.
  destruct filled' ; [| exfalso ; false_assumption ].
  apply b2p in Hles'. rewrite Hles in Heqves.
  destruct l1 ; inversion Heqves as [[ Ha Hes ]].
  rewrite Hles'. rewrite Ha. simpl. unfold drop. trivial.
Qed.  
 *) 
(*
Lemma reduce_trap: forall v es es' σ σ' efs obs,
    reducible es σ ->
    prim_step ([AI_basic (BI_const v)] ++ es) σ obs es' σ' efs ->
    In AI_trap es ->
    es' = [AI_trap] /\ prim_step es σ obs [AI_trap] σ' efs.
Proof.
  intros v es es' σ σ' efs obs Hes Hves Htrap.
  destruct Hes as (obs0 & es0 & σ0 & efs0 & H).
  unfold prim_step, iris.prim_step in Hves.
  destruct σ as [[[ ??]?]?].
  destruct σ' as [[[??]?]?].
  destruct Hves as (Hred & Hobs & Hefs).
  remember ([AI_basic (BI_const v)] ++ es) as ves.
  remember {| f_locs := l ; f_inst := i|} as f.
  remember {| f_locs := l0 ; f_inst := i0 |} as f0.
  induction Hred ; (* try by inversion Heqves ; *)
    (try by inversion Heqves as [[ Hhd Htl ]] ; found_intruse AI_trap Htl Hxl1 ) ;
    try by destruct ves ; inversion Heqves as [[ Hhd Htl ]] ;
    found_intruse AI_trap Htl Hxl1 ; last done ;
    apply in_app_or in Hxl1 as [ Habs | Habs ] ; last (by inversion Habs) ;
    assert (const_list (a0 :: ves)) as Hconst ;
    [ rewrite H2 ; by apply v_to_e_is_const_list |
      simpl in Hconst ; apply andb_true_iff in Hconst as [_ Hconst] ;
      intruse_among_values ves Habs Hconst ].
  destruct H0 ;  (try by
    inversion Heqves as [[ Hhd Htl ]] ; found_intruse AI_trap Htl Hxl1) ; 
    try by (destruct vs ; inversion Heqves as [[ Hhd Htl ]] ;
            found_intruse AI_trap Htl Hxl1 ;
            last done ;
            apply in_app_or in Hxl1 as [ Habs | Habs ] ; last (by inversion Habs) ;
            simpl in H0 ; apply andb_true_iff in H0 as [_ H0] ;
            intruse_among_values vs Habs H0) .
  repeat split => //=. rewrite <- Heqf ; rewrite <- Heqf0.
  apply r_simple. unfold lfilled, lfill in H1.
  destruct lh as [bef aft|] ; last by false_assumption.
  remember (const_list bef) as b eqn:Hbef ; destruct b ; last by false_assumption.
  apply b2p in H1. rewrite H1 in Heqves. destruct bef ; inversion Heqves.
  apply (rs_trap (lh := LH_base bef aft)).
  unfold language.prim_step, wasm_lang, iris.prim_step in H.
  destruct σ0 as [[[ ??]?]?]. destruct H as (H & Hobs0 & Hefs0).
  intro Habs ; rewrite Habs in H4 ; no_reduce H4 H.
  unfold lfilled, lfill.
  simpl in Hbef ; apply Logic.eq_sym, andb_true_iff in Hbef as [_ Hbef].
  by rewrite Hbef.
  unfold lfilled, lfill in H0.
  destruct k. { destruct lh as [bef aft |] ; last by false_assumption.
                remember (const_list bef) as b eqn:Hbef.
                destruct b ; last by false_assumption.
                apply b2p in H0.
           *)     
  
  
Lemma reduce_ves: forall v es es' σ σ' efs obs,
    reducible es σ ->
    prim_step ([AI_basic (BI_const v)] ++ es) σ obs es' σ' efs ->
    (es' = [AI_basic (BI_const v)] ++ drop 1 es' /\ prim_step es σ obs (drop 1 es') σ' efs)
      \/ (es' = [AI_trap] /\ prim_step es σ obs [AI_trap] σ' efs).
Proof.
  cut (forall n v es es' σ σ' efs obs,
          length es < n ->
          reducible es σ ->
          prim_step ([AI_basic (BI_const v)] ++ es) σ obs es' σ' efs ->
          (es' = [AI_basic (BI_const v)] ++ drop 1 es' /\
             prim_step es σ obs (drop 1 es') σ' efs)
          \/ (es' = [AI_trap] /\ prim_step es σ obs [AI_trap] σ' efs)).
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
    { right. repeat split => //=.
      unfold lfilled, lfill in H0. destruct lh ; last by false_assumption.
      remember (const_list l2) as b eqn:Hl2.
      destruct b ; last by false_assumption.
      apply b2p in H0.
      destruct l2 ; rewrite H0 in Heqves ; inversion Heqves as [[ Ha Hes ]].
      rewrite <- Heqf0 ; rewrite <- Heqf. apply r_simple.
      apply (rs_trap (lh:= LH_base l2 l3)). intro Htrap ; rewrite Htrap in Hes.
      no_reduce Hes Hred0.
      unfold lfilled, lfill. simpl in Hl2.
      apply Logic.eq_sym in Hl2.
      apply andb_true_iff in Hl2 as [_ Hl2]. by rewrite Hl2.
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
  destruct k. { destruct lh as [bef aft|] ; [| exfalso ; false_assumption ].
                remember (const_list bef) as b eqn:Hbef.
                destruct b ; [| exfalso ; false_assumption].
                apply b2p in Hles.
                unfold lfilled, lfill in Hles'. rewrite <- Hbef in Hles'.
                apply b2p in Hles'.
                rewrite Hles in Heqves.
                destruct bef.
                { destruct ces ; first by empty_list_no_reduce Hred.
                  inversion Heqves as [[ Ha Hes ]].
                  Admitted. (* proof in progress
                
                destruct l1. { destruct es'.
                               { empty_list_no_reduce Hred. }
                               inversion Heqves as [[ Ha Hes ]].
                               rewrite Hles'. rewrite app_nil_l.
                               destruct l2. { do 2 rewrite app_nil_r.
                                              rewrite app_nil_r in Hes.
                                              rewrite <- Hes in IHreduce.
                                              rewrite Ha in IHreduce.
                                              apply IHreduce ; auto.
                                              rewrite Hes ; assumption. }
                               assert (const_list es' -> False).
                               intro Hconst. apply (values_no_reduce _ _ _ _ _ _ _ _ Hred).
                               simpl. apply andb_true_iff. split.
                               rewrite Ha ; trivial. exact Hconst.
                               rewrite <- Hes in H.
                               (* assert (iris.to_val es' = None).
                               remember (iris.to_val es') as tv.
                               destruct tv ; [trivial |].
                               exfalso ; apply H0.
                               destruct v0.
                               apply (to_val_const_list _ l1 (Logic.eq_sym Heqtv)).
                               rewrite (to_val_trap_is_singleton (Logic.eq_sym Heqtv))
                                 in Hes.
                               rewrite <- Hes in Htrap. exfalso ; apply Htrap.
                               simpl. left ; reflexivity. reflexivity. *)
                               (*remember (iris.to_val es') as tv.
                               destruct tv.
                               { apply Logic.eq_sym in Heqtv.
                                 destruct v0. { exfalso ; apply H0.
                                                apply (to_val_const_list _ l1 Heqtv). }
                                 Check (to_val_trap_is_singleton Heqtv).
                                 remember es' as es3 in Heqtv.
                                 rewrite (to_val_trap_is_singleton Heqtv) in Heqes3.
                                 subst. 
                                 { induction l1. { simpl in Heqtv.
                                                   subst.
                                                   *)
                               apply (prim_step_split_reduce_r _ _ _ _ _ _ _ H1) in H.
                               destruct H as (es1 & Hes0 & Hes').
                               assert (prim_step es' (hs, s, l, i) obs
                                                 (drop 1 es'') (hs', s', l0, i0) efs).
                               { apply (IHlen v es' es'' (hs, s, l, i)
                                              (hs', s', l0, i0) efs obs).
                                 + rewrite <- Hes in Hlen.
                                   rewrite app_length in Hlen. simpl in Hlen.
                                   lia.
                                 + unfold reducible, language.reducible.
                                   exists obs0, es1, σ0, efs0 ; exact Hes'.
                                 + unfold prim_step, iris.prim_step.
                                   split. rewrite Ha in Hred. simpl.
                                   rewrite Heqf in Hred.
                                   rewrite Heqf0 in Hred. exact Hred.
                                   split ; trivial.
                                 + intro ; apply Htrap. rewrite <- Hes.
                                   apply in_or_app. left ; assumption. }
                               destruct es''.
                               { unfold drop in H.
                                 cut ([] = [AI_basic (BI_const v)] ++ drop 1 []).
                                 intro Habs ; inversion Habs.
                                 apply (reduce_ves1 v es' [] (hs,s,l,i)
                                                    (hs',s',l0,i0) [] []).
                                 + unfold reducible, language.reducible.
                                   exists obs, [], (hs',s',l0,i0), efs.
                                   exact H.
                                 + unfold prim_step, iris.prim_step.
                                   rewrite Heqf in Hred.
                                   rewrite Heqf0 in Hred.
                                   rewrite Ha in Hred.
                                   split ; [ assumption | split ; trivial].
                                 + intro ; apply Htrap. rewrite <- Hes.
                                   apply in_or_app ; left ; assumption. }
                               simpl. unfold drop. simpl in H. unfold drop in H.
                               split ; [| split ; trivial].
                               destruct H as [H _ _].
                               Check r_label.
                               apply (r_label (lh := LH_base [] (a0 :: l2)) (k := 0) H).
                               unfold lfilled, lfill.
                               assert (const_list []) ; [trivial |]. rewrite H2.
                               eauto.
                               unfold lfilled, lfill.
                               assert (const_list []) ; [trivial |]. rewrite H2.
                               eauto. }
    rewrite Hles'. simpl. unfold drop. inversion Heqves as [[ Ha Htl ]].
                split ; [|split ; trivial].
                simpl in Heqb ; apply Logic.eq_sym in Heqb ;
                  apply andb_true_iff in Heqb ; destruct Heqb as [_ Heqb].
                rewrite Heqf in Hred ; rewrite Heqf0 in Hred ;
                  apply (r_label (lh := LH_base l1 l2) (k := 0) Hred) ;
                  unfold lfilled, lfill ; rewrite Heqb ; eauto. }
  fold lfill in Hles. destruct lh ; [ exfalso ; false_assumption |].
  remember (const_list l1) as b. destruct b ; [| exfalso ; false_assumption].
  remember (lfill k lh es') as filled.
  destruct filled ; [| exfalso ; false_assumption ].
  apply b2p in Hles. unfold lfilled, lfill in Hles'. fold lfill in Hles'.
  rewrite <- Heqb in Hles'. remember (lfill k lh es'') as filled'.
  destruct filled' ; [| exfalso ; false_assumption ].
  apply b2p in Hles'. rewrite Hles in Heqves.
  destruct l1 ; inversion Heqves as [[ Ha Hes ]].
  rewrite Hles'. rewrite Ha. simpl. unfold drop.
  split ; [|split ; trivial].
  rewrite Heqf in Hred ; rewrite Heqf0 in Hred.
  simpl in Heqb ; apply Logic.eq_sym in Heqb ;
    apply andb_true_iff in Heqb ; destruct Heqb as [_ Heqb].
  apply (r_label (lh := LH_rec l1 n l2 lh l3) (k := S k) Hred) ;
    unfold lfilled, lfill ; rewrite Heqb ; fold lfill.
  rewrite <- Heqfilled ; trivial.
  rewrite <- Heqfilled' ; trivial.
Qed.                         

(* New formulation of lemma *)

Lemma reduce_ves: forall v es es' σ σ' efs obs,
    reducible es σ ->
    prim_step ([AI_basic (BI_const v)] ++ es) σ obs es' σ' efs ->
    (es' = [AI_basic (BI_const v)] ++ drop 1 es' /\ prim_step es σ obs (drop 1 es') σ' efs) \/ (es' = [AI_trap] /\ prim_step es σ obs [AI_trap] σ' efs).
Admitted.
*)


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

Lemma fmap_insert_set_nth: forall T (l: list T) i vd v,
  i < length l ->
  <[i := v]> l = set_nth vd l i v.
Proof.
  move => T l i vd v Hlen.
  move: i vd v Hlen.
  induction l; move => i vd v Hlen; destruct i => //=; simpl in Hlen; try by lia.
  apply lt_S_n in Hlen.
  f_equal.
  by apply IHl.
Qed.

Lemma lfilled_swap : ∀ i lh es LI es', 
  lfilled i lh es LI ->
  ∃ LI', lfilled i lh es' LI'.
Proof.
  intros i.
  induction i;intros lh es LI es' Hfill%lfilled_Ind_Equivalent.
  { inversion Hfill; subst.
    exists (vs ++ es' ++ es'0).
    apply lfilled_Ind_Equivalent. by constructor. }
  { inversion Hfill;subst.
    apply lfilled_Ind_Equivalent in H1.
    apply IHi with (es':=es') in H1 as [LI' HLI'].
    exists (vs ++ [AI_label n es'0 LI'] ++ es'').
    apply lfilled_Ind_Equivalent. constructor;auto.
    by apply lfilled_Ind_Equivalent. }
Qed.

Lemma lfilled_inj : ∀ i lh es LI LI',
  lfilled i lh es LI ->
  lfilled i lh es LI' ->
  LI = LI'.
Proof.
  intros i.
  induction i; intros lh es LI LI'
                      Hfill1%lfilled_Ind_Equivalent
                      Hfill2%lfilled_Ind_Equivalent.
  { inversion Hfill1; subst.
    inversion Hfill2; subst. done. }
  { inversion Hfill1; subst.
    inversion Hfill2; subst.
    rewrite (IHi lh' es LI0 LI);auto;by apply lfilled_Ind_Equivalent. }
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
  pose proof (lfilled_swap _ _ _ _ e' Hfill) as [LI' HLI'].
  exists [], LI', σ', [].
  destruct σ as [[[? ?] ?] ?].
  destruct σ' as [[[? ?] ?] ?].
  rewrite /= /iris.prim_step in Hred.
  destruct Hred as [Hred [-> ->]].
  split;auto.
  eapply r_label. apply Hred. apply Hfill. apply HLI'.
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

(* Warning: this axiom is not actually true -- Wasm does not have a deterministic
   opsem for mem_grow and host function calls; due to the interaction between r_label
   and rs_trap, traps also have non-det behaviours in terms of reduction paths.
   However, the rest of the opsem are indeed deterministic. Use with caution. *)
(* TODO: find a condition for es that guarantees deterministic reduction. *)
Local Axiom reduce_det: forall hs f ws es hs1 f1 ws1 es1 hs2 f2 ws2 es2,
  reduce hs f ws es hs1 f1 ws1 es1 ->
  reduce hs f ws es hs2 f2 ws2 es2 ->
  (hs1, f1, ws1, es1) = (hs2, f2, ws2, es2).



(* A Definition of a context dependent WP for WASM expressions *)

Definition wp_wasm `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wlocsG Σ, !winstG Σ}
          (s : stuckness) (E : coPset) (e : language.expr wasm_lang)
           (Φ : val -> iProp Σ) (i : nat) (lh : lholed) : iProp Σ := 
  ∀ LI, ⌜lfilled i lh e LI⌝ -∗ WP LI @ s; E {{ Φ }}.

Notation "'WP' e @ s ; E 'CTX' i ; lh {{ Φ } }" := (wp_wasm s E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh {{ Φ } }" := (wp_wasm NotStuck E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh ? {{ Φ } }" := (wp_wasm MaybeStuck E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e 'CTX' i ; lh {{ Φ } }" := (wp_wasm NotStuck ⊤ e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e 'CTX' i ; lh ? {{ Φ } }" := (wp_wasm MaybeStuck ⊤ e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ s ; E 'CTX_EMPTY' {{ Φ } }" := (wp_wasm s E e%E Φ 0 (LH_base [] []))
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.


Notation "'WP' e @ s ; E 'CTX' i ; lh {{ v , Q } }" := (wp_wasm s E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ s ; E 'CTX_EMPTY' {{ v , Q } }" := (wp_wasm s E e%E (λ v, Q) 0 (LH_base [] []))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'CTX_EMPTY'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh {{ v , Q } }" := (wp_wasm NotStuck E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @ '[' E  '/' ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm MaybeStuck E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' E  '/' ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'CTX' i ; lh {{ v , Q } }" := (wp_wasm NotStuck ⊤ e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm MaybeStuck ⊤ e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

  
(* wp for instructions *)

Section lifting.
Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wlocsG Σ, !winstG Σ}.

(* Predicate for memory blocks *)

(* TODO: switch to monotone implementation of mem_size once we have that? *)
Definition mem_block (n: N) (m: memory) :=
  (([∗ list] i ↦ b ∈ (m.(mem_data).(ml_data)), n ↦[wm][ (N.of_nat i) ] b ) ∗
     n ↦[wmlength] mem_length m)%I.
(* mem_size_exact (N.succ_pos n) (mem_size m))%I*)

Notation "n ↦[wmblock] m" := (mem_block n m)
                           (at level 20, format "n ↦[wmblock] m"): bi_scope.

Definition mem_block_equiv (m1 m2: memory) :=
  m1.(mem_data).(ml_data) = m2.(mem_data).(ml_data).

Notation "m1 ≡ₘ m2" := (mem_block_equiv m1 m2)
                        (at level 70, format "m1 ≡ₘ m2").

(* empty lists, frame and context rules *)

Lemma wp_wasm_empty_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) e :
  ⊢ WP e @ s ; E {{ Φ }} ∗-∗ WP e @ s ; E CTX_EMPTY {{ Φ }}.
Proof.
  iSplit.
  { iIntros "HWP". iIntros (LI Hfill%lfilled_Ind_Equivalent).
    inversion Hfill. subst. erewrite app_nil_l; erewrite app_nil_r. done. }
  { iIntros "HWP".
    iDestruct ("HWP" $! e with "[]") as "$".
    iPureIntro. cbn. rewrite app_nil_r eqseqE. apply eq_refl. }
Qed.

Lemma wp_nil (s : stuckness) (E : coPset) (Φ : iProp Σ) :
  Φ ⊢ WP [] @ s ; E CTX_EMPTY {{ fun v => Φ }}%I.
Proof.
  iIntros "H". iApply wp_wasm_empty_ctx.
  by rewrite wp_unfold /wp_pre.
Qed.

Lemma wp_seq_ctx (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) (i : nat) (lh : lholed) :
  (WP es1 @ NotStuck; E {{ w, Ψ w }} ∗
  ∀ w, Ψ w -∗ WP (iris.of_val w ++ es2) @ s; E CTX i; lh {{ v, Φ v }})%I
  ⊢ WP (es1 ++ es2) @ s; E CTX i; lh {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ i lh).
{ iIntros "[Hes1 Hes2]".
  (* iDestruct (wp_wasm_empty_ctx with "Hes1") as "Hes1". *)
  iIntros (LI Hfilled).
  repeat rewrite wp_unfold /wp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val LI) as [vs|] eqn:Hetov.
  { destruct vs.
    { pose proof (filled_is_val_imm _ _ _ _ _ Hetov Hfilled) as
        [vs [es' [-> [-> [Hconst1 Hconst2]]]]].
      apply const_list_is_val in Hconst1 as [v1 Hv1].
      apply const_list_is_val in Hconst2 as [v2 Hv2].
      edestruct fill_val as [vs12 [Hvs12 Heql]];eauto.
      assert (Hvs12':=Hvs12).
      apply to_val_cat in Hvs12' as [-> Hev2].
      apply iris.of_to_val in Hev2 as <-.
      iMod "Hes1".
      iSpecialize ("Hes2" with "Hes1").
      unfold iris.of_val.
      rewrite - fmap_app take_drop.
      rewrite of_val_imm.
      pose proof (lfilled_swap _ _ _ _ (iris.of_val (immV vs12)) Hfilled) as [LI' Hfilled'].
      iSpecialize ("Hes2" $! _ Hfilled').
      rewrite wp_unfold /wp_pre /=.
      assert (iris.to_val LI' = Some (immV l)) as ->;[|iFrame].
      apply lfilled_Ind_Equivalent in Hfilled'. inversion Hfilled';subst.
      apply to_val_cat_inv;auto. apply to_val_cat_inv;auto. apply iris.to_of_val.
    }
    { apply to_val_trap_is_singleton in Hetov. subst.
      apply lfilled_Ind_Equivalent in Hfilled.
      inversion Hfilled;subst.
      2: { exfalso. do 2 destruct vs =>//=. }
      apply app_eq_singleton in H as [[HH HH']|[HH HH']];subst.
      { exfalso. destruct es1,es2,es' =>//=. }
      apply app_eq_singleton in HH' as [[HH HH']|[HH HH']];subst.
      { apply app_eq_singleton in HH as [[-> ->]|[-> ->]].
        simpl.
        all:iMod "Hes1".
        all: iSpecialize ("Hes2" with "Hes1").
        all:rewrite /=.
        all: iDestruct (wp_wasm_empty_ctx with "Hes2") as "Hes2".
        all:by rewrite wp_unfold /wp_pre /=. }
      { destruct es1,es2 =>//=.
        iMod "Hes1".
        iSpecialize ("Hes2" with "Hes1").
        rewrite /=.
        iSpecialize ("Hes2" $! [AI_trap] with "[]").
        { iPureIntro. constructor. }
        by rewrite wp_unfold /wp_pre /=.  }
    }
  }
  {
  (* Ind *)
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod "Hes1".
    iSpecialize ("Hes2" with "Hes1").
    iSpecialize ("Hes2" $! _ Hfilled).
    rewrite wp_unfold /wp_pre /=.
    rewrite Hetov.
    iSpecialize ("Hes2" $! σ ns κ κs nt with "Hσ").
    iMod "Hes2" as "[%H1 H2]".
    iIntros "!>".
    iSplit.
    - iPureIntro. by apply H1. 
    - by iApply "H2".
  }
  {
    iSpecialize ("Hes1" $! σ ns κ κs nt with "Hσ").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct s => //.
      apply append_reducible with (es2:=es2) in H1;auto.
      eapply lfilled_reducible. apply Hfilled. auto.
    - iIntros (e2 σ2 efs HStep').
      eapply lfilled_prim_step_split_reduce_r in HStep' as Heq;[|apply Hfilled|apply H1].
      destruct Heq as [e' [HStep'' Hlfilled']].
      apply prim_step_obs_efs_empty in HStep'' as Hemp. inversion Hemp;subst;clear Hemp.
      apply prim_step_obs_efs_empty in HStep' as Hemp. inversion Hemp;subst;clear Hemp.
      iSpecialize ("H2" $! e' σ2 [] HStep'').
      iMod "H2".
      repeat iModIntro.
      repeat iMod "H2".
      iModIntro.
      iDestruct "H2" as "(Hσ & Hes'' & Hefs)".
      iFrame.
      iDestruct ("IH" with "[$Hes'' $Hes2]") as "Hcont".
      iSplit;[|done]. iApply "Hcont". auto.
  } } }
Qed.

Print rs_trap.

Print r_label.

(*
value1
value2
value3
Trap
expr3
expr2
expr1

could reduce to either a Trap directly, or 
value1
Trap
expr1,

But ultimately they reduce to a single Trap.
*)

(*
Lemma wp_trap s E es Φ:
  WP @ s; E ([AI_trap] ++ es) {{ w, Φ w }} ⊢
  |={E}=> Φ trapV.
Proof.
  rewrite wp_unfold/ wp_pre.
Admitted.
 *)

(* behaviour of seq might be a bit unusual due to how reductions work. *)
(* Note that the sequence wp is also true without the premise that Ψ doesn't trap, but it is very tricky to prove that version. The following is the fault-avoiding version.*)
Lemma wp_seq_nontrap (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) :
  (¬ Ψ trapV) ∗ 
  (WP es1 @ s; E {{ w, Ψ w }} ∗
  ∀ w, Ψ w -∗ WP (iris.of_val w ++ es2) @ s; E {{ v, Φ v }})%I
  ⊢ WP (es1 ++ es2) @ s; E {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ).
  iIntros "(Hntrap & Hes1 & Hes2)".
  repeat rewrite wp_unfold /wp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val (es1 ++ es2)) as [vs|] eqn:Hetov.
  {
    destruct vs.
    {
      apply to_val_cat in Hetov as [-> Hev2].
      apply iris.of_to_val in Hev2 as <-.
      iMod "Hes1".
      iSpecialize ("Hes2" with "Hes1").
      unfold iris.of_val.
      rewrite - fmap_app take_drop.
      rewrite of_val_imm.
      rewrite wp_unfold /wp_pre /=.
      rewrite of_val_imm to_of_val.
      by iAssumption.
    }
    {
      apply to_val_trap_is_singleton in Hetov.
      apply app_eq_singleton in Hetov as [[-> ->]|[-> ->]].
      all:iMod "Hes1".
      all: iSpecialize ("Hes2" with "Hes1").
      all:rewrite /=.
      all:by rewrite wp_unfold /wp_pre /=. 
    }
  }
  (* Ind *)
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod "Hes1".
    iSpecialize ("Hes2" with "Hes1").
    rewrite wp_unfold /wp_pre /=.
    rewrite Hetov.
    iSpecialize ("Hes2" $! σ ns κ κs nt with "Hσ").
    iMod "Hes2" as "[%H1 H2]".
    iIntros "!>".
    iSplit.
    - iPureIntro. by apply H1. 
    - by iApply "H2".
  }
  {
    iSpecialize ("Hes1" $! σ ns κ κs nt with "Hσ").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct s => //.
      by apply append_reducible.
    - iIntros (e2 σ2 efs HStep).
      apply prim_step_split_reduce_r in HStep; last by [].
      destruct HStep as [[es'' [-> HStep]] | [n [m [Hlf [-> HStep]]]]].
      + iSpecialize ("H2" $! es'' σ2 efs HStep).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        iModIntro.
        destruct σ2 as [[??] ?].
        iDestruct "H2" as "(Hσ & Hes'' & Hefs)".
        iFrame.
        iApply "IH".
        by iFrame.
      + move/lfilledP in Hlf.
        inversion Hlf; subst; clear Hlf.
        iSpecialize ("H2" $! [AI_trap] σ efs HStep).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        destruct σ as [[??] ?].
        iDestruct "H2" as "(Hσ & Hes'' & Hefs)".
        replace [AI_trap] with (iris.of_val trapV) => //.
        rewrite wp_value_fupd'.
        iMod "Hes''".
        by iSpecialize ("Hntrap" with "Hes''").
        (* iModIntro.
        iFrame.
        iSpecialize ("Hes2" with "Hes''").
        by iApply wp_trap_r.*)
  }
Qed.

(*
(* This requires inverting wp again........ It would be really amazing
   if we can actually prove this, since I can't find anywhere in Iris where
   this has been done. *)
Lemma wp_trap_lfilled (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (es : language.expr wasm_lang) (lh: lholed):
  lfilled 0 lh [AI_trap] es ->
  WP es @ s; E {{ v, Φ v }} ⊢
  |={E}=> Φ trapV.
Proof.
  move => Hlf.
  iIntros "H".
  repeat rewrite wp_unfold /wp_pre /=.
  move/lfilledP in Hlf.
  inversion Hlf; subst; clear Hlf.
  (* if both vs and es' are empty then we're good: wp_value is directly applicable. *)
  destruct (iris.to_val (vs ++ [AI_trap] ++ es')) as [v|] eqn:Hetov.
  {
    destruct v.
    (* actual value, which is impossible *)
    {
      apply to_val_cat in Hetov as [Hvs He].
      apply to_val_cat in He as [Het He'].
      simpl in Het.
      by inversion He'.
    }
    (* trapV *)
    {
      apply iris.of_to_val in Hetov.
      simpl in Hetov.
      destruct vs; by [destruct es' | destruct vs].
    }
  }
  rewrite Hetov.
  (* We now need to feed an explicit configuration and state to the premise. *)
Admitted.

Lemma wp_seq_trap (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) :
  (WP es1 @ s; E {{ w, ⌜ w = trapV ⌝ }} ∗
  WP ([AI_trap] ++ es2) @ s; E {{ v, Φ v }})%I
  ⊢ WP (es1 ++ es2) @ s; E {{ v, Φ v }}.
Proof.
  iIntros "(Hes1 & Hes2)".
  repeat rewrite wp_unfold /wp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val (es1 ++ es2)) as [vs|] eqn:Hetov.
  {
    destruct vs.
    {
      apply to_val_cat in Hetov as [-> Hev2].
      apply iris.of_to_val in Hev2 as <-.
      by iMod "Hes1" as "%Hes1".
    }
    {
      apply to_val_trap_is_singleton in Hetov.
      apply app_eq_singleton in Hetov as [[-> ->]|[-> ->]] => //.
      iMod "Hes1" => //.
      by iDestruct "Hes1" as "%Hes1".
    }
  }
  (* Ind *)
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod "Hes1" as "->".
    destruct es2 => //.
    iSpecialize ("Hes2" $! σ ns κ κs nt with "Hσ").
    iMod "Hes2" as "[%H1 H2]".
    iIntros "!>".
    iSplit.
    - iPureIntro. by apply H1. 
    - by iApply "H2".
  }
  {
    iSpecialize ("Hes1" $! σ ns κ κs nt with "Hσ").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct s => //.
      by apply append_reducible.
    - iIntros (e2 σ2 efs HStep).
      apply prim_step_split_reduce_r_correct in HStep; last by [].
      destruct HStep as [[es'' [-> HStep]] | [n [m [Hlf [-> HStep]]]]].
      + iSpecialize ("H2" $! es'' σ2 efs HStep).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        iModIntro.
        destruct σ2 as [[??] ?].
        iDestruct "H2" as "(Hσ & Hes'' & Hefs)".
        iFrame.
Admitted.
*)

(* The following operation mirrors the opsem of AI_trap *)
(* in which a trap value swallows all other stack values *)
Definition val_combine (v1 v2 : val) :=
  match v1 with
  | immV l => match v2 with
             | immV l' => immV (l ++ l')
             | trapV => trapV
             end
  | trapV => trapV
  end.

(* Knowing hypothesis "Hred : objs -> _" (with frames (locs, inst) and (locs', inst')),
   attempts to exfalso away most of the possible ways Hred could hold, leaving the user
   with only the one possible desired case. Tactic will also attempt to trivially solve
   this one case, but may give it to user if attempt fails. 

   At this point, tactic only works if objs is a list of length exactly 2. Work is in
   progress to refine this tactic so it would work on lists of any length *)
Ltac only_one_reduction Hred objs locs inst locs' inst' :=
  let a := fresh "a" in
  let aft := fresh "aft" in
  let bef := fresh "bef" in
  let e := fresh "e" in
  let e' := fresh "e'" in
  let es := fresh "es" in
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
  let Heqes0 := fresh "Heqes" in
  let Heqes2 := fresh "Heqes" in
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
  let t1s := fresh "t1s" in
  let t2s := fresh "t2s" in
  let vs := fresh "vs" in
  remember objs as es0 eqn:Heqes0 ;
  remember {| f_locs := locs ; f_inst := inst |} as f eqn:Heqf ;
  remember {| f_locs := locs' ; f_inst := inst' |} as f' eqn:Heqf' ;
  apply Logic.eq_sym in Heqes0 ;
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
         inversion Heqes0 as [[ Hhd ]] ; subst ;
         (try by found_intruse (AI_basic (BI_block (Tf t1s t2s) es)) Hhd Hxl1) ;
         (try by found_intruse (AI_basic (BI_loop (Tf t1s t2s) es)) Hhd Hxl1) ;
         (try by filled_trap H0 Hxl1) ) ;
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
                        (( by simpl in H0 ; rewrite H0 in H1 ;
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
       ) ;        
  (* at this point, only one case should be remaining.
     we attempt to solve this case too trivially, as the following line is often
     what user would be going to do next anyway *)
  try by inversion Heqes0 ; subst ; inversion Heqf' ; subst ; iFrame.

(* An attempt at making reduce_det a proved lemma. Work in progress

Lemma reduce_det: forall hs f ws es hs1 f1 ws1 es1 hs2 f2 ws2 es2,
  reduce hs f ws es hs1 f1 ws1 es1 ->
  reduce hs f ws es hs2 f2 ws2 es2 ->
  ( In (AI_basic BI_grow_memory) es -> False ) ->
  ( forall a, In (AI_invoke a) es -> False) -> 
  (hs1, f1, ws1, es1) = (hs2, f2, ws2, es2).
Proof.
  intros hs f ws es hs1 f1 ws1 es1 hs2 f2 ws2 es2 Hred1 Hred2 Hgrow_memory Hinvoke.
  destruct es as [ | e0 es ].
  { empty_list_no_reduce Hred1. }
  destruct es as [ | e1 es ].
  { remember [e0] as es.
    apply Logic.eq_sym in Heqes.
    destruct e0.
    destruct b ; try by exfalso ; no_reduce Heqes Hred1. *)

Lemma wp_val (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v0 : value) (es : language.expr wasm_lang) :
  WP es @ NotStuck ; E {{ v, (Φ (val_combine (immV [v0]) v))  }}
  ⊢ WP ((AI_basic (BI_const v0)) :: es) @ s ; E {{ v, Φ v }}%I.
Proof.
  (* This also needs an iLob. *)
  iLöb as "IH" forall (v0 es Φ).
  iIntros "H".
  repeat rewrite wp_unfold /wp_pre /=.
  destruct (iris.to_val es) as [vs|] eqn:Hes.
  {
    destruct vs.
    { by apply of_to_val in Hes as <-.
      }
    { apply to_val_trap_is_singleton in Hes as ->.
      iIntros (σ ns κ κs nt) "Hσ".
      iMod "H".
      destruct σ as [[[hs ws] locs] inst].
      iApply fupd_frame_l. iSplit.
      { destruct s;auto. iPureIntro.
        unfold language.reducible.
        pose proof (AI_trap_reducible_2 [AI_basic (BI_const v0)]) as H.
        apply H;auto. }
      iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hmask".
      iIntros (es2 σ2 efs HStep).
      rewrite -cat1s in HStep.
      assert ((κ, efs) = ([],[])) as Hobsefs; first by eapply prim_step_obs_efs_empty.
      inversion Hobsefs; subst; clear Hobsefs.
      destruct σ2 as [[[hs2 ws2] locs2] inst2].
      iModIntro. iNext. iMod "Hmask".
      iApply fupd_mask_intro_subseteq. solve_ndisj.
      unfold iris.prim_step in *.
      assert (iris.prim_step (host_instance:=host_instance)
                             ([AI_basic (BI_const v0)] ++ [AI_trap])%SEQ 
                             (hs, ws, locs, inst) [] [AI_trap] (hs, ws, locs, inst) []) as Hstep.
      { repeat constructor. econstructor;auto.
        instantiate (1:=LH_base [AI_basic (BI_const v0)] []).
        rewrite /lfilled /lfill => //=. }
      destruct HStep as [HStep _].
      destruct Hstep as [Hstep _].
      apply AI_trap_reduce_det in HStep => //.
      inversion HStep; subst; clear HStep.
      iFrame.
      iSplit => //.
      iApply wp_value => //.
      by rewrite/IntoVal.
    }
  }
  {
    iIntros (σ ns κ κs nt) "Hσ".
    iSpecialize ("H" $! σ ns κ κs nt with "Hσ").
    iMod "H".
    iModIntro.
    iDestruct "H" as "(%H1 & H)".
    iSplit.
    - iPureIntro.
      destruct s => //=.
      rewrite - cat1s.
      by eapply prepend_reducible; eauto.
    - iIntros (es2 σ2 efs HStep).
      rewrite -cat1s in HStep.
      eapply reduce_ves in H1; last by apply HStep.
      assert ((κ, efs) = ([],[])) as Hobsefs; first by eapply prim_step_obs_efs_empty.
      inversion Hobsefs; subst; clear Hobsefs.
      destruct H1 as [[-> HStep2] | [-> HStep2]].
      + iSpecialize ("H" $! (drop 1 es2) σ2 [] HStep2).
        iMod "H".
        repeat iModIntro.
        repeat iMod "H".
        iModIntro.
        iDestruct "H" as "(Hσ & Hes & Hefs)".
        iSimpl.
        iFrame.
        iSplit => //.
        by iApply "IH".
      + iSpecialize ("H" $! [AI_trap] σ2 [] HStep2).
        iMod "H".
        repeat iModIntro.
        repeat iMod "H".
        iDestruct "H" as "(Hσ & Hes & Hefs)".
        iSimpl.
        iFrame.
        iApply fupd_frame_r.
        iSplit => //.
        rewrite wp_unfold /wp_pre /=.
        iMod "Hes".
        by iApply wp_value; first instantiate (1 := trapV); rewrite/IntoVal => //.
  }

Qed.
  
Lemma wp_val_app' (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs (es : language.expr wasm_lang) :
  WP es @ NotStuck ; E {{ v, (Φ (val_combine (immV vs) v)) }}%I
  ⊢ WP ((v_to_e_list vs) ++ es) @ s ; E {{ v, Φ v }}%I.

Proof.
  iInduction vs as [|c vs] "IH" forall (Φ s E es).
  { simpl.
    iIntros "HWP".
    destruct s.
    2: iApply wp_stuck_weaken.
    all: iApply (wp_wand with "HWP").
    all: iIntros (v).
    all: destruct v => /=.
    all: iIntros "HΦ" => //.
  }
  { iIntros "HWP".
    iSimpl.
    iApply wp_val.
    iApply "IH" => //=.
    iApply (wp_mono with "HWP").
    iIntros (vs') "HΦ".
    iSimpl. destruct vs';auto.
  }
Qed.

Lemma wp_val_app (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs v' (es : language.expr wasm_lang) :
  iris.to_val vs = Some (immV v') ->
  WP es @ NotStuck ; E {{ v, (Φ (val_combine (immV v') v)) }}%I
  ⊢ WP (vs ++ es) @ s ; E {{ v, Φ v }}%I.
Proof.
  iIntros "%Hves Hwp".
  apply of_to_val in Hves; subst.
  by iApply wp_val_app'.
Qed.
                                  
(* basic instructions with simple(pure) reductions *)

(* numerics *)

Lemma wp_unop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v v' : value) (t: value_type) (op: unop):
  app_unop op v = v' ->
  Φ (immV [v']) ⊢
  WP [AI_basic (BI_const v); AI_basic (BI_unop t op)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros (Hunop) "HΦ".
  iApply wp_lift_atomic_step. simpl ; trivial.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v')], σ, [].
    destruct σ as [[[ hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //. apply r_simple. rewrite <- Hunop. apply rs_unop.
  - destruct σ as [[[hs ws] locs] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'].
    destruct HStep as (H & -> & ->).    
    only_one_reduction H [AI_basic (BI_const v) ; AI_basic (BI_unop t op)]
                       locs inst locs' inst'.       
Qed.

  
Lemma wp_binop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v1 v2 v : value) (t: value_type) (op: binop):
  app_binop op v1 v2 = Some v ->
  Φ (immV [v]) ⊢
  WP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros (Hbinop) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v)], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    by apply rs_binop_success.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                          AI_basic (BI_binop t op)] locs inst locs' inst'.
    inversion Heqf' ; subst. rewrite Hbinop in H. inversion H; subst. by iFrame.
    rewrite Hbinop in H ; inversion H.
Qed.

(* There is a problem with this case: AI_trap is not a value in our language.
   This can of course be circumvented if we only consider 'successful reductions',
   but otherwise this needs some special treatment. *)

(* 20210929: with [::AI_trap] potentially becoming a value, this might get proved at some point *)
Lemma wp_binop_failure (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v1 v2 : value) (t: value_type) (op: binop):
  Φ trapV ∗
  ⌜app_binop op v1 v2 = None⌝ ⊢
  WP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros "(HΦ & %Hbinop)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_trap], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    by apply rs_binop_failure.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H; last by apply r_simple, rs_binop_failure.
    inversion H; subst; clear H.
    iFrame.
    iSimpl => //.
Qed.
    
Lemma wp_relop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v1 v2 : value) (b: bool) (t: value_type) (op: relop):
  app_relop op v1 v2 = b ->
  Φ (immV [(xb b)]) ⊢
  WP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros (Hrelop) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (xb b))], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_relop.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                          AI_basic (BI_relop t op)] locs inst locs' inst'. 
Qed.

Lemma wp_testop_i32 (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v : i32) (b: bool) (t: value_type) (op: testop):
  app_testop_i (e:=i32t) op v = b ->
  Φ (immV [(xb b)]) ⊢
    WP [AI_basic (BI_const (VAL_int32 v)); AI_basic (BI_testop T_i32 op)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros (Htestop) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (xb b))], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_testop_i32.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H [AI_basic (BI_const (VAL_int32 v));
                          AI_basic (BI_testop T_i32 op) ]
                       locs inst locs' inst'.
Qed.

Lemma wp_testop_i64 (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v : i64) (b: bool) (t: value_type) (op: testop):
  app_testop_i (e:=i64t) op v = b ->
  Φ (immV [(xb b)]) ⊢
    WP [AI_basic (BI_const (VAL_int64 v)); AI_basic (BI_testop T_i64 op)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros (Htestop) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (xb b))], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_testop_i64.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H [AI_basic (BI_const (VAL_int64 v)) ;
                          AI_basic (BI_testop T_i64 op)]
                       locs inst locs' inst'.
Qed.

Lemma wp_cvtop_convert (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v v': value) (t1 t2: value_type) (sx: option sx):
  cvt t2 sx v = Some v' ->
  types_agree t1 v ->
  Φ (immV [v']) ⊢
    WP [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros (Hcvtop Htype) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v')], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_convert_success.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H [AI_basic (BI_const v) ; AI_basic (BI_cvtop t2 CVO_convert t1 sx)]
                       locs inst locs' inst'.
    rewrite Hcvtop in H0. inversion H0 ; inversion Heqf' ; subst ; iFrame ;done.
    rewrite Hcvtop in H0 ; inversion H0.
Qed.

Lemma wp_cvtop_reinterpret (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v v': value) (t1 t2: value_type):
  wasm_deserialise (bits v) t2 = v' ->
  types_agree t1 v ->
  Φ (immV [v']) ⊢
    WP [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros (Hcvtop Htype) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v')], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_reinterpret.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H [AI_basic (BI_const v) ;
                          AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)]
                       locs inst locs' inst'.
Qed.

(* Non-numerics -- stack operations, control flows *)

Lemma wp_nop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ):
  Φ (immV []) ⊢
    WP [AI_basic (BI_nop)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_nop.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    only_one_reduction H [AI_basic (BI_nop)] locs inst locs' inst'.
Qed.




Lemma wp_drop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) v :
  Φ (immV []) ⊢ WP [AI_basic (BI_const v) ; AI_basic BI_drop] @ s; E {{ w, Φ w }}.
Proof.
  iIntros "HΦ".
  iApply wp_lift_atomic_step. simpl ; trivial.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [], σ, [].
    destruct σ as [[[ hs ws ] locs ] inst ].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple ; apply rs_drop.
  - destruct σ as [[[ hs ws ] locs ] inst ].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[ hs' ws' ] locs' ] inst'].
    destruct HStep as (H & -> & ->).
    only_one_reduction H [AI_basic (BI_const v); AI_basic BI_drop] locs inst locs' inst'. 
Qed.

Lemma wp_select_false (s: stuckness) (E :coPset) (Φ : val -> iProp Σ) n v1 v2 :
  n = Wasm_int.int_zero i32m ->
  Φ (immV [v2]) ⊢ WP [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                      AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_select) ] @ s;
E {{ w, Φ w }}.
Proof.
  iIntros (Hn) "HΦ".
  iApply wp_lift_atomic_step. simpl ; trivial.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v2)], σ, [].
    destruct σ as [[[ hs ws ] locs ] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply r_simple ; by apply rs_select_false.
  - destruct σ as [[[ hs ws ] locs ] inst ].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[ hs' ws' ] locs' ] inst'].
    destruct HStep as (H & -> & ->).
    only_one_reduction H [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                          AI_basic (BI_const (VAL_int32 n)) ; AI_basic BI_select]
                       locs inst locs' inst'.
Qed.

Lemma wp_select_true (s: stuckness) (E : coPset) (Φ: val -> iProp Σ) n v1 v2 :
  n <> Wasm_int.int_zero i32m ->
  Φ (immV [v1]) ⊢ WP [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                      AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_select) ] @ s;
E {{ w, Φ w }}.
Proof.
  iIntros (Hn) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro. destruct s => //=. unfold language.reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v1)], σ, [].
    destruct σ as [[[ hs ws ] locs ] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply r_simple ; by apply rs_select_true.
  - destruct σ as [[[ hs ws ] locs ] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[ hs' ws' ] locs' ] inst'].
    destruct HStep as (H & -> & ->).
    only_one_reduction H [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ;
                          AI_basic (BI_const (VAL_int32 n)) ; AI_basic BI_select]
                       locs inst locs' inst'.
Qed.
    
(* Control flows *)

            
               

Fixpoint labels e :=
  match e with
  | AI_label _ _ LI => S (list_sum (map labels LI))
  | _ => 0
  end .
Definition amount_of_labels es := list_sum (map labels es).

Lemma amount_of_labels_app l1 l2 :
  amount_of_labels (app l1 l2) = amount_of_labels l1 + amount_of_labels l2.
Proof.
  unfold amount_of_labels. rewrite map_app. rewrite list_sum_app. done.  
Qed. 
  
(*
Fixpoint depth e :=
  match e with
  | AI_label _ _ LI => fold_left (fun d e => max d (depth e)) LI 0
  | _ => 0
  end .

Definition maximum_depth es := fold_left (fun d e => max d (depth e)) es 0. 
*)
(*
Fixpoint flatten_labels es :=
  match es with
  | [] => []
  | AI_label n es LI :: q => flatten_labels LI ++ flatten_labels q
  | t :: q => t :: flatten_labels q
  end .

Inductive amount_of_labels : (seq.seq administrative_instruction) -> nat -> Prop :=
| NilLabels : amount_of_labels [] 0
| LabelLabels : forall n es LI q kLI kq,
    amount_of_labels LI kLI ->
    amount_of_labels q kq ->
    amount_of_labels (AI_label n es LI :: q) (S (kLI + kq))
| BasicLabels : forall a q k, amount_of_labels q k -> amount_of_labels (AI_basic a :: q) k 
| TrapLabels : forall q k, amount_of_labels q k -> amount_of_labels (AI_trap :: q) k 
| InvokeLabels : forall a q k, amount_of_labels q k -> amount_of_labels (AI_invoke a :: q) k
| LocalLabels : forall a b c q k, amount_of_labels q k ->
                             amount_of_labels (AI_local a b c :: q) k.

Lemma got_an_amount i lh es LI kes :
  amount_of_labels es kes -> lfilled i lh es LI -> exists k, amount_of_labels LI k.
  intros Hes Hfill.  cut (forall n, length LI < n -> exists k, amount_of_labels LI k).
  { intro H ; assert (length LI < S (length LI)) as Hlen ;
      [ lia | by apply (H (S (length LI)) Hlen)]. }
  intros n Hlen. generalize dependent LI ; generalize dependent i ;
                   generalize dependent lh ; generalize dependent es ;
                   induction n ; intros es Hes lh i LI Hfill Hlen.
  { exfalso ; lia. } 
  induction i.
  unfold lfilled, lfill in Hfill.
  destruct lh ; last by false_assumption.
  remember (const_list l) as b.
  destruct b ; last by false_assumption.
  apply b2p in Hfill.
  assert (amount_of_labels (l ++ es) kes). {
    clear Hfill. induction l => //=.
(*    generalize dependent LI ; induction l ; intros LI Hfill.
    { simpl in Hfill ; rewrite app_nil_r in Hfill ; by subst. }
    destruct LI ; inversion Hfill. *)
    unfold const_list in Heqb. simpl in Heqb. apply Logic.eq_sym in Heqb.
    apply andb_true_iff in Heqb as [Ha Hl]. unfold is_const in Ha.
    destruct a ; try by false_assumption. apply BasicLabels.
    apply IHl => //=. }
  destruct l0 ; first by (rewrite app_nil_r in Hfill ; subst ; exists kes).
  apply (IHn es Hes (LH_base l []) 0).
  
  

Lemma got_an_amount es : exists k, amount_of_labels es k.
  induction es. { exists 0. exact NilLabels. }
  destruct IHes as [k Hlab].
  induction Hlab.
  exists k ; by apply BasicLabels.
  exists k ; by apply TrapLabels.
  exists k ; by apply InvokeLabels.
  
  
 

Fixpoint depth e :=
  match e with
    | AI_label _ _ LI ->  *)

Lemma wp_br (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n vs es i LI lh :
  const_list vs ->
  length vs = n ->
  lfilled i lh (vs ++ [::AI_basic (BI_br i)]) LI ->
  ▷ WP (vs ++ es) @ s; E {{ Φ }}
  ⊢ WP [AI_label n es LI] @ s; E {{ Φ }}.
Proof.
  iIntros (Hvs Hlen Hfill) "HΦ".
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  - iPureIntro. destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], (vs ++ es), σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    constructor. econstructor =>//.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    Admitted. (* attempt at removing reduce_det, work in progress
    only_one_reduction H [AI_label n es LI] locs inst locs' inst'.
    + simple_filled Hfill i lh bef aft n l l'.
      * found_intruse (AI_basic (BI_br 0)) Hfill Hxl1.
        -- by intruse_among_values vs0 Hxl1 H.
        -- apply in_or_app. right. apply in_or_app. left.
           apply in_or_app. right. left. done.
      * by intruse_among_values vs0 Hxl1 H.
    + simple_filled Hfill i lh bef aft n l l'.
      found_intruse (AI_basic (BI_br 0)) Hfill Hxl1.
      apply in_or_app ; right. apply in_or_app ; left.
      apply in_or_app ; right ; left ; done.
    + cut (forall n lh0 lh i0 i0' i i' LI0,
              lfilled i0 lh0 (vs0 ++ [AI_basic (BI_br i0')]) LI0 ->
              lfilled i lh (vs ++ [AI_basic (BI_br i')]) LI0 ->
              amount_of_labels LI0 < n ->
              vs = vs0).
      intro Hn ; assert (amount_of_labels LI0 < S (amount_of_labels LI0)) as Hlen ;
        [ lia |
          by rewrite (Hn (S (amount_of_labels LI0)) lh0 lh i0 i0 i i LI0
                         H1 Hfill Hlen) ; inversion Heqf' ; subst ; iFrame].
      clear Heqes. 
      intro n. 
      induction n ;
        intros lh1 lh2 i1 i1' i2 i2' LI Hfill1 Hfill2 Hlen ; first ( exfalso ; lia ).
      unfold lfilled, lfill in Hfill2. destruct i2.
      { destruct lh2 as [bef2 aft2|] ; last by false_assumption.
        remember (const_list bef2) as b eqn:Hbef2.
        destruct b ; last by false_assumption.
        apply b2p in Hfill2.
        unfold lfilled, lfill in Hfill1 ; destruct i1.
        { destruct lh1 as [bef1 aft1|] ; last by false_assumption.
          remember (const_list bef1) as b0 eqn:Hbef1.
          destruct b0 ; last by false_assumption.
          apply b2p in Hfill1.
          rewrite Hfill2 in Hfill1. do 2 rewrite <- app_assoc in Hfill1.
          rewrite app_assoc in Hfill1. rewrite (app_assoc bef1 _ _) in Hfill1.
          apply first_values in Hfill1 as [Hvv _] ; try done ;
            try by unfold const_list ; rewrite forallb_app ; apply andb_true_iff.
          by apply app_inj_2 in Hvv as [_ ?]. }
        fold lfill in Hfill1. destruct lh1 ; first by false_assumption.
        remember (const_list l) as b.
        destruct b ; last by false_assumption.
        destruct (lfill i1 lh1 _) ; last by false_assumption.
        apply b2p in Hfill1. rewrite Hfill2 in Hfill1.
        rewrite <- app_assoc in Hfill1. rewrite app_assoc in Hfill1.
        apply first_values in Hfill1 as [ _ Habs ] => //=.
        unfold const_list ; rewrite forallb_app ; by apply andb_true_iff. }
      fold lfill in Hfill2. 
      destruct lh2 as [| bef2 n2 l2 lh2 aft2] ; first by false_assumption.
      remember (const_list bef2) as b ; destruct b ; last by false_assumption.
      remember (lfill i2 lh2 (vs ++ [AI_basic (BI_br i2')])) as les.
      destruct les ; last by false_assumption.
      apply b2p in Hfill2.
      unfold lfilled, lfill in Hfill1 ; destruct i1.
      { destruct lh1 as [bef1 aft1 |] ; last by false_assumption.
        remember (const_list bef1) as b ; destruct b ; last by false_assumption.
        apply b2p in Hfill1. rewrite Hfill2 in Hfill1.
        rewrite <- app_assoc in Hfill1. rewrite app_assoc in Hfill1.
        apply first_values in Hfill1 as [ _ Habs ] => //=.
        unfold const_list ; rewrite forallb_app ; by apply andb_true_iff. }
      fold lfill in Hfill1.
      destruct lh1 as [| bef1 n1 l1 lh1 aft1] ; first by false_assumption.
      remember (const_list bef1) as b ; destruct b ; last by false_assumption.
      remember (lfill i1 lh1 (vs0 ++ [AI_basic (BI_br i1')])) as les0.
      destruct les0 ; last by false_assumption.
      apply b2p in Hfill1. rewrite Hfill2 in Hfill1.
      apply first_values in Hfill1 as [ Hl Hlab ] => //=.
      inversion Hlab ; subst.
      apply (IHn lh1 lh2 i1 i1' i2 i2' l0) => //=.
      unfold lfilled ; rewrite <- Heqles0 ; done.
      unfold lfilled ; rewrite <- Heqles ; done.
      rewrite amount_of_labels_app in Hlen.
      assert (AI_label n1 l1 l0 :: aft2 = [AI_label n1 l1 l0] ++ aft2) as Heq => //=.
      rewrite Heq in Hlen. rewrite amount_of_labels_app in Hlen. simpl in Hlen.
      rewrite Nat.add_0_r in Hlen. rewrite <- Nat.add_succ_l in Hlen.
      fold (amount_of_labels l0) in Hlen. lia.
    + iDestruct "Hσ" as "( ? & ? & ? & ? & ? & ? & ? )". iFrame. unfold lfilled in Hfill ; destruct i.
      { unfold lfill in Hfill.
        destruct lh as [bef0 aft0|] ; last by false_assumption.
        remember (const_list bef0) as b eqn:Hbef0.
        destruct b ; last by false_assumption.
        apply b2p in Hfill. subst.
        destruct bef ;
          last by (inversion H1 as [[ Hhd Htl ]] ;
                   found_intruse (AI_label n0 l l0) Htl Hxl1).
        inversion H1 ; subst.
        unfold lfilled in H2.
        remember (lfill (S k) (LH_rec [] (length vs) l lh1 []) _) as les. 
        destruct les ; last by false_assumption. apply b2p in H2. subst.
        unfold lfill in Heqles. destruct (const_list []) ; try by false_assumption.
        destruct k. { destruct lh1 as [bef1 aft1|] ; last by inversion Heqles.
                      remember (const_list bef1) as b eqn:Hbef1.
                      destruct b ; inversion Heqles.
                      unfold lfill in Heqles1.
                      rewrite <- Hbef1 in Heqles1. inversion Heqles1.
      
      
     
      



Admitted. *)

      
Lemma wp_block (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs es n m t1s t2s :
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ▷ WP [::AI_label m [::] (vs ++ to_e_list es)] @ s; E {{ Φ }}
  ⊢ WP (vs ++ [::AI_basic (BI_block (Tf t1s t2s) es)]) @ s; E {{ Φ }}.
Proof.
  iIntros (Hvs Hlen1 Hlen2 Hlen3) "HΦ".
  iApply wp_lift_step => //=.
  apply to_val_cat_None2. done.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  - iPureIntro. destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], _, σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    constructor. econstructor =>//.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H; last by eapply r_simple, rs_block.
    inversion H; subst; clear H.
    by iFrame.
Qed.

Lemma wp_label_value (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es m ctx v :
  iris.to_val es = Some (immV v) -> 
  Φ (immV v) ⊢ WP [::AI_label m ctx es] @ s; E {{ Φ }}.
Proof.
  iIntros (Hval) "HP".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], es, σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.  apply rs_label_const.
    eapply to_val_const_list. apply Hval.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es1 σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H.
    2: { apply r_simple.  apply rs_label_const.
         eapply to_val_const_list. apply Hval. }
    inversion H; subst; clear H.
    rewrite Hval. by iFrame.
Qed.
Lemma wp_label_trap (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es m ctx :
  iris.to_val es = Some trapV -> 
  Φ trapV ⊢ WP [::AI_label m ctx es] @ s; E {{ Φ }}.
Proof.
  iIntros (Hval) "HP".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [AI_trap], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply to_val_trap_is_singleton in Hval as ->.
    apply r_simple.  apply rs_label_trap.
  - apply to_val_trap_is_singleton in Hval as ->.
    destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es1 σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H.
    2: { apply r_simple.  apply rs_label_trap. }
    inversion H; subst; clear H.
    by iFrame.
Qed.

Lemma wp_val_return (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs vs' es' es'' n :
  const_list vs ->
  WP vs' ++ vs ++ es'' @ s; E {{ Φ }}
  ⊢ WP vs @ s; E CTX 1; LH_rec vs' n es' (LH_base [] []) es'' {{ Φ }}.
Proof.
  iIntros (Hconst) "HWP".
  iLöb as "IH".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  inversion Hfill;subst.
  inversion H8;subst.
  assert (vs' ++ [AI_label n es' ([] ++ vs ++ [])] ++ es''
          = ((vs' ++ [AI_label n es' ([] ++ vs ++ [])]) ++ es''))%SEQ as ->.
  { erewrite app_assoc. auto. }
  apply const_list_is_val in Hconst as [v1 Hv1].
  apply const_list_is_val in H7 as [v2 Hv2].
  eapply to_val_cat_inv in Hv1 as Hvv;[|apply Hv2].
  iApply (wp_seq_nontrap _ _ Φ (λ ret, ⌜ret = immV (v2 ++ v1)⌝)%I).
  iSplit => //.
  iSplitR.
  iApply wp_val_app; first by apply Hv2.
  iApply wp_label_value;[|auto]. erewrite app_nil_l. erewrite app_nil_r. apply Hv1.
  iIntros (w ->). erewrite of_to_val;[|apply Hvv]. rewrite app_assoc. auto.
Qed.

Lemma wp_base (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs vs' es'' :
  const_list vs ->
  WP vs' ++ vs ++ es'' @ s; E {{ Φ }}
  ⊢ WP vs @ s; E CTX 0; LH_base vs' es'' {{ Φ }}.
Proof.
  iIntros (Hconst) "HWP".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  inversion Hfill;subst. iFrame.
Qed.

Fixpoint push_base (lh : lholed) n es' vs_pre es_post :=
  match lh with
  | LH_base vs_pre' es_post' => LH_rec vs_pre' n es' (LH_base vs_pre es_post) es_post'
  | LH_rec vs m es'' lh' es => LH_rec vs m es'' (push_base lh' n es' vs_pre es_post) es
  end.

Fixpoint frame_base (lh : lholed) l1 l2 :=
  match lh with
  | LH_base vs es => LH_base (vs ++ l1) (l2 ++ es)
  | LH_rec vs m es' lh' es => LH_rec vs m es' (frame_base lh' l1 l2) es
  end.

Lemma lfilledInd_push i : ∀ lh n es' es LI l1 l2,
  const_list l1 ->
  lfilledInd i lh ([::AI_label n es' (l1 ++ es ++ l2)]) LI ->
  lfilledInd (S i) (push_base lh n es' l1 l2) es LI.
Proof.
  induction i.
  all: intros lh n es' es LI l1 l2 Hconst Hfill.
  { inversion Hfill;subst.
    constructor. auto. constructor. auto.
    (* apply lfilled_Ind_Equivalent. cbn. rewrite eqseqE app_nil_r. done.  *)}
  { inversion Hfill;subst. simpl. constructor. auto.
    apply IHi. auto. auto. }
Qed.
Lemma lfilledInd_frame i : ∀ lh l1 es l2 LI,
    const_list l1 ->
    lfilledInd i lh (l1 ++ es ++ l2) LI ->
    lfilledInd i (frame_base lh l1 l2) (es) LI.
Proof.
  induction i.
  all: intros lh l1 es l2 LI Hconst Hfill.
  { inversion Hfill;subst.
    assert (vs ++ (l1 ++ es ++ l2) ++ es'
            = (vs ++ l1) ++ es ++ (l2 ++ es'))%SEQ as ->.
    { repeat erewrite app_assoc. auto. }
    constructor. apply const_list_concat;auto. }
  { inversion Hfill;subst. simpl. constructor. auto.
    apply IHi. auto. auto. }
Qed.
      

Lemma wp_base_push (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es l1 l2 i lh :
  const_list l1 ->
  WP es @ s; E CTX i; frame_base lh l1 l2 {{ Φ }}
  ⊢ WP l1 ++ es ++ l2 @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hconst) "HWP".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  apply lfilledInd_frame in Hfill.
  iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
  iPureIntro. by apply lfilled_Ind_Equivalent. auto.
Qed.
Lemma wp_label_push (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es i lh n es' l1 l2 :
  const_list l1 ->
  WP es @ s; E CTX S i; push_base lh n es' l1 l2 {{ Φ }}
  ⊢ WP [::AI_label n es' (l1 ++ es ++ l2)] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hconst) "HWP".
  iIntros (LI Hfill%lfilled_Ind_Equivalent).
  apply lfilledInd_push in Hfill.
  iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
  iPureIntro. by apply lfilled_Ind_Equivalent. auto.
Qed.
Lemma wp_label_push_nil (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) es i lh n es' :
  WP es @ s; E CTX S i; push_base lh n es' [] [] {{ Φ }}
  ⊢ WP [::AI_label n es' es] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros "HWP".
  iDestruct (wp_label_push with "HWP") as "HWP". auto.
  erewrite app_nil_l. erewrite app_nil_r. done.
Qed.

Lemma lfilled_to_val i  :
  ∀ lh es LI, is_Some (iris.to_val LI) ->
  lfilled i lh es LI ->
  is_Some (iris.to_val es).
Proof.
  induction i.
   { intros lh es LI [x Hsome] Hfill.
    apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill;subst.
    destruct (to_val es) eqn:Hnone;eauto.
    exfalso.
    apply (to_val_cat_None1 _ es') in Hnone.
    apply (to_val_cat_None2 vs) in Hnone.
    rewrite Hnone in Hsome. done.
  }
  { intros lh es LI Hsome Hfill.
    apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill;simplify_eq.
    clear -Hsome. exfalso.
    induction vs =>//=.
    simpl in Hsome. by inversion Hsome.
    simpl in Hsome; inversion Hsome.
    destruct a =>//=.
    destruct b =>//=.
    destruct (iris.to_val (vs ++ [AI_label n es' LI0] ++ es'')%SEQ) eqn:Hcontr.
    apply IHvs;eauto.
    rewrite Hcontr in H. done.
    destruct vs;done.
  }
Qed.

Lemma wp_block_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (i : nat) (lh : lholed) vs t1s t2s es n m :
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ▷ WP [::AI_label m [::] (vs ++ to_e_list es)] @ s; E CTX i; lh {{ Φ }}
  ⊢ WP (vs ++ [::AI_basic (BI_block (Tf t1s t2s) es)]) @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hconst Hn Hn' Hm) "HWP".
  iIntros (LI Hfill).
  destruct (iris.to_val LI) eqn:Hcontr.
  { apply lfilled_to_val in Hfill as [v' Hv];eauto.
    assert (iris.to_val [AI_basic (BI_block (Tf t1s t2s) es)] = None) as Hnone;auto.
    apply (to_val_cat_None2 vs) in Hnone.
    rewrite Hv in Hnone. done. }
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  { iPureIntro. destruct s;auto.
    apply lfilled_swap with (es':=[::AI_label m [::] (vs ++ to_e_list es)]) in Hfill as Hfill'.
    destruct Hfill' as [LI' Hfill'].
    eexists [],_,σ,[]. simpl.
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple. eapply rs_block.
    apply Hconst. apply Hn. apply Hn'. apply Hm. eauto. eauto. }
  destruct σ as [[[hs ws] locs] inst] => //=.
  iApply fupd_mask_intro;[solve_ndisj|].
  iIntros "Hcls !>" (es1 σ2 efs HStep).
  iMod "Hcls". iModIntro.
  destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
  apply lfilled_swap with (es':=[::AI_label m [::] (vs ++ to_e_list es)]) in Hfill as Hfill'.
  destruct Hfill' as [LI' Hfill'].
  destruct HStep as [H [-> ->]].
  eapply reduce_det in H; cycle 1.
  { eapply r_label. apply r_simple. eapply rs_block;eauto. all: eauto. }
  inversion H; subst; clear H.
  iFrame. iSplit;[|done].
  iSpecialize ("HWP" $! _ Hfill'). iFrame.
Qed.

Lemma wp_br_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n vs es i lh vs' es' :
  const_list vs ->
  length vs = n ->
  ▷ WP (vs' ++ vs ++ es ++ es') @ s; E {{ Φ }}
  ⊢ WP vs ++ [::AI_basic (BI_br i)] @ s; E CTX S i; LH_rec vs' n es lh es' {{ Φ }}.
Proof.
  iIntros (Hvs Hlen) "HΦ".
  iIntros (LI Hfill).
  destruct (iris.to_val LI) eqn:Hcontr.
  { apply lfilled_to_val in Hfill as [v' Hv];eauto.
    assert (iris.to_val [AI_basic (BI_br i)] = None) as Hnone;auto.
    apply (to_val_cat_None2 (vs)) in Hnone.
    rewrite Hv in Hnone. done. }
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplit.
  { apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;subst.
    iPureIntro. destruct s;auto.
    apply lfilled_Ind_Equivalent in H8 as Hfill'.
    apply lfilled_swap with (es':=vs ++ es) in Hfill' as Hfill''.
    destruct Hfill'' as [LI' Hfill''].    
    eexists [],_,σ,[].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.   
    eapply r_label with (lh:=(LH_base vs' es')).
    2: { erewrite cons_middle. apply lfilled_Ind_Equivalent.
         econstructor;auto. }
    2: { apply lfilled_Ind_Equivalent. econstructor;auto. }
    apply r_simple. eapply rs_br.
    apply Hvs. auto. eauto. }
  destruct σ as [[[hs ws] locs] inst] => //=.
  iApply fupd_mask_intro;[solve_ndisj|].
  iIntros "Hcls !>" (es1 σ2 efs HStep).
  iMod "Hcls". iModIntro.
  destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
  apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;subst.
  apply lfilled_Ind_Equivalent in H8 as Hfill'.
  apply lfilled_swap with (es':=vs ++ es) in Hfill' as Hfill''.
  destruct Hfill'' as [LI' Hfill''].    
  destruct HStep as [H [-> ->]].
  eapply reduce_det in H; cycle 1.
  { eapply r_label with (lh:=(LH_base vs' es')).
    2: { apply lfilled_Ind_Equivalent.
         econstructor;auto. }
    2: { apply lfilled_Ind_Equivalent. econstructor;auto. }
    apply r_simple. eapply rs_br. apply Hvs. all:eauto. }
  inversion H; subst; clear H.
  iFrame. iSplit;[|done].
  erewrite !app_assoc. iFrame.
Qed.

Lemma wp_loop_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs es n m t1s t2s i lh :
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ▷ WP [::AI_label n [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)] @ s; E CTX i; lh {{ Φ }}
  ⊢ WP vs ++ [::AI_basic (BI_loop (Tf t1s t2s) es)] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hvs Hn Hn' Hm) "HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iDestruct ("HP" $! _ Hfill') as "HP".
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill].
    assert (iris.to_val [AI_basic (BI_loop (Tf t1s t2s) es)] = None) as HH;auto.
    apply (to_val_cat_None2 vs) in HH. rewrite Hfill in HH. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. eapply rs_loop;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H.
    2: { eapply r_label. apply r_simple;eauto. eapply rs_loop;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    by iFrame.
Qed.
Lemma wp_loop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs es n m t1s t2s :
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  ▷ WP [::AI_label n [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)] @ s; E {{ Φ }}
  ⊢ WP vs ++ [::AI_basic (BI_loop (Tf t1s t2s) es)] @ s; E {{ Φ }}.
Proof.
  iIntros (Hvs Hn Hn' Hm) "HP".
  iApply wp_wasm_empty_ctx. iApply wp_loop_ctx;eauto.
  iNext. iApply wp_wasm_empty_ctx. iFrame.
Qed.

Lemma wp_if_true_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s i lh :
  n ≠ Wasm_int.int_zero i32m ->
  ▷ WP [::AI_basic (BI_block tf e1s)] @ s; E CTX i; lh {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hn) "HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iDestruct ("HP" $! _ Hfill') as "HP".
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. eapply rs_if_true;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H.
    2: { eapply r_label. apply r_simple;eauto. eapply rs_if_true;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    by iFrame.
Qed.
Lemma wp_if_true (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s :
  n ≠ Wasm_int.int_zero i32m ->
  ▷ WP [::AI_basic (BI_block tf e1s)] @ s; E {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E {{ Φ }}.
Proof.
  iIntros (?) "HP".
  iApply wp_wasm_empty_ctx. iApply wp_if_true_ctx;eauto.
  iNext. iApply wp_wasm_empty_ctx. iFrame.
Qed.
  
Lemma wp_if_false_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s i lh :
  n = Wasm_int.int_zero i32m ->
  ▷ WP [::AI_basic (BI_block tf e2s)] @ s; E CTX i; lh {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E CTX i; lh {{ Φ }}.
Proof.
  iIntros (Hn) "HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iDestruct ("HP" $! _ Hfill') as "HP".
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. eapply rs_if_false;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H.
    2: { eapply r_label. apply r_simple;eauto. eapply rs_if_false;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    by iFrame.
Qed.
Lemma wp_if_false (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n tf e1s e2s :
  n = Wasm_int.int_zero i32m ->
  ▷ WP [::AI_basic (BI_block tf e2s)] @ s; E {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] @ s; E {{ Φ }}.
Proof.
  iIntros (?) "HP".
  iApply wp_wasm_empty_ctx. iApply wp_if_false_ctx;eauto.
  iNext. iApply wp_wasm_empty_ctx. iFrame.
Qed.

Lemma wp_br_if_true_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n i j lh :
  n ≠ Wasm_int.int_zero i32m ->
  ▷ WP [::AI_basic (BI_br i)] @ s; E CTX j; lh {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] @ s; E CTX j; lh {{ Φ }}.
Proof.
  iIntros (Hn) "HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iDestruct ("HP" $! _ Hfill') as "HP".
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. eapply rs_br_if_true;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H.
    2: { eapply r_label. apply r_simple;eauto. eapply rs_br_if_true;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    by iFrame.
Qed.
Lemma wp_br_if_true (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n i :
  n ≠ Wasm_int.int_zero i32m ->
  ▷ WP [::AI_basic (BI_br i)] @ s; E {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] @ s; E {{ Φ }}.
Proof.
  iIntros (?) "HP".
  iApply wp_wasm_empty_ctx. iApply wp_br_if_true_ctx;eauto.
  iNext. iApply wp_wasm_empty_ctx. iFrame.
Qed.

(* The following expression reduces to a value reguardless of context, 
   and thus does not need a context aware version *)
Lemma wp_br_if_false (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) n i :
  n = Wasm_int.int_zero i32m ->
  ▷ Φ (immV [])
  ⊢ WP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] @ s; E {{ Φ }}.
Proof.
  iIntros (Hn) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [], σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_br_if_false.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H; last by apply r_simple, rs_br_if_false.
    inversion H; subst; clear H.
    by iFrame.
Qed.


Lemma wp_br_table_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i j k lh :
  ssrnat.leq (S (Wasm_int.nat_of_uint i32m c)) (length iss) ->
  List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
  ▷ WP [::AI_basic (BI_br j)] @ s; E CTX k; lh {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E CTX k; lh {{ Φ }}.
Proof.
  iIntros (Hiss Hj) "HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iDestruct ("HP" $! _ Hfill') as "HP".
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. apply rs_br_table;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H.
    2: { eapply r_label. apply r_simple;eauto. eapply rs_br_table;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    by iFrame.
Qed.
Lemma wp_br_table (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i j :
  ssrnat.leq (S (Wasm_int.nat_of_uint i32m c)) (length iss) ->
  List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
  ▷ WP [::AI_basic (BI_br j)] @ s; E {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E {{ Φ }}.
Proof.
  iIntros (? ?) "HP".
  iApply wp_wasm_empty_ctx. iApply wp_br_table_ctx;eauto.
  iNext. iApply wp_wasm_empty_ctx. iFrame.
Qed.

Lemma wp_br_table_length_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i j lh :
  ssrnat.leq (length iss) (Wasm_int.nat_of_uint i32m c) ->
  ▷ WP [::AI_basic (BI_br i)] @ s; E CTX j; lh {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E CTX j; lh {{ Φ }}.
Proof.
  iIntros (Hiss) "HP".
  iIntros (LI Hfill).
  eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
  iDestruct ("HP" $! _ Hfill') as "HP".
  iApply wp_lift_step => //=.
  { destruct (iris.to_val LI) eqn:Hcontr;auto.
    apply lfilled_to_val in Hfill;eauto.
    destruct Hfill as [? Hfill]. simpl in Hfill. done. }
  iIntros (σ ns κ κs nt) "Hσ".
  iApply fupd_frame_l.
  iSplitR.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [], LI', σ, [].
    destruct σ as [[[hs ws] locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_label. apply r_simple;eauto. apply rs_br_table_length;eauto.
    eauto. eauto.
  - destruct σ as [[[hs ws] locs] inst] => //=.
    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 σ2 efs HStep).
    iMod "Hcls". iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H.
    2: { eapply r_label. apply r_simple;eauto. eapply rs_br_table_length;eauto.
         eauto. eauto. }
    inversion H; subst; clear H.
    by iFrame.
Qed.
Lemma wp_br_table_length (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) iss c i :
  ssrnat.leq (length iss) (Wasm_int.nat_of_uint i32m c) ->
  ▷ WP [::AI_basic (BI_br i)] @ s; E {{ Φ }}
  ⊢ WP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] @ s; E {{ Φ }}.
Proof.
  iIntros (?) "HP".
  iApply wp_wasm_empty_ctx. iApply wp_br_table_length_ctx;eauto.
  iNext. iApply wp_wasm_empty_ctx. iFrame.
Qed.

 (*| rs_return :
      forall n i vs es lh f,
        const_list vs ->
        length vs = n ->
        lfilled i lh (vs ++ [::AI_basic BI_return]) es ->
        reduce_simple [::AI_local n f es] vs*)
(* return is a contextual rule, but it is also a function rule. Before we tackle with wp, 
   we must have set up the way in which to handle AI_local. 
   intuitively, AI_local functions as a fresh bind, in a fresh ctx, very similar to wp_seq_ctx 
   solution idea: another WP now that can abstract away the AI_local "wrapper", using AI_local 
   instead of AI_label. Note that AI_label and contexts can still occur within an AI_local....
   Main difference is that AI_local is not nested in the same way as label, in which label 
   knows about the nesting structure for br, whereas local "stops" br from exiting.

   Why is there a need for a new WP? because there can be a nested label structure inside a 
   label, and we need to have knowledge of that for the return instruction. The label wrapper
   is always the outermost layer! so current ctxWP does not work for that reason.
*)

                      
Lemma wp_return: False.
Proof.
Admitted.

(* --------------------------------------------------------------------------------------------- *)
(* -------------------------------- CONTROL FLOW EXAMPLES -------------------------------------- *)
(* --------------------------------------------------------------------------------------------- *)

(* Helper lemmas and tactics for necessary list manipulations for expressions *)
Lemma iRewrite_nil_l (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (e : iris.expr) :
  (WP [] ++ e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Φ }}).
Proof. rewrite app_nil_l. auto. Qed.
Lemma iRewrite_nil_r (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (e : iris.expr) :
  (WP e ++ [] @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Φ }}).
Proof. rewrite app_nil_r. auto. Qed.
Lemma iRewrite_nil_l_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (e : iris.expr) i lh :
  (WP [] ++ e @ s; E CTX i; lh {{ Φ }} ⊢ WP e @ s; E CTX i; lh {{ Φ }}).
Proof. rewrite app_nil_l. auto. Qed.
Lemma iRewrite_nil_r_ctx (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (e : iris.expr) i lh :
  (WP e ++ [] @ s; E CTX i; lh {{ Φ }} ⊢ WP e @ s; E CTX i; lh {{ Φ }}).
Proof. rewrite app_nil_r. auto. Qed.

Ltac take_drop_app_rewrite n :=
  match goal with
  | |- context [ WP ?e @ _; _ CTX _; _ {{ _ }} %I ] =>
      rewrite -(take_drop n e);simpl take; simpl drop
  | |- context [ WP ?e @ _; _ {{ _ }} %I ] =>
      rewrite -(take_drop n e);simpl take; simpl drop
  end.

Ltac take_drop_app_rewrite_twice n m :=
  take_drop_app_rewrite n;
  match goal with
  | |- context [ WP _ ++ ?e @ _; _ CTX _; _ {{ _ }} %I ] =>
      rewrite -(take_drop (length e - m) e);simpl take; simpl drop
  | |- context [ WP _ ++ ?e @ _; _ {{ _ }} %I ] =>
      rewrite -(take_drop (length e - m) e);simpl take; simpl drop
  end.

(* Examples of blocks that return normally *)
Lemma label_check_easy :
  ⊢ WP [::AI_basic
         (BI_block (Tf [] [T_i32;T_i32])
            [::BI_const (xx 2); BI_const (xx 3)] )] {{ λ v, ⌜v = immV [xx 2;xx 3]⌝ }}.
Proof.
  rewrite -iRewrite_nil_l.
  iApply wp_block;eauto. iNext.
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil. simpl.
  iApply wp_val_return;auto.
  iApply wp_value;eauto. done.
Qed.
Lemma label_check_easy' :
  ⊢ WP [::AI_basic
         (BI_block (Tf [] [T_i32;T_i32])
                   [:: (BI_block (Tf [] [T_i32;T_i32])
                                [::BI_const (xx 2); BI_const (xx 3)] )] )] {{ λ v, ⌜v = immV [xx 2;xx 3]⌝ }}.
Proof.
  rewrite -iRewrite_nil_l.
  iApply wp_block;eauto. iNext.
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil. simpl.
  iApply iRewrite_nil_r_ctx.
  iApply (wp_seq_ctx _ _ _ (λ v, ⌜v = immV [xx 2; xx 3]⌝)%I).
  iSplitR.
  iApply label_check_easy.
  iIntros (w ->). simpl.
  iApply wp_val_return;auto.
  iApply wp_value;eauto. done.
Qed.

Lemma br_check_bind_return :
  ⊢ WP [::AI_basic
         (BI_block (Tf [] [T_i32])
         [:: BI_block (Tf [] [])
            [::BI_const (xx 3); BI_br 1] ])] {{ λ v, ⌜v = immV [xx 3]⌝ }}.
Proof.
  iApply iRewrite_nil_l.
  iApply wp_block;eauto. iNext.
  simpl.
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil.
  simpl.
  iApply iRewrite_nil_l_ctx.
  iApply wp_block_ctx;eauto. iNext.
  simpl.
  iApply wp_label_push_nil.
  simpl.
  take_drop_app_rewrite 1.
  iApply wp_br_ctx;auto. iNext.
  iApply wp_value;auto. done.
Qed.

Lemma br_check_bind_return_2 :
  ⊢ WP [::AI_basic
         (BI_block (Tf [] [T_i32])
         [:: BI_block (Tf [] [])
            [::BI_const (xx 2);BI_const (xx 3); BI_br 1] ])] {{ λ v, ⌜v = immV [xx 3]⌝ }}.
Proof.
  iApply iRewrite_nil_l.
  iApply wp_block;eauto. iNext.
  simpl.
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil.
  simpl.
  iApply iRewrite_nil_l_ctx.
  iApply wp_block_ctx;eauto. iNext.
  simpl.
  iApply wp_label_push_nil.
  simpl.
  take_drop_app_rewrite 1.
  iApply iRewrite_nil_r_ctx.
  rewrite -app_assoc.
  iApply wp_base_push;auto.
  take_drop_app_rewrite 1.
  iApply wp_br_ctx;auto. iNext.
  iApply wp_value;auto. done.
Qed.

Lemma br_check_bind_return_3 :
  ⊢ WP [::AI_basic
         (BI_block (Tf [] [T_i32])
         [:: BI_block (Tf [] [])
            [::BI_const (xx 2); BI_const (xx 3); (BI_binop T_i32 (Binop_i BOI_add)); BI_br 1] ])] {{ λ v, ⌜v = immV [xx 5]⌝ }}.
Proof.
  iApply iRewrite_nil_l.
  iApply wp_block;eauto. iNext. simpl.
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil.
  iApply iRewrite_nil_l_ctx.
  iApply wp_block_ctx;eauto;simpl.
  iApply wp_label_push_nil. iNext. simpl.
  take_drop_app_rewrite 3.
  iApply (wp_seq_ctx _ _ _ (λ v, ⌜v = immV [xx 5]⌝)%I).
  iSplitR.
  { iApply wp_binop;eauto. }
  iIntros (w ->). simpl.
  take_drop_app_rewrite 1.
  iApply iRewrite_nil_l_ctx.
  iApply iRewrite_nil_r_ctx. rewrite -!app_assoc.
  iApply wp_br_ctx;auto. iNext. simpl.
  iApply wp_value;eauto. done.  
Qed.

Lemma br_check_bind_return_4 :
  ⊢ WP [::AI_basic
         (BI_block (Tf [] [T_i32]) (* this block returns normally *)
                   [:: BI_const (xx 1);
                    BI_block (Tf [] [T_i32]) (* this block gets br'ed to *)
                             [::BI_block (Tf [] []) (* this block will never return *)
                               [::BI_const (xx 2);
                                BI_const (xx 3);
                                (BI_binop T_i32 (Binop_i BOI_add));
                                BI_br 1;
                                (BI_binop T_i32 (Binop_i BOI_add))] (* this expression gets stuck without br *) ];
                    (BI_binop T_i32 (Binop_i BOI_add)) ])] (* this expression only reds after previous block is reduced *)
    {{ λ v, ⌜v = immV [xx 6]⌝ }}.
Proof.
  iApply iRewrite_nil_l.
  iApply wp_block;eauto. iNext. simpl.
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil. simpl.
  iApply iRewrite_nil_r_ctx.
  iApply (wp_seq_ctx _ _ _ (λ v, ⌜v = immV [xx 6]⌝)%I).
  iSplitR.
  { take_drop_app_rewrite_twice 1 1.
    iApply wp_wasm_empty_ctx.
    iApply wp_base_push;auto. simpl.
    iApply iRewrite_nil_r_ctx.
    iApply (wp_seq_ctx _ _ _ (λ v, ⌜v = immV [xx 5]⌝)%I).
    iSplitR.
    { iApply iRewrite_nil_l.
      iApply wp_block;eauto. iNext. simpl.
      iApply wp_wasm_empty_ctx.
      iApply wp_label_push_nil. simpl.
      iApply iRewrite_nil_l_ctx.
      iApply wp_block_ctx;eauto. simpl. iNext.
      iApply wp_label_push_nil. simpl.
      take_drop_app_rewrite 3.
      iApply (wp_seq_ctx _ _ _ (λ v, ⌜v = immV [xx 5]⌝)%I).
      iSplitR.
      { iApply wp_binop;eauto. }
      iIntros (w ->). simpl.
      take_drop_app_rewrite 2.
      iApply iRewrite_nil_l_ctx.
      iApply wp_base_push;auto. simpl.
      take_drop_app_rewrite 1.
      iApply wp_br_ctx;auto. iNext.
      iApply wp_value;eauto. done. }
    iIntros (w ->). simpl.
    iApply wp_base;auto. simpl.
    iApply wp_binop;eauto. }
  iIntros (w ->) "/=".
  iApply wp_val_return;auto;simpl.
  iApply wp_value;eauto. done.
Qed.
  

(* --------------------------------------------------------------------------------------------- *)
(* --------------------------------- END OF EXAMPLES ------------------------------------------- *)
(* --------------------------------------------------------------------------------------------- *)



(* basic instructions with non-simple(non-pure) reductions *)

(* Function related *)

Lemma wp_call: False.
Proof.
Admitted.

Lemma wp_call_indirect: False.
Proof.
Admitted.

(* Function frame *)
Lemma wp_local: False.
Proof.
Admitted.

(* Reduction result for call/call_indirect *)
Lemma wp_invoke: False.
Proof.
Admitted.



(* Instance related *)

Lemma wp_get_local (s : stuckness) (E : coPset) (v: value) (i: nat) (ϕ: val -> Prop):
  ϕ (immV [v]) ->
  N.of_nat i ↦[wl] v ⊢
  WP ([AI_basic (BI_get_local i)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ N.of_nat i ↦[wl] v }}.
Proof.
  iIntros (Hϕ) "Hli".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] inst].
  iDestruct "Hσ" as "(? & ? & ? & ? & Hl & ? & ?)".
  iDestruct (gen_heap_valid with "Hl Hli") as "%Hli".
  rewrite gmap_of_list_lookup Nat2N.id in Hli.
  rewrite - nth_error_lookup in Hli.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v)], (hs, ws, locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    by apply r_get_local.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H; last eapply r_get_local; eauto.
    inversion H; subst; clear H.
    by iFrame => //=.
Qed.

Lemma wp_set_local (s : stuckness) (E : coPset) (v v0: value) (i: nat) (ϕ: val -> Prop):
  ϕ (immV []) ->
  N.of_nat i ↦[wl] v0 ⊢
  WP ([AI_basic (BI_const v); AI_basic (BI_set_local i)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ N.of_nat i ↦[wl] v }}.
Proof.
  iIntros (Hϕ) "Hli".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] inst].
  iDestruct "Hσ" as "(? & ? & ? & ? & Hl & ? & ?)".
  iDestruct (gen_heap_valid with "Hl Hli") as "%Hli".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [], (hs, ws, set_nth v locs i v, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    by eapply r_set_local.
  - iIntros "!>" (es σ2 efs HStep).
    (* modify locs[i]. This has to be done before the update modality is used. *)
    iMod (gen_heap_update with "Hl Hli") as "(Hl & Hli)".
    iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H; last eapply r_set_local with (f' := {| f_locs := set_nth v locs i v; f_inst := inst |}); eauto.
    inversion H; subst; clear H.
    iFrame.
    repeat iSplit => //.
    assert (i < length locs) as Hlength.
    { rewrite gmap_of_list_lookup Nat2N.id in Hli.
      by apply lookup_lt_Some in Hli.
    }
    rewrite - gmap_of_list_insert; rewrite Nat2N.id => //.
    by erewrite fmap_insert_set_nth.
Qed.

(* tee_local is not atomic in the Iris sense, since it requires 2 steps to be reduced to a value. *)
Lemma wp_tee_local (s : stuckness) (E : coPset) (v v0: value) (n: nat) (ϕ: val -> Prop):
  ϕ (immV [v]) ->
  N.of_nat n ↦[wl] v0 ⊢
  WP ([AI_basic (BI_const v); AI_basic (BI_tee_local n)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ N.of_nat n ↦[wl] v }}.
Proof.
  iIntros (Hϕ) "Hli".
  iApply wp_lift_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  destruct σ as [[[hs ws] locs] inst].
  iApply fupd_mask_intro; first by solve_ndisj.
  iIntros "Hfupd".
  iDestruct "Hσ" as "(? & ? & ? & ? & Hl & ? & ?)".
  iDestruct (gen_heap_valid with "Hl Hli") as "%Hli".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v); AI_basic (BI_const v); AI_basic (BI_set_local n)], (hs, ws, locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    by apply rs_tee_local => //.
  - iIntros "!>" (es σ2 efs HStep).
    iMod "Hfupd".
    iModIntro.
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H; last apply r_simple, rs_tee_local => //=.
    inversion H; subst; clear H.
    iFrame.
    repeat iSplit => //.
    iApply wp_val => //=.
    iApply wp_mono; last iApply wp_set_local; eauto => //.
Qed.

(* r_get_global involves finding the reference index to the global store via
   the instance first. *)

(* TODO: Weaken the ownership of instance (and global) *)
Lemma wp_get_global (s : stuckness) (E : coPset) (v: value) (inst: instance) (n: nat) (ϕ: val -> Prop) (g: global) (k: nat):
  inst.(inst_globs) !! n = Some k ->
  g.(g_val) = v ->
  ϕ (immV [v]) ->
  (↦[wi] inst ∗
  N.of_nat k ↦[wg] g) ⊢
                      WP ([AI_basic (BI_get_global n)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ ↦[wi] inst ∗ N.of_nat k ↦[wg] g }}.
Proof.
  iIntros (Hinstg Hgval Hϕ) "(Hinst & Hglob)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hg & ? & Hi & ?)".
  iDestruct (gen_heap_valid with "Hg Hglob") as "%Hglob".
  iDestruct (gen_heap_valid with "Hi Hinst") as "%Hinst".
  rewrite gmap_of_list_lookup Nat2N.id in Hglob.
  rewrite - nth_error_lookup in Hglob.
  rewrite - nth_error_lookup in Hinstg.
  rewrite lookup_insert in Hinst.
  inversion Hinst; subst; clear Hinst.
  assert ( sglob_val (host_function:=host_function) ws
                     (f_inst {| f_locs := locs; f_inst := inst |}) n =
           Some (g_val g) ) as Hsglob.
  { unfold sglob_val, option_map, sglob, option_bind, sglob_ind => /=.
    by rewrite Hinstg Hglob.
  }
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (g_val g))], (hs, ws, locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    by apply r_get_global.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] winst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H; last by apply r_get_global.
    inversion H; subst; clear H.
    by iFrame => /=.
Qed.
(*
Print  sglob_val.
Print supdate_glob.
*)
Lemma wp_set_global (s : stuckness) (E : coPset) (v:value) (inst :instance) (n:nat)
      (Φ : val -> Prop) (g: global) (k:nat):
  inst.(inst_globs) !! n = Some k ->
  Φ (immV []) ->
  ( ↦[wi] inst ∗
    N.of_nat k ↦[wg] g) ⊢
                        WP [AI_basic (BI_const v) ; AI_basic (BI_set_global n)] @ s ; E {{ w,  ⌜ Φ w ⌝ ∗ ↦[wi] inst ∗ N.of_nat k ↦[wg] {| g_mut := g_mut g ; g_val := v |} }}.
Proof.
  iIntros (Hinstg HΦ) "[Hinst Hglob]".
  iApply wp_lift_atomic_step. simpl ; trivial.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[ hs ws] locs ] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hg & ? & Hi & ?)". 
  iDestruct (gen_heap_valid with "Hg Hglob") as "%Hglob".
  iDestruct (gen_heap_valid with "Hi Hinst") as "%Hinst".
  rewrite gmap_of_list_lookup Nat2N.id in Hglob.
  rewrite - nth_error_lookup in Hglob.
  rewrite - nth_error_lookup in Hinstg.
  rewrite lookup_insert in Hinst.
  inversion Hinst ; subst ; clear Hinst.
  iDestruct (gen_heap_update with "Hg Hglob") as "H".
  remember {|
      s_funcs := datatypes.s_funcs ws;
      s_tables := datatypes.s_tables ws;
      s_mems := datatypes.s_mems ws;
      s_globals :=
        update_list_at (datatypes.s_globals ws) k
          {| g_mut := g_mut g; g_val := v |}
    |} as ws'.
  assert ( supdate_glob (host_function := host_function) ws
                     (f_inst {| f_locs := locs ; f_inst := inst |}) n v =
             Some ws') as Hsglob.
  { unfold supdate_glob, option_bind, sglob_ind, supdate_glob_s, option_map => /=.
    by rewrite Hinstg Hglob Heqws'. }
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [], (hs, ws', locs, inst), [].
    unfold language.prim_step => /=. repeat split => /=.
    by apply r_set_global.
  - iIntros "!>" (es σ2 efs Hstep). iMod "H". iModIntro. 
    destruct σ2 as [[[ hs2 ws2 ] locs' ] inst'].
    destruct Hstep as (H & -> & ->).
    only_one_reduction H [AI_basic (BI_const v) ; AI_basic (BI_set_global n)]
                       locs inst locs' inst'.   
    inversion Heqes ; subst. inversion Heqf' ; subst. rewrite H in Hsglob.
    destruct s0. simpl in Hsglob. inversion Hsglob. simpl.
    iDestruct "H" as "[Hg Hk]". iFrame. iSplit ; last done.
    assert (N.to_nat (N.of_nat k) < length s_globals) as Hlen.
    { rewrite Nat2N.id. simpl in Hglob. 
      apply nth_error_Some. rewrite Hglob. done. }
    rewrite <- (gmap_of_list_insert (l:= s_globals) {|g_mut := g_mut g ; g_val := v0 |} (n := N.of_nat k) Hlen).
    rewrite Nat2N.id.
    cut (<[k:={| g_mut := g_mut g ; g_val := v0 |}]> s_globals =
           update_list_at s_globals k {| g_mut := g_mut g ; g_val := v0 |}) ;
      [ intro Heq ; rewrite Heq ; done |].
    rewrite Nat2N.id in Hlen. unfold update_list_at.
    clear - Hlen. (* Hglob Hinstg Hsglob H1. *)
    generalize dependent s_globals. 
    induction k ; intros s_globals Hlen. 
    { destruct s_globals.
      { exfalso. simpl in Hlen. lia. }
      simpl. unfold drop. done. }
    destruct s_globals. { exfalso ; simpl in Hlen ; lia. }
    simpl. simpl in IHk. assert (k < (length s_globals)). { simpl in Hlen. lia. }
    rewrite (IHk s_globals H). done.
Qed.


Check dom.
Lemma update_list_same_dom (l : seq.seq global) k v :
  k < length l -> 
  dom (gset N) (gmap_of_list l) = dom (gset N) (gmap_of_list (update_list_at l k v)).
Proof.
  induction k ; unfold update_list_at. 
  destruct l. simpl. intro ; exfalso ; lia.
  intro ; simpl. destruct l. simpl. unfold gmap_of_list. simpl.
  unfold dom, gset_dom, mapset.mapset_dom, mapset.mapset_dom_with, merge, gmap_merge.
  unfold merge, pmap.Pmerge. Search (gmap_of_list _).
  
Admitted.

(* Auxiliary lemmas for load/store *)

Lemma store_length (m m': memory) (n: N) (off: static_offset) (bs: bytes) (l: nat) :
  store m n off bs l = Some m' ->
  length m.(mem_data).(ml_data) = length m'.(mem_data).(ml_data).
Proof.
Admitted.

Lemma mem_equiv_length (m m': memory):
  m ≡ₘ m' ->
  mem_length m = mem_length m'.
Proof.
  move => Hm.
  unfold mem_length, memory_list.mem_length.
  by rewrite Hm.
Qed.

Lemma store_data_inj (m1 m2 m1': memory) (n: N) (off: static_offset) (bs: bytes) (l: nat) :
  m1 ≡ₘ m2 ->
  store m1 n off bs l = Some m1' ->
  exists m2', store m2 n off bs l = Some m2' /\ m1' ≡ₘ m2'.
Proof.
  move => Hmequiv Hstore.
  Print memory_list.
  exists (Build_memory (Build_memory_list (ml_init (mem_data m2)) (ml_data (mem_data m1'))) (mem_max_opt m2)).
  unfold store in Hstore.
  unfold store.
Admitted.

Lemma update_list_at_insert {T: Type} (l: list T) (x: T) (n: nat):
  n < length l ->
  update_list_at l n x = <[n := x]> l.
Proof.
  move => Hlen.
  unfold update_list_at.
  move: n x Hlen.
  elim: l => //=.
  - move => n.
    by destruct n; lia.
  - move => a l IH n x Hlen.
    destruct n => //=.
    f_equal.
    apply IH.
    lia.
Qed.
    
(* A version of gen_heap_update specifically for wasm memories. *)
Lemma gen_heap_update_big_wm σ n ml ml':
  gen_heap_interp σ -∗ 
  ([∗ list] i ↦ b ∈ ml, N.of_nat n ↦[wm][N.of_nat i] b) ==∗
  gen_heap_interp ((new_2d_gmap_at_n (N.of_nat n) ml') ∪ σ) ∗
  ([∗ list] i ↦ b ∈ ml', N.of_nat n ↦[wm][N.of_nat i] b).
Proof.
(*  revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
  { rewrite left_id_L. auto. }
  iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
  decompose_map_disjoint.
  rewrite !big_opM_insert // -insert_union_l //.
  by iMod (gen_heap_alloc with "Hσ'σ") as "($ & $ & $)";
    first by apply lookup_union_None.*)
Admitted.



Lemma wp_load: False.
Proof.
Admitted.

Lemma wp_store (s: stuckness) (E: coPset) (t: value_type) (v: value) (inst: instance) (mem mem': memory) (off: static_offset) (a: alignment_exponent) (k: i32) (n: nat) (ϕ: val -> Prop) :
  types_agree t v ->
  inst.(inst_memory) !! 0 = Some n ->
  store mem (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t) = Some mem' ->
  ϕ (immV []) ->
  ( ↦[wi] inst ∗
  N.of_nat n ↦[wmblock] mem) ⊢
  (WP ([AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store t None a off)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ ↦[wi] inst ∗ (N.of_nat n) ↦[wmblock] mem' }}).
Proof.
  iIntros (Hvt Hinstn Hstore Hϕ) "[Hinst Hwmblock]".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  unfold mem_block.
  iDestruct "Hwmblock" as "(Hwmdata & Hwmlength)".
  iDestruct "Hσ" as "(? & ? & Hm & ? & ? & Hi & Hγ)".
  iDestruct (gen_heap_valid with "Hi Hinst") as "%Hinst".
  rewrite lookup_insert in Hinst.
  inversion Hinst; subst; clear Hinst.
  iDestruct (gen_heap_valid with "Hγ Hwmlength") as "%Hwmlength".
  rewrite gmap_of_list_lookup list_lookup_fmap Nat2N.id in Hwmlength.
  destruct (s_mems ws !! n) as [m|] eqn: Hm => //.
  simpl in Hwmlength.
  inversion Hwmlength as [Hwmlength']; clear Hwmlength.
  iAssert ( (∀ i, ⌜(ml_data (mem_data mem)) !! i = (ml_data (mem_data m)) !! i ⌝)%I) as "%Hmeq".
  {
    iIntros (i).
    destruct (ml_data (mem_data mem) !! i) eqn:Hmd.
    - iDestruct (big_sepL_lookup with "Hwmdata") as "H" => //.
      iDestruct (gen_heap_valid with "Hm H") as "%H".
      rewrite gmap_of_list_2d_lookup list_lookup_fmap Nat2N.id Hm in H.
      unfold memory_to_list in H.
      simpl in H.
      by rewrite Nat2N.id in H.
    - apply lookup_ge_None in Hmd.
      iPureIntro.
      symmetry.
      apply lookup_ge_None.
      unfold mem_length, memory_list.mem_length in Hwmlength'.
      lia.
  }
  iAssert (⌜mem ≡ₘm⌝%I) as "%Hmem".
  {
    unfold mem_block_equiv.
    by rewrite (list_eq (ml_data (mem_data mem)) (ml_data (mem_data m))).
  }
  specialize (store_data_inj mem m mem' (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t) Hmem Hstore) as [m' [Hstore' Hmdata']].
  rewrite - nth_error_lookup in Hm.
  rewrite - nth_error_lookup in Hinstn.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [], [], (hs, upd_s_mem ws (update_list_at (s_mems ws) n m'), locs, inst), [].
    repeat split => //.
    by eapply r_store_success.
  - iIntros "!>" (es σ2 efs HStep).
    (* Need something like gen_heap_update_big here to update all at once *)
    iMod (gen_heap_update_big_wm with "Hm Hwmdata") as "(Hm & Hwmdata)".
    iModIntro.
    destruct σ2 as [[[hs2 ws2] locs2] winst2].
    destruct HStep as [HStep [-> ->]].
    eapply reduce_det in HStep; last by eapply r_store_success.
    inversion HStep; subst; clear HStep => /=.
    iFrame.
    rewrite update_list_at_insert; last by rewrite nth_error_lookup in Hm; apply lookup_lt_Some in Hm.
    erewrite gmap_of_memory_insert_block => //; [ idtac | by rewrite - nth_error_lookup | by apply store_length in Hstore'; lia ].
    rewrite list_fmap_insert.
    assert (mem_length m' = mem_length m) as Hmsize.
    { apply store_length in Hstore'. by unfold mem_length, memory_list.mem_length; rewrite Hstore'. }
    rewrite Hmsize.
    assert (mem_length mem' = mem_length mem) as Hmsize'.
    { apply mem_equiv_length in Hmem.
      apply mem_equiv_length in Hmdata'.
      lia.
    }
    rewrite Hmsize'.
    rewrite list_insert_id; last by rewrite list_lookup_fmap; rewrite - nth_error_lookup; rewrite Hm.
    rewrite Hmdata' Hwmlength'.
    by iFrame.
Qed.
    
Lemma wp_current_memory (s: stuckness) (E: coPset) (k: nat) (n: N) (inst: instance) (mem: memory) (ϕ: val -> Prop) :
  inst.(inst_memory) !! 0 = Some k ->
  ϕ (immV [(VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (N.div n page_size))))]) ->
  ( ↦[wi] inst ∗
   (N.of_nat k) ↦[wmlength] n) ⊢
   WP ([AI_basic (BI_current_memory)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ ↦[wi] inst ∗ (N.of_nat k) ↦[wmlength] n }}.
Proof.
  iIntros (Hi Hϕ) "[Hinst Hmemlength]".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  iDestruct "Hσ" as "(? & ? & Hm & ? & ? & Hi & Hγ)".
  iDestruct (gen_heap_valid with "Hi Hinst") as "%Hinst".
  iDestruct (gen_heap_valid with "Hγ Hmemlength") as "%Hmemlength".
  rewrite lookup_insert in Hinst.
  inversion Hinst; subst; clear Hinst.
  rewrite - nth_error_lookup in Hi.
  rewrite gmap_of_list_lookup list_lookup_fmap Nat2N.id in Hmemlength => /=.
  destruct (s_mems ws !! k) eqn:Hmemlookup => //.
  rewrite - nth_error_lookup in Hmemlookup.
  simpl in Hmemlength.
  inversion Hmemlength; clear Hmemlength.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (N.div n page_size)))))], (hs, ws, locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_current_memory => //.
    unfold mem_size.
    by f_equal.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    eapply reduce_det in H; last eapply r_current_memory; eauto.
    inversion H; subst; clear H.
    unfold mem_size.
    by iFrame => //=.
Qed.

Lemma reduce_grow_memory hs ws f c hs' ws' f' es' k mem mem':
  f.(f_inst).(inst_memory) !! 0 = Some k ->
  nth_error (s_mems ws) k = Some mem ->
  reduce hs ws f [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_grow_memory)] hs' ws' f' es' ->
  ((hs', ws', f', es') = (hs, ws, f, [AI_basic (BI_const (VAL_int32 int32_minus_one))] ) \/
   (hs', ws', f', es') = (hs, (upd_s_mem ws (update_list_at (s_mems ws) k mem')), f, [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (mem_size mem)))))]) /\
  mem_grow mem (Wasm_int.N_of_uint i32m c) = Some mem').
Proof.
  move => Hinst Hmem HReduce.
  destruct f as [locs inst].
  destruct f' as [locs' inst'].
  (*only_one_reduction HReduce [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (mem_size mem)))))] locs inst locs' inst'.*)
Admitted.

Lemma wp_grow_memory (s: stuckness) (E: coPset) (k: nat) (n: N) (inst: instance) (mem: memory) (Φ Ψ: val -> iProp Σ) (c: i32) :
  inst.(inst_memory) !! 0 = Some k ->
  match mem_max_opt mem with
  | Some maxlim => (mem_size mem + (Wasm_int.N_of_uint i32m c) <=? maxlim)%N
  | None => true
  end ->
  (Φ (immV [VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (mem_size mem)))]) ∗
  (Ψ (immV [VAL_int32 int32_minus_one])) ∗
   ↦[wi] inst ∗
     (N.of_nat k) ↦[wmblock] mem ) ⊢ WP ([AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_grow_memory)]) @ s; E {{ w, ((Φ w ∗ (N.of_nat k) ↦[wmblock] {| mem_data:= {| ml_init := ml_init mem.(mem_data); ml_data := ml_data mem.(mem_data) ++ repeat (#00)%byte (N.to_nat ((Wasm_int.N_of_uint i32m c) * page_size)) |}; mem_max_opt:= mem_max_opt mem |}) ∨ (Ψ w ∗ (N.of_nat k) ↦[wmblock] mem)) ∗ ↦[wi] inst  }}.
Proof.
  iIntros (Hi Hmsizelim) "(HΦ & HΨ & Hinst & Hmemblock)".
  iDestruct "Hmemblock" as "(Hmemdata & Hmemlength)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] winst].
  iDestruct "Hσ" as "(? & ? & Hm & ? & ? & Hi & Hγ)".
  iDestruct (gen_heap_valid with "Hi Hinst") as "%Hinst".
  iDestruct (gen_heap_valid with "Hγ Hmemlength") as "%Hmemlength".
  rewrite lookup_insert in Hinst.
  inversion Hinst; subst; clear Hinst.
  rewrite - nth_error_lookup in Hi.
  rewrite gmap_of_list_lookup list_lookup_fmap Nat2N.id in Hmemlength => /=.
  destruct (s_mems ws !! k) eqn:Hmemlookup => //.
  simpl in Hmemlength.
  inversion Hmemlength as [Hmemlength']; clear Hmemlength.
  iAssert ( (∀ i, ⌜(ml_data (mem_data mem)) !! i = (ml_data (mem_data m)) !! i ⌝)%I) as "%Hmeq".
  {
    iIntros (i).
    destruct (ml_data (mem_data mem) !! i) eqn:Hmd.
    - iDestruct (big_sepL_lookup with "Hmemdata") as "H" => //.
      iDestruct (gen_heap_valid with "Hm H") as "%H".
      rewrite gmap_of_list_2d_lookup list_lookup_fmap Nat2N.id Hmemlookup in H.
      unfold memory_to_list in H.
      simpl in H.
      by rewrite Nat2N.id in H.
    - apply lookup_ge_None in Hmd.
      iPureIntro.
      symmetry.
      apply lookup_ge_None.
      unfold mem_length, memory_list.mem_length in Hmemlength'.
      lia.
  }
  iAssert (⌜mem ≡ₘm⌝%I) as "%Hmem".
  {
    unfold mem_block_equiv.
    by rewrite (list_eq (ml_data (mem_data mem)) (ml_data (mem_data m))).
  }
  iSplit.
  assert (exists mem', mem_grow mem (Wasm_int.N_of_uint i32m c) = Some mem') as [mem' Hmem'].
  { unfold mem_grow.
    destruct (mem_max_opt mem) eqn:Hmaxsize; eexists => //.
    by rewrite Hmsizelim.
  }
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (mem_size mem)))))], (hs, (upd_s_mem ws (update_list_at (s_mems ws) k mem')), locs, inst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_grow_memory_success => //.
    rewrite - nth_error_lookup in Hmemlookup.
    rewrite Hmemlookup.
    f_equal.
  (* There's a small bug in memory_list: mem_grow should not be using ml_init but #00 instead. Finish this when that is fixed *)
    admit.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[[hs' ws'] locs'] inst'] => //=.
    destruct HStep as [H [-> ->]].
    (* DO NOT USE reduce_det here -- grow_memory is NOT determinstic. *)
    eapply reduce_grow_memory in H; [ idtac | by rewrite - nth_error_lookup | by rewrite nth_error_lookup ].
    destruct H as [HReduce | [HReduce Hmem']]; inversion HReduce; subst; clear HReduce; iFrame.
    (* failure *)
    + iSplit => //.
      iRight.
      iFrame.
      by rewrite Hmemlength'.
    (* success *)
    + admit.
Admitted.






(* Example Programs *)

Definition my_add : expr :=
  [AI_basic (BI_const (xx 3));
     AI_basic (BI_const (xx 2));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add))].

Lemma myadd_spec (s : stuckness) (E : coPset) (Φ: val -> iProp Σ) :
  Φ (immV [xx 5]) ⊢ WP my_add @ s; E {{ v, Φ v }}.
Proof.
  iIntros "HΦ".
  unfold my_add.
  by iApply wp_binop.
Qed.

(* An example to show framing from the stack. *)
Definition my_add2: expr :=
  [AI_basic (BI_const (xx 1));
  AI_basic (BI_const (xx 2));
  AI_basic (BI_binop T_i32 (Binop_i BOI_add));
  AI_basic (BI_const (xx 2));
  AI_basic (BI_binop T_i32 (Binop_i BOI_add))].

Lemma myadd2_spec (s : stuckness) (E : coPset) (Φ: val -> iProp Σ) :
  Φ (immV [xx 5]) ⊢ WP my_add2 @ s; E {{ v, Φ v }}.
Proof.
  iIntros "HΦ".
  replace my_add2 with (take 3 my_add2 ++ drop 3 my_add2) => //.
  iApply wp_seq_nontrap => /=.
  instantiate (1 := fun v => (⌜ v = immV [xx 3] ⌝)%I ).
  iSplit => //.
  iSplitR "HΦ"; first by iApply wp_binop.
  iIntros (? ->) => /=.
  by iApply wp_binop.
Qed.

End lifting.

(* What should a function spec look like?
  A (Wasm) function closure is of the form

    FC_func_native inst ft vts bes

  but this is not an expression nor a value, so we need to define our custom version of wp for it, like

    ▷ WP (FC_func_native inst ft vts bes) {{ v, Φ v }}.

    ( Would WP bes {{ ... }} be enough? )

  to express our function specs.

  What should such a wp require (to be established), and how to use it? 

  Given a spec in the above form, we expect to be able to use it to
    figure out a spec for Invoke i, when s.funcs[i] is a Wasm function...
 
  s.funcs[a] = FC_func_native i (Tf t1s t2s) ts bes ->
  f' = {| inst := i; locs := vcs ++ zs |} ->
  ... ->
  (hs, s, f, ves ++ [AI_invoke a]) ↪ 
  (hs, s, f, [AI_local m f' [AI_basic (BI_block (Tf [] t2s) bes)]])

Lemma invoke_native_spec `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ, !wlocsG Σ} (s : stuckness) (E : coPset) (Φs: list (val -> iProp Σ)) inst ft vts bes :
  [∗ list] i ↦ Φ ∈ Φs, (i ↦[wf] FC_func_native inst ft vts bes ∗ □ (WP (FC_func_native inst ft vts bes)
*)

End Host.

Local Hint Resolve language.val_irreducible : core.
Local Hint Resolve to_of_val : core.
Local Hint Unfold language.irreducible : core.

Ltac solve_atomic :=
  apply is_atomic_correct; simpl; repeat split;
    rewrite ?to_of_val; eapply mk_is_Some; fast_done.

Global Hint Extern 0 (Atomic _ _) => solve_atomic : core.
Global Hint Extern 0 (Atomic _ _) => solve_atomic : typeclass_instances.
