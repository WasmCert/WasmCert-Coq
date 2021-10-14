(** Example of Iris usage **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre lifting.
From iris.base_logic Require Export gen_heap proph_map.
Require Export iris iris_locations.
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

Instance heapG_irisG `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ, !wlocsG Σ, !winstG Σ} : irisG wasm_lang Σ := {
  iris_invG := func_invG; (* Check: do we actually need this? *)
  state_interp σ _ κs _ :=
    let: (_, s, locs, inst) := σ in
     ((gen_heap_interp (gmap_of_list s.(s_funcs))) ∗
      (gen_heap_interp (gmap_of_table s.(s_tables))) ∗
      (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
      (gen_heap_interp (gmap_of_list s.(s_globals)) ∗
      (gen_heap_interp (gmap_of_list locs)) ∗
      (gen_heap_interp (<[tt := inst]> ∅))
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
  iris.to_val es = Some vs ->
  const_list es.
Proof.
  move => es. 
  elim: es => [|e es'] //=.
  move => IH vs.
  destruct e => //=.
  destruct b => //=.
  move => H.
  destruct (iris.to_val es') eqn:HConst => //=.
  inversion H; subst; clear H.
  by eapply IH; eauto.
Qed.
  
Lemma to_val_cat (es1 es2: list administrative_instruction) (vs: val) :
  iris.to_val (es1 ++ es2) = Some vs ->
  iris.to_val es1 = Some (take (length es1) vs) /\
  iris.to_val es2 = Some (drop (length es1) vs).
Proof.
  move => H.
  apply iris.of_to_val in H.
  unfold iris.of_val in H.
  apply fmap_split in H; destruct H as [H1 H2].
  remember (length es1) as n1.
  remember (length es2) as n2.
  rewrite - H1.
  rewrite - H2.
  by repeat rewrite iris.to_of_val.
Qed.

Lemma to_val_cat_None1 (es1 es2: list administrative_instruction) :
  iris.to_val es1 = None ->
  iris.to_val (es1 ++ es2) = None.
Proof.
  move => H.
  destruct (iris.to_val (es1 ++ es2)) eqn: HContra => //.
  apply to_val_cat in HContra as [H1 _].
  rewrite H1 in H.
  by inversion H.
Qed.

Lemma to_val_cat_None2 (es1 es2: list administrative_instruction) :
  iris.to_val es2 = None ->
  iris.to_val (es1 ++ es2) = None.
Proof.
  move => H.
  destruct (iris.to_val (es1 ++ es2)) eqn: HContra => //.
  apply to_val_cat in HContra as [_ H1].
  rewrite H1 in H.
  by inversion H.
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

(* The following few auxiliary lemmas are intuitive, but tedious to prove. *)
Lemma prim_step_split_reduce_r (es1 es2 es' : list administrative_instruction) σ σ' obs efs :
  iris.to_val es1 = None ->
  prim_step (es1 ++ es2) σ obs es' σ' efs ->
  exists es'', es' = es'' ++ es2 /\ prim_step es1 σ obs es'' σ' efs.
Proof.
  move: es2 es' σ σ' obs efs.
  elim: es1 => //=.
  - move => e es0 IH es2 es' σ σ' obs efs HConst HStep.
    unfold prim_step, iris.prim_step in HStep.
    specialize IH with es2 es' σ σ' [] [].
    destruct σ as [[[hs ws] locs] inst].
    destruct σ' as [[[hs' ws'] locs'] inst'].
    destruct HStep as [HStep [-> ->]].
Admitted.

(* Context lemmas -- could be very tedious to prove *)
Lemma b2p: forall {T:eqType} (a b:T), a==b -> a=b.
Proof. move => T a b Hb. by move/eqP in Hb. Qed.


Ltac false_assumption := apply ssrbool.not_false_is_true ; assumption.


Lemma found_intruse l1 l2 (x : administrative_instruction) :
  l1 = l2 -> (In x l1 -> False) -> In x l2 -> False.
Proof.
  intros. rewrite H in H0. apply H0 ; exact H1.
Qed.

(* If H is a hypothesis that states the equality between 2 lists, attempts to prove
   False by showing object x is in the rhs of H, but not in the lhs.
   If attempt fails, user is given a hypothesis Hxl1 to end proof manually *)
Ltac found_intruse x H Hxl1 :=
  apply (found_intruse _ _ x H) ;
  [intro Hxl1 ; repeat ((destruct Hxl1 as [Hxl1 | Hxl1] ; [ inversion Hxl1 |]) +
                          assumption  ) |
    try by (apply in_or_app ; right ; left ; trivial) ].

(* Attempts to prove False from hypothesis H, which states that an lholed is filled
   with AI_trap. If attempt fails, user is given a hypothesis Hxl1 to end proof manually *)
Ltac filled_trap H Hxl1 :=
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
  unfold lfilled, lfill in H ;
  destruct k ;
  [ destruct lh as [vs l0|] ; [| false_assumption] ;
    destruct (const_list vs) ; [| false_assumption] ; apply b2p in H |
    fold lfill in H ; destruct lh as [|vs n l1 lh' l2] ; [false_assumption |] ;
    destruct (const_list vs) ; [| false_assumption ] ;
    destruct (lfill k lh' _) as [l3|] ; [| false_assumption ] ;
    apply b2p in H ; found_intruse (AI_label n l1 l3) H Hxl1].
    

Lemma empty_list_no_reduce hs s f hs' s' f' es' :
  reduce hs s f [] hs' s' f' es' -> False.
Proof.
  intro H. remember [] as es in H.
  apply Logic.eq_sym in Heqes.
  induction H ; try by inversion Heqes ; try by found_intruse (AI_invoke a) Heqes Hxl1.
  { destruct H ; (try by inversion Heqes) ;
      [ found_intruse (AI_basic (BI_block (Tf t1s t2s) es)) Heqes Hxl1 |
        found_intruse (AI_basic (BI_loop (Tf t1s t2s) es)) Heqes Hxl1 | 
        rewrite <- Heqes in H0 ; filled_trap H0 Hxl1 ].
  }
  - rewrite <- Heqes in H0. simple_filled H0 k lh bef aft n l l'.
    apply Logic.eq_sym in H0 ; apply app_eq_nil in H0 ;
        destruct H0 as [_ H0] ; apply app_eq_nil in H0 ;
        destruct H0 as [H0 _] ; rewrite H0 in IHreduce ;
        apply IHreduce ; trivial.
Qed.


(* Applies empty_list_no_reduce after rewriting "Hes0 : es = []" into the reduction 
   hypothesis *)
Ltac empty_list_no_reduce Hes0 Hred :=
  try (rewrite Hes0 in Hred + rewrite <- Hes0 in Hred) ; exfalso ;
  apply (empty_list_no_reduce _ _ _ _ _ _ _ Hred).

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


(* From hypothesis "Heqes : [obj] = es" and "Hred : es -> es'", attempts to prove False *)
Ltac no_reduce1 Heqes Hred :=
  let a := fresh "a" in
  let aft := fresh "aft" in
  let bef := fresh "bef" in
  let e := fresh "e" in
  let e' := fresh "e" in
  let es := fresh "es" in
  let es' := fresh "es" in
  let f := fresh "f" in
  let f' := fresh "f" in
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
  let H0 := fresh "H0" in
  let Hconst := fresh "Hconst" in
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
                      reducible empty_instance prim_step
                      Hred Heqes ;
  induction Hred as [e e' s f hs H | | | | | a | a | a | | | | | | | | | | | | | | | |
                      s f es les s' f' es' les' k lh hs hs' Hred IHreduce H0 _ |
    ]; (try by inversion Heqes) ; (try by found_intruse (AI_invoke a) Heqes Hxl1) ;
  [ destruct H as [ | | | | | | | | | | | | | | 
                    vs es n' m t1s t2s Hconst Hvs Ht1s Ht2s |
                    vs es n' m t1s t2s Hconst Hvs Ht1s Ht2s |
                  | | | | | | | | | | | | | 
                    es' lh Htrap' H0 ]; (try by inversion Heqes) ;
    [ found_intruse (AI_basic (BI_block (Tf t1s t2s) es)) Heqes Hxl1 |
      found_intruse (AI_basic (BI_loop (Tf t1s t2s) es)) Heqes Hxl1 |
      rewrite <- Heqes in H0 ; filled_trap H0 Hxl1]
  | rewrite <- Heqes in H0 ;
    simple_filled H0 k lh bef aft n l l' ;
    apply Logic.eq_sym in H0 ;  apply app_eq_unit in H0 ;
    destruct H0 as [[ _ Hes ] | [ _ Hes]] ;
    [ apply app_eq_unit in Hes ;
      destruct Hes as [[ Hes _ ]|[ Hes _ ]] ;
      [ empty_list_no_reduce Hes Hred |
        rewrite Hes in IHreduce ; apply IHreduce ; trivial ] |
      apply app_eq_nil in Hes ;
      destruct Hes as [Hes _] ;
      empty_list_no_reduce Hes Hred ] ] . 

(* From hypothesis "Heqes : [obj1 ; obj2] = es" and "Hred : es -> es'", 
   attempts to prove False. Calls no_reduce1 *)
Ltac no_reduce2 Heqes Hred :=
  let e := fresh "e" in
  let e' := fresh "e" in
  let s := fresh "s" in
  let f := fresh "f" in
  let hs := fresh "hs" in
  let H := fresh "H" in
  let a := fresh "a" in
  let es := fresh "es" in
  let les := fresh "les" in
  let s' := fresh "s" in
  let f' := fresh "f" in
  let es' := fresh "es" in
  let les' := fresh "les" in
  let k := fresh "k" in
  let lh := fresh "lh" in
  let hs' := fresh "hs" in
  let IHreduce := fresh "IHreduce" in
  let H0 := fresh "H" in
  let vs := fresh "vs" in
  let n' := fresh "n" in
  let m := fresh "m" in
  let t1s := fresh "t1s" in
  let t2s := fresh "t2s" in
  let Hconst := fresh "Hconst" in
  let Hvs := fresh "Hvs" in
  let Ht1s := fresh "Ht1s" in
  let Ht2s := fresh "Ht2s" in
  let Htrap' := fresh "Htrap" in
  let es0 := fresh "es" in
  let Heqes0 := fresh "Heqes" in
  let hv := fresh "hv" in
  let he := fresh "he" in
  let Hhd := fresh "Hhd" in
  let Htl := fresh "Htl" in
  let Hhd1 := fresh "Hhd" in
  let Hhd2 := fresh "Hhd" in
  let Hxl1 := fresh "Hxl1" in
  let aft := fresh "aft" in
  let n := fresh "n" in
  let l := fresh "l" in
  let l' := fresh "l" in
  clear - host_function host function_closure store_record
                        host_instance reduce wasm_mixin expr val
                        reducible empty_instance prim_step
                        Hred Heqes ;
  induction Hred as [e e' s f hs H | | | | | 
                      a | a | a | | | | | | | | | | | | | | | |
                      s f es les s' f' es' les' k lh hs hs' Hred IHreduce H0 _ |
    ]; (try by inversion Heqes) ; (try by found_intruse (AI_invoke a) Heqes Hxl1) ;
  [ destruct H as [ | | | | | | | | | | | | | | 
                    vs es n' m t1s t2s Hconst Hvs Ht1s Ht2s |
                    vs es n' m t1s t2s Hconst Hvs Ht1s Ht2s |
                  | | | | | | | | | | | | | 
                    es' lh Htrap' H0 ]; (try by inversion Heqes) ;
    [ found_intruse (AI_basic (BI_block (Tf t1s t2s) es)) Heqes Hxl1 |
      found_intruse (AI_basic (BI_loop (Tf t1s t2s) es)) Heqes Hxl1 |
      rewrite <- Heqes in H0 ; filled_trap H0 Hxl1 ]
  | rewrite <- Heqes in H0 ;
    simple_filled H0 k lh vs aft n l l' ;
    apply Logic.eq_sym in H0 ;
    destruct vs as [ | hv vs] ;
    [ destruct es as [ | he es ] ;
      [ apply (empty_list_no_reduce _ _ _ _ _ _ _ Hred)
      | inversion H0 as [[ Hhd Htl ]] ;
        apply app_eq_unit in Htl ;
        destruct Htl as [[ Hes _ ]|[Hes _ ]] ;
        [ rewrite Hes in Hred ; remember [he] as es0 eqn:Heqes0 ;
          rewrite Hhd in Heqes0 ; apply Logic.eq_sym in Heqes0 ;
          no_reduce1 Heqes0 Hred
        | rewrite Hhd in IHreduce ; rewrite Hes in IHreduce ;
          apply IHreduce ; trivial ]]
    | destruct vs ;
      [ inversion H0 as [[ Hhd Htl ]] ;
        apply app_eq_unit in Htl ;
        destruct Htl as [[ Hes _ ]|[ Hes _ ]] ;
        [ empty_list_no_reduce Hes Hred
        | apply Logic.eq_sym in Hes ; no_reduce1 Hes Hred ]
      | inversion H0 as [[ Hhd1 Hhd2 Htl ]] ;
        apply app_eq_nil in Htl ; destruct Htl as [_ Hes] ;
        apply app_eq_nil in Hes ; destruct Hes as [Hes _ ] ;
        empty_list_no_reduce Hes Hred ]] ].

(* From hypothesis "Heqes : [obj1 ; obj2 ; obj3] = es" and "Hred : es -> es'", 
   attempts to prove False. Calls no_reduce2 and no_reduce1.  *)
Ltac no_reduce3 Heqes Hred :=
  let e := fresh "e" in
  let e' := fresh "e" in
  let s := fresh "s" in
  let f := fresh "f" in
  let hs := fresh "hs" in
  let H := fresh "H" in
  let a := fresh "a" in
  let es := fresh "es" in
  let les := fresh "les" in
  let s' := fresh "s" in
  let f' := fresh "f" in
  let es' := fresh "es" in
  let les' := fresh "les" in
  let k := fresh "k" in
  let lh := fresh "lh" in
  let hs' := fresh "hs" in
  let IHreduce := fresh "IHreduce" in
  let H0 := fresh "H" in
  let vs := fresh "vs" in
  let n' := fresh "n" in
  let m := fresh "m" in
  let t1s := fresh "t1s" in
  let t2s := fresh "t2s" in
  let Hconst := fresh "Hconst" in
  let Hvs := fresh "Hvs" in
  let Ht1s := fresh "Ht1s" in
  let Ht2s := fresh "Ht2s" in
  let Htrap' := fresh "Htrap" in
  let es0 := fresh "es" in
  let Heqes0 := fresh "Heqes" in
  let e1 := fresh "e" in
  let e2 := fresh "e" in
  let v1 := fresh "v" in
  let v2 := fresh "v" in
  let He1 := fresh "He" in
  let He2 := fresh "He" in
  let Hesl := fresh "Hesl" in
  let Hesl' := fresh "Hesl" in
  let Hves := fresh "Hves" in
  let Hevs' := fresh "Hves" in
  let Hxl1 := fresh "Hxl1" in
  let aft := fresh "aft" in
  let n := fresh "n" in
  let l := fresh "l" in
  let l' := fresh "l" in
  clear - host_function host function_closure store_record
                        host_instance reduce wasm_mixin expr val
                        reducible empty_instance prim_step
                        Hred Heqes ;
  induction Hred as [e e' s f hs H | | | | | 
                      a | a | a | | | | | | | | | | | | | | | |
                      s f es les s' f' es' les' k lh hs hs' Hred IHreduce H0 _ |
    ]; (try by inversion Heqes) ; (try by found_intruse (AI_invoke a) Heqes Hxl1) ;
  [ destruct H as [ | | | | | | | | | | | | | | 
                    vs es n' m t1s t2s Hconst Hvs Ht1s Ht2s |
                    vs es n' m t1s t2s Hconst Hvs Ht1s Ht2s |
                  | | | | | | | | | | | | | 
                    es' lh Htrap' H0 ]; (try by inversion Heqes) ;
    [ found_intruse (AI_basic (BI_block (Tf t1s t2s) es)) Heqes Hxl1|
      found_intruse (AI_basic (BI_loop (Tf t1s t2s) es)) Heqes Hxl1|
      rewrite <- Heqes in H0 ; filled_trap H0 Hxl1 ]
  | rewrite <- Heqes in H0 ;
    simple_filled H0 k lh vs aft n l l';
    apply Logic.eq_sym in H0 ;
    destruct vs as [ | v1 vs ];
    [ destruct es as [ | e1 es ];
      [ apply (empty_list_no_reduce _ _ _ _ _ _ _ Hred) 
      | inversion H0 as [[ He1 Hesl ]] ;
        destruct es as [ | e2 es ] ;
          [ remember [e1] as es0 eqn:Heqes0 ;
            apply Logic.eq_sym in Heqes0 ;
            rewrite He1 in Heqes0 ;
            no_reduce1 Heqes0 Hred 
          | inversion Hesl as [[ He2 Hesl' ]] ;
            apply app_eq_unit in Hesl' ;
            destruct Hesl' as [[ Hes _ ]|[ Hes _ ]] ;
            [ rewrite Hes in Hred ;
              remember [e1 ; e2] as es0 eqn:Heqes0 ;
              apply Logic.eq_sym in Heqes0 ;
              rewrite He1 in Heqes0 ;
              rewrite He2 in Heqes0 ;
              no_reduce2 Heqes0 Hred
            | rewrite Hes in IHreduce ;
              rewrite He1 in IHreduce ;
              rewrite He2 in IHreduce ;
              apply IHreduce ; trivial
            ]
          ]
      ] 
    | inversion H0 as [[ Hv1 Hves ]] ; destruct vs as [ | v2 vs ] ;
      [ destruct es as [ | e1 es ];
        [ apply (empty_list_no_reduce _ _ _ _ _ _ _ Hred) 
        | inversion Hves as [[ He1 Hesl ]] ; 
          apply app_eq_unit in Hesl ;
          destruct Hesl as [[ Hes _ ]|[ Hes _ ]] ;
          [ rewrite Hes in Hred ; remember [e1] as es0 eqn:Heqes0 ;
            rewrite He1 in Heqes0 ; apply Logic.eq_sym in Heqes0 ;
            no_reduce1 Heqes0 Hred 
          | remember (e1 :: es) as es0 eqn:Heqes0 ;
            rewrite He1 in Heqes0 ; rewrite Hes in Heqes0;
            apply Logic.eq_sym in Heqes0 ;
            no_reduce2 Heqes0 Hred
          ]
        ]
      | inversion Hves as [[ Hv2 Hves' ]] ; apply app_eq_unit in Hves' ;
        destruct Hves' as [[ _ Hesl ]|[ _ Hesl]] ;
        [ apply app_eq_unit in Hesl ;
          destruct Hesl as [[ Hes _ ]|[ Hes _ ]] ;
          [ empty_list_no_reduce Hes Hred
          | apply Logic.eq_sym in Hes ;
            no_reduce1 Hes Hred
          ] 
        | apply app_eq_nil in Hesl; destruct Hesl as [Hes _] ;
          empty_list_no_reduce Hes Hred
        ]
      ]
    ]
  ]. 

(* Knowing hypothesis "Hin : In obj vs" and "Hvs : const_list vs", tries to prove False *)
Ltac intruse_among_values vs Hin Hvs :=
  try unfold const_list in Hvs ;
  let x := fresh "Hf" in
  destruct (forallb_forall is_const vs) as [x _] ;
  apply (x Hvs) in Hin ; inversion Hin.

(* given a nonempty list x :: xs, gives user a hypothesis "Htail : x :: xs = ys ++ [y]" *)
Ltac get_tail x xs ys y Htail :=
  cut (exists ys y, x :: xs = ys ++ [y]) ;
  [ intro Htail ; destruct Htail as (ys & y & Htail) |
    exists (removelast (x :: xs)) ;
    exists (List.last (x :: xs) AI_trap) ;
    apply app_removelast_last ;
    apply not_eq_sym ; apply nil_cons ].


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
            [ apply (empty_list_no_reduce _ _ _ _ _ _ _ Hred) |] ;
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
    { destruct es. { apply (empty_list_no_reduce _ _ _ _ _ _ _ Hred). }
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
    { destruct es. { apply (empty_list_no_reduce _ _ _ _ _ _ _ Hred). }
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
     inversion Heqves as [[ Hhd Htl ]] ; no_reduce1 Htl Hred0 );
    (try by exfalso ;  unfold language.prim_step, wasm_lang, iris.prim_step in H ;
     destruct σ0 as [[[??]?]?] ; destruct H as (Hred0 & Hobs0 & Hefs0) ;
     inversion Heqves as [[ Hhd Htl ]] ; no_reduce2 Htl Hred0 ).
  {  unfold language.prim_step, wasm_lang, iris.prim_step in H ;
     destruct σ0 as [[[??]?]?] ; destruct H as (Hred0 & Hobs0 & Hefs0).
    destruct Hredsimpl as [ | | | | | | | | | | | | | |
                            vs es' n m t1s t2s Hconst Hlenvs Ht1s Ht2s |
                            vs es' n m t1s t2s Hconst Hlenvs Ht1s Ht2s |
                          | | | | | | | | | | | | | ] ; exfalso ;
       inversion Heqves as [[ Hhd Htl ]] ;
      (try by no_reduce1 Htl Hred0) ; (try by no_reduce2 Htl Hred0) ;
      (try by no_reduce3 Htl Hred0).
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
                               { exfalso.
                                 apply (empty_list_no_reduce _ _ _ _ _ _ _ Hred). }
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
                               apply (to_val_const_list _ v0 (Logic.eq_sym Heqtv)).
                               trivial.
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


Lemma reduce_ves2: forall v es es' σ σ' efs obs,
    reducible es σ ->
    prim_step ([AI_basic (BI_const v)] ++ es) σ obs es' σ' efs ->
    (In AI_trap es -> False) ->
    prim_step es σ obs (drop 1 es') σ' efs.
Proof.
  cut (forall n v es es' σ σ' efs obs,
          length es < n ->
          reducible es σ ->
          prim_step ([AI_basic (BI_const v)] ++ es) σ obs es' σ' efs ->
          (In AI_trap es -> False) ->
          prim_step es σ obs (drop 1 es') σ' efs).
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
  remember {| f_locs := l0 ; f_inst := i0 |} as f0.
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
     inversion Heqves as [[ Hhd Htl ]] ; no_reduce1 Htl Hred0 );
    (try by exfalso ;  unfold language.prim_step, wasm_lang, iris.prim_step in H ;
     destruct σ0 as [[[??]?]?] ; destruct H as (Hred0 & Hobs0 & Hefs0) ;
     inversion Heqves as [[ Hhd Htl ]] ; no_reduce2 Htl Hred0 ).
  {  unfold language.prim_step, wasm_lang, iris.prim_step in H ;
     destruct σ0 as [[[??]?]?] ; destruct H as (Hred0 & Hobs0 & Hefs0).
    destruct Hredsimpl as [ | | | | | | | | | | | | | |
                            vs es' n m t1s t2s Hconst Hlenvs Ht1s Ht2s |
                            vs es' n m t1s t2s Hconst Hlenvs Ht1s Ht2s |
                          | | | | | | | | | | | | | ] ; exfalso ;
       inversion Heqves as [[ Hhd Htl ]] ;
      (try by no_reduce1 Htl Hred0) ; (try by no_reduce2 Htl Hred0) ;
      (try by no_reduce3 Htl Hred0).
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
                               { exfalso.
                                 apply (empty_list_no_reduce _ _ _ _ _ _ _ Hred). }
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
                               assert (iris.to_val es' = None).
                               remember (iris.to_val es') as tv.
                               destruct tv ; [trivial |].
                               exfalso ; apply H0.
                               apply (to_val_const_list _ v0 (Logic.eq_sym Heqtv)).
                               trivial.
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
  
Lemma prepend_reducible (es1 es2: list administrative_instruction) vs σ:
  iris.to_val es1 = Some vs ->
  reducible es2 σ ->
  reducible (es1 ++ es2) σ.
Proof.
  unfold reducible => /=.
  move => Htv [κ [es' [σ' [efs HStep]]]].
  exists κ, (es1 ++ es'), σ', efs.
  unfold iris.prim_step in * => //=.
  destruct σ as [[[hs ws] locs] inst].
  destruct σ' as [[[hs' ws'] locs'] inst'].
  destruct HStep as [HStep [-> ->]].
  repeat split => //.
  apply r_eliml => //.
  by eapply to_val_const_list; eauto.
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
  
(* Warning: this axiom is not actually true -- Wasm does not have a deterministic
   opsem for mem_grow and host function calls. However, the rest of the opsem
   are indeed deterministic. Use with caution. *)
Local Axiom reduce_det: forall hs f ws es hs1 f1 ws1 es1 hs2 f2 ws2 es2,
  reduce hs f ws es hs1 f1 ws1 es1 ->
  reduce hs f ws es hs2 f2 ws2 es2 ->
  (hs1, f1, ws1, es1) = (hs2, f2, ws2, es2).




(* wp for instructions *)

Section lifting.

Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ, !wlocsG Σ, !winstG Σ}.
  
(* empty lists, frame rules *)

Lemma wp_nil (s : stuckness) (E : coPset) (Φ : iProp Σ) :
  Φ ⊢ WP [] @ s ; E {{ fun v => Φ }}%I.
Proof.
  iIntros "H".
  by rewrite wp_unfold /wp_pre.
Qed.

(* behaviour of seq might be a bit unusual due to how reductions work. *)
Lemma wp_seq (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) :
  (WP es1 @ s; E {{ w, Ψ w }} ∗
  ∀ w, Ψ w -∗ WP (iris.of_val w ++ es2) @ s; E {{ v, Φ v }})%I
  ⊢ WP (es1 ++ es2) @ s; E {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (s E es1 es2 Φ Ψ).
  iIntros "[Hes1 Hes2]".
  repeat rewrite wp_unfold /wp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val (es1 ++ es2)) as [vs|] eqn:Hetov.
  {
    apply to_val_cat in Hetov as [-> Hev2].
    apply iris.of_to_val in Hev2 as <-.
    iMod "Hes1".
    iSpecialize ("Hes2" with "Hes1").
    unfold iris.of_val.
    rewrite - map_app take_drop.
    rewrite wp_unfold /wp_pre /=.
    rewrite to_of_val.
    by iAssumption.
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
      apply prim_step_split_reduce_r in HStep as [es'' [-> HStep]] => //.
      iSpecialize ("H2" $! es'' σ2 efs HStep).
      iMod "H2".
      repeat iModIntro.
      repeat iMod "H2".
      iModIntro.
      destruct σ2 as [[i s0] locs].
      iDestruct "H2" as "(Hσ & Hes'' & Hefs)".
      iFrame.
      iApply "IH".
      by iFrame.
  }
Qed.

Lemma wp_val (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v0 : value) (es : language.expr wasm_lang) :
  WP es @ NotStuck ; E {{ v, (Φ (v0 :: v)) }}%I
  ⊢ WP ((AI_basic (BI_const v0)) :: es) @ s ; E {{ v, Φ v }}%I.
Proof.
  (* This also needs an iLob. *)
  iLöb as "IH" forall (v0 es Φ).
  iIntros "H".
  repeat rewrite wp_unfold /wp_pre /=.
  destruct (iris.to_val es) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod "H".
    by iModIntro.
  }
  { iIntros (σ ns κ κs nt) "Hσ".
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
      assert (es2 = [AI_basic (BI_const v0)] ++ drop 1 es2) as Hes2; first by eapply reduce_ves1; eauto.
      assert (prim_step es σ κ (drop 1 es2) σ2 efs) as HStep2; first by eapply reduce_ves2; eauto.
      assert ((κ, efs) = ([],[])) as Hobsefs; first by eapply prim_step_obs_efs_empty.
      inversion Hobsefs; subst; clear Hobsefs.
      iSpecialize ("H" $! (drop 1 es2) σ2 [] HStep2).
      iMod "H".
      repeat iModIntro.
      repeat iMod "H".
      iModIntro.
      iDestruct "H" as "(Hσ & Hes & Hefs)".
      iSimpl.
      iFrame.
      iSplit => //.
      destruct es2 => //=.
      inversion Hes2; subst; clear Hes2.
      rewrite drop_0.
      by iApply "IH".
  }
Qed.





(* basic instructions with simple(pure) reductions *)

(* numerics *)

Lemma wp_unop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v v' : value) (t: value_type) (op: unop):
  app_unop op v = v' ->
  Φ [v'] ⊢
  WP [AI_basic (BI_const v); AI_basic (BI_unop t op)] @ s; E {{ v, Φ v }}.
Proof.
Admitted.
  
Lemma wp_binop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v1 v2 v : value) (t: value_type) (op: binop):
  app_binop op v1 v2 = Some v ->
  Φ [v] ⊢
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
    eapply reduce_det in H; last by apply r_simple, rs_binop_success.
    inversion H; subst; clear H.
    by iFrame.
Qed.

(* There is a problem with this case: AI_trap is not a value in our language.
   This can of course be circumvented if we only consider 'successful reductions',
   but otherwise this needs some special treatment. *)

(* 20210929: with [::AI_trap] potentially becoming a value, this might get proved at some point *)
Lemma wp_binop_failure (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v1 v2 : value) (t: value_type) (op: binop):
  ⌜app_binop op v1 v2 = None⌝ ⊢
  WP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] @ s; E {{ v, True }}.
Proof.
  iIntros "%Hbinop".
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
    iSimpl.
    (* Has to be false at this point -- AI_trap is not a value. 
       The culprit is that we used wp_lift_atomic_step in the beginning -- that
       lemma requires the given expression to be reduced to a value after
       one step. However, a non-successful binop will never be reduced to any
       value. *)
    admit.
Admitted.

Lemma wp_relop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v1 v2 : value) (b: bool) (t: value_type) (op: relop):
  app_relop op v1 v2 = b ->
  Φ [(xb b)] ⊢
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
    eapply reduce_det in H; last by apply r_simple, rs_relop.
    inversion H; subst; clear H.
    by iFrame.
Qed.

Lemma wp_testop_i32 (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v : i32) (b: bool) (t: value_type) (op: testop):
  app_testop_i (e:=i32t) op v = b ->
  Φ [(xb b)] ⊢
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
    eapply reduce_det in H; last by apply r_simple, rs_testop_i32.
    inversion H; subst; clear H.
    by iFrame.
Qed.

Lemma wp_testop_i64 (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v : i64) (b: bool) (t: value_type) (op: testop):
  app_testop_i (e:=i64t) op v = b ->
  Φ [(xb b)] ⊢
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
    eapply reduce_det in H; last by apply r_simple, rs_testop_i64.
    inversion H; subst; clear H.
    by iFrame.
Qed.

Lemma wp_cvtop_convert (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v v': value) (t1 t2: value_type) (sx: option sx):
  cvt t2 sx v = Some v' ->
  types_agree t1 v ->
  Φ [v'] ⊢
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
    eapply reduce_det in H; last by apply r_simple, rs_convert_success.
    inversion H; subst; clear H.
    by iFrame.
Qed.

Lemma wp_cvtop_reinterpret (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v v': value) (t1 t2: value_type):
  wasm_deserialise (bits v) t2 = v' ->
  types_agree t1 v ->
  Φ [v'] ⊢
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
    eapply reduce_det in H; last by apply r_simple, rs_reinterpret.
    inversion H; subst; clear H.
    by iFrame.
Qed.

(* Non-numerics -- stack operations, control flows *)

Lemma wp_nop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ):
  Φ [] ⊢
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
    eapply reduce_det in H; last by apply r_simple, rs_nop.
    inversion H; subst; clear H.
    by iFrame.
Qed.

Lemma wp_drop: False.
Proof.
Admitted.

Lemma wp_select: False.
Proof.
Admitted.

(* Control flows *)

Lemma wp_block: False.
Proof.
Admitted.

Lemma wp_loop: False.
Proof.
Admitted.

Lemma wp_if: False.
Proof.
Admitted.

Lemma wp_br: False.
Proof.
Admitted.

Lemma wp_br_if: False.
Proof.
Admitted.

Lemma wp_br_table: False.
Proof.
Admitted.

Lemma wp_return: False.
Proof.
Admitted.

(* Control-flow frame *)
Lemma wp_label: False.
Proof.
Admitted.



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

Lemma wp_get_local: False.
Proof.
Admitted.

Lemma wp_set_local (s : stuckness) (E : coPset) (v v0: value) (i: nat):
  N.of_nat i ↦[wl] v0 ⊢
  WP ([AI_basic (BI_const v); AI_basic (BI_set_local i)]) @ s; E {{ w, ⌜ w = [] ⌝ ∗ N.of_nat i ↦[wl] v }}.
Proof.
  iIntros "Hli".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[[hs ws] locs] inst].
  iDestruct "Hσ" as "(? & ? & ? & ? & Hl & ?)".
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
    
Lemma wp_tee_local: False.
Proof.
Admitted.

Lemma wp_get_global: False.
Proof.
Admitted.

Lemma wp_set_global: False.
Proof.
Admitted.

Lemma wp_load: False.
Proof.
Admitted.

Lemma wp_store: False.
Proof.
Admitted.

Lemma wp_current_memory: False.
Proof.
Admitted.

Lemma wp_grow_memory: False.
Proof.
Admitted.






(* Example Programs *)

Definition my_add : expr :=
  [AI_basic (BI_const (xx 3));
     AI_basic (BI_const (xx 2));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add))].

Lemma myadd_spec (s : stuckness) (E : coPset) (Φ: val -> iProp Σ) :
  Φ [xx 5] ⊢ WP my_add @ s; E {{ v, Φ v }}.
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
  Φ [xx 5] ⊢ WP my_add2 @ s; E {{ v, Φ v }}.
Proof.
  iIntros "HΦ".
  replace my_add2 with (take 3 my_add2 ++ drop 3 my_add2) => //.
  iApply wp_seq => /=.
  instantiate (1 := fun v => (⌜ v = [xx 3] ⌝)%I ).
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

