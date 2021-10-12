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
  induction Hred using reduce_ind; subst; try done.
  all: try by (repeat (destruct vcs;try done)).
  { inversion H;subst.
    all: repeat (destruct vs;try done).
    apply lfilled_Ind_Equivalent in H1.
    inversion H1;subst.
    repeat (destruct vs;try done). }
  { apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    pose proof (reduce_not_nil Hred) as Hnil.
    inversion H;subst.
    { repeat destruct vs,es,es'0 => //=.
      destruct es => //=.
      destruct es, es'0 => //=.
      destruct vs, es => //=. }
    { repeat destruct vs => //=. }
  }
Qed.

Lemma reduce_store_false hs s0 f hs' s' f' es es' x0 x1 x2 x3 :
  es = [AI_basic (BI_store x0 x1 x2 x3)] ->
  reduce hs s0 f es hs' s' f' es' -> False.
Proof.
  intros Heq Hred.
  induction Hred using reduce_ind; subst; try done.
  all: try by (repeat (destruct vcs;try done)).
  { inversion H;subst.
    all: repeat (destruct vs;try done).
    apply lfilled_Ind_Equivalent in H1.
    inversion H1;subst.
    repeat (destruct vs;try done). }
  { apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    pose proof (reduce_not_nil Hred) as Hnil.
    inversion H;subst.
    { repeat destruct vs,es,es'0 => //=.
      destruct es => //=.
      destruct es, es'0 => //=.
      destruct vs, es => //=. }
    { repeat destruct vs => //=. }
  }
Qed.

Lemma reduce_store_false_2 hs s0 f hs' s' f' es es' x0 x1 x2 x3 v :
  es = [AI_basic (BI_const v); AI_basic (BI_store x0 x1 x2 x3)] ->
  reduce hs s0 f es hs' s' f' es' -> False.
Proof.
  intros Heq Hred.
  induction Hred using reduce_ind; subst; try done.
  all: try by (repeat (destruct vcs;try done)).
  { inversion H;subst.
    all: repeat (destruct vs;try done).
    apply lfilled_Ind_Equivalent in H1.
    inversion H1;subst.
    repeat (destruct vs;try done). }
  { apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    pose proof (reduce_not_nil Hred) as Hnil.
    inversion H;subst.
    { repeat destruct vs,es,es'0 => //=.
      repeat destruct es => //=.
      repeat destruct es, es'0 => //=.
      inversion H1;subst. eapply reduce_val_false;eauto.
      eauto.
      repeat destruct es => //=.
      repeat destruct vs, es => //=.
      inversion H1;subst. eapply reduce_store_false;eauto.
      all:repeat destruct vs => //=.
    }
    { repeat destruct vs => //=. }
  }
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

Lemma reduce_ves1: forall v es es' σ σ' efs obs,
    reducible es σ ->
    prim_step ([AI_basic (BI_const v)] ++ es) σ obs es' σ' efs ->
    es' = [AI_basic (BI_const v)] ++ drop 1 es'.
Proof.
Admitted.
  
Lemma reduce_ves2: forall v es es' σ σ' efs obs,
    reducible es σ ->
    prim_step ([AI_basic (BI_const v)] ++ es) σ obs es' σ' efs ->
    prim_step es σ obs (drop 1 es') σ' efs.
Proof.
Admitted.

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
   opsem for mem_grow and host function calls. However, the rest of the opsem
   are indeed deterministic. Use with caution. *)
Local Axiom reduce_det: forall hs f ws es hs1 f1 ws1 es1 hs2 f2 ws2 es2,
  reduce hs f ws es hs1 f1 ws1 es1 ->
  reduce hs f ws es hs2 f2 ws2 es2 ->
  (hs1, f1, ws1, es1) = (hs2, f2, ws2, es2).



(* A Definition of a context dependent WP for WASM expressions *)

Definition wp_wasm `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ, !wlocsG Σ, !winstG Σ}
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

Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ, !wlocsG Σ, !winstG Σ}.

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

(* empty lists, frame rules *)

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

Lemma wp_val (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v0 : value) (es : language.expr wasm_lang) :
  WP es @ NotStuck ; E {{ v, (Φ (val_combine (immV [v0]) v)) }}%I
  ⊢ WP ((AI_basic (BI_const v0)) :: es) @ s ; E {{ v, Φ v }}%I.
Proof.
  (* This also needs an iLob. *)
  iLöb as "IH" forall (v0 es Φ).
  iIntros "H".
  repeat rewrite wp_unfold /wp_pre /=.
  destruct (iris.to_val es) as [vs|] eqn:Hes.
  {
    destruct vs.
    { apply of_to_val in Hes as <-.
      iMod "H".
      by iModIntro. }
    { apply to_val_trap_is_singleton in Hes as ->.
      iIntros (σ ns κ κs nt) "Hσ".
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
      assert (iris.prim_step (host_instance:=host_instance)
                             ([AI_basic (BI_const v0)] ++ [AI_trap])%SEQ 
                             (hs, ws, locs, inst) [] [AI_trap] (hs, ws, locs, inst) []) as Hstep.
      { repeat constructor. econstructor;auto.
        instantiate (1:=LH_base [AI_basic (BI_const v0)] []).
        rewrite /lfilled /lfill => //=. }
      (* TODO: use bespoke determinism lemma *)
      unfold iris.prim_step in *.
      destruct HStep as [HStep _].
      destruct Hstep as [Hstep _].
      eapply reduce_det in HStep;[|apply Hstep].
      inversion HStep;subst. iFrame. iSplit;auto.
      iMod "H".
      iApply wp_value;[|iFrame].
      rewrite /IntoVal. auto.
    }
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

Lemma wp_val_app (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) vs v' (es : language.expr wasm_lang) :
  iris.to_val vs = Some (immV v') ->
  WP es @ NotStuck ; E {{ v, (Φ (val_combine (immV v') v)) }}%I
  ⊢ WP (vs ++ es) @ s ; E {{ v, Φ v }}%I.
Proof.
  iInduction vs as [|c vs] "IH" forall (Φ v' s E es).
  { simpl. iIntros (Hval) "HWP".
    destruct v'; inversion Hval.
    destruct s.
    2: iApply wp_stuck_weaken.
    all: iApply (wp_wand with "HWP").
    all: iIntros (v).
    all: destruct v;auto. }
  { iIntros (Hval) "HWP".
    destruct v';inversion Hval.
    { exfalso.
      destruct c.
      destruct b.
      all:try done.
      destruct (iris.to_val vs) eqn:Hsome.
      destruct v0. all: try done.
      destruct vs;done. }
    destruct c;[|destruct vs;done|done..].
    destruct b =>//=.
    destruct (iris.to_val vs) eqn:Hsome;[|done].
    destruct v1;[|done]. simplify_eq.
    iApply wp_val. iApply ("IH" $! (λ v0, Φ (val_combine (immV [v]) v0))). eauto.
    iApply (wp_wand with "HWP").
    iIntros (v'') "HH".
    iSimpl. destruct v'';auto.
  }
Qed.
                                  
(* basic instructions with simple(pure) reductions *)

(* numerics *)

Lemma wp_unop (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v v' : value) (t: value_type) (op: unop):
  app_unop op v = v' ->
  Φ (immV [v']) ⊢
  WP [AI_basic (BI_const v); AI_basic (BI_unop t op)] @ s; E {{ v, Φ v }}.
Proof.
Admitted.
  
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
    eapply reduce_det in H; last by apply r_simple, rs_relop.
    inversion H; subst; clear H.
    by iFrame.
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
    eapply reduce_det in H; last by apply r_simple, rs_testop_i32.
    inversion H; subst; clear H.
    by iFrame.
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
    eapply reduce_det in H; last by apply r_simple, rs_testop_i64.
    inversion H; subst; clear H.
    by iFrame.
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
    eapply reduce_det in H; last by apply r_simple, rs_convert_success.
    inversion H; subst; clear H.
    by iFrame.
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
    eapply reduce_det in H; last by apply r_simple, rs_reinterpret.
    inversion H; subst; clear H.
    by iFrame.
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
    eapply reduce_det in H; last by eapply r_simple, rs_br.
    inversion H; subst; clear H.
    by iFrame.
Qed.

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
  iApply (wp_seq _ _ Φ (λ ret, ⌜ret = immV (v2 ++ v1)⌝)%I).
  iSplitR.
  iApply wp_val_app. apply Hv2.
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

Lemma wp_loop: False.
Proof.
Admitted.

Lemma wp_if: False.
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
  iDestruct "Hσ" as "(? & ? & ? & ? & Hl & ?)".
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
  iDestruct "Hσ" as "(? & ? & ? & ? & Hl & ?)".
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
    iApply wp_val.
    by iApply wp_set_local.
Qed.

(* r_get_global involves finding the reference index to the global store via
   the instance first. *)
Lemma wp_get_global (s : stuckness) (E : coPset) (v: value) (inst: instance) (n: nat) (ϕ: val -> Prop) (g: global) (k: nat) :
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
  iDestruct "Hσ" as "(? & ? & ? & Hg & ? & Hi)".
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
  iApply wp_seq => /=.
  instantiate (1 := fun v => (⌜ v = immV [xx 3] ⌝)%I ).
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
