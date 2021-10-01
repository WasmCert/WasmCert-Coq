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
Lemma wp_tee_local (s : stuckness) (E : coPset) (v v0: value) (i: nat) (ϕ: val -> Prop):
  ϕ (immV [v]) ->
  N.of_nat i ↦[wl] v0 ⊢
  WP ([AI_basic (BI_const v); AI_basic (BI_tee_local i)]) @ s; E {{ w, ⌜ ϕ w ⌝ ∗ N.of_nat i ↦[wl] v }}.
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
    exists [], [AI_basic (BI_const v); AI_basic (BI_const v); AI_basic (BI_set_local i)], (hs, ws, locs, inst), [].
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
