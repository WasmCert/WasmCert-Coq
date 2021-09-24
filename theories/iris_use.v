(** Example of Iris usage **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre lifting.
From iris.base_logic Require Export gen_heap proph_map.
Require Export iris iris_locations.
Require Export datatypes host operations opsem.
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

Let wasm_mixin : LanguageMixin _ _ _ := wasm_mixin host_instance.

Canonical Structure wasm_lang := Language wasm_mixin.

Let expr := iris.expr.
Let val := iris.val.

(*
Record loc := { loc_car : Z }.
Instance loc_eq_decision : EqDecision loc.
Proof. solve_decision. Defined.

Instance loc_inhabited : Inhabited loc := populate {|loc_car := 0 |}.

Instance loc_countable : Countable loc.
Proof. by apply (inj_countable' loc_car (λ i, {| loc_car := i |})); intros []. Qed.

(* FIXME *)
Program Instance loc_infinite : Infinite loc :=
  inj_infinite (λ p, {| loc_car := p |}) (λ l, Some (loc_car l)) _.
Next Obligation. done. Qed.
*)

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
Notation " ↦[wi] v" := (mapsto (L:=unit) (V:=instance) tt (DfracOwn 1) v%V)
                      (at level 20, format " ↦[wi] v") : bi_scope.

Definition proph_id := positive.

(*
(* FIXME: This code was removed in branch type_soundness? *)
Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_gen_heapG :> gen_heapG loc val Σ;
  heapG_proph_mapG :> proph_mapG proph_id (val * val) Σ
}.
 *)

Instance heapG_irisG `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ, !wlocsG Σ, !winstG Σ} : irisG wasm_lang Σ := {
  iris_invG := func_invG;
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

Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : iris.prim_step ?e _ _ _ _ _ |- _ =>
     inversion H; subst; clear H
  | H : _ = [] /\ _ = [] |- _ => (* this is to resolve the resulting equalities from head_step. *) 
     destruct H
         end.

Definition xx i := (VAL_int32 (Wasm_int.int_of_Z i32m i)).

Let empty_instance := Build_instance [] [] [] [] [].

Definition my_add : expr :=
  [AI_basic (BI_const (xx 3));
     AI_basic (BI_const (xx 2));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add))].

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
  
Lemma wp_nil `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ, !wlocsG Σ, !winstG Σ} (s : stuckness) (E : coPset) (Φ : iProp Σ) :
  Φ ⊢ WP [] @ s ; E {{ fun v => Φ }}%I.
Proof.
  iIntros "H".
  by rewrite wp_unfold /wp_pre.
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
  
Let prim_step := @iris.prim_step host_function host_instance.

(* This is not actually true. We need another way to prove the wp_val lemma. *)
Lemma prim_step_split_reduce_l (es1 es2 es' : list administrative_instruction) vs σ σ' obs1 obs2 :
  iris.to_val es1 = Some vs ->
  prim_step (es1 ++ es2) σ obs1 es' σ' obs2 ->
  exists es'', es' = es1 ++ es'' /\ prim_step es2 σ obs1 es'' σ' obs2.
Proof.
  move: es2 es' vs σ σ' obs1 obs2.
  elim: es1 => //=.
  - move => es2 es' vs σ σ' obs1 obs2 H HStep.
    inversion H; subst; clear H.
    by exists es'. 
  - move => a l IH es2 es' vs σ σ' obs1 obs2 H HStep.
    destruct a => //=.
    destruct b => //=.
    
Admitted.

Lemma prim_step_split_reduce_r (es1 es2 es' : list administrative_instruction) σ σ' obs1 obs2 :
  iris.to_val es1 = None ->
  prim_step (es1 ++ es2) σ obs1 es' σ' obs2 ->
  exists es'', es' = es'' ++ es2 /\ prim_step es1 σ obs1 es'' σ' obs2.
Proof.
Admitted.

Lemma prim_step_append_reduce (es1 es2 es' : list administrative_instruction) σ σ' obs1 obs2 :
  iris.to_val es1 = None ->
  prim_step es1 σ obs1 es' σ' obs2 ->
  prim_step (es1 ++ es2) σ obs1 (es' ++ es2) σ' obs2.
Proof.
Admitted.

Lemma append_reducible (es1 es2: list administrative_instruction) σ:
  iris.to_val es1 = None ->
  @reducible wasm_lang es1 σ ->
  @reducible wasm_lang (es1 ++ es2) σ.
Proof.
Admitted.

Lemma prepend_reducible (es1 es2: list administrative_instruction) vs σ:
  iris.to_val es1 = Some vs ->
  @reducible wasm_lang es2 σ ->
  @reducible wasm_lang (es1 ++ es2) σ.
Proof.
Admitted.
  
(* behaviour of seq might be a bit unusual due to how reductions work. *)
Lemma wp_seq `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ, !wlocsG Σ, !winstG Σ} (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) :
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

Lemma wp_val `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ, !wlocsG Σ, !winstG Σ} (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v0 : value) (es : language.expr wasm_lang) :
  WP es @ s ; E {{ v, (Φ (v0 :: v)) }}%I
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
      eapply prim_step_split_reduce_l in HStep; eauto.
      destruct HStep as [es'' [-> HStep]].
      iSpecialize ("H" $! es'' σ2 efs HStep).
      iMod "H".
      repeat iModIntro.
      repeat iMod "H".
      iModIntro.
      iDestruct "H" as "(Hσ & Hes & Hefs)".
      iFrame.
      rewrite -> cat1s.
      by iApply "IH".
  }
Qed.

Local Lemma binop_reduce: forall hs f ws hs' f' ws' es v1 v2 v t op,
  app_binop op v1 v2 = Some v ->
  @reduce host_function host_instance hs f ws [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] hs' f' ws' es ->
  (hs', f', ws', es) = (hs, f, ws, [AI_basic (BI_const v)]).
Proof.
  move => hs f ws hs' f' ws' es v1 v2 v t op Hbinop HRed.
  inversion HRed; subst=> //=.
  - inversion H; subst => //=; clear H; try by rewrite H5 in Hbinop; inversion Hbinop; subst.
    + by repeat destruct vs => //.
    + by repeat destruct vs => //.
    + clear H0.
      move/lfilledP in H1.
      inversion H1; subst; clear H1.
      by repeat destruct vs => //.
  - by repeat destruct vcs => //=.      
  - by repeat destruct vcs => //=.      
  - by repeat destruct vcs => //=.      
  - (* r_label case is problematic since it has a case of self-implication *)
    admit.
Admitted.
  
Lemma wp_binop `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ, !wlocsG Σ, !winstG Σ} (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v1 v2 v : value) (t: value_type) (op: binop):
  app_binop op v1 v2 = Some v ->
  Φ [v] ⊢
  WP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] @ s; E {{ v, Φ v }}.
Proof.
  iIntros (Hbinop) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iModIntro.
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
    eapply binop_reduce in H as H; eauto.
    inversion H; subst; clear H.
    by iFrame.
Qed.
(*
Local Lemma myadd_reduce: forall hs f ws hs' f' ws' es,
  @reduce host_function host_instance hs f ws my_add hs' f' ws' es ->
  (hs', f', ws') = (hs, f, ws) /\ es = [AI_basic (BI_const (xx 5))].
Proof.
  move => hs f ws hs' f' ws' es HRed.
  unfold my_add in HRed.
  dependent induction HRed; subst=> //=.
  - inversion H; subst => //=; clear H; try by (simpl in H5; inversion H5).
    + by repeat destruct vs => //.
    + by repeat destruct vs => //.
    + clear H0.
      move/lfilledP in H1.
      inversion H1; subst; clear H1.
      by repeat destruct vs => //.
  - by repeat destruct vcs => //=.      
  - by repeat destruct vcs => //=.      
  - by repeat destruct vcs => //=.      
  - move/lfilledP in H0.
    move/lfilledP in H.
    inversion H; subst; clear H; last by repeat destruct vs => //.
    (* r_label case is problematic since it has a case of self-implication *)
    admit.
Admitted.
  *)
Lemma myadd_spec `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ, !wlocsG Σ, !winstG Σ} (s : stuckness) (E : coPset) (Φ: val -> iProp Σ) :
  Φ [xx 5] ⊢ WP my_add @ s; E {{ v, Φ v }}.
Proof.
  iIntros "HΦ".
  unfold my_add.
  by iApply wp_binop.
Qed.

Print r_invoke_native.

Print datatypes.function_closure.

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

