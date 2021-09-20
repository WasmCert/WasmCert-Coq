(** Example of Iris usage **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import eqtype.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre lifting.
From iris.base_logic Require Export gen_heap proph_map.
Require Export iris iris_locations.
Require Export datatypes host operations.

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

Definition proph_id := positive.

(*
(* FIXME: This code was removed in branch type_soundness? *)
Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_gen_heapG :> gen_heapG loc val Σ;
  heapG_proph_mapG :> proph_mapG proph_id (val * val) Σ
}.
 *)

Instance heapG_irisG `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ} : irisG wasm_lang Σ := {
  iris_invG := func_invG;
  state_interp σ _ κs _ :=
    let (_, s) := σ in
     ((gen_heap_interp (gmap_of_list s.(s_funcs))) ∗
      (gen_heap_interp (gmap_of_table s.(s_tables))) ∗
      (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
      (gen_heap_interp (gmap_of_list s.(s_globals)))
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

Definition my_add : expr :=
  [AI_basic (BI_const (xx 3));
     AI_basic (BI_const (xx 2));
     AI_basic (BI_binop T_i32 (Binop_i BOI_add))].

Lemma wp_nil `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ} (s : stuckness) (E : coPset) (Φ : iProp Σ) :
  Φ ⊢ WP [] @ s ; E {{ fun v => Φ }}%I.
Proof.
  iIntros "H".
  by rewrite wp_unfold /wp_pre.
Qed.

Lemma to_val_cat (es1 es2: list administrative_instruction) (vs: val) :
  iris.to_val (es1 ++ es2) = Some vs ->
  iris.to_val es1 = Some (take (length es1) vs) /\
  iris.to_val es2 = Some (drop (length es1) vs).
Admitted.

Let prim_step := @iris.prim_step host_function host_instance.

Lemma prim_step_cat_reduce (es1 es2 es' : list administrative_instruction) σ σ' obs1 obs2 :
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
  
(* behaviour of seq might be a bit unusual due to how reductions work. *)
Lemma wp_seq `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ} (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) :
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
      apply prim_step_cat_reduce in HStep as [es'' [-> HStep]] => //.
      iSpecialize ("H2" $! es'' σ2 efs HStep).
      iMod "H2".
      repeat iModIntro.
      repeat iMod "H2".
      iModIntro.
      destruct σ2 as [i s0].
      iDestruct "H2" as "((Hwf & Hwt & Hwm & Hwg) & Hes'' & Hefs)".
      iFrame.
      iApply "IH".
      by iFrame.
  }
Qed.

Lemma wp_val `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ} (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v0 : value) (es : language.expr wasm_lang) (v : val) :
  WP es @ s ; E {{ v, (Φ (v0 :: v)) }}%I
  ⊢ WP ((AI_basic (BI_const v0)) :: es) @ s ; E {{ v, Φ v }}%I.
Proof.
Admitted. (* TODO *)

Lemma myadd_spec `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ} (s : stuckness) (E : coPset) (Φ : val -> iProp Σ) (v : val) :
  (Φ (xx 5 :: v)) -∗ WP my_add @ s;E {{ Φ }}%I.
Proof.
  iIntros "HΦ".
  unfold my_add.

  iApply wp_value.
  simpl.
  (* FIXME: iApply. *)
Admitted.

End Host.

