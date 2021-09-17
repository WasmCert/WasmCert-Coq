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

(* behaviour of seq might be a bit unusual due to how reductions work.
  TODO: fix the formulation *)
Lemma wp_seq `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ} (s : stuckness) (E : coPset) (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) :
  (WP es1 @ s; E {{ w, Ψ w }} ∗
  ∀ w, Ψ w -∗ WP (v_to_e_list w ++ es2) @ s; E {{ v, Φ v }})%I
  ⊢ WP (es1 ++ es2) @ s; E {{ v, Φ v }}.
(*  WP es2 @ s ; E {{ fun v =>
   WP es1 @ s ; E {{ fun v' =>
     Φ (v ++ v') }}%I }}%I
  ⊢ WP (es1 ++ es2) @ s ; E {{ Φ }}%I.*)
Proof.
  elim: es1.
  { iIntros "[Hnil Hes]".
    rewrite wp_unfold /wp_pre.
    iSimpl in "Hnil".
    iSimpl.
    iSpecialize ("Hes" with "Hnil").
    iSimpl in "Hes".
    iMod "Hes".
    by iApply "Hes".
  }
  { move => e es H.
    iIntros "H".
    iSimpl.
    (* FIXME: iSimpl "H". *)
Admitted. (* TODO *)

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

