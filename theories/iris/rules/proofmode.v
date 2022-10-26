From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.bi Require Export weakestpre.
Require Import iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Import iris_rules iris_example_helper.
Require Import datatypes operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

Lemma build_llfill_local n f llh es e l1 l2 :
  llfill llh e = es ->
  llfill (LL_local l1 n f llh l2) e = (v_to_e_list l1) ++ [AI_local n f es] ++ l2.
Proof.
  simpl. intros ->. auto.
Qed.
Lemma build_llfill_label n es' llh es e l1 l2 :
  llfill llh e = es ->
  llfill (LL_label l1 n es' llh l2) e = (v_to_e_list l1) ++ [AI_label n es' es] ++ l2.
Proof.
  simpl. intros ->. auto.
Qed.
Lemma build_llfill_base l1 l2 e :
  llfill (LL_base l1 l2) e = (v_to_e_list l1) ++ e ++ l2.
Proof. simpl. auto. Qed.

Class DecomposeLocal (l: list administrative_instruction) l1 n f es l2 :=
  { MkDecomposeLocal: l = (v_to_e_list l1) ++ [AI_local n f es] ++ l2 }.

Hint Mode DecomposeLocal ! - - - - - : typeclass_instances.

Instance DecomposeLocalConsHere : forall n f es l2, DecomposeLocal (AI_local n f es :: l2) [] n f es l2.
Proof. intros. constructor. auto. Qed.

Instance DecomposeLocalCons : forall n f es l2 l l' e, DecomposeLocal l2 l n f es l' -> DecomposeLocal ((AI_basic (BI_const e)) :: l2) (e :: l) n f es l'.
Proof.
  intros. constructor. inversion H. rewrite MkDecomposeLocal0.
  simpl. auto.
Qed.

Lemma decompose_local_list l l1 l2 es n f :
  DecomposeLocal l l1 n f es l2 ->
  l = v_to_e_list l1 ++ [AI_local n f es] ++ l2.
Proof.
  intros D. destruct D. auto.
Qed.

Ltac build_llfill_local :=
  match goal with
  | |- context [ llfill _ _ = ?l ] =>
      erewrite (decompose_local_list);[|once (typeclasses eauto)];
      apply build_llfill_local
  end.

Class DecomposeLabel (l: list administrative_instruction) l1 n f es l2 :=
  { MkDecomposeLabel: l = (v_to_e_list l1) ++ [AI_label n f es] ++ l2 }.

Hint Mode DecomposeLabel ! - - - - - : typeclass_instances.

Instance DecomposeLabelConsHere : forall n f es l2, DecomposeLabel (AI_label n f es :: l2) [] n f es l2.
Proof. intros. constructor. auto. Qed.

Instance DecomposeLabelCons : forall n f es l2 l l' e, DecomposeLabel l2 l n f es l' -> DecomposeLabel ((AI_basic (BI_const e)) :: l2) (e :: l) n f es l'.
Proof.
  intros. constructor. inversion H. rewrite MkDecomposeLabel0.
  simpl. auto.
Qed.

Lemma decompose_label_list l l1 l2 es n f :
  DecomposeLabel l l1 n f es l2 ->
  l = v_to_e_list l1 ++ [AI_label n f es] ++ l2.
Proof.
  intros D. destruct D. auto.
Qed.

Ltac build_llfill_label :=
  match goal with
  | |- context [ llfill _ _ = ?l ] =>
      erewrite (decompose_label_list);[|typeclasses eauto];
      apply build_llfill_label
  end.

Class DecomposeBase l e l1 l2 :=
  { MkDecomposeBase: l = (v_to_e_list l1) ++ e ++ l2 }.

Hint Mode DecomposeBase ! ! - - : typeclass_instances.

(* Instance DecomposeBaseAppHere : forall e l2, DecomposeBase (e ++ l2) e [] l2. *)
(* Proof. intros. constructor. auto. Qed. *)

Instance DecomposeBaseConsSingletonHere : forall e l2, DecomposeBase (e :: l2) [e] [] l2.
Proof. intros. constructor. auto. Qed.

Instance DecomposeBaseConsHere : forall l e es l2, DecomposeBase l es [] l2 -> DecomposeBase (e :: l) (e :: es) [] l2.
Proof. intros. constructor. inversion H;subst. simpl. auto. Qed.

Instance DecomposeBaseCons : forall l l1 e l2 e', DecomposeBase l e l1 l2 -> DecomposeBase ((AI_basic (BI_const e')) :: l) e (e' :: l1) l2.
Proof. intros. inversion H. constructor. subst. simpl. auto. Qed.

Lemma decompose_base_list l e l1 l2 :
  DecomposeBase l e l1 l2 ->
  l = v_to_e_list l1 ++ e ++ l2.
Proof.
  intros. inversion H. auto.
Qed.

Ltac build_llfill_base :=
  match goal with
  | |- context [ llfill _ _ = ?l ] =>
      erewrite (@decompose_base_list l [AI_call_host _ _ _]);[|once (typeclasses eauto)];
      apply build_llfill_base
  end.

Ltac build_llfill :=
  repeat (build_llfill_local + build_llfill_label + build_llfill_base).

Class BuildCtx i lh es LI :=
  { MkBuildCtx: lfilled i lh es LI }.

Hint Mode BuildCtx - - ! ! : typeclass_instances.

Class DeconstructCtx i lh es LI :=
  { MkDeconstruct: lfilled i lh es LI }.

Hint Mode DeconstructCtx - - ! - : typeclass_instances.

Instance DeconstructCtxBaseApp :
  forall es l1 l2,
    DeconstructCtx 0 (LH_base (v_to_e_list l1) l2) es (v_to_e_list l1 ++ es ++ l2).
Proof.
  intros.
  constructor. apply lfilled_Ind_Equivalent. constructor.
  apply v_to_e_is_const_list.
Qed.

Instance BuildCtxBase :
  forall LI es l1 l2,
    DecomposeBase LI es l1 l2 ->
    BuildCtx 0 (LH_base (v_to_e_list l1) l2) es LI.
Proof.
  intros.
  inversion H as [Heq]. subst.
  constructor. apply lfilled_Ind_Equivalent. constructor.
  apply v_to_e_is_const_list.
Qed.

Instance DeconstructCtxLabelApp :
  forall l1 n es es' e l2 i lh,
    DeconstructCtx i lh e es ->
    DeconstructCtx (S i) (LH_rec (v_to_e_list l1) n es' lh l2) e ((v_to_e_list l1) ++ [AI_label n es' es] ++ l2).
Proof.
  intros until lh. intros B.
  inversion B as [fill%lfilled_Ind_Equivalent].
  constructor. apply lfilled_Ind_Equivalent.
  constructor;auto.
  apply v_to_e_is_const_list.
Qed.

Instance BuildCtxLabel :
  forall LI l1 n es es' e l2 i lh,
    DecomposeLabel LI l1 n es' es l2 ->
    BuildCtx i lh e es ->
    BuildCtx (S i) (LH_rec (v_to_e_list l1) n es' lh l2) e LI.
Proof.
  intros until lh. intros D B.
  inversion D as [Heq].
  inversion B as [fill%lfilled_Ind_Equivalent].
  constructor. apply lfilled_Ind_Equivalent.
  rewrite Heq. constructor;auto.
  apply v_to_e_is_const_list.
Qed.

Lemma wp_build_ctx `{!wasmG Σ} es i lh LI s E P :
  BuildCtx i lh es LI ->
  WP es @ s; E CTX i; lh {{ P }} -∗ WP LI @ s; E {{ P }}.                                  
Proof.
  iIntros (B) "W".
  inversion B as [fill].
  iDestruct ("W" $! _ fill) as "W".
  iFrame.
Qed.

Lemma wp_deconstruct_ctx `{!wasmG Σ} es i lh LI s E P :
  DeconstructCtx i lh es LI ->
  WP LI @ s; E {{ P }} -∗ WP es @ s; E CTX i; lh {{ P }}.
Proof.
  iIntros (B) "W".
  inversion B as [fill].
  iIntros (LI' fill').
  eapply lfilled_inj in fill;eauto. subst.
  iFrame.
Qed.

Ltac build_ctx e :=
  match goal with
  | |- context [ (WP ?es @ ?s; ?E {{ ?P }})%I ] =>
      iApply (@wp_build_ctx _ _ e)
  end.

Ltac deconstruct_ctx :=
  match goal with
  | |- context [ (WP ?es @ ?s; ?E CTX ?i; ?lh {{ ?P }})%I ] =>
      iApply (@wp_deconstruct_ctx _ _ es);
      try (constructor;cbn;rewrite eqseqE;eauto);
      iSimpl
  end.

Lemma bind_seq_base_imm `{!wasmG Σ} es P LI l1 l2 s E Q w :
  DecomposeBase LI es l1 l2 ->
  WP es @ E {{ λ v, ⌜v = immV w⌝ ∗ P v }}
  -∗ (∀ v, ⌜v = immV w⌝ ∗ P v
                -∗ WP (v_to_e_list l1) ++ (iris.of_val v) ++ l2 @ s; E {{ Q }})
  -∗ WP LI @ s; E {{ Q }}.
Proof.
  intros. iIntros "H1 H2".
  build_ctx es.
  rewrite <- (app_nil_r es).
  iApply (wp_seq_ctx s E Q (λ v, ⌜v = immV _⌝ ∗ _)%I es).
  iSplitR;[by iIntros "[%Hcontr _]"|].
  rewrite app_nil_r. iFrame.
  iIntros (v') "H".
  rewrite app_nil_r.
  iApply wp_base_pull. iApply wp_wasm_empty_ctx.
  iApply "H2". iFrame.
Qed.

Lemma bind_seq_base_callhost `{!wasmG Σ} es P LI l1 l2 s E Q a1 a2 a3 a4 :
  DecomposeBase LI es l1 l2 ->
  WP es @ E {{ λ v, ⌜v = callHostV a1 a2 a3 a4⌝ ∗ P v }}
  -∗ (∀ v, ⌜v = callHostV a1 a2 a3 a4⌝ ∗ P v -∗ WP (v_to_e_list l1) ++ (iris.of_val v) ++ l2 @ s; E {{ Q }})
  -∗ WP LI @ s; E {{ Q }}.
Proof.
  intros. iIntros "H1 H2".
  build_ctx es.
  rewrite <- (app_nil_r es).
  iApply (wp_seq_ctx s E Q (λ v, ⌜v = callHostV a1 a2 a3 a4⌝ ∗ _)%I es).
  iSplitR;[by iIntros "[%Hcontr _]"|].
  rewrite app_nil_r. iFrame.
  iIntros (v') "H".
  rewrite app_nil_r.
  iApply wp_base_pull. iApply wp_wasm_empty_ctx.
  iApply "H2". iFrame.
Qed.

Ltac bind_seq_base_imm e h :=
  iApply (@bind_seq_base_imm _ _ e with h).

Tactic Notation "bind_seq_base_imm" constr(e) "with" constr(h) :=
  bind_seq_base_imm e h.

Ltac bind_seq_base_callhost e h :=
  iApply (@bind_seq_base_callhost _ _ e with h).

Tactic Notation "bind_seq_base_callhost" constr(e) "with" constr(h) :=
  bind_seq_base_callhost e h.

Ltac take_drop_app_rewrite n :=
  match goal with
  | |- context [ WP ?e @ _; _ CTX _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  | |- context [ WP ?e @ _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  | |- context [ WP ?e @ _; _ FRAME _; _ CTX _; _  {{ _, _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  | |- context [ WP ?e @ _; _ FRAME _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  end.
  
Ltac take_drop_app_rewrite_twice n m :=
  take_drop_app_rewrite n;
  match goal with
  | |- context [ WP _ ++ ?e @ _; _ CTX _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop (length e - m) e);simpl take; simpl drop
  | |- context [ WP _ ++ ?e @ _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop (length e - m) e);simpl take; simpl drop
  end.
