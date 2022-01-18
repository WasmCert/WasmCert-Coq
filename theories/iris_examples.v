From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_rules.
Require Export datatypes host operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

(* Example Programs *)
Section Examples.
  
Import DummyHosts.
Let reduce := @reduce host_function host_instance.

Let reducible := @reducible wasm_lang.

Context `{!wfuncG Σ, !wtabG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ}.

Definition xx i := (VAL_int32 (Wasm_int.int_of_Z i32m i)).
Definition xb b := (VAL_int32 (wasm_bool b)).

Let expr := iris.expr.

Definition my_add : expr :=
  [AI_basic (BI_const (xx 3));
     AI_basic (BI_const (xx 2));
  AI_basic (BI_binop T_i32 (Binop_i BOI_add))].

Lemma myadd_spec (s : stuckness) (E : coPset) (Φ: val -> iProp Σ) (f0: frame): 
  ↪[frame] f0 -∗ Φ (immV [xx 5]) -∗ WP my_add @ s; E {{ v, Φ v ∗  ↪[frame] f0  }}.
Proof.
  iIntros "HP".
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

Lemma myadd2_spec (s : stuckness) (E : coPset) (Φ: val -> iProp Σ) f0:
  ↪[frame] f0 -∗ Φ (immV [xx 5]) -∗ WP my_add2 @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros "Hf0 HΦ".
  replace my_add2 with (take 3 my_add2 ++ drop 3 my_add2) => //.
  iApply wp_seq => /=.
  instantiate (1 := fun v => (⌜ v = immV [xx 3] ⌝ ∗ ↪[frame] f0)%I ).
  iSplitL ""; first by iIntros "(%H & ?)".
  iSplitL "Hf0"; first by iApply (wp_binop with "[$]") => //.
  iIntros (?) "(-> & Hf0)" => /=.
  by iApply (wp_binop with "[$]").
Qed.

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
Lemma label_check_easy f0:
  ↪[frame] f0
  ⊢ WP [::AI_basic
         (BI_block (Tf [] [T_i32;T_i32])
            [::BI_const (xx 2); BI_const (xx 3)] )] {{ λ v, ⌜v = immV [xx 2;xx 3]⌝ ∗ ↪[frame] f0}}.
Proof.
  rewrite -iRewrite_nil_l.
  iIntros "Hf0"; iApply (wp_block with "[$]");eauto. iNext.
  iIntros "Hf0".
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil. simpl.
  iApply (wp_val_return with "[$]");auto.
  iIntros "Hf0"; iApply wp_value;eauto. done.
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

End Examples.
