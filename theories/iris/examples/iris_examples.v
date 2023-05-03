From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris_example_helper.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Example Programs *)
Section Examples.
  


Context `{!wasmG Σ}.

Definition my_add : expr :=
  [AI_basic (BI_const (xx 3));
     AI_basic (BI_const (xx 2));
  AI_basic (BI_binop T_i32 (Binop_i BOI_add))].

Lemma myadd_spec (s : stuckness) (E : coPset) (Φ: val -> iProp Σ) (f0: frame): 
  ↪[frame] f0 -∗ Φ (immV [xx 5]) -∗ WP my_add @ s; E {{ v, Φ v ∗  ↪[frame] f0  }}.
Proof.
  iIntros "Hf HP".
  iApply (wp_binop with "[$]");eauto.
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

Lemma label_check_easy' f0 :
  ↪[frame] f0
  ⊢ WP [::AI_basic
         (BI_block (Tf [] [T_i32;T_i32])
                   [:: (BI_block (Tf [] [T_i32;T_i32])
                                [::BI_const (xx 2); BI_const (xx 3)] )] )] {{ λ v, ⌜v = immV [xx 2;xx 3]⌝ ∗ ↪[frame] f0 }}.
Proof.
  rewrite -iRewrite_nil_l.
  iIntros "Hf0".
  iApply (wp_block with "[$]");eauto. iNext.
  iIntros "Hf0".
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil. simpl.
  iApply iRewrite_nil_r_ctx.
  iApply (wp_seq_ctx _ _ _ (λ v, ⌜v = immV [xx 2; xx 3]⌝ ∗ ↪[frame] f0)%I).
  iSplitR; [by iIntros "[%Hcontr _]"|].
  iSplitL "Hf0"; first by iApply label_check_easy.
  iIntros (w) "(-> & Hf0)". simpl.
  iApply (wp_val_return with "[$]") ;auto.
  iIntros "Hf0".
  iApply wp_value;eauto. done.
Qed.

Lemma br_check_bind_return f0 :
  ↪[frame] f0
  ⊢ WP [::AI_basic
         (BI_block (Tf [] [T_i32])
         [:: BI_block (Tf [] [])
            [::BI_const (xx 3); BI_br 1] ])] {{ λ v, ⌜v = immV [xx 3]⌝ ∗ ↪[frame] f0}}.
Proof.
  iIntros "Hf".
  iApply iRewrite_nil_l.
  iApply (wp_block with "[$]");eauto. iNext.
  simpl. iIntros "Hf".
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil.
  simpl.
  iApply iRewrite_nil_l_ctx.
  iApply (wp_block_ctx with "[$]");eauto. iNext.
  simpl. iIntros "Hf".
  iApply wp_label_push_nil.
  simpl.
  take_drop_app_rewrite 1.
  iApply (wp_br_ctx with "[$]");auto. iNext.
  iIntros "Hf".
  iApply wp_value;auto. done.
Qed.

Lemma br_check_bind_return_2 f0 :
  ↪[frame] f0
  ⊢ WP [::AI_basic
         (BI_block (Tf [] [T_i32])
         [:: BI_block (Tf [] [])
            [::BI_const (xx 2);BI_const (xx 3); BI_br 1] ])] {{ λ v, ⌜v = immV [xx 3]⌝ ∗ ↪[frame] f0}}.
Proof.
  iIntros "Hf".
  iApply iRewrite_nil_l.
  iApply (wp_block with "[$]");eauto. iNext. iIntros "?".
  simpl.
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil.
  simpl.
  iApply iRewrite_nil_l_ctx.
  iApply (wp_block_ctx with "[$]");eauto. iNext. iIntros "?".
  simpl.
  iApply wp_label_push_nil.
  simpl.
  take_drop_app_rewrite 1.
  iApply iRewrite_nil_r_ctx.
  rewrite -app_assoc.
  iApply wp_base_push;auto.
  take_drop_app_rewrite 1.
  iApply (wp_br_ctx with "[$]");auto. iNext. iIntros "?".
  iApply wp_value;auto. done.
Qed.

Lemma br_check_bind_return_3 f0 :
  ↪[frame] f0
  ⊢ WP [::AI_basic
         (BI_block (Tf [] [T_i32])
         [:: BI_block (Tf [] [])
            [::BI_const (xx 2); BI_const (xx 3); (BI_binop T_i32 (Binop_i BOI_add)); BI_br 1] ])] {{ λ v, ⌜v = immV [xx 5]⌝ ∗ ↪[frame] f0}}.
Proof.
  iIntros "Hf".
  iApply iRewrite_nil_l.
  iApply (wp_block with "[$]");eauto. iNext. simpl. iIntros "?".
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil.
  iApply iRewrite_nil_l_ctx.
  iApply (wp_block_ctx with "[$]");eauto;simpl. iNext. iIntros "?".
  iApply wp_label_push_nil. simpl.
  take_drop_app_rewrite 3.
  iApply (wp_seq_ctx _ _ _ (λ v, ⌜v = immV [xx 5]⌝ ∗ ↪[frame] f0)%I).
  iSplitR; [by iIntros "[%Hcontr _]"|].
  iSplitL.
  { iApply (wp_binop with "[$]");eauto. }
  iIntros (w) "[-> ?]". simpl.
  take_drop_app_rewrite 1.
  iApply iRewrite_nil_l_ctx.
  iApply iRewrite_nil_r_ctx. rewrite -!app_assoc.
  iApply (wp_br_ctx with "[$]");auto. iNext. iIntros "?". simpl.
  iApply wp_value;eauto. done.  
Qed.

Lemma br_check_bind_return_4 f0 :
  ↪[frame] f0
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
    {{ λ v, ⌜v = immV [xx 6]⌝ ∗ ↪[frame] f0}}.
Proof.
  iIntros "?".
  iApply iRewrite_nil_l.
  iApply (wp_block with "[$]");eauto. iNext. iIntros "?". simpl.
  iApply wp_wasm_empty_ctx.
  iApply wp_label_push_nil. simpl.
  iApply iRewrite_nil_r_ctx.
  iApply (wp_seq_ctx _ _ _ (λ v, ⌜v = immV [xx 6]⌝ ∗ ↪[frame] f0)%I).
  iSplitR; [by iIntros "[%Hcontr _]"|].
  iSplitL.
  { take_drop_app_rewrite_twice 1 1.
    iApply wp_wasm_empty_ctx.
    iApply wp_base_push;auto. simpl.
    iApply iRewrite_nil_r_ctx.
    iApply (wp_seq_ctx _ _ _ (λ v, ⌜v = immV [xx 5]⌝ ∗ ↪[frame] f0)%I).
    iSplitR; [by iIntros "[%Hcontr _]"|].
    iSplitL.
    { iApply iRewrite_nil_l.
      iApply (wp_block with "[$]");eauto. iNext. iIntros "?". simpl.
      iApply wp_wasm_empty_ctx.
      iApply wp_label_push_nil. simpl.
      iApply iRewrite_nil_l_ctx.
      iApply (wp_block_ctx with "[$]");eauto. simpl. iNext. iIntros "?".
      iApply wp_label_push_nil. simpl.
      take_drop_app_rewrite 3.
      iApply (wp_seq_ctx _ _ _ (λ v, ⌜v = immV [xx 5]⌝ ∗ ↪[frame] f0)%I).
      iSplitR; [by iIntros "[%Hcontr _]"|].
      iSplitL.
      { iApply (wp_binop with "[$]");eauto. }
      iIntros (w) "[-> ?]". simpl.
      take_drop_app_rewrite 2.
      iApply iRewrite_nil_l_ctx.
      iApply wp_base_push;auto. simpl.
      take_drop_app_rewrite 1.
      iApply (wp_br_ctx with "[$]");auto. iNext. iIntros "?".
      iApply wp_value;eauto. done. }
    iIntros (w) "[-> ?]". simpl.
    iApply wp_base;auto. simpl.
    iApply (wp_binop with "[$]");eauto. }
  iIntros (w) "[-> ?] /=".
  iApply (wp_val_return with "[$]");auto;simpl. iIntros "?".
  iApply wp_value;eauto. done.
Qed.
  

(* --------------------------------------------------------------------------------------------- *)
(* ------------------------- SIMPLE CALL INDIRECT EXAMPLE -------------------------------------- *)
(* --------------------------------------------------------------------------------------------- *)

(* Module 1 *)

Definition f1_instrs : seq.seq basic_instruction :=
  [BI_const (xx 0);
   BI_load T_i32 None 0%N 0%N].
Definition f1 : expr := to_e_list f1_instrs.
Definition store42_instrs : seq.seq basic_instruction :=
  [BI_const (xx 0);
   BI_const (xx 42);
   BI_store T_i32 None 0%N 0%N].
Definition store42 : expr := to_e_list (store42_instrs).

(* Module 2 *)

Definition store11_instrs : seq.seq basic_instruction :=
  [BI_const (xx 0);
   BI_const (xx 11);
   BI_store T_i32 None 0%N 0%N].
Definition store11 : expr := to_e_list (store11_instrs).
Definition doIt_instrs i: seq.seq basic_instruction :=
  [BI_const (xx 0);
   BI_call_indirect i].
Definition doIt i : expr := to_e_list (doIt_instrs i).

(* Note that the frame instance will be different for the spec of the two modules. *)

Lemma f1_spec f n v :
  types_agree T_i32 v ->
  f.(f_inst).(inst_memory) !! 0 = Some n ->
  ↪[frame] f -∗
  (N.of_nat n) ↦[wms][ 0%N ] (bits v) -∗
  WP f1 {{ w, (⌜w = immV [v]⌝ ∗ (N.of_nat n) ↦[wms][ 0%N ] (bits v)) ∗ ↪[frame] f }}.
Proof.
  iIntros (Htypes Hfmem) "Hf Hn".
  iApply wp_wand_r. iSplitL.
  iApply (wp_load (λ w, ⌜w = immV [v]⌝)%I with "[$Hf Hn]");eauto.
  iIntros (w) "[[-> Hn] Hf]".
  iFrame. auto.
Qed.

Lemma store42_spec f n c :
  f.(f_inst).(inst_memory) !! 0 = Some n ->
  ↪[frame] f -∗
   (N.of_nat n) ↦[wms][ 0%N ] (bits (VAL_int32 c)) -∗
   WP store42 {{ w, (⌜w = immV []⌝ ∗ (N.of_nat n) ↦[wms][ 0%N ] (bits (xx 42))) ∗ ↪[frame] f }}.
Proof.
  iIntros (Hfmem) "Hf Hn".
  iApply wp_wand_r. iSplitL.  
  iApply (wp_store (λ w, ⌜w = immV ([])⌝)%I with "[$Hf Hn]");eauto.
  by rewrite Memdata.encode_int_length.
  iIntros (v) "[[-> Hn] Hf]". rewrite /= N.add_0_l.
  iFrame. auto.
Qed.


Lemma store11_spec f n c :
  f.(f_inst).(inst_memory) !! 0 = Some n ->
  ↪[frame] f -∗
   (N.of_nat n) ↦[wms][ 0%N ] (bits (VAL_int32 c)) -∗
   WP store11 {{ w, (⌜w = immV []⌝ ∗ (N.of_nat n) ↦[wms][ 0%N ] (bits (xx 11))) ∗ ↪[frame] f }}.
Proof.
  iIntros (Hfmem) "Hf Hn".
  iApply wp_wand_r. iSplitL.  
  iApply (wp_store (λ w, ⌜w = immV ([])⌝)%I with "[$Hf Hn]");eauto.
  by rewrite Memdata.encode_int_length.
  iIntros (v) "[[-> Hn] Hf]". rewrite /= N.add_0_l.
  iFrame. auto.
Qed.

Lemma doIt_spec t i2 f0 a v n :
  (inst_types (f_inst f0)) !! t = Some (Tf [] [T_i32]) ->
  (inst_tab (f_inst f0)) !! 0 = Some t ->
  types_agree T_i32 v ->
  inst_memory i2 !! 0 = Some n ->
  (* ghost state of current instance *)
  (N.of_nat t) ↦[wt][ 0%N ] (Some a) -∗
  (N.of_nat a) ↦[wf] (FC_func_native i2 (Tf [] [T_i32]) [] f1_instrs) -∗
  ↪[frame] f0 -∗
  (* ghost state of instance i2 *)
  N.of_nat n ↦[wms][0] bits v -∗
  WP doIt t {{  λ _, True ∗ ↪[frame] f0  }}.
Proof.
  iIntros (Htype Ht Hv Hn) "Ht Ha Hf Hn".
  iApply (wp_call_indirect_success with "[Ht] Ha Hf");eauto.
  iNext. iIntros "[Ht [Ha Hf]]".
  take_drop_app_rewrite 0.
  iApply (wp_invoke_native with "Hf Ha");eauto.
  iNext. iIntros "[Hf Ha] /=".
  rewrite /= -wp_frame_rewrite.
  iApply wp_wasm_empty_ctx_frame.
  take_drop_app_rewrite 1.
  iApply (wp_seq_ctx_frame _ _ _ (λ w, ⌜w = immV [v]⌝ ∗ N.of_nat n↦[wms][0]bits v)%I).
  { intros LI HLI%lfilled_Ind_Equivalent. inversion HLI;subst. cbn. auto. }
  iFrame "Hf".
  iSplitR;[by iIntros "[%Hcontr _]"|].
  iSplitL "Hn".
  { iIntros "Hf /=".
    take_drop_app_rewrite 0.
    iApply (wp_block with "[$]");eauto.
    iNext. Local Opaque to_e_list.
    iIntros "Hf /=".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil. simpl push_base.
    iApply iRewrite_nil_r_ctx.
    iApply (wp_seq_ctx with "[-]").
    iSplitR; cycle 1.
    iSplitL.
    iApply (f1_spec with "Hf Hn");auto.
    iIntros (w) "[[-> Hn] Hf] /=".
    iApply (wp_val_return with "[$]");auto.
    iIntros "Hf /=".
    iApply wp_value. by instantiate (1:=immV [_]).
    iFrame. auto.
    by iIntros "[[%Hcontr _] _]".
  }

  iIntros (w) "[[-> Hn] Hf] /=".
  iApply wp_wasm_empty_ctx_frame.
  iApply (wp_frame_value with "[$]");eauto.
Qed.

End Examples.

