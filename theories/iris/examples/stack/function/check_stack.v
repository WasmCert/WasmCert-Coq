From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export stack_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.



Section stack.


 Context `{!wasmG Σ}. 

Section code.

Definition check_stack :=
  [
    BI_get_local 0 ;
    i32const 65536 ;
    BI_binop T_i32 (Binop_i (BOI_rem SX_U)) ;
    BI_if (Tf [] [T_i32]) [
        i32const 0
      ] [
        BI_get_local 0 ;
        BI_current_memory ;
        i32const 65536 ;
        BI_binop T_i32 (Binop_i BOI_mul) ;
        BI_relop T_i32 (Relop_i (ROI_lt SX_U))
      ]
  ].

   
End code.



Section specs.

  Lemma spec_new_stack f0 n v s E len:
    ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝
          ∗ ⌜ f0.(f_locs) !! 0 = Some (value_of_int v) ⌝
          ∗ ⌜ (0 ≤ v ≤ Wasm_int.Int32.max_unsigned)%Z ⌝
          ∗ isStack v s n
          ∗ ↪[frame] f0
          ∗ (N.of_nat n) ↦[wmlength] len }}}
      to_e_list check_stack @ E
      {{{ w, ⌜ w = immV [value_of_int 1] ⌝ ∗ ↪[frame] f0
                        ∗ (N.of_nat n) ↦[wmlength] len
                        ∗ isStack v s n}}}. 
  Proof.
    iIntros "!>" (Φ) "(%Hinst & %Hlocv & %Hv & Hstack & Hf & Hlen) HΦ" => /=.
    rewrite (separate1 (AI_basic _)).
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [value_of_int v] ⌝ ∗ ↪[frame] f0)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
    - iApply (wp_get_local with "[] [$Hf]") => //=.
    - iIntros (w) "[-> Hf]".
      unfold iris.of_val, fmap, list_fmap.
      iSimpl.
      rewrite separate3.
      iApply wp_seq.
      iSplitR ; last first.
      iSplitL "Hf".
      iApply (wp_binop with "Hf") => //=.
      by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    - iIntros (w) "[-> Hf]".
      iSimpl.
      iDestruct "Hstack" as "(% & % & Hstack)". 
      iApply (wp_if_false with "Hf").
      unfold Wasm_int.Int32.modu.
      repeat rewrite Wasm_int.Int32.unsigned_repr.
      unfold two16 in H.
      unfold Z.divide in H.
      destruct H as [z ->].
      rewrite Z.mod_mul.
      done.
      done.
      done.
      done.
    - iIntros "!> Hf".
      rewrite - (app_nil_l [AI_basic _]).
      iApply wp_wasm_empty_ctx.
      iApply (wp_block_ctx with "Hf") => //=.
      iIntros "!> Hf".
      iApply (wp_label_push_nil _ _ _ _ 0 (LH_base [] []) with "[Hf Hstack Hlen HΦ]") ;
        last unfold lfilled, lfill => //=.
      simpl.
      rewrite (separate1 (AI_basic (BI_get_local 0))).
      iApply wp_seq_ctx; eauto.
      iSplitR ; last first.
    - iSplitL "Hf".
      iApply (wp_get_local with "[] [$Hf]") => /= ; first done.
      instantiate (1 := (λ x, ( ⌜x = immV _ ⌝)%I)) => //=.
    - iIntros (w) "[-> Hf]".
      iSimpl.
      rewrite separate2.
      iApply wp_seq_ctx.
      iSplitR ; last first.
      iSplitL "Hf Hlen".
    - rewrite separate1.
      iApply wp_val_app ; first done.
      iSplitR ; last first.
      iApply wp_wand_r.
      iSplitL.
      iApply wp_current_memory.
      done.
      iFrame.
      by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
      iIntros (w) "[[-> Hlen] Hf]".
      iSimpl.
      by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] f0 ∗ _ ↦[wmlength] _)%I) ;
      iFrame.
      by iIntros "!> [% _]".
    - iIntros (w) "(-> & Hf & Hlen)".
      iSimpl.
      rewrite separate4.
      iApply wp_seq_ctx.
      iSplitR ; last first.
      iSplitL "Hf".
      rewrite separate1.
      iApply wp_val_app.
      done.
      iSplitR ; last first.
      instantiate (1 :=  λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] f0)%I).
      iApply (wp_binop with "Hf").
      done.
      done.
      by iIntros "!> [% _]".
    - iIntros (w) "[-> Hf]".
      iSimpl.
      rewrite separate3.
      iApply wp_seq_ctx.
      iSplitR ; last first.
      iSplitL "Hf".
      iApply (wp_relop with "Hf").
      done.
      by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
      iIntros (w) "[-> Hf]".
      iSimpl.
      iIntros (lh) "%Hfill".
      unfold lfilled, lfill in Hfill ; simpl in Hfill.
      apply b2p in Hfill as ->.
      iApply wp_wand_r.
      iSplitL "Hf".
      iApply (wp_label_value with "Hf").
      done.
      by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
      iIntros (w) "[-> Hf]".
      iApply "HΦ".
      unfold Wasm_int.Int32.imul.
      unfold Wasm_int.Int32.mul.
      repeat rewrite Wasm_int.Int32.unsigned_repr.
      replace (ssrnat.nat_of_bin (len `div` page_size) * 65536)%Z with (Z.of_N len).
      
      
      
