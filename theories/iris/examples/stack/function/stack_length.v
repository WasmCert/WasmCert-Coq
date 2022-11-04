From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export stack_common iris_fundamental proofmode.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section stack.

 Context `{!wasmG Σ}. 
 
Section code.

(*
  stack_length: [i32] -> [i32]
  locals declared: []

  Given a stack pointer, find the length of the stack.

  Implemented by simply subtracting the stack top pointer by the stack pointer.
  Performs an input validation check prior to execution. Can trap only if validation fails.

  Returns the length of the stack as a u32.

  Parameters/Locals:
  0 (input)     stack pointer
 *)
  
Definition stack_length_op :=
  [
    BI_get_local 0 ;
    BI_load T_i32 None N.zero N.zero ;
    BI_get_local 0 ;
    BI_binop T_i32 (Binop_i BOI_sub) ;
    (i32const 4) ;
    BI_binop T_i32 (Binop_i (BOI_div SX_U))
  ].


Definition stack_length :=
  validate_stack 0 ++
  validate_stack_bound 0 ++
  stack_length_op.

End code.



Section specs.
  
Lemma spec_stack_length_op f0 n (v: N) s E (len: N): 
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ (f_locs f0) !! 0 = Some (value_of_uint v) ⌝ ∗ 
        ⌜ (N.of_nat (length s) = len)%N ⌝ ∗ 
        ↪[frame] f0 ∗
        isStack v s n }}}
    to_e_list stack_length_op @ E
    {{{ w, ⌜ w = immV [value_of_uint len] ⌝ ∗ isStack v s n ∗
           ↪[frame] f0}}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hlocv & %Hlen & Hf & Hstack) HΦ" => /=.

  iDestruct (stack_pure with "Hstack") as "(%Hdiv & %Hvb & %Hlens & Hstack)".
  
  rewrite (separate1 (AI_basic _)).
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: {
    iApply (wp_get_local with "[] [$Hf]") => //.
    by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "[-> Hf]" => /=.
  rewrite separate2.
  iApply wp_seq.
  iSplitR; last iSplitL "Hstack Hf".
  2: { by iApply (stack_load_0 with "[] [$Hstack] [$Hf]") => //. }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hstack & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { rewrite separate1.
       iApply wp_val_app => //.
       iSplit.
       2: { iApply (wp_wand with "[Hf]").
            { iApply (wp_get_local with "[] [$Hf]") => //.
              by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
            }
            { iIntros (w) "(-> & Hf)" => /=.
              by instantiate (1 := λ w, (⌜ w = immV _ ⌝ ∗ ↪[frame] _)%I); iFrame.
            }
       }
       { by iIntros "!> (%Habs & _)". }
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate3.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply (wp_binop with "Hf") => //=.
       unfold Wasm_int.Int32.isub, Wasm_int.Int32.sub => /=.
       repeat rewrite Wasm_int.Int32.Z_mod_modulus_id.
       2: { unfold ffff0000 in Hvb; rewrite u32_modulus; lia. }
       2: { unfold ffff0000 in Hvb; unfold two14 in Hlens; rewrite u32_modulus.
            remember (length s) as x; rewrite - Heqx.
            lia.
       }
       rewrite Hlen.
       rewrite - N2Z.inj_sub; last lia.
       replace (v + len * 4 - v)%N with (len * 4)%N; last lia.
       by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)".
  iApply (wp_wand with "[Hf]").
  { iApply (wp_binop with "Hf") => //=.
    unfold Wasm_int.Int32.divu => /=.
    rewrite Wasm_int.Int32.Z_mod_modulus_id.
    2: { unfold ffff0000 in Hvb; unfold two14 in Hlens; rewrite u32_modulus; lia. }
    rewrite N2Z.inj_mul => /=.
    rewrite Z.div_mul => //.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  }
  
  iIntros (w) "(-> & Hf)".
  iApply "HΦ".
  by iFrame.
Qed.

Lemma spec_stack_length f0 n (v: N) s E (len: N): 
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ (f_locs f0) !! 0 = Some (value_of_uint v) ⌝ ∗ 
        ⌜ (N.of_nat (length s) = len)%N ⌝ ∗ 
        ↪[frame] f0 ∗
        isStack v s n }}}
    to_e_list stack_length @ E
    {{{ w, ⌜ w = immV [value_of_uint len] ⌝ ∗ isStack v s n ∗
           ↪[frame] f0}}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hlocv & %Hlen & Hf & Hstack) HΦ" => /=.
  
  rewrite separate4.
  iApply wp_seq.
  instantiate (1 := λ x,  (⌜ x = immV [] ⌝ ∗ isStack v s n ∗ ↪[frame] f0)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hstack Hf"; first by iApply (is_stack_valid with "[$Hstack $Hf]").
  iIntros (w) "(-> & Hstack & Hf)".
  simpl.

  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ x,  (⌜ x = immV [] ⌝ ∗ isStack v s n ∗ ↪[frame] f0)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hstack Hf"; first by iApply (is_stack_bound_valid with "[$Hstack $Hf]").
  
  iIntros (w) "(-> & Hstack & Hf)".
  simpl.
  by iApply (spec_stack_length_op with "[$Hf $Hstack] [HΦ]") => //.
Qed.

End specs.

End stack.    
      
