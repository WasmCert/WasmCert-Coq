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

(*
  is_full: [i32] -> [i32]
  locals declared: []

  Given a stack pointer, determine if the stack is full.

  Implemented by reading the stack top pointer address and taking remainder against 65536. In the case of a full stack,
  the stack top pointer will be pointing to (starting address + 65532), resulting in the remainder being 65532.
  Performs an input validation check prior to execution. Can trap only if validation fails.

  Returns 1 if the stack is full, 0 otherwise.

  Parameters/Locals:
  0 (input)     stack pointer
*)
                 
Definition is_full_op := 
  [
    i32const 1 ;
    i32const 0 ;
    BI_get_local 0 ;
    BI_load T_i32 None N.zero N.zero ;
    i32const 65536 ;
    BI_binop T_i32 (Binop_i (BOI_rem SX_U)) ;
    i32const 65532 ;
    BI_relop T_i32 (Relop_i ROI_eq) ;  
    BI_select
  ].

Definition is_full :=
  validate_stack 0 ++ validate_stack_bound 0 ++ is_full_op.

End code.

Section specs.

Lemma spec_is_full_op f0 n (v : N) (s : seq.seq i32) E: 
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ (f_locs f0) !! 0 = Some (value_of_uint v) ⌝ ∗ 
        ↪[frame] f0 ∗
        isStack v s n }}}
    to_e_list is_full_op @ E
    {{{ w, ∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s n ∗
                           ⌜ (k = 1) /\ (N.of_nat (length s) = (two14 - 1)%N)%N \/ (k = 0) /\ (N.of_nat (length s) < two14 - 1)%N ⌝ ∗
          ↪[frame] f0 }}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hlocv & Hf & Hstack) HΦ" => /=.
  
  iDestruct (stack_pure with "Hstack") as "(%Hdiv & %Hvb & %Hlens & Hstack)".
  
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int 1 ; value_of_int 0 ;
                                      value_of_uint v] ⌝ ∗ ↪[frame] f0)%I).
  iSplitR ; first by iIntros "[%Habs _]".
  iSplitL "Hf".
  - rewrite separate2.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply wp_get_local => //.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate4.
    iApply wp_seq.
    instantiate ( 1 := λ x, ((⌜ x = immV [value_of_int 1 ; value_of_int 0 ;
                                            value_of_uint (v + N.of_nat (length s) * 4)%N] ⌝
                                          ∗ isStack v s n ∗ ↪[frame] f0)%I)).
    iSplitR ; first by iIntros "(%Habs & _)".
    iSplitR "HΦ".
  - rewrite separate2.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> (%Habs & _)".
    iApply wp_wand_r.
    iSplitL.
    iApply (stack_load_0 with "[] [$] [$]") => //.
    
  - iIntros (w) "(-> & Hstack & Hf)" => /=.
    by iFrame => //.
      
  - iIntros (w) "(-> & Hstack & Hf)" => /=.
    rewrite separate5.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [value_of_int 1 ; value_of_int 0 ;
                                        value_of_uint ((v + N.of_nat (length s) * 4) `mod` 65536)%N
                                    ]⌝ ∗ ↪[frame] f0)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
    rewrite separate2.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_binop with "Hf") => //.
    iPureIntro => //=.
    unfold value_of_int, value_of_uint.
    repeat f_equal.
    unfold Wasm_int.Int32.modu.
    rewrite wasm_int_unsigned => //=.
    repeat f_equal.
    by rewrite N2Z.inj_mod.
    unfold ffff0000 in Hvb; unfold two14 in Hlens.
    clear - Hvb Hlens.
    remember (length s) as x.
    rewrite - Heqx.
    by lias.
  - iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite separate5.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [value_of_int 1 ; value_of_int 0 ; _ ]⌝ ∗ ↪[frame] f0)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
    rewrite separate2.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_relop with "Hf") => //.
  - iIntros (w) "[-> Hf]".
    iSimpl.
    remember ((v+N.of_nat (length s) * 4) `mod` 65536)%N as modres.
    rewrite -Heqmodres.
    destruct (decide (modres = 65532)%N) eqn:Hmod.
    { rewrite e.
      simpl.
      iApply wp_wand_r.
      iSplitL "Hf".
      iApply (wp_select_true with "Hf") => //; first by instantiate (1 := λ v, ⌜ v = immV _ ⌝%I).
      iIntros (w) "(-> & Hf)".
      iApply "HΦ".
      iExists _.
      iSplit => //.
      iFrame "Hstack Hf".
      iPureIntro.
      left; split => //.
      remember (length s) as x.
      rewrite - Heqx.
      unfold two14, two16 in *.
      destruct Hdiv as [m Hdiv].
      subst v.
      rewrite N.add_comm N.mod_add in Heqmodres => //.
      rewrite N.mod_small in Heqmodres; last by lias.
      by lias.
    }
    { rewrite Wasm_int.Int32.eq_false => //=; last first.
      { move => H.
        apply Wasm_int.Int32.repr_inv in H; try by lias.
        unfold ffff0000 in Hvb; unfold two14 in Hlens.
        clear - Hvb Hlens Heqmodres.
        remember (length s) as x.
        rewrite u32_modulus.
        split; first lia.
        { assert (modres < 65536)%N.
          subst.
          apply N.mod_upper_bound => //.
          by lias.
        }
      }
      iApply wp_wand_r.
      iSplitL "Hf".
      iApply (wp_select_false with "Hf") => //; first by instantiate (1 := λ v, ⌜ v = immV _ ⌝%I).
      iIntros (w) "(-> & Hf)".
      iApply "HΦ".
      iExists _.
      iSplit => //.
      iFrame "Hstack Hf".
      iPureIntro.
      right; split => //.
      remember (length s) as x.
      rewrite - Heqx.
      clear - Hlens Heqmodres n0 Hdiv.
      unfold two14, two16 in *.
      destruct Hdiv as [e Hdiv].
      subst v.
      rewrite N.add_comm N.mod_add in Heqmodres => //.
      rewrite N.mod_small in Heqmodres; last by lias.
      by lias.
    }
Qed.    
    
Lemma spec_is_full f0 n (v : N) (s : seq.seq i32) E: 
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ (f_locs f0) !! 0 = Some (value_of_uint v) ⌝ ∗ 
        ↪[frame] f0 ∗
        isStack v s n }}}
    to_e_list is_full @ E
    {{{ w, ∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s n ∗
                           ⌜ (k = 1) /\ (N.of_nat (length s) = (two14 - 1)%N)%N \/ (k = 0) /\ (N.of_nat (length s) < two14 - 1)%N ⌝ ∗
          ↪[frame] f0 }}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hlocv & Hf & Hstack) HΦ" => /=.
  
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

  by iApply (spec_is_full_op with "[$Hf $Hstack] [HΦ]") => //.
Qed.

End specs.


End stack.    
      
