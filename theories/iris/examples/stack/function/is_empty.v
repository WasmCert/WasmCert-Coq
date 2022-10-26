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
  is_empty: [i32] -> [i32]
  locals declared: []

  Given a stack pointer, determine if the stack is empty.

  Implemented by comparing the stack top pointer against the stack pointer itself: in the case of an empty stack,
    the stack top pointer will be identical to the stack pointer itself.
  Performs an input validation check prior to execution. Can trap only if validation fails.

  Returns 1 if the stack is empty, 0 otherwise.

  Parameters/Locals:
  0 (input)     stack pointer
*)
Definition is_empty_op :=
  [
    BI_get_local 0 ;
    BI_get_local 0 ;
    BI_load T_i32 None N.zero N.zero ;
    BI_relop T_i32 (Relop_i ROI_eq)
  ].


Definition is_empty :=
  validate_stack 0 ++
  validate_stack_bound 0 ++
  is_empty_op.

End code.



Section specs.
  
Lemma spec_is_empty_op f0 n v s E: 
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ (f_locs f0) !! 0 = Some (value_of_int v) ⌝ ∗ 
        ↪[frame] f0 ∗
        isStack v s n }}}
    to_e_list is_empty_op @  E
    {{{ w, ∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s n ∗
                           ⌜ (k = 1 /\ s = []) \/
                  (k = 0 /\ s <> []) ⌝ ∗
           ↪[frame] f0}}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hlocv & Hf & Hstack) HΦ" => /=.

  
  rewrite separate1.
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int v] ⌝ ∗ ↪[frame] f0)%I).
  iSplitR.
  by iIntros "[%Habs _]".
  iSplitL "Hf".
  - iApply (wp_get_local with "[] [$Hf]") => //=.
  - iIntros (w) "[-> Hf]".
    rewrite - separate1.
    rewrite separate2.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [value_of_int v%Z; value_of_int v%Z] ⌝ ∗ ↪[frame] f0)%I).
    iSplitR.
    by iIntros "[%Habs _]".
    iSplitL "Hf".
  - rewrite separate1.
    iApply wp_val_app => //=.
    iSplitR.
    by iIntros "!> [%Habs _]".
    iApply (wp_get_local with "[] [$Hf]") => //=.
  - iIntros (w) "[-> Hf]".
    rewrite - separate2.
    rewrite separate3.
    iApply wp_seq.
    instantiate ( 1 := λ x, ((((⌜ x = immV [value_of_int v%Z ;
                                            value_of_int (v + length s * 4)%Z] ⌝
                                          ∗ [∗ list] i↦w ∈ s,
                                N.of_nat n ↦[i32][ Z.to_N (v + length s * 4 -  4 * i)] w) ∗
                                           (∃ bs, ⌜ (Z.of_nat (length bs) = two16 - 4 - length s * 4)%Z ⌝ ∗ N.of_nat n↦[wms][Z.to_N (v + length s * 4) + 4]bs))
                                           ∗  N.of_nat n↦[wms][(Wasm_int.N_of_uint i32m (Wasm_int.int_of_Z i32m v) + N.zero)%N]bits (value_of_int (v + length s * 4)) )
                                           ∗ ↪[frame] f0)%I).
    iSplitR ; first by iIntros "[[[[%Habs _ ]_ ] _] _]".
    iDestruct "Hstack" as "(%Hdiv & %Hvb & %Hlen & Hv & Hs & Hrest)". 
    iSplitR "HΦ".
  - rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [[[[%Habs _ ] _ ] _ ] _ ]".
    unfold value_of_int.
    iApply wp_load => //=.
    iSplitL "Hs Hrest".
    iFrame.
    done.
    iFrame.
    rewrite N.add_0_r.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold ffff0000 in Hvb; rewrite u32_modulus ; lia.
    iDestruct (i32_wms with "Hv") as "Hv" => //.
  - iIntros (w) "[[[[->  Hs] Hrest] Hp] Hf]".
    iAssert (isStack v s n)%I with "[Hrest Hp Hs]" as "Hstack".
    unfold isStack.
    iFrame.
    rewrite N.add_0_r.
    simpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold ffff0000 in Hvb; rewrite u32_modulus ; lia.
    repeat iSplit => //=.
    iApply i32_wms => //.
  - unfold of_val, fmap, list_fmap.
    rewrite - separate2.
    iApply wp_wand_r.
    iSplitL "Hf".
    iApply (wp_relop with "Hf") => //=.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  - iIntros (w) "[-> Hf]".
    iApply "HΦ".
    iExists _.
    iSplitR.
    iPureIntro.
    unfold value_of_int.
    unfold wasm_bool.
    instantiate (1 := if Wasm_int.Int32.eq (Wasm_int.Int32.repr v)
                                           (Wasm_int.Int32.repr (v + length s * 4))
                      then 1%Z else 0%Z).
    remember (Wasm_int.Int32.eq (Wasm_int.Int32.repr v)
                                (Wasm_int.Int32.repr (v + length s * 4))) as eqv.
    rewrite - Heqeqv.
    by destruct eqv => //=.
  - iFrame "Hstack Hf".
    iPureIntro.
    destruct s.
    left.
    split => //=.
    replace (v + 0%nat * 4)%Z with v%Z ; last lia.
    by rewrite Wasm_int.Int32.eq_true.
    right.
    split => //=.
    rewrite Wasm_int.Int32.eq_false => //=.
    intro.
    unfold ffff0000 in Hvb.
    simpl in Hlen.
    unfold two14 in Hlen.
    apply Wasm_int.Int32.repr_inv in H ; try rewrite u32_modulus; by lias.
Qed.



Lemma spec_is_empty f0 n v s E: 
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ (f_locs f0) !! 0 = Some (value_of_int v) ⌝ ∗ 
        ↪[frame] f0 ∗
        isStack v s n }}}
    to_e_list is_empty @  E
    {{{ w, ∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s n ∗
                           ⌜ (k = 1 /\ s = []) \/
                  (k = 0 /\ s <> []) ⌝ ∗
           ↪[frame] f0}}}.
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
  by iApply (spec_is_empty_op with "[$Hf $Hstack] [HΦ]") => //.
Qed.

End specs.


End stack.    
      
