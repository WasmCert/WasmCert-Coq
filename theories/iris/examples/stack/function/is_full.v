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

Definition is_full :=
  validate_stack 0 ++
  [
    i32const 0 ;
    i32const 1 ;
    BI_get_local 0 ;
    BI_load T_i32 None N.zero N.zero ;
    i32const 65536 ;
    BI_binop T_i32 (Binop_i (BOI_rem SX_U)) ;
    BI_select
  ].


End code.

Section specs.

Lemma spec_is_full f0 n (v : Z) (s : seq.seq i32) E: 
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ (f_locs f0) !! 0 = Some (value_of_int v) ⌝ ∗ 
        ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - length s * 4 )%Z ⌝ ∗ 
        ↪[frame] f0 ∗
        isStack v s n }}}
    to_e_list is_full @ E
    {{{ w, ∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s n ∗
                           ⌜ k = 1 \/ (length s < two14 - 1)%Z ⌝ ∗
          ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1⌝ }}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hlocv & %Hv & Hf & Hstack) HΦ" => /=.
  rewrite separate4.
  iApply wp_seq.
  instantiate (1 := λ x,  (⌜ x = immV [] ⌝ ∗ isStack v s n ∗ ↪[frame] f0)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hstack Hf"; first by iApply (is_stack_valid with "[$Hstack $Hf]").
  iIntros (w) "(-> & Hstack & Hf)".
  simpl.
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int 0 ; value_of_int 1 ;
                                      value_of_int v] ⌝ ∗ ↪[frame] f0)%I).
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
    instantiate ( 1 := λ x, ((((⌜ x = immV [value_of_int 0 ; value_of_int 1 ;
                                            value_of_int (v + 4 + length s * 4)%Z] ⌝
                                          ∗ [∗ list] i↦w ∈ s,
                                N.of_nat n ↦[i32][ Z.to_N (v + 4 + length s * 4 - 4 - 4 * i)] w) ∗

                                                                                                 (∃ bs, ⌜ (Z.of_nat (length bs) = two16 - 4 - length s * 4)%Z ⌝ ∗ N.of_nat n↦[wms][Z.to_N (v + 4 + length s * 4)] bs)
                              )
                                           ∗  N.of_nat n↦[wms][(Wasm_int.N_of_uint i32m (Wasm_int.int_of_Z i32m v) + N.zero)%N]bits (value_of_int (v + 4 + length s * 4)) )
                               ∗ ↪[frame] f0)%I).
    iSplitR ; first by iIntros "[[[[%Habs _] _] _] _]".
    iDestruct "Hstack" as "(%Hdiv & %Hlen & Hv & Hs & Hrest)".
    iSplitR "HΦ".
  - rewrite separate2.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [[[[%Habs _] _] _] _]".
    iApply wp_load => //.
    iSplitL "Hs Hrest".
    iFrame.
    done.
    iFrame.
    rewrite N.add_0_r.
    iSimpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    iDestruct (i32_wms with "Hv") as "Hv" => //.
  - iIntros (w) "[[[[->  Hs] Hrest] Hp] Hf]".
    iAssert (isStack v s n)%I with "[Hrest Hp Hs]" as "Hstack".
    unfold isStack.
    iFrame.
    rewrite N.add_0_r.
    simpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    repeat iSplit => //.
    iApply i32_wms => //.
  - unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate5.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [value_of_int 0 ; value_of_int 1 ;
                                        value_of_int ((v + 4 + length s * 4) `mod` 65536)%Z
                                    ]⌝ ∗ ↪[frame] f0)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
    rewrite separate2.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_binop with "Hf") => //.
    iPureIntro => //=.
    unfold Wasm_int.Int32.modu.
    rewrite Wasm_int.Int32.unsigned_repr.
    rewrite Wasm_int.Int32.unsigned_repr.
    done.
    unfold Wasm_int.Int32.max_unsigned.
    unfold Wasm_int.Int32.modulus.
    unfold Wasm_int.Int32.wordsize.
    unfold Integers.Wordsize_32.wordsize.
    replace (two_power_nat 32) with 4294967296%Z ; last done.
    lia.
    split ; try lia.
    destruct Hv.
    apply (Z.add_le_mono v (Wasm_int.Int32.max_unsigned - 4 - length s * 4) (4 + length s * 4) (4 + length s * 4)) in H0.
    replace (Wasm_int.Int32.max_unsigned - 4 - length s * 4)%Z with (Wasm_int.Int32.max_unsigned - (4 + length s * 4))%Z in H0 ; last lia.
    rewrite Z.sub_add in H0.
    rewrite Z.add_assoc in H0.
    exact H0.
    lia.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    destruct ((v + 4 + length s * 4) `mod` 65536)%Z eqn:Hmod.
  - iApply wp_wand_r.
    iSplitL "Hf".
    iApply (wp_select_false with "Hf") => //.
    rewrite Hmod.
    done.
    instantiate (1 := λ x, ⌜ x = immV [value_of_int 1] ⌝%I).
    done.
    iIntros (w) "[-> Hf]".
    iApply "HΦ".
    iExists _.
    iSplitR => //=.
    iFrame.
    iSplitR.
    iLeft.
    done.
    iExists _ ; by iFrame.
  - iApply wp_wand_r.
    iSplitL "Hf".
    iApply (wp_select_true with "Hf") => //.
    unfold Wasm_int.int_of_Z => //=.
    unfold Wasm_int.Int32.zero.
    intro Habs.
    apply Wasm_int.Int32.repr_inv in Habs => //=.
    rewrite Hmod in Habs. done.
    rewrite Hmod.
    unfold Wasm_int.Int32.modulus.
    unfold Wasm_int.Int32.wordsize.
    unfold Integers.Wordsize_32.wordsize.
    replace (two_power_nat 32) with 4294967296%Z ; last done.
    split ; try lia.
    assert (( v + 4 + length s * 4) `mod` 65536 < 65536)%Z ; last lia.
    apply Z.mod_bound_pos ; lia.
    instantiate (1 := λ x, ⌜ x = immV [value_of_int 0] ⌝%I).
    done.
    iIntros (w) "[-> Hf]".
    iApply "HΦ".
    iExists _.
    iSplitR => //=.
    iFrame.
    iSplitR.
    iRight.
    iPureIntro.
    edestruct (Z.lt_total) as [ H | [ H | H]] => //=.     
    rewrite H in Hmod.
    replace (v + 4 + (two14 - 1) * 4 )%Z with (v + 1 * 65536)%Z in Hmod ;
      last by unfold two14 ; lia.
    rewrite Z.mod_add in Hmod.
    replace (v `mod` 65536)%Z with 0%Z in Hmod.
    done.
    unfold Z.divide in Hdiv.
    destruct Hdiv as [z ->].
    rewrite Z.mod_mul.
    done.
    unfold two16 ; lia.
    lia.
    remember (length s) as x in *.
    rewrite - Heqx in H.
    clear - Hlen H.
    lia.
    iExists _ ; by iFrame.
  - assert ( 0 <= v + 4 + length s * 4 )%Z ; first lia.
    assert (0 <65536)%Z ; first lia.
    apply (Z.mod_bound_pos _ _ H) in H0 as [Habs _].
    rewrite Hmod in Habs.
    lia.
Qed.    
    
End specs.


End stack.    
      
