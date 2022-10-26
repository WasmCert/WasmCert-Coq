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


Print BI_relop.
 
Section code.

Definition is_full :=
  validate_stack 0 ++
  validate_stack_bound 0 ++
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


End code.

Section specs.

Lemma spec_is_full f0 n (v : Z) (s : seq.seq i32) E: 
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ (f_locs f0) !! 0 = Some (value_of_int v) ⌝ ∗ 
        ↪[frame] f0 ∗
        isStack v s n }}}
    to_e_list is_full @ E
    {{{ w, ∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s n ∗
                           ⌜ k = 1 \/ (length s < two14 - 1)%Z ⌝ ∗
          ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1⌝ }}}.
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
  
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int 1 ; value_of_int 0 ;
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
 (*   iDestruct "Hstack" as "(%Hdiv & %Hvb & %Hlen & Hv & Hs & Hrest)".
    iSplitR; last iSplitL "Hf Hv".
    2: {
      rewrite separate2.
      iApply wp_val_app => //.
      iSplitR.
      2: {
        iApply (wp_wand with "[Hf Hv]").
        iApply wp_load => //.
        2: {
          iFrame "Hf".
          iSplitR; last first.
          iDestruct (i32_wms with "Hv") as "Hv" => //.
          rewrite N.add_0_r => /=.
          rewrite Wasm_int.Int32.Z_mod_modulus_eq.
          rewrite Z.mod_small; last by unfold ffff0000 in Hvb; rewrite u32_modulus; lias.
          by instantiate (1 := VAL_int32 _) => /=.
          by instantiate (1 := λ v, ⌜ v = immV _ ⌝%I).
        }
        { done. }
        iIntros (w) "((-> & Hv) & Hf)" => /=.
        rewrite N.add_0_r.
        instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗ (N.of_nat ↦[wms][Z.to_N _] _) ∗ ↪[frame] _)%I).
        iFrame "Hf".
        
        
        
          
          simpl.
        iDestruct (wp_load with "[] [$Hf]") as "HWP".
        iApply wp_load => //.*)
    instantiate ( 1 := λ x, ((((⌜ x = immV [value_of_int 1 ; value_of_int 0 ;
                                            value_of_int (v + length s * 4)%Z] ⌝
                                          ∗ [∗ list] i↦w ∈ s,
                                N.of_nat n ↦[i32][ Z.to_N (v + length s * 4 - 4 * i)] w) ∗

                                                                                                 (∃ bs, ⌜ (Z.of_nat (length bs) = two16 - 4 - length s * 4)%Z ⌝ ∗ N.of_nat n↦[wms][Z.to_N (v + length s * 4) + 4] bs)
                              )
                                           ∗  N.of_nat n↦[wms][(Wasm_int.N_of_uint i32m (Wasm_int.int_of_Z i32m v) + N.zero)]bits (value_of_int (v + length s * 4)) )
                               ∗ ↪[frame] f0)%I).
    iSplitR ; first by iIntros "[[[[%Habs _] _] _] _]".
    iDestruct "Hstack" as "(%Hdiv & %Hvb & %Hlen & Hv & Hs & Hrest)".
    iSplitR "HΦ".
  - rewrite separate2.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [[[[%Habs _] _] _] _]".
    unfold value_of_int.
    iApply wp_load => //.
    iSplitL "Hs Hrest".
    iFrame.
    done.
    iFrame.
    rewrite N.add_0_r.
    iSimpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold ffff0000 in Hvb; rewrite u32_modulus; lia.
    iDestruct (i32_wms with "Hv") as "Hv" => //.
  - iIntros (w) "[[[[->  Hs] Hrest] Hp] Hf]".
    iAssert (isStack v s n)%I with "[Hrest Hp Hs]" as "Hstack".
    unfold isStack.
    iFrame.
    rewrite N.add_0_r.
    simpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold ffff0000 in Hvb; rewrite u32_modulus; lia.
    repeat iSplit => //.
    iApply i32_wms => //.
  - iSimpl.
    rewrite separate5.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [value_of_int 1 ; value_of_int 0 ;
                                        value_of_int ((v + length s * 4) `mod` 65536)%Z
                                    ]⌝ ∗ ↪[frame] f0)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
    rewrite separate2.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_binop with "Hf") => //.
    iPureIntro => //=.
    unfold value_of_int.
    repeat f_equal.
    unfold Wasm_int.Int32.modu.
    rewrite wasm_int_unsigned => //.
    unfold ffff0000 in Hvb; unfold two14 in Hlen.
    clear - Hvb Hlen.
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
    remember ((v+length s * 4) `mod` 65536)%Z as modres.
    rewrite -Heqmodres.
    destruct (decide ((modres)%Z = 65532))%Z eqn:Hmod.
    { rewrite e.
      simpl.
      iApply wp_wand_r.
      iSplitL "Hf".
      iApply (wp_select_true with "Hf") => //; first by instantiate (1 := λ v, ⌜ v = immV _ ⌝%I).
      iIntros (w) "(-> & Hf)".
      iApply "HΦ".
      iExists _.
      iSplit => //.
      iFrame "Hstack".
      iSplit => //; last by iExists f0; iFrame "Hf".
      iPureIntro.
      by left.
    }
    { rewrite Wasm_int.Int32.eq_false => //=; last first.
      { move => H.
        apply Wasm_int.Int32.repr_inv in H; try by lias.
        unfold ffff0000 in Hvb; unfold two14 in Hlen.
        clear - Hvb Hlen Heqmodres.
        remember (length s) as x.
        rewrite u32_modulus.
        split.
        { assert (0 <= modres)%Z.
          subst.
          apply Z_mod_pos; by lias.
          by lias.
        }
        { assert (modres < 65536)%Z.
          subst.
          apply Z.mod_pos_bound; lias.
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
      iFrame "Hstack".
      iSplit => //; last by iExists f0; iFrame "Hf".
      iPureIntro.
      right.
      remember (length s) as x.
      rewrite - Heqx.
      clear - Hlen Heqmodres n0 Hdiv.
      unfold two14, two16 in *.
      destruct Hdiv as [e Hdiv].
      subst v.
      rewrite Z.add_comm Z_mod_plus_full in Heqmodres.
      rewrite Z.mod_small in Heqmodres; last by lias.
      by lias.
    }
Qed.    
    
End specs.


End stack.    
      
