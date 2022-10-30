From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export stack_common is_empty.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.



Section stack.

 Context `{!wasmG Σ}. 

Print mem_block_at_pos.
 
 Lemma points_to_i32_eq n1 i1 v1 n2 i2 v2:
   n1 = n2 ->
   i1 = i2 ->
   v1 = v2 ->
   n1 ↦[i32][i1] v1 -∗
   n2 ↦[i32][i2] v2.
 Proof.
   intros -> -> ->.
   by iIntros.
 Qed.

Lemma points_to_wm_eq n1 b1 k1 n2 b2 k2:
   n1 = n2 ->
   b1 = b2 ->
   k1 = k2 ->
   n1 ↦[wm][k1] b1 -∗
   n2 ↦[wm][k2] b2.
 Proof.
   intros -> -> ->.
   by iIntros.
 Qed.
 
Lemma points_to_wms_eq n1 l1 k1 n2 l2 k2:
   n1 = n2 ->
   l1 = l2 ->
   k1 = k2 ->
   n1 ↦[wms][k1] l1 -∗
   n2 ↦[wms][k2] l2.
 Proof.
   intros -> -> ->.
   by iIntros.
 Qed.
 
Section code.


(*
  pop: [i32] -> [i32]
  locals declared: [i32]

  Given a stack pointer, pop the top i32 value from the stack.

  Implementation contains the is_empty check which results in a trap if the stack is empty. Otherwise, load the 
  stack top pointer from the stack pointer address, retrieve the value to be popped, then decrement the stack
  top pointer address by 4 and update it.
  
  Returns the popped value of type i32. Can trap only if the stack pointer is invalid or the stack is empty.

  Parameters/Locals:
  0 (input)     stack pointer
  1             temporary variable storing the new address of the stack top pointer
*)
Definition pop_op :=
  is_empty_op ++
  [
    BI_if (Tf [] []) [BI_unreachable] [];
    BI_get_local 0 ;
    BI_load T_i32 None N.zero N.zero ;
    BI_tee_local 1 ;
    BI_load T_i32 None N.zero N.zero ;
    BI_get_local 0 ;
    BI_get_local 1 ;
    i32const 4 ;
    BI_binop T_i32 (Binop_i BOI_sub) ;
    BI_store T_i32 None N.zero N.zero
  ].

Definition pop :=
  validate_stack 0 ++ validate_stack_bound 0 ++ pop_op.

End code.

Section specs.

Lemma spec_pop_op f0 n (v:N) (a : i32) s E:
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝
         ∗ ⌜ f0.(f_locs) !! 0 = Some (value_of_uint v) ⌝
         ∗ ⌜ length f0.(f_locs) >= 2 ⌝
         ∗ isStack v (a :: s) n
         ∗ ↪[frame] f0 }}}
    to_e_list pop_op @ E
    {{{ w, ⌜ w = immV [VAL_int32 a] ⌝ ∗
                      isStack v s n ∗
                      ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝ }}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hlocv & %Hlocs & Hstack & Hf) HΦ" => /=.
  
  iDestruct (stack_pure with "Hstack") as "(%Hdiv & %Hvb & %Hlens & Hstack)".
  
  rewrite separate4.
  iApply wp_seq.
  instantiate (1 := λ x,  (⌜x = immV [value_of_int 0]⌝ ∗ isStack v (a :: s) n ∗ ↪[frame] f0)%I).
  iSplitR; last iSplitL "Hstack Hf".
  2: { iApply (spec_is_empty_op with "[$Hstack $Hf]") => //.
       iIntros (w) "H".
       iDestruct "H" as (k) "(-> & Hstack & %Hk & Hf)".
       iFrame "Hstack Hf".
       by destruct Hk as [[-> ?] | [-> _]] => //.
  }
  { by iIntros "(%Habs & ?)". }
  
  iIntros (w) "(-> & Hstack & Hf)".
  simpl.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜ w = immV [ ]⌝ ∗ ↪[frame] f0)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hf".
  iApply (wp_if_false with "Hf") => //.
  { iIntros "!> Hf".
    take_drop_app_rewrite 0.
    iApply (wp_block with "Hf") => //.
    iIntros "!> Hf /=".
      by iApply (wp_label_value with "Hf").
  }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite (separate1 (AI_basic _)).
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_uint v] ⌝ ∗ ↪[frame] f0)%I).
  iSplitR ; first by iIntros "[%Habs _]".
  iSplitL "Hf".
  - iApply (wp_get_local with "[] [$Hf]") => //=.
  - iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite separate2.
    iApply wp_seq.
    iSplitR ; last iSplitL "Hstack Hf".
    2: { by iApply (stack_load_0 with "[] [$] [$]") => //. }
    { by iIntros "(%Habs & _)". }
    
  - iIntros (w) "(-> & Hstack & Hf)" => /=.
    rewrite separate2.
    iApply (wp_seq _ _ _ (λ x, (⌜ x = immV [value_of_uint (v + N.of_nat (S (length s)) * 4)] ⌝
                                           ∗ ↪[frame] _)%I)).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - iApply (wp_tee_local with "Hf").
    iIntros "!> Hf".
    rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_set_local with "[]Hf") => //.
    
  - iIntros (w) "[-> Hf]".
    remember {| f_locs := set_nth (value_of_uint (v + N.of_nat (S (length s)) * 4)) (f_locs f0) 1
                                  (value_of_uint (v + N.of_nat (S (length s)) * 4)) ;
                f_inst := f_inst f0 |} as f1.
    rewrite - Heqf1.
    iSimpl.
    rewrite separate2.
    iApply wp_seq.
    iSplitR; last iSplitL "Hstack Hf".
    2: {
      iApply (stack_load_j_alt with "[] [] [] [] [$Hstack] [$Hf]") => //.
      { by subst f1 => /=. }
      { iPureIntro => /=.
        lia. }
      { by instantiate (1 := a) => /=. }
    }
    { by iIntros "(%Habs & _)". }
    
  - iIntros (w) "(-> & Hstack & Hf)" => /=.
    rewrite separate2.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [VAL_int32 a ; value_of_uint v] ⌝ ∗ ↪[frame] f1)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    subst.
    iApply (wp_get_local with "[] [$Hf]") => //=.
    unfold set_nth.
    by destruct (f_locs f0) => //=.
    
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate3.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [VAL_int32 a ; value_of_uint v ;
                                        value_of_uint (v + N.of_nat (S (length s)) * 4)] ⌝ ∗
                                       ↪[frame] f1)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - rewrite separate2.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_get_local with "[] [$Hf]") => //=.
    subst f1 => //=.
    by rewrite set_nth_read.
      
  - iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite separate5.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [VAL_int32 a ; value_of_uint v ;
                                        value_of_uint (v + N.of_nat (length s) * 4)] ⌝ ∗
                                       ↪[frame] f1)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
    rewrite (separate2 (AI_basic _)).
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_binop with "Hf") => //.
    simpl.
    iModIntro.
    iPureIntro.
    unfold value_of_uint.
    repeat f_equal.
    unfold Wasm_int.Int32.isub, Wasm_int.Int32.sub => /=.
    f_equal.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    remember (length s) as x.
    rewrite - Heqx.
    rewrite Z.mod_small; first by lias.
    unfold ffff0000 in Hvb.
    unfold two14 in Hlens. simpl in Hlens.
    rewrite - Heqx in Hlens.
    rewrite u32_modulus.
    by lias.

  - iIntros (w) "[-> Hf]".
    iSimpl.
    iApply wp_wand_r.
    iDestruct "Hstack" as "(_ & _ & _ & Hp & Hrest)".
    iSplitL "Hp Hf".
  - rewrite (separate1 (AI_basic _)).
    iApply wp_val_app => //.
    instantiate (1 := λ x, ((⌜ x = immV [VAL_int32 a] ⌝ ∗
                                       N.of_nat n↦[wms][Wasm_int.N_of_uint i32m
                                                                           (Wasm_int.int_of_Z i32m (Z.of_N v)) + N.zero]bits (value_of_uint (v + N.of_nat (length s) * 4))) ∗ ↪[frame] f1)%I).
    iSplit ; first by iIntros "!> [[%Habs _] _]".
    iApply wp_store => //.
    instantiate (1 := bits (value_of_uint (v + N.of_nat (length (a :: s)) * 4))) => //=.
    subst f1 => //=.
    iSimpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small; last by unfold ffff0000 in Hvb; rewrite u32_modulus; lias.
    rewrite N.add_0_r N2Z.id.
    iFrame.
    iSplitR => //=.
    by iDestruct (i32_wms with "Hp") as "Hp" => //.
    
  - iIntros (w) "[[-> Hp] Hf]".
    iApply "HΦ".
    iSplitR => //.
    unfold isStack.
    rewrite cons_length in Hlens.
    iSplitR "Hf".
    repeat iSplit => //.
    iPureIntro.
    remember (length s) as x. clear Heqx s ; lia.
    iSplitL "Hp".
  - simpl. rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small; last by unfold ffff0000 in Hvb; rewrite u32_modulus; lias.
    rewrite N.add_0_r.
    iApply i32_wms => //.
  - unfold value_of_uint => /=.
    remember (length s) as x. rewrite - Heqx.
    by rewrite N2Z.id.
    iDestruct "Hrest" as "((Ha & Hs) & Hrest)".
    iSplitL "Hs".
    iApply (big_sepL_impl with "Hs").
    iIntros "!>" (k y) "% H".
    rewrite cons_length.
    remember (length s) as x.
    iApply (points_to_i32_eq with "H") => //.
    lia.
  - iDestruct "Hrest" as (bs) "(%Hbs & Hrest)".
    iExists (serialise_i32 a ++ bs).
    iSplit.
    iPureIntro.
    rewrite app_length.
    rewrite Nat2N.inj_add.
    rewrite Hbs.
    remember (serialise_i32 a) as l.
    repeat (destruct l ; first done).
    destruct l ; last done.
    repeat rewrite cons_length.
    rewrite nil_length.
    remember (length s) as x.
    unfold two16.
    unfold two14 in Hlens.
    by lias.
  - unfold mem_block_at_pos.
    rewrite big_sepL_app.
    iSplitL "Ha".
    iDestruct (i32_wms with "Ha") as "Ha".
    iApply (big_sepL_impl with "Ha").
    iIntros "!>" (k ?) "%Hbits H".
    do 2 rewrite of_nat_to_nat_plus.
    unfold Wasm_int.N_of_uint => //=.
    iApply (points_to_wm_eq with "H") => //.
    lia.
    
  - iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (k ?) "%Hbits H".
    repeat rewrite of_nat_to_nat_plus.
    remember (serialise_i32 a) as l.
    repeat (destruct l => //).
    iApply (points_to_wm_eq with "H") => //.
    repeat rewrite cons_length.
    by lias.
    iExists _ ; by subst ; iFrame.
Qed.    
    
Lemma spec_pop f0 n v (a : i32) s E:
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝
         ∗ ⌜ f0.(f_locs) !! 0 = Some (value_of_uint v) ⌝
         ∗ ⌜ length f0.(f_locs) >= 2 ⌝
         ∗ isStack v (a :: s) n
         ∗ ↪[frame] f0 }}}
    to_e_list pop @ E
    {{{ w, ⌜ w = immV [VAL_int32 a] ⌝ ∗
                      isStack v s n ∗
                      ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝ }}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hlocv & %Hlocs & Hstack & Hf) HΦ" => /=.
  
  rewrite separate4.
  iApply wp_seq.
  instantiate (1 := λ x,  (⌜ x = immV [] ⌝ ∗ isStack v _ n ∗ ↪[frame] f0)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hstack Hf"; first by iApply (is_stack_valid with "[$Hstack $Hf]").
  
  iIntros (w) "(-> & Hstack & Hf) /=".
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ x,  (⌜ x = immV [] ⌝ ∗ isStack v _ n ∗ ↪[frame] f0)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hstack Hf"; first by iApply (is_stack_bound_valid with "[$Hstack $Hf]").
  
  iIntros (w) "(-> & Hstack & Hf) /=".
  iApply (spec_pop_op with "[$Hf $Hstack] [$]").
  auto.
Qed.


End specs.


End stack.    
      
