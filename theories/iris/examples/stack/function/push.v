From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export stack_common is_full.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.



Section stack.
  Context `{!wasmG Σ}.
  
  Section code.

(*
  push: [i32, i32] -> []
  locals declared: [i32]

  Given a stack pointer and an i32, push the i32 to the top of the stack.

  Implementation contains the is_full check which results in a trap if the stack is full. Otherwise, load the 
  stack top pointer from the stack pointer address, increment it by 4, store the given i32 to the new cell and 
  update the stack top pointer. Does not cause u32 overflow when the stack pointer is at the last page 
  of memory.
  
  Returns nothing. Can trap only if the stack pointer is invalid or the stack is full.

  Parameters/Locals:
  0 (input)     stack pointer
  1 (input)     i32 value to be pushed
  2             temporary variable storing the new address of the stack top pointer
*)
    Definition push_op :=
      is_full_op ++ 
     [
       BI_if (Tf [] []) [BI_unreachable] [];
       BI_get_local 0 ;
       BI_load T_i32 None N.zero N.zero ;
       i32const 4 ;
       BI_binop T_i32 (Binop_i BOI_add) ;
       BI_tee_local 2 ;
       BI_get_local 1 ;
       BI_store T_i32 None N.zero N.zero ;
       BI_get_local 0 ;
       BI_get_local 2 ;
       BI_store T_i32 None N.zero N.zero
      ].
        
    Definition push :=
      validate_stack 0 ++ validate_stack_bound 0 ++ push_op.

  End code.

  Section specs.

    Lemma spec_push_op f0 n v (a : i32) s E :
      ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝
          ∗ ⌜ f0.(f_locs) !! 0 = Some (value_of_int v) ⌝
          ∗ ⌜ f0.(f_locs) !! 1 = Some (VAL_int32 a) ⌝ 
          ∗ ⌜ length f0.(f_locs) >= 3 ⌝
          ∗ ⌜ (length s < two14 - 1)%Z ⌝
          ∗ isStack v s n
          ∗ ↪[frame] f0 }}}
        to_e_list push_op @ E
        {{{ w, ⌜ w = immV [] ⌝ ∗
                       isStack v (a :: s) n ∗
                       ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝ }}}. 
    Proof.
      iIntros "!>" (Φ) "(%Hinst & %Hlocv & %Hloca & %Hlocs & %Hlens & Hstack & Hf) HΦ" => /=.
      
      rewrite (separate9 (AI_basic _)).
      iApply wp_seq.
      iSplitR; last iSplitL "Hf Hstack".
      2: { iApply (spec_is_full_op with "[$Hf $Hstack] []") => //.
           iIntros (w).
           instantiate (1 := λ w, (∃ k : Z, ⌜w = immV [value_of_int k]⌝ ∗ isStack v s n ∗ ⌜(k = 1 ∧ (Z.of_nat (length s)) = (two14 - 1)%Z) ∨ k = 0 ∧ (length s < two14 - 1)%Z⌝ ∗ ↪[frame] f0)%I).
           auto.
      }
      { iIntros "H".
        by iDestruct "H" as (k) "(%Habs & ?)".
      }           

      iIntros (w) "H".
      iDestruct "H" as (k) "(-> & Hstack & %Hret & Hf)".
      destruct Hret as [Hret | Hret] => //.
      { destruct Hret as [-> Hlens'].
        rewrite Hlens' in Hlens.
        by lias.
      }

      destruct Hret as [-> _] => /=.

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
      
      instantiate (1 := λ x, (⌜ x = immV [value_of_int v] ⌝ ∗ ↪[frame] f0)%I).
      iSplitR ; first by iIntros "[%Habs _]".
      iSplitL "Hf".
      - iApply (wp_get_local with "[] [$Hf]") => //=.
      - iIntros (w) "[-> Hf]".
        simpl.
        rewrite separate2.
        iApply wp_seq.
        instantiate ( 1 := λ x, ((((⌜ x = immV [ value_of_int (v + (length s) * 4)%Z] ⌝
                                            ∗ [∗ list] i↦w ∈  s,
                                     N.of_nat n ↦[i32][ Z.to_N (v + (length s) * 4 - 4 * i)] w) ∗

                                     (∃ bs, ⌜ Z.of_nat (length bs) = (two16 - 4 - length s * 4)%Z ⌝ ∗ N.of_nat n↦[wms][Z.to_N (v + length s * 4) + 4]bs)
                                  )
                                    ∗  N.of_nat n↦[wms][(Wasm_int.N_of_uint i32m (Wasm_int.int_of_Z i32m v) + N.zero)%N]bits (value_of_int (v + length s * 4)) )
                                   ∗ ↪[frame] f0)%I).
        iSplitR ; first by iIntros "[[[[%Habs _] _] _] _]".
        iDestruct "Hstack" as "(%Hdiv & %Hvb & %Hlen & Hv & Hs & Hrest)".
        iSplitR "HΦ".
      - iApply wp_load => //.
        iSplitL "Hs Hrest".
        iFrame.
        done.
        iFrame.
        rewrite N.add_0_r.
        iSimpl.
        rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        rewrite Z.mod_small ; last by unfold ffff0000 in Hvb ; rewrite u32_modulus; lia.
        by iDestruct (i32_wms with "Hv") as "Hv" => //.

      - iIntros (w) "[[[[->  Hs] Hrest] Hp] Hf]".
        iSimpl.
        iAssert (isStack v (s) n)%I with "[Hrest Hp Hs]" as "Hstack".
        unfold isStack.
        iFrame.
        rewrite N.add_0_r.
        simpl.
        rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        rewrite Z.mod_small ; last by unfold ffff0000 in Hvb ; rewrite u32_modulus; lia.
        repeat iSplit => //=.
        by iApply i32_wms => //.
      - rewrite separate3.
        iApply (wp_seq _ _ _ (λ x, (⌜ x = immV [value_of_int (v + 4 + length s * 4)] ⌝
                                            ∗ ↪[frame] _)%I)).
        iSplitR ; first by iIntros "[%Habs _]".
        iSplitL "Hf".
        iApply (wp_binop with "Hf") => //.
        iIntros "!>".
        iPureIntro.
        unfold value_of_int => /=.
        repeat f_equal.
        unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add => /=.
        f_equal.
        rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        rewrite Z.mod_small ; first by lias.
        rewrite u32_modulus.
        unfold ffff0000 in Hvb.
        unfold two14 in Hlen.
        remember (length s) as x.
        rewrite -Heqx.
        by lias.
      - iIntros (w) "[-> Hf]".
        simpl.

        rewrite separate2.
        iApply wp_seq; iSplitR; last iSplitL "Hf".
        instantiate (1 := λ w, (⌜ w = immV [value_of_int (v + 4 + length s * 4)] ⌝ ∗ ↪[frame] _) %I).
        2: {
             iApply (wp_tee_local with "Hf").
             iIntros "!> Hf".
             rewrite separate1.
             iApply wp_val_app => //.
             iSplitR; first by iIntros "!> [%Habs _]".
             iApply (wp_set_local with "[] [$Hf]") => //=.
        }
        { by iIntros "(%Habs & _)". }
        
      - iIntros (w) "[-> Hf]".
        simpl.

        remember {| f_locs := set_nth (value_of_int (v + 4 + length s * 4))
                                (f_locs f0) 2 (value_of_int (v + 4 + length s * 4)) ;
                   f_inst := f_inst f0 |} as f1.
        rewrite - Heqf1.
        rewrite separate2.
        iApply wp_seq.
        instantiate (1 := λ x, (⌜ x = immV [value_of_int (v + 4 + length s * 4) ;
                                            VAL_int32 a] ⌝ ∗ ↪[frame] f1)%I).
        iSplitR ; first by iIntros "[%Habs _]".
        iSplitL "Hf".
      - rewrite separate1.
        iApply wp_val_app => //.
        iSplitR ; first by iIntros "!> [%Habs _]".
        subst f1 ; iApply (wp_get_local with "[] [$Hf]") => //.
        simpl.
        rewrite - fmap_insert_set_nth; last by lias.
        by rewrite list_lookup_insert_ne => //.
      - iIntros (w) "[-> Hf]".
        iSimpl.
        rewrite separate3.
        iApply wp_seq.
        instantiate
          (1 := λ x, (((⌜ x = immV [] ⌝ ∗ N.of_nat n↦[i32][ Z.to_N v] Wasm_int.Int32.repr (v+length s * 4) ∗ ([∗ list] i↦w ∈ s, N.of_nat n↦[i32][Z.to_N (v + length s * 4 - 4 * i)] w) ∗ (∃ bs, ⌜ Z.of_nat (length bs) = (two16 - 4 - length (s) * 4 - 4)%Z ⌝ ∗ N.of_nat n↦[wms][Z.to_N (v + 4 + S (length s) * 4)]bs) )
                         ∗ N.of_nat n ↦[wms][Wasm_int.N_of_uint i32m (Wasm_int.int_of_Z i32m (v + 4 + length s * 4)%Z) + N.zero]bits (VAL_int32 a)) ∗ ↪[frame] f1)%I).
        iSplitR ; first by iIntros "[[[ %Habs _ ] _] _]". 
        iDestruct "Hstack" as "(_ & _ & _ & Hp & Hs & Hrest)".
        iDestruct "Hrest" as (bs) "[%Hbs Hrest]".
        unfold two16 in Hbs.
        unfold two14 in Hlens.
        remember (length s) as x.
        rewrite - Heqx.
        do 4 (destruct bs ; first by exfalso ; clear Heqx s ; simpl in Hbs ; lia).
        rewrite separate4.
        unfold mem_block_at_pos at 1.
        rewrite big_sepL_app.
        iDestruct "Hrest" as "[Ha Hrest]".
        iSplitR "HΦ".
      - iApply wp_wand_r. iSplitL. iApply wp_store ; last first.
        iFrame.
        iSplitR "Ha".
        iNext.
        simpl.
        subst x.
        by instantiate (1 := λ x, (⌜ x = immV [] ⌝ ∗ N.of_nat n ↦[i32][ Z.to_N v] Wasm_int.Int32.repr (v + length s * 4) ∗ ([∗ list] i↦w ∈ s, N.of_nat n ↦[i32][ Z.to_N (v + length s * 4 - 4 * i)] w) ∗ ([∗ list] k↦y ∈ bs, N.of_nat n↦[wm][N.of_nat (N.to_nat (Z.to_N (v + length s * 4)+4) + S (S (S (S k))))]y))%I);
        iFrame.
        3: instantiate (1 := [b ; b0 ; b1 ; b2]) => //=. 
        3: done.
        2: subst f1 => //=.
        iApply (big_sepL_impl with "Ha").
        iIntros "!>" (k y) "% H".
        rewrite of_nat_to_nat_plus.
        simpl.
        rewrite Wasm_int.Int32.Z_mod_modulus_eq Z.mod_small.
        rewrite of_nat_to_nat_plus.
        rewrite N.add_0_r.
        replace (Z.to_N (v+x*4)+4)%N with (Z.to_N (v+4+x*4)) => //; last by lias.
        unfold ffff0000 in Hvb.
        rewrite u32_modulus.
        lia.
        
      - iIntros (w) "[[(-> & Hp & Hs & Hrest) Ha] Hf]".
        iFrame.
        iSplit ; first done.
        subst x ; iFrame.
        iExists bs.
        iSplit ; first iPureIntro.
        simpl in Hbs.
        remember (length s) as x.
        rewrite - Heqx in Hbs.
        unfold two16. lia.
        iApply (big_sepL_impl with "Hrest").
        iIntros "!>" (k x) "% H".
        do 2 rewrite of_nat_to_nat_plus.
        remember (length s) as y.
        clear Heqy s.
        replace (Z.to_N (v + y * 4) + 4 + N.of_nat (S (S (S (S k)))))%N with
          (Z.to_N (v + 4 + S y * 4) + N.of_nat k)%N => //.
        lia.
      - iIntros (w) "[[(-> & Hp & Hs & Hrest) Ha] Hf]".
        iSimpl.
        rewrite (separate1 (AI_basic _)).
        iApply wp_seq.
        instantiate (1 := λ x, ( ⌜ x = immV [value_of_int v] ⌝ ∗ ↪[frame]f1)%I).
        iSplitR ; first by iIntros "[%Habs _]".
        iSplitL "Hf".
      - iApply (wp_get_local with "[] [$Hf]") => //.
        subst f1 => //=.
        rewrite - fmap_insert_set_nth; last by lias.
        by rewrite list_lookup_insert_ne => //.
          
      - iIntros (w) "[-> Hf]".
        iSimpl.
        rewrite separate2.
        iApply wp_seq.
        instantiate (1 := λ x, ( ⌜ x = immV [value_of_int v ;
                                             value_of_int ( v + 4 + length s * 4 ) ] ⌝
                                         ∗ ↪[frame] f1)%I).
        iSplitR ; first by iIntros "[%Habs _]".
        iSplitL "Hf".
      - rewrite separate1.
        iApply wp_val_app => //.
        iSplitR ; first by iIntros "!> [%Habs _]".
        iApply (wp_get_local with "[] [$Hf]") => //.
        subst f1 => //=.
        rewrite set_nth_read => //=.
        by subst x.
          
      - iIntros (w) "[-> Hf]".
        iSimpl.
        iApply wp_wand_r.
        iSplitL "Hf Hp".
      - iApply wp_store.
        done.
        instantiate (1 := bits (value_of_int (v + length s * 4))) => //=.
        instantiate (2 := f1).
        subst f1 => //=.
        instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
        iFrame.
        iSplit => //=.
        rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        rewrite Z.mod_small ; last by unfold ffff0000 in Hvb ; rewrite u32_modulus; lia.
        iDestruct (i32_wms with "Hp") as "Hp" => //.
        rewrite N.add_0_r.
        by subst x.
      - iIntros (w) "[[-> Hp] Hf]".
        iApply "HΦ".
        iSplit => //=.
        unfold isStack.
        iSplitR "Hf".
        repeat iSplit => //=.
        iPureIntro ; rewrite - Heqx ; clear Heqx s ; unfold two14 ; lia.
        iSplitL "Hp".
        rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        rewrite Z.mod_small ; last by unfold ffff0000 in Hvb ; rewrite u32_modulus; lia.
        iApply i32_wms => //.
        rewrite N.add_0_r.
        rewrite -Heqx.
        replace (v+4+x*4)%Z with (v+S x * 4)%Z => //.
        by lias.
        
        iSplitR "Hrest".
        iSplitL "Ha".
        iApply i32_wms => //.
        rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        rewrite Z.mod_small ; last by unfold ffff0000 in Hvb ; rewrite u32_modulus; lia.
        rewrite N.add_0_r.
        rewrite - Heqx.
        replace (v + S x * 4 - 4 * 0%nat)%Z
          with (v + 4 + x * 4)%Z ; last lia.
        done.
        iApply (big_sepL_impl with "Hs").
        iIntros "!>" (k y) "%Hbits H".
        rewrite - Heqx.
        replace (v + S x * 4 - 4 * S k)%Z
          with  (v + x * 4 - 4 * k)%Z ; last lia.
        done.
        iDestruct "Hrest" as (bs0) "[%Hbs0 Hrest]".
        iExists bs0.
        iSplit => //=.
        iPureIntro.
        rewrite - Heqx.
        lia.
        rewrite - Heqx.
        replace (Z.to_N (v+4+S x*4)) with (Z.to_N (v+S x * 4) + 4)%N => //.
        by lias.
        subst x.
        iExists _ ; by subst ; iFrame.
    Qed.

    
    Lemma spec_push f0 n v (a : i32) s E :
      ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝
          ∗ ⌜ f0.(f_locs) !! 0 = Some (value_of_int v) ⌝
          ∗ ⌜ f0.(f_locs) !! 1 = Some (VAL_int32 a) ⌝ 
          ∗ ⌜ length f0.(f_locs) >= 3 ⌝
          ∗ ⌜ (length s < two14 - 1)%Z ⌝
          ∗ isStack v s n
          ∗ ↪[frame] f0 }}}
        to_e_list push @ E
        {{{ w, ⌜ w = immV [] ⌝ ∗
                       isStack v (a :: s) n ∗
                       ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝ }}}. 
    Proof.
      iIntros "!>" (Φ) "(%Hinst & %Hlocv & %Hloca & %Hlocs & %Hlens & Hstack & Hf) HΦ" => /=.
      
      rewrite separate4.
      iApply wp_seq.
      instantiate (1 := λ x,  (⌜ x = immV [] ⌝ ∗ isStack v s n ∗ ↪[frame] f0)%I).
      iSplitR; first by iIntros "(%H & _)".
      iSplitL "Hstack Hf"; first by iApply (is_stack_valid with "[$Hstack $Hf]").
      
      iIntros (w) "(-> & Hstack & Hf) /=".
      rewrite separate3.
      iApply wp_seq.
      instantiate (1 := λ x,  (⌜ x = immV [] ⌝ ∗ isStack v s n ∗ ↪[frame] f0)%I).
      iSplitR; first by iIntros "(%H & _)".
      iSplitL "Hstack Hf"; first by iApply (is_stack_bound_valid with "[$Hstack $Hf]").
      
      iIntros (w) "(-> & Hstack & Hf) /=".
      iApply (spec_push_op with "[$Hf $Hstack] [$]").
      auto.
    Qed.
      
  End specs.


End stack.    

