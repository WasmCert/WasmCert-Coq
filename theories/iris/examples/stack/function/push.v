From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export stack_common is_full iris_fundamental proofmode.

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

    Lemma push_not_full v (s: list i32) f E:
      (two16 | v)%Z ->  
      (length s < two14 - 1)%Z ->
      ↪[frame] f ⊢
        WP [AI_basic (BI_const (value_of_int (v + 4 + length s * 4))); AI_basic (i32const 65536);
            AI_basic (BI_binop T_i32 (Binop_i (BOI_rem SX_U))); AI_basic (BI_if (Tf [] []) [] [BI_unreachable])] @ E
        {{ w, ⌜ w = immV [] ⌝ ∗ ↪[frame] f }}.
    Proof.
      move => Hdiv Hsize.
      iIntros "Hf".
      rewrite separate3.
      iApply wp_seq.
      instantiate (1 := λ w, (⌜ w = immV [ _ ]⌝ ∗ ↪[frame] f)%I).
      iSplitR; first by iIntros "(%H & _)".
      iSplitL "Hf"; first by iApply (wp_binop with "Hf") => //.
      iIntros (w) "(-> & Hf)".
      iApply (wp_if_true with "Hf").
      {
        unfold Wasm_int.Int32.modu.
        simpl.
        move => Hcontra.
        apply Znumtheory.Zdivide_mod in Hdiv.
        assert ((4 + length s * 4 < 65536)%Z) as Hsub.
        { unfold two14 in Hsize. by lias. }
        assert ((4 <= 4 + length s * 4)%Z) as Hslb.
        { by lias. }
        unfold Wasm_int.Int32.zero in Hcontra.
        apply Wasm_int.Int32.repr_inv in Hcontra => //=.
        { 
          rewrite Wasm_int.Int32.Z_mod_modulus_eq in Hcontra.
          unfold Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize in Hcontra.
          rewrite <- Znumtheory.Zmod_div_mod in Hcontra => //; last by apply Znumtheory.Zmod_divide => //.
          unfold two16 in Hdiv.
          rewrite - Z.add_assoc in Hcontra.
          rewrite Zplus_mod Hdiv Z.add_0_l in Hcontra.
          rewrite Z.mod_mod in Hcontra => //.
          rewrite Z.mod_small in Hcontra; first by lias.
          split; by lias.
        }
        rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        unfold Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
        rewrite <- Znumtheory.Zmod_div_mod => //; last by apply Znumtheory.Zmod_divide => //.
        rewrite - Z.add_assoc.
        rewrite Zplus_mod Hdiv Z.add_0_l.
        rewrite Z.mod_mod => //.
        remember (4 + length s * 4)%Z as x.
        rewrite - Heqx.
        split.
        { 
          assert ((0 <= x `mod` 65536)%Z); first by apply Z_mod_pos.
          by lias.
        }
        assert ((x `mod` 65536 < 65536)%Z); first by apply Z_mod_lt.
        replace (two_power_nat 32) with (4294967296)%Z => //.
        by lias.
      }
      iIntros "!> Hf".
      replace ([AI_basic (BI_block (Tf [] []) [])]) with ([] ++ [AI_basic (BI_block (Tf [] []) [])]) => //.
      iApply (wp_block with "Hf") => //.
      iIntros "!> Hf".
      by iApply (wp_label_value with "Hf").
    Qed.

    Lemma push_full v (s: list i32) f E:
      (0 ≤ v ≤ ffff0000)%Z ->
      (two16 | v)%Z ->  
      (Z.of_nat (length s) = two14 - 1)%Z ->
      ↪[frame] f ⊢
        WP [AI_basic (BI_const (value_of_int (v + 4 + length s * 4))); AI_basic (i32const 65536);
            AI_basic (BI_binop T_i32 (Binop_i (BOI_rem SX_U))); AI_basic (BI_if (Tf [] []) [] [BI_unreachable])] @ E
        {{ w, ⌜ w = trapV ⌝ ∗ ↪[frame] f }}.
    Proof.
      move => Hoverflow Hdiv Hsize.
      iIntros "Hf".
      rewrite separate3.
      iApply wp_seq.
      instantiate (1 := λ w, (⌜ w = immV [ _ ]⌝ ∗ ↪[frame] f)%I).
      iSplitR; first by iIntros "(%H & _)".
      iSplitL "Hf"; first by iApply (wp_binop with "Hf") => //.
      iIntros (w) "(-> & Hf)".
      iApply (wp_if_false with "Hf").
      { unfold Wasm_int.Int32.modu. simpl.
        rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        fold two16.
        rewrite Hsize.
        rewrite - Z.add_assoc.
        assert (4 + (two14 - 1) * 4 = two16)%Z as ->;[lias|].
        rewrite - Znumtheory.Zmod_div_mod;try lias.
        f_equal. apply Znumtheory.Zdivide_mod.
        apply Z.divide_add_r;auto. apply Z.divide_refl.
        apply two16_div_i32.
      }
      iIntros "!> Hf".
      take_drop_app_rewrite 0.
      iApply (wp_block with "Hf") => //.
      iIntros "!> Hf /=".
      build_ctx [AI_basic BI_unreachable].
      iApply wp_label_bind.
      iApply (wp_wand _ _ _ (λ v, ⌜v = trapV⌝ ∗ _)%I with "[Hf]").
      iApply (wp_unreachable with "[$]");auto.
      iIntros (w) "[-> Hf]".
      deconstruct_ctx.
      iApply (wp_label_trap with "Hf");auto.
    Qed.    
    
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
      
      iDestruct (stack_pure with "Hstack") as "(%Hdiv & %Hvb & _ & Hstack)".
      
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
        instantiate ( 1 := λ x, ((⌜ x = immV [ value_of_int (v + (length s) * 4)%Z] ⌝ ∗ isStack v s n ∗ ↪[frame] f0)%I)).
        iSplitR ; first by iIntros "(%Habs & _)".
        iSplitR "HΦ".
        { by iApply (stack_load_0 with "[] [$] [$]") => //. }

      - iIntros (w) "(-> & Hstack & Hf)" => /=.
        rewrite separate3.
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
        unfold two14 in Hlens.
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


  Section valid.
    Context `{!logrel_na_invs Σ}.
    Set Bullet Behavior "Strict Subproofs".

    Lemma valid_new_stack m t funcs :
    let i0 := {| inst_types := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
                     inst_funcs := funcs;
                     inst_tab := [t];
                     inst_memory := [m];
                     inst_globs := []
              |} in
    na_inv logrel_nais stkN (stackModuleInv (λ (a : Z) (b : seq.seq i32), isStack a b m) (λ n : nat, N.of_nat m↦[wmlength]N.of_nat n)) -∗
    interp_closure_native i0 [T_i32;T_i32] [] [T_i32] (to_e_list push) [].
  Proof.
    iIntros "#Hstk".
    iIntros (vcs f) "#Hv Hown Hf".
    iIntros (LI HLI%lfilled_Ind_Equivalent);inversion HLI;inversion H8;subst;simpl.
    iApply (wp_frame_bind with "[$]");auto.
    iIntros "Hf".
    match goal with | |- context [ [AI_label _ _ ?l] ] => set (e:=l) end.
    build_ctx e.
    iApply wp_label_bind.
    subst e.
    iDestruct "Hv" as "[%Hcontr|Hws]";[done|iDestruct "Hws" as (ws) "[%Heq Hws]"].
    iDestruct (big_sepL2_length with "Hws") as %Hlen. inversion Heq;subst.
    destruct ws as [|w0 ws];[done|destruct ws as [|w1 ws];[done|destruct ws as [|w2 ws];[|done]]].
    iSimpl in "Hws".
    iDestruct "Hws" as "[Hw0 [Hw1 _]]".
    iDestruct "Hw0" as (z0) "->".
    iDestruct "Hw1" as (z1) "->".
    pose proof (value_of_int_repr z0) as [v ->]. iSimpl in "Hf".
    take_drop_app_rewrite (length (validate_stack 1)).

    match goal with | |- context [ (WP ?e @ _; _ {{ _ }} )%I ] => set (e0:=e) end.
    match goal with | |- context [ (↪[frame] ?f0)%I ] => set (f':=f0) end.
    build_ctx e0. subst e0.
    iApply wp_seq_can_trap_ctx.
    instantiate (1:=(λ f0, ⌜f0 = f'⌝ ∗ na_own logrel_nais ⊤)%I).
    iFrame "Hf".
    iSplitR;[|iSplitR;[|iSplitL]];cycle 1.
    - iIntros (f0) "(Hf & -> & Hown)".
      deconstruct_ctx.
      iApply (wp_wand _ _ _ (λ v, ⌜v = trapV⌝ ∗ _)%I with "[Hf]").
      iApply (wp_label_trap with "Hf");auto.
      iIntros (v0) "[-> Hf]". iExists _. iFrame.
      iIntros "Hf".
      iApply (wp_frame_trap with "Hf").
      iNext. iLeft. iLeft. auto.
    - iIntros "Hf". iFrame.
      iApply (wp_wand with "[Hf]").
      iApply check_stack_valid;iFrame;subst;eauto.
      iIntros (v0) "[$ HH]". eauto.
    - subst f'. iIntros (w f0) "([-> %Hdiv] & Hf & -> & Hown) /=".
      deconstruct_ctx.
      take_drop_app_rewrite (length (validate_stack_bound 0)).
      
      
      
      (* bind_seq_base_imm [AI_basic (BI_get_local 1)] with "[Hf]". *)
      (* iApply (wp_get_local with "[] Hf");eauto. *)
      (* iIntros (v0) "[-> Hf] /=". *)
      iApply fupd_wp.
      iMod (na_inv_acc with "Hstk Hown") as "(>Hstkres & Hown & Hcls)";[solve_ndisj..|].
      iDestruct "Hstkres" as (l Hmul) "[Hlen Hstkres]".
      iDestruct "Hstkres" as (l' Hmultiple) "Hl'".
      assert (0 <= v < l)%Z as Hbounds. admit.
      assert (page_size | Z.to_N v)%N as Hdiv';[destruct Hdiv;exists (Z.to_N x)|].
      { rewrite H Z2N.inj_mul. replace page_size with 65536%N =>//. all: lia. }
      eapply multiples_upto_in in Hmultiple as Hin;[..|apply Hdiv'];[|lia].
      apply elem_of_list_lookup_1 in Hin as [i Hi].
      iDestruct (big_sepL_lookup_acc with "Hl'") as "[Hv Hl']";[eauto|].
      iDestruct "Hv" as (stk) "Hstack".
      rewrite Z2N.id;[|lia].
      iModIntro.
      
      iApply (spec_op_push with "[$Hf $Hstack]").
      simpl. repeat iSplit;eauto. iPureIntro;lia.
      admit.
      
      iDestruct (big_sepL_)
      
      build_ctx [AI_basic (BI_get_local 1)].
      
      iApply (wp_wand _ _ _)
      iApply (wp_get_local).
      

    
    iApply (wp_wand with "[Hf Hown]").
    { iApply (wp_seq_can_trap_same_empty_ctx with "[$Hf Hown]").
      iSplitR;[|iSplitR;[|iSplitR;[iIntros "Hf";iApply check_stack_valid;eauto|]]].
      - by iIntros "[% _]".
      - instantiate (1:=(λ w1, ((⌜w1 = trapV⌝ ∨ (∃ ws : seq.seq (leibnizO value), ⌜w1 = immV ws⌝
          ∗ ([∗ list] w2;τ ∈ ws;[], interp_value τ w2))) ∨ interp_call_host_cls [] [] w1) ∗ _)%I). iSimpl. iLeft;auto.
      - iIntros (w) "([-> %Hdiv] & Hf) /=".
        
      
    }
    
    iApply fupd_wp.
    iMod (na_inv_acc with "Hstk Hown") as "(>Hstkres & Hown & Hcls)";[solve_ndisj..|].
    iDestruct "Hstkres" as (len) "[% [Hlen Hstkres]]".
    

    
  End valid.

End stack.    

