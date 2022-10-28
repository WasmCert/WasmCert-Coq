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
  map: [i32, i32] -> []
  locals declared: [i32, i32]

  Given a stack pointer and a function reference from table 0, apply the function to all elements of the stack and
  storing the results in the original stack.

  Implementation is done via looping through the stack, loading each element and call_indirect the function, then
  store the element back to the original address. The loop variable represents the top address that *has* been 
  dealt with, to avoid u32 overflow. The loop upper bound is then simply the stack top pointer, retrieved from the value
  stored in the stack pointer address.

  The spec of the map function allows description of a relationship between the old and the new stack via an arbitrary
  assertion, which is given by the spec of the input function reference.
  
  Returns nothing. Can trap if the stack validation traps, or any of the function application traps.

  Parameters/Locals:
  0 (input)     stack pointer
  1 (input)     function reference from table 0, which must be of type [i32] -> [i32]
  2             temporary variable storing the loop variable
  3             temporary variable storing the loop upper bound
*)
  
Definition map_initialise :=
  [
    BI_get_local 0 ;
    BI_load T_i32 None N.zero N.zero ;
    BI_set_local 3 ;
  
    BI_get_local 0 ;
    BI_set_local 2
  ].

Definition map_loop_body :=
  [
    (* Check if the loop is done *)
    BI_get_local 2 ;
    BI_get_local 3 ;
    BI_relop T_i32 (Relop_i ROI_eq) ;
    BI_br_if 1 ;

    (* Update the loop variable and add a copy to the stack (for storing later) *)
    BI_get_local 2 ;
    i32const 4 ;
    BI_binop T_i32 (Binop_i BOI_add) ;
    BI_tee_local 2 ;

    (* Load the stack element, apply the function and store the result back to the stack *)
    BI_get_local 2 ;
    BI_load T_i32 None N.zero N.zero ;
    BI_get_local 1 ;
    BI_call_indirect 1 ;
    BI_store T_i32 None N.zero N.zero ;

    (* Keep the loop alive *)
    BI_br 0
  ].

Definition map_op :=
  map_initialise ++
  [
    BI_block (Tf [] [])
             [BI_loop (Tf [] []) map_loop_body]
  ].

Definition stack_map :=
  validate_stack 0 ++ validate_stack_bound 0 ++ map_op.

End code.

Lemma stack_pure v s n:
  isStack v s n -∗
  ⌜(two16 | v)%Z⌝ ∗ ⌜(0 <= v <= ffff0000)%Z⌝ ∗ ⌜(length s < two14)%Z⌝ ∗ isStack v s n.
Proof.
  iIntros "Hs".
  repeat iSplit => //; by iDestruct "Hs" as "(% & (% & %) & % & ?)".
Qed.


Lemma stack_load_0 v s n f E:
  ⌜ f.(f_inst).(inst_memory) !! 0 = Some n ⌝ -∗
  isStack v s n -∗
  ↪[frame] f -∗
  WP [AI_basic (BI_const (value_of_int v)); AI_basic (BI_load T_i32 None N.zero N.zero)] @ E
  {{ w, ⌜ w = immV [value_of_int (v + length s * 4)] ⌝ ∗ isStack v s n ∗ ↪[frame] f }}.
Proof.
  iIntros "%Hinstmem Hs Hf" => /=.
  
  iDestruct (stack_pure with "Hs") as "(%Hdiv & %Hvb & %Hlens & Hs)".
  
  iApply (wp_wand with "[Hs Hf]").
  iApply wp_load => //; last first.
  { unfold isStack.
    iDestruct "Hs" as "(% & % & % & Hn & Hrest)".
    iDestruct (i32_wms with "Hn") as "Hn".
    rewrite N.add_0_r.
    simpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small; last by unfold ffff0000 in Hvb; rewrite u32_modulus; lia.
    unfold bits.
    instantiate (1 := VAL_int32 _) => /=.
    iFrame.
    iNext.
    instantiate (1 := λ w, (⌜ w = immV _ ⌝ ∗ _)%I) => /=.
    iSplit => //.
    by iApply "Hrest".
  }
  { done. }
  { iIntros (w) "(((-> & Hrest) & Hn) & Hf)".
    iSplit => //.
    iFrame.
    repeat iSplit => //=.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small; last by unfold ffff0000 in Hvb; rewrite u32_modulus; lia.
    rewrite N.add_0_r.
    by iApply i32_wms.
  }
Qed.

Lemma stack_load_j v s n f E j sv:
  ⌜ f.(f_inst).(inst_memory) !! 0 = Some n ⌝ -∗
  ⌜ s !! (Z.to_nat j) = Some sv ⌝ -∗
  ⌜ (0 <= j < length s)%Z ⌝ -∗
  isStack v s n -∗
  ↪[frame] f -∗
  WP [AI_basic (BI_const (value_of_int (v + length s * 4 - 4 * j))); AI_basic (BI_load T_i32 None N.zero N.zero)] @ E
  {{ w, ⌜ w = immV [VAL_int32 sv] ⌝ ∗ isStack v s n ∗ ↪[frame] f }}.
Proof.
  iIntros "%Hinstmem %Hsv %Hjbound Hs Hf" => /=.

  iDestruct (stack_pure with "Hs") as "(%Hdiv & %Hvb & %Hlens & Hs)".
  
  assert (0 <= j < 16383)%Z as Hjb; first by unfold two14 in Hlens; lia.
  
  iApply (wp_wand with "[Hs Hf]").
  iApply wp_load => //; last first.
  { unfold isStack.
    iDestruct "Hs" as "(_ & _ & _ & Hn & Hcontent & Hrest)".
    iDestruct (big_sepL_lookup_acc with "Hcontent") as "(Hj & Hcrest)" => //=.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small; last first.
    { unfold ffff0000 in Hvb; unfold two14 in Hlens; rewrite u32_modulus.
      remember (length s) as x.
      rewrite - Heqx.
      lia.
    }
    rewrite N.add_0_r.
    iDestruct (i32_wms with "Hj") as "Hj".
    unfold bits.
    instantiate (1 := VAL_int32 sv) => /=.
    iSplitR "Hf Hj"; last first.
    iFrame "Hf".
    replace (4*Z.to_nat j)%Z with (4*j)%Z => //.
    lia.
    instantiate (1 := λ w, (⌜ w = immV [VAL_int32 sv] ⌝ ∗ _)%I).
    iIntros "!>" => /=.
    iSplit => //.
    iCombine "Hn Hrest Hcrest" as "H".
    by iApply "H".
  }
  { done. }

  iIntros (w) "(((-> & Hn & Hrest & Hcrest) & Hj) & Hf)".
  iSplit => //.
  iFrame.
  repeat iSplit => //=.
  iApply "Hcrest".
  iDestruct (i32_wms with "Hj") as "Hj".
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small; last first.
  { unfold ffff0000 in Hvb; unfold two14 in Hlens; rewrite u32_modulus.
    remember (length s) as x.
    rewrite - Heqx.
    lia.
  }
  rewrite N.add_0_r.
  replace (4*Z.to_nat j)%Z with (4*j)%Z => //.
  lia.  
Qed.

Lemma stack_store_j v (s: list i32) n f E j sv (v0: i32):
  ⌜ f.(f_inst).(inst_memory) !! 0 = Some n ⌝ -∗
  ⌜ s !! (Z.to_nat j) = Some sv ⌝ -∗
  ⌜ (0 <= j < length s)%Z ⌝ -∗
  isStack v s n -∗
  ↪[frame] f -∗
  WP [AI_basic (BI_const (value_of_int (v + length s * 4 - 4 * j))); AI_basic (BI_const (VAL_int32 v0)); AI_basic (BI_store T_i32 None N.zero N.zero)] @ E
  {{ w, ⌜ w = immV [] ⌝ ∗ isStack v (<[ Z.to_nat j := v0 ]> s) n ∗ ↪[frame] f }}.
Proof.
  iIntros "%Hinstmem %Hsv %Hjbound Hs Hf" => /=.

  iDestruct (stack_pure with "Hs") as "(%Hdiv & %Hvb & %Hlens & Hs)".
  
  assert (0 <= j < 16383)%Z as Hjb; first by unfold two14 in Hlens; lia.
  
  iApply (wp_wand with "[Hs Hf]").
  iApply wp_store => //; last first.
  { unfold isStack.
    iDestruct "Hs" as "(_ & _ & _ & Hn & Hcontent & Hrest)".
    iDestruct (big_sepL_insert_acc with "Hcontent") as "(Hj & Hcrest)" => //=.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small; last first.
    { unfold ffff0000 in Hvb; unfold two14 in Hlens; rewrite u32_modulus.
      remember (length s) as x.
      rewrite - Heqx.
      lia.
    }
    rewrite N.add_0_r.
    iDestruct (i32_wms with "Hj") as "Hj".
    iSplitR "Hf Hj"; last first.
    iFrame "Hf".
    replace (4*Z.to_nat j)%Z with (4*j)%Z => //.
    lia.
    instantiate (1 := λ w, (⌜ w = immV [] ⌝ ∗ _)%I).
    iIntros "!>" => /=.
    iSplit => //.
    iCombine "Hn Hrest Hcrest" as "H".
    by iApply "H".
  }
  { done. }

  iIntros (w) "(((-> & Hn & Hrest & Hcrest) & Hj) & Hf)".
  iSplit => //.
  iFrame "Hf".
  repeat iSplit => //=.
  { by rewrite insert_length. }
  repeat rewrite insert_length.
  iFrame.
  iApply "Hcrest".
  iDestruct (i32_wms with "Hj") as "Hj".
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small; last first.
  { unfold ffff0000 in Hvb; unfold two14 in Hlens; rewrite u32_modulus.
    remember (length s) as x.
    rewrite - Heqx.
    lia.
  }
  rewrite N.add_0_r.
  replace (4*Z.to_nat j)%Z with (4*j)%Z => //.
  lia.  
Qed.



Section specs.

Lemma spec_map_initialise (f: frame) s v n E:
  ⊢ {{{ ⌜ f.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ f.(f_locs) !! 0 = Some (value_of_int v) ⌝ ∗
        ⌜ length f.(f_locs) >= 4 ⌝ ∗
        isStack v s n ∗
        ↪[frame] f }}}
    to_e_list map_initialise @ E
    {{{ w, ⌜ w = immV [] ⌝ ∗
           isStack v s n ∗
           ↪[frame] {|
             f_locs := <[ 2 := value_of_int v ]>
                       (<[ 3 := value_of_int (v + length s * 4) ]> f.(f_locs));
             f_inst := f_inst f
           |}
    }}}.
Proof.
  iIntros "!>" (Φ) "(%Hinstmem & %Hlocs0 & %Hlocs & Hs & Hf) HΦ" => /=.

  iDestruct (stack_pure with "Hs") as "(%Hdiv & %Hvb & %Hlens & Hs)".
  
  rewrite separate1.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply wp_get_local => //.
       by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
  }
  { by iIntros "(%Habs & _)". }
  
  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜w = immV [_]⌝ ∗ isStack v s n ∗ ↪[frame] f)%I).
  iSplitR; last iSplitL "Hs Hf".
  2: { by iApply (stack_load_0 with "[] [$Hs] [$Hf]") => //. }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hs & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply wp_set_local => //.
       by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate1.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply wp_get_local; last by iApply "Hf".
       { simpl.
         rewrite - fmap_insert_set_nth; last lia.
         by rewrite list_lookup_insert_ne => //.
       }
       by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  iApply (wp_wand with "[Hf]").
  { iApply wp_set_local; last by iApply "Hf".
    { simpl.
      rewrite - fmap_insert_set_nth; last lia.
      rewrite insert_length.
      lia.
    }
    by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
  }

  iIntros (w) "(-> & f)" => /=.
  iApply "HΦ".
  iFrame.
  iSplit => //.
  
  erewrite fmap_insert_set_nth => /=; last by rewrite insert_length; lia.
  erewrite fmap_insert_set_nth => /=; last lia.
  done.
Qed.

Lemma spec_map_loop_body_terminate f s v n E j k:
  ⊢ {{{ ⌜ f.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ f.(f_locs) !! 0 = Some (value_of_int v) ⌝ ∗
        ⌜ f.(f_locs) !! 2 = Some (value_of_int j) ⌝ ∗
        ⌜ f.(f_locs) !! 3 = Some (value_of_int k) ⌝ ∗
        ⌜ j = k ⌝ ∗
        ⌜ length f.(f_locs) >= 4 ⌝ ∗
        isStack v s n ∗
        ↪[frame] f }}}
    to_e_list map_loop_body @ E
    {{{ w, ⌜ exists es, w = brV (VH_base 1 [] es) ⌝ ∗
           isStack v s n ∗ ↪[frame] f
    }}}.
Proof.
  iIntros "!>" (Φ) "(%Hinstmem & %Hlocs0 & %Hlocs2 & %Hlocs3 & <- & %Hlocs & Hs & Hf) HΦ" => /=.

  iDestruct (stack_pure with "Hs") as "(%Hdiv & %Hvb & %Hlens & Hs)".

  rewrite separate1.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply wp_get_local => //.
       by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜ w = immV [value_of_int j; value_of_int j] ⌝ ∗ ↪[frame] f)%I).
  iSplitR; last iSplitL "Hf".
  { by iIntros "(%Habs & _)". }
  { rewrite separate1.
    iApply wp_val_app => //.
    iSplit; first by iIntros "!> (%Habs & _)".
    by iApply wp_get_local => //.
  }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate3.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply (wp_relop with "Hf") => //=.
       rewrite Wasm_int.Int32.eq_true => /=.
       by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply (wp_br_if_true with "Hf") => //=.
       iIntros "!> Hf".
       instantiate (1 := λ w, (⌜ w = brV (VH_base 1 [] []) ⌝ ∗ ↪[frame] f)%I).
       iApply wp_value; last by iFrame.
       done.
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  iApply (wp_wand with "[Hf]").
  { iApply wp_value; last iFrame.
    { instantiate (1 := brV (VH_base 1 [] _)).
      rewrite separate1.
      unfold IntoVal.
      simpl.
      done.
    }
    { by instantiate (1 := λ w, (⌜ w = brV _ ⌝ ∗ ↪[frame] f)%I); iFrame. }
  }
  
  iIntros (w) "(-> & Hf)" => /=.
  iApply "HΦ".
  iFrame.
  iPureIntro; by eexists.
Qed.

Lemma spec_map_loop_body_continue f (s: list i32) v n E j fn (sv: i32) j0 a cl
      (Φ : i32 -> iPropI Σ) (Ψ: i32 -> i32 -> iPropI Σ):
  ⊢ {{{ ⌜ f.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ f.(f_locs) !! 0 = Some (value_of_int v) ⌝ ∗
        ⌜ f.(f_locs) !! 1 = Some (VAL_int32 fn) ⌝  ∗
        ⌜ f.(f_locs) !! 2 = Some (value_of_int (v + (length s) * 4 - 4 * j - 4)) ⌝ ∗
        ⌜ f.(f_locs) !! 3 = Some (value_of_int (v + (length s) * 4)) ⌝ ∗
        ⌜ length f.(f_locs) >= 4 ⌝ ∗
        ⌜ (0 <= j < length s)%Z ⌝ ∗
        ⌜ s !! (Z.to_nat j) = Some sv ⌝ ∗
        isStack v s n ∗
        Φ sv ∗
            ⌜ f.(f_inst).(inst_types) !! 1 = Some (Tf [T_i32] [T_i32]) ⌝ ∗

            ⌜ f.(f_inst).(inst_tab) !! 0 = Some j0 ⌝ ∗
            (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m fn) ] (Some a) ∗
            (N.of_nat a) ↦[wf] cl ∗
            ⌜ cl_type cl = Tf [T_i32] [T_i32] ⌝ ∗ 
            (∀ (u : i32) (fc : frame),
                {{{ Φ u ∗
                      ⌜ f_inst f = f_inst fc ⌝ ∗
                       ↪[frame] fc ∗
                       (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m fn) ] (Some a) ∗
                       (N.of_nat a) ↦[wf] cl
                  }}}
                  [ AI_basic (BI_const (VAL_int32 u)) ;
                    AI_invoke a ] @ E
                  {{{ w, (∃ v, ⌜ w = immV [VAL_int32 v] ⌝ ∗ Ψ u v)
                           ∗ ↪[frame] fc
                           ∗ (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m fn) ] (Some a) 
                           ∗ (N.of_nat a) ↦[wf] cl }}}) ∗   
        ↪[frame] f }}}
    to_e_list map_loop_body @ E
    {{{ w, ⌜ w = brV (VH_base 0 [] []) ⌝ ∗
           (∃ (sv': i32), isStack v (<[Z.to_nat j := sv']> s) n ∗ Ψ sv sv') ∗
            (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m fn) ] (Some a) ∗
            (N.of_nat a) ↦[wf] cl ∗
            ↪[frame]
            {| f_locs := <[ 2 := value_of_int (v + (length s) * 4 - 4 * j) ]> f.(f_locs);
               f_inst := f.(f_inst)
            |}
    }}}.
Proof.
  iIntros "!>" (Ξ) "(%Hinstmem & %Hlocs0 & %Hlocs1 & %Hlocs2 & %Hlocs3 & %Hlocs & %Hjbound & %Hslookup & Hs & HΦ & %Htypes & %Htab & Htab & Hcl & %Hclt & #Hspec & Hf) HΞ" => /=.

  iDestruct (stack_pure with "Hs") as "(%Hdiv & %Hvb & %Hlens & Hs)".

  assert (0 <= j < 16383)%Z as Hjb.
  { unfold two14 in Hlens. by lias. }
  
  rewrite (separate1 (AI_basic _)).
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply wp_get_local => //.
       by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜ w = immV [value_of_int (v + length s * 4 - 4 * j - 4); value_of_int (v + length s * 4)] ⌝ ∗ ↪[frame] f)%I).
  iSplitR; last iSplitL "Hf".
  { by iIntros "(%Habs & _)". }
  { rewrite (separate1 (AI_basic _)).
    iApply wp_val_app => //.
    iSplit; first by iIntros "!> (%Habs & _)".
    by iApply wp_get_local => //.
  }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate3.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply (wp_relop with "Hf") => //=.
       rewrite Wasm_int.Int32.eq_false => /=; first by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
       remember (length s) as x.
       rewrite - Heqx.
       move => Hcontra.
       apply Wasm_int.Int32.repr_inv in Hcontra.
       { by lias. }
       { rewrite u32_modulus; unfold ffff0000 in Hvb; unfold two14 in Hlens; by lias. }
       { rewrite u32_modulus; unfold ffff0000 in Hvb; unfold two14 in Hlens; by lias. }
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply (wp_br_if_false with "Hf") => //=.
       by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite (separate1 (AI_basic _)).
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply wp_get_local => //.
       by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
  }
  { by iIntros "(%Habs & _)". }
  
  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate3.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply (wp_binop with "Hf") => //=.
       instantiate (1 := λ w, ⌜ w = immV [value_of_int (v + length s * 4 - 4 * j)]⌝%I) => /=.
       iIntros "!>".
       iPureIntro.
       unfold value_of_int.
       repeat f_equal.
       unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add => /=.
       f_equal.
       rewrite Wasm_int.Int32.Z_mod_modulus_eq.
       rewrite Z.mod_small; last first.
       { remember (length s) as x; rewrite - Heqx.
         unfold ffff0000 in Hvb; rewrite u32_modulus; unfold two14 in Hlens.
         lia.
       }
       lia.
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜ w = immV [value_of_int (v+length s * 4 - 4 * j)] ⌝ ∗ ↪[frame] _)%I).
  iSplitR; last iSplitL "Hf".
  2: { iApply (wp_tee_local with "Hf").
       iIntros "!> Hf".
       rewrite (separate1 (AI_basic _)).
       iApply wp_val_app => //.
       iSplit; first by iIntros "!> (%Habs & _)" => /=.
       iApply (wp_set_local with "[] [$Hf]"); first lia.
       done.
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜ w = immV [value_of_int (v+length s * 4 - 4 * j); value_of_int (v+length s * 4 - 4 * j)] ⌝ ∗ ↪[frame] _)%I).
  iSplitR; last iSplitL "Hf".
  2: { rewrite (separate1 (AI_basic _)).
       iApply wp_val_app => //.
       iSplit; first by iIntros "!> (%Habs & _)" => /=.
       iApply (wp_get_local with "[] [$Hf]").
       { rewrite - fmap_insert_set_nth => /=; last lia.
         by rewrite list_lookup_insert; last lia.
       }
       done.
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜ w = immV [value_of_int (v+length s * 4 - 4 * j); VAL_int32 sv] ⌝ ∗ isStack v s n ∗ ↪[frame] _)%I).
  iSplitR; last iSplitL "Hf Hs".
  2: { rewrite (separate1 (AI_basic _)).
       iApply wp_val_app => //.
       iSplit; first by iIntros "!> (%Habs & _)" => /=.
       iApply (wp_wand with "[Hf Hs]").
       { by iApply (stack_load_j with "[] [] [] [$Hs] [$Hf]") => //. }
       iIntros (w) "(-> & Hs & Hf)" => /=.
       iSplit => //.
       by iFrame.
  }
  { by iIntros "(%Habs & _)". }
  
  iIntros (w) "(-> & Hs & Hf)" => /=.
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜ w = immV [value_of_int (v+length s * 4 - 4 * j); VAL_int32 sv; VAL_int32 fn] ⌝ ∗ ↪[frame] _)%I).
  iSplitR; last iSplitL "Hf".
  2: { rewrite (separate2 (AI_basic _)).
       iApply wp_val_app => //.
       iSplit; first by iIntros "!> (%Habs & _)" => /=.
       iApply (wp_get_local with "[] [$Hf]").
       { rewrite - fmap_insert_set_nth => /=; last lia.
         by rewrite list_lookup_insert_ne; last lia.
       }
       done.
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate4.
  iApply wp_seq.
  instantiate (1 := λ w, (∃ v0, ⌜ w = immV [value_of_int (v+length s * 4 - 4 * j); VAL_int32 v0] ⌝ ∗ Ψ sv v0 ∗ _)%I).
  iSplitR; last iSplitL "Hf HΦ Htab Hcl".
  2: { rewrite (separate1 (AI_basic _)).
       iApply wp_val_app => //.
       iSplit; first by iIntros "!> H" => /=; iDestruct "H" as (v0) "(%Habs & _)".
       iApply (wp_call_indirect_success_ctx with "[$Htab] [$Hcl] [$Hf] [HΦ]") => /=.
       { by rewrite Hclt. }
       { done. }
       2: { iPureIntro.
            instantiate (1 := (LH_base [AI_basic (BI_const (VAL_int32 sv))] [])).
            instantiate (1 := 0).
            unfold lfilled, lfill.
            simpl.
            by apply/eqP.
       }
       { iIntros "!> (Htab & Hcl & Hf)".
         iApply wp_base_pull.
         iApply wp_wasm_empty_ctx.
         iApply ("Hspec" with "[$HΦ $Htab $Hcl $Hf]"); first done.
         iIntros (w) "(Hret & Hf & Htab & Hcl)".
         iDestruct "Hret" as (v0) "(-> & HΨ)".
         iExists v0.
         iSplit => //.
         iFrame "HΨ".
         iCombine "Hf Htab Hcl" as "H".
         by iApply "H".
       }
  }
  { by iIntros "H"; iDestruct "H" as (v0) "(%Habs & _)". }

  iIntros (w) "H".
  iDestruct "H" as (v0) "(-> & HΨ & Hf & Htab & Hcl)" => /=.
  rewrite separate3.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf Hs".
  2: { by iApply (stack_store_j with "[] [] [] [$Hs] [$Hf]") => //. }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hs & Hf)" => /=.
  iApply (wp_wand with "[Hf]").
  { iApply wp_value; last iFrame.
    { by instantiate (1 := brV (VH_base 0 [] [])). }
    { by instantiate (1 := λ w, (⌜ w = brV _ ⌝ ∗ ↪[frame] _)%I); iFrame. }
  }
  
  iIntros (w) "(-> & Hf)" => /=.
  iApply "HΞ".
  iSplit => //.
  iSplitL "HΨ Hs"; first by iExists v0; iFrame.
  iFrame.
  by rewrite - fmap_insert_set_nth; last lia.
Qed.

Lemma spec_map_loop_j f (s: list i32) v n E j fn j0 a cl
      (Φ : i32 -> iPropI Σ) (Ψ: i32 -> i32 -> iPropI Σ) (s': list i32):
  ⊢ ( ⌜ f.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ f.(f_locs) !! 0 = Some (value_of_int v) ⌝ ∗
        ⌜ f.(f_locs) !! 1 = Some (VAL_int32 fn) ⌝  ∗
        ⌜ f.(f_locs) !! 2 = Some (value_of_int (v + (length s) * 4 - 4 * j)) ⌝ ∗
        ⌜ f.(f_locs) !! 3 = Some (value_of_int (v + (length s) * 4)) ⌝ ∗
        ⌜ length f.(f_locs) >= 4 ⌝ ∗
        ⌜ (0 <= j <= length s)%Z ⌝ ∗
        ⌜ (j + length s' = length s)%Z ⌝ ∗
        isStack v (take (Z.to_nat j) s ++ s') n ∗
        stackAll (take (Z.to_nat j) s) Φ ∗
        stackAll2 (drop (Z.to_nat j) s) s' Ψ ∗
            ⌜ f.(f_inst).(inst_types) !! 1 = Some (Tf [T_i32] [T_i32]) ⌝ ∗
            ⌜ f.(f_inst).(inst_tab) !! 0 = Some j0 ⌝ ∗
            (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m fn) ] (Some a) ∗
            (N.of_nat a) ↦[wf] cl ∗
            ⌜ cl_type cl = Tf [T_i32] [T_i32] ⌝ ∗ 
            (∀ (u : i32) (fc : frame),
                {{{ Φ u ∗
                      ⌜ f_inst f = f_inst fc ⌝ ∗
                       ↪[frame] fc ∗
                       (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m fn) ] (Some a) ∗
                       (N.of_nat a) ↦[wf] cl
                  }}}
                  [ AI_basic (BI_const (VAL_int32 u)) ;
                    AI_invoke a ] @ E
                  {{{ w, (∃ v, ⌜ w = immV [VAL_int32 v] ⌝ ∗ Ψ u v)
                           ∗ ↪[frame] fc
                           ∗ (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m fn) ] (Some a) 
                           ∗ (N.of_nat a) ↦[wf] cl }}}) ∗   
            ↪[frame] f) -∗
  WP (to_e_list map_loop_body) @ E CTX 2;
  push_base (LH_rec [] 0 [] (LH_base [] []) []) 0
    [AI_basic
       (BI_loop (Tf [] [])
          map_loop_body)] [] []
    {{ w, ⌜ w = immV [] ⌝ ∗
           (∃ s', isStack v s' n ∗ stackAll2 s s' Ψ) ∗
           (∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f = f_inst f1 ⌝) ∗
            (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m fn) ] (Some a) ∗
            (N.of_nat a) ↦[wf] cl
    }}.
Proof.
  remember (Z.to_nat j) as k.
  iRevert (Heqk).
  iRevert (j s' s f).
  iInduction k as [|k] "IHk".
  
  { iIntros (j s' s f Habs).
    iIntros "(%Hinstmem & %Hlocs0 & %Hlocs1 & %Hlocs2 & %Hlocs3 & %Hlocs & %Hjbound & %Hlen & Hs & HΦ & HΨ & %Htypes & %Htab & Htab & Hcl & %Hclt & #Hspec & Hf)" => /=.

    iDestruct (stack_pure with "Hs") as "(%Hdiv & %Hvb & %Hlens & Hs)".
    
    assert (j=0)%Z as ->; first lia.
    iApply wp_ctx_bind => //.
    iApply (spec_map_loop_body_terminate with "[Hs Hf]").
    { iFrame.
      repeat iSplit => //.
      iPureIntro.
      lia.
    }
    iIntros (w) "(%Hes & Hs & Hf)".
    destruct Hes as [es ->] => /=.
    rewrite (separate1 (AI_basic _)).
    replace ([AI_basic (BI_br 1)] ++ es) with ([] ++ [AI_basic (BI_br 1)] ++ es) => //.
    iApply wp_base_push => //.
    replace ([AI_basic (BI_br 1)]) with ([] ++ [AI_basic (BI_br 1)]) => //.
    iApply (wp_br_ctx with "Hf") => //.
    iIntros "!> Hf" => /=.
    iApply wp_value; first by instantiate (1 := immV []).
    iSplit => //.
    iSplitL "HΨ Hs".
    { iExists s'.
      rewrite drop_0.
      by iFrame.
    }
    iSplitL "Hf".
    { by iExists f; iSplit => //. }
    by iFrame.
  }
  
  { iIntros (j s' s f Habs).
    iIntros "(%Hinstmem & %Hlocs0 & %Hlocs1 & %Hlocs2 & %Hlocs3 & %Hlocs & %Hjbound & %Hlen & Hs & HΦ & HΨ & %Htypes & %Htab & Htab & Hcl & %Hclt & #Hspec & Hf)" => /=.
    
    iDestruct (stack_pure with "Hs") as "(%Hdiv & %Hvb & %Hlens & Hs)".

    assert (j = Z.of_nat (k+1)) as ->; first lia.

    assert (exists sv, s !! k = Some sv) as Hsvlookup.
    { destruct (s !! k) eqn:Hol => //; first by eexists.
      apply lookup_ge_None in Hol.
      lia.
    }
    destruct Hsvlookup as [sv Hsvlookup].

    assert (take (S k) s = take k s ++ [sv]) as HStake; first by erewrite take_S_r.
    rewrite HStake.

    iDestruct (stackAll_app with "HΦ") as "(HΦ & HsvΦ)".
    simpl.
    iDestruct "HsvΦ" as "(HsvΦ & _)".

    rewrite - HStake.

    iApply wp_ctx_bind => //.
    iApply (spec_map_loop_body_continue with "[Hs HsvΦ Htab Hcl Hf]").
    { iFrame.
      repeat rewrite app_length take_length.
      replace (S k `min` length s) with (S k); last lia.
      replace (S k + length s') with (length s); last lia.
      instantiate (6 := k).
      repeat iSplit => //.
      { rewrite Hlocs2.
        iPureIntro.
        do 2 f_equal.
        lia.
      }
      { iPureIntro. lia. }
      { iPureIntro. lia. }
      { iPureIntro.
        rewrite lookup_app.
        replace (take _ _ !! Z.to_nat k) with (Some sv) => //.
        rewrite lookup_take; last lia.
        by rewrite Nat2Z.id.
      }
    }
    
    iIntros (w) "(-> & H)" => /=.

    iDestruct "H" as "(HsvΨ & Htab & Hcl & Hf)".
    iDestruct "HsvΨ" as (sv') "(Hs & HΨ')".
    
    replace ([AI_basic (BI_br 0)]) with ([] ++ [AI_basic (BI_br 0)]) => //.
    iApply (wp_br_ctx_nested with "Hf") => //; first lia.
    { by instantiate (1 := LH_rec [] 0 [] (LH_base [] []) []) => //=. }

    iIntros "!> Hf".
    rewrite - (app_nil_l [AI_basic (BI_loop _ _)]).
    iApply (wp_loop_ctx with "Hf") => //.
    iIntros "!> Hf".
    replace (cat [] (to_e_list map_loop_body)) with ([] ++ to_e_list map_loop_body ++ []); last done.
    iApply wp_label_push => //.
    simpl.
    remember ({| f_locs := <[2:=value_of_int (v + length (take (S k) s ++ s') * 4 - 4 * k)]> (f_locs f);
                 f_inst := f_inst f |}) as f'.
    rewrite -Heqf'.
    replace (f_inst f) with (f_inst f'); last by rewrite Heqf'.

    iApply "IHk"; first by iPureIntro; instantiate (1 := k); rewrite Nat2Z.id.
    rewrite Heqf' => /=.
    iCombine "HΨ HΨ'" as "HΨcomb".
    iFrame.
    instantiate (1 := (sv' :: s')).
    rewrite app_length take_length.
    assert (S k `min` length s = S k) as Hmin; first lia.
    rewrite Hmin.
    repeat iSplit => //.
    { by rewrite list_lookup_insert_ne. }
    { by rewrite list_lookup_insert_ne. }
    { rewrite list_lookup_insert; last lia.
      iPureIntro.
      do 2 f_equal.
      rewrite - Hlen.
      by lias.
    }
    { by rewrite list_lookup_insert_ne. }
    { rewrite insert_length. iPureIntro; lia. }
    { iPureIntro. lia. }
    { iPureIntro.
      assert (k+1 <= length s)%Z as H; first lias. clear - H.
      remember (length s) as x.
      rewrite - Heqx.
      lia.
    }
    { iPureIntro.
      simpl.
      clear - Hlen.
      remember (length s) as x; rewrite - Heqx.
      remember (length s') as x'; rewrite - Heqx'.
      lia.
    }
    iSplitL "Hs".
    { replace (<[_ := _]> _) with (take k s ++ sv' :: s'); first done.
      erewrite take_S_r => //.
      rewrite insert_app_l; last first.
      { rewrite app_length take_length => /=.
        remember (length s) as x.
        rewrite - Heqx.
        lia.
      }
      rewrite insert_app_r_alt; last first.
      { rewrite take_length => /=.
        remember (length s) as x.
        rewrite - Heqx.
        lia.
      }
      rewrite take_length.
      remember (length s) as x.
      rewrite - Heqx.
      replace (k `min` x) with k; last lia.
      replace (Z.to_nat k - k) with 0; last lia.
      simpl.
      rewrite - app_assoc.
      done.
    }
    iSplitL "HΨcomb".
    { assert ((drop k s) = (sv :: (drop (S k) s))) as Hdeq; first by erewrite drop_S.
      rewrite Hdeq => /=.
      by iDestruct "HΨcomb" as "(? & ?)"; iFrame.
    }
    by repeat iSplit => //.
  }  
Qed.
  
Lemma spec_stack_map (f0 : frame) (n : immediate) (f : i32) (v : Z) (s : seq.seq i32) E
      j0 a cl 
      (Φ : i32 -> iPropI Σ) (Ψ : i32 -> i32 -> iPropI Σ) :
  ⊢ {{{  ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝  ∗
            ⌜ f0.(f_locs) !! 0 = Some (value_of_int v) ⌝ ∗
            ⌜ f0.(f_locs) !! 1 = Some (VAL_int32 f) ⌝  ∗
            ⌜ length f0.(f_locs) >= 4 ⌝ ∗
            isStack v s n ∗
            stackAll s Φ ∗
            ⌜ f0.(f_inst).(inst_types) !! 1 = Some (Tf [T_i32] [T_i32]) ⌝ ∗
            ⌜ f0.(f_inst).(inst_tab) !! 0 = Some j0 ⌝ ∗
            (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
            (N.of_nat a) ↦[wf] cl ∗
            ⌜ cl_type cl = Tf [T_i32] [T_i32] ⌝ ∗ 
            (∀ (u : i32) (fc : frame),
                {{{ Φ u ∗
                      ⌜ f_inst f0 = f_inst fc ⌝ ∗
                       ↪[frame] fc ∗
                       (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
                       (N.of_nat a) ↦[wf] cl
                  }}}
                  [ AI_basic (BI_const (VAL_int32 u)) ;
                    AI_invoke a ] @ E
                  {{{ w, (∃ v, ⌜ w = immV [VAL_int32 v] ⌝ ∗ Ψ u v)
                           ∗ ↪[frame] fc
                           ∗ (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) 
                           ∗ (N.of_nat a) ↦[wf] cl }}}) ∗   
            ↪[frame] f0 }}}
    to_e_list stack_map @ E
    {{{ w, ⌜ w = immV [] ⌝ ∗
           (∃ s', isStack v s' n ∗ stackAll2 s s' Ψ) ∗
           (∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝) ∗
            (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
            (N.of_nat a) ↦[wf] cl
    }}}.
Proof.
  iIntros "!>" (Ξ) "(%Hinstmem & %Hlocs0 & %Hlocs1 & %Hlocs & Hs & HΦ & %Htypes & %Htab & Htab & Hcl & %Hclt & #Hspec & Hf) HΞ" => /=.

  rewrite separate4.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf Hs".
  2: { by iApply (is_stack_valid with "[$Hf $Hs]") => //. }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hs & Hf)" => /=.
  rewrite separate3.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf Hs".
  2: { by iApply (is_stack_bound_valid with "[$Hf $Hs]") => //. }
  { by iIntros "(%Habs & _)". }
  
  iIntros (w) "(-> & Hs & Hf)" => /=.
  rewrite separate5.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf Hs".
  2: { iApply (spec_map_initialise with "[$Hf $Hs]") => //.
       iIntros (w) "(-> & Hs & Hf)".
       instantiate (1 := λ w, (⌜w = immV []⌝ ∗ _)%I).
       iSplit => //.
       iCombine "Hs Hf" as "H".
       by iApply "H".
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hs & Hf)" => /=.
  rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
  iApply (wp_block with "Hf") => //.
  iIntros "!> Hf".
  iSimpl.
  iApply wp_wasm_empty_ctx.
  rewrite - (cat0s [AI_basic (BI_loop _ _)]) - (cats0 [AI_basic (BI_loop _ _)]).
  iApply wp_label_push ; first done.
  rewrite - (app_nil_l [AI_basic (BI_loop _ _)]).
  iApply (wp_loop_ctx with "Hf") => //.
  iIntros "!> Hf".
  simpl.
  rewrite - (cat0s (AI_basic (BI_get_local 2) :: _)).
  rewrite - (cats0 [AI_basic _;_;_;_;_;_;_;_;_;_;_;_;_;_]). 
  iApply wp_label_push ; first done.

  iApply (wp_wand_ctx with "[HΦ Htab Hcl Hs Hf]").
  { iApply spec_map_loop_j.
    iFrame.
    repeat iSplit => /=.
    { done. }
    { rewrite list_lookup_insert_ne; last lia.
      rewrite list_lookup_insert_ne; last lia.
      by rewrite Hlocs0.
    }
    { rewrite list_lookup_insert_ne; last lia.
      rewrite list_lookup_insert_ne; last lia.
      by rewrite Hlocs1.
    }
    { rewrite list_lookup_insert; last by rewrite insert_length; lia.
      instantiate (1 := (length s)).
      instantiate (1 := s).
      simpl.
      iPureIntro.
      do 2 f_equal.
      lia.
    }
    { rewrite list_lookup_insert_ne; last lia.
      rewrite list_lookup_insert; last lia.
      done.
    }
    { by repeat rewrite insert_length. }
    { iPureIntro. lia. }
    { done. }
    { instantiate (1 := []) => /=.
      iPureIntro. lia. }
    { rewrite Nat2Z.id.
      rewrite firstn_all cats0.
      iFrame.
      rewrite drop_all.
      instantiate (1 := Ψ).
      by repeat iSplit => //.
    }
  }
  done.
Qed.


End specs.


End stack.    
      
