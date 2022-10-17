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


Definition pop :=
  validate_stack 0 ++
  [
    BI_get_local 0 ;
    BI_load T_i32 None N.zero N.zero ;
    i32const 4 ;
    BI_binop T_i32 (Binop_i BOI_sub) ;
    BI_tee_local 1 ;
  (* Check if stack is empty *)
    BI_get_local 0 ;
    BI_relop T_i32 (Relop_i ROI_eq) ;
    BI_if (Tf [] []) [BI_unreachable] [] ;
    BI_get_local 1 ; 
    BI_load T_i32 None N.zero N.zero ;
    BI_get_local 0 ;
    BI_get_local 1 ;
    BI_store T_i32 None N.zero N.zero
  ].

End code.



Section specs.

Lemma pop_not_empty (s: list i32) v E f:
  (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - S (length s) * 4 )%Z ->
  f.(f_locs) !! 0 = Some (value_of_int v) ->
  ↪[frame] f ⊢
  WP [AI_basic (BI_const (value_of_int (v + S (length s) * 4))); AI_basic (BI_get_local 0);
     AI_basic (BI_relop T_i32 (Relop_i ROI_eq)); AI_basic (BI_if (Tf [] []) [BI_unreachable] [])] @ E
     {{ w, ⌜ w = immV [] ⌝ ∗ ↪[frame] f }}.
Proof.
  move => Hbounds Hlocs.
  iIntros "Hf".
  remember ((v + (S (length s) * 4))%Z) as x.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜ w = immV [value_of_int x; value_of_int v] ⌝ ∗ ↪[frame] f)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hf".
  { rewrite separate1. iApply wp_val_app => //.
    iSplit => //.
    { iIntros "!>".
      by iIntros "(%H & _)".
    }
    by iApply (wp_get_local with "[] [Hf]") => //.
  }
  iIntros (w) "(-> & Hf)".

  simpl.
  rewrite separate3.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply (wp_relop with "Hf") => //.
       replace (app_relop _ _ _) with (false) => /=.
       instantiate (1 := λ w, ⌜ w = immV [_]⌝%I) => //.
       rewrite Wasm_int.Int32.eq_false => //.
       move => Hcontra.
       destruct Hbounds as [Hlb Hub].
       unfold Wasm_int.Int32.max_unsigned in Hub.
       apply Wasm_int.Int32.repr_inv in Hcontra => //=.
       { subst.
         assert ((S (length s) * 4 > 0)%Z) as Hlb2; by lias.
       }
       2: {
         split; by lias.
       }
       { split; by lias. }
     }
  { by iIntros "(%H & _)". }

  iIntros (w) "(-> & Hf)".
  simpl.
  iApply (wp_if_false with "Hf") => //.
  iIntros "!> Hf".
  replace ([AI_basic (BI_block (Tf [] []) [])]) with ([] ++ [AI_basic (BI_block (Tf [] []) [])]) => //.
  iApply (wp_block with "Hf") => //.
  iIntros "!> Hf".
  by iApply (wp_label_value with "Hf").
Qed.
  
Lemma spec_pop f0 n v (a : i32) s E:
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝
         ∗ ⌜ f0.(f_locs) !! 0 = Some (value_of_int v) ⌝
         ∗ ⌜ length f0.(f_locs) >= 2 ⌝
         ∗ ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - S (length s) * 4 )%Z ⌝
         ∗ isStack v (a :: s) n
         ∗ ↪[frame] f0 }}}
    to_e_list pop @ E
    {{{ w, ⌜ w = immV [VAL_int32 a] ⌝ ∗
                      isStack v s n ∗
                      ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝ }}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hlocv & %Hlocs & %Hv & Hstack & Hf) HΦ" => /=.
  rewrite separate4.
  iApply wp_seq.
  instantiate (1 := λ x,  (⌜ x = immV [] ⌝ ∗ isStack v (a :: s) n ∗ ↪[frame] f0)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hstack Hf"; first by iApply (is_stack_valid with "[$Hstack $Hf]").
  iIntros (w) "(-> & Hstack & Hf)".
  simpl.
  rewrite (separate1 (AI_basic _)).
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int v] ⌝ ∗ ↪[frame] f0)%I).
  iSplitR ; first by iIntros "[%Habs _]".
  iSplitL "Hf".
  - iApply (wp_get_local with "[] [$Hf]") => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate2.
    iApply wp_seq.
    iSplitR ; last first.
    iDestruct "Hstack" as "(%Hdiv & %Hlen & Hv & Hs & Hrest)".
    iSplitR "HΦ".
  - iApply wp_load ; last first.
    iSplitL "Hs Hrest" ; last first.
    iFrame.
    iDestruct (i32_wms with "Hv") as "Hv" => //=.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    instantiate (1 := VAL_int32 _) => /=.
    rewrite N.add_0_r.
    done.
    iNext.
   
    by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ( [∗ list] i↦w ∈ (a :: s)%SEQ, N.of_nat n
                                      ↦[i32][ Z.to_N
                                                (v + 4 + length (a :: s) * 4 - 4 - 4 * i)] w) ∗ ( ∃ bs : seq.seq byte, ⌜Z.of_nat (length bs) = (two16 - 4 - length (a :: s) * 4)%Z⌝ ∗
              N.of_nat n↦[wms][Z.to_N (v + 4 + length (a :: s) * 4)]bs))%I) ; iFrame.
    done.
    done.
  - iIntros (w) "[[(-> & Hs & Hrest) Hp] Hf]". 
    iAssert (isStack v (a :: s) n)%I with "[Hrest Hp Hs]" as "Hstack".
    unfold isStack.
    iFrame.
    rewrite N.add_0_r.
    simpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    repeat iSplit => //=.
    iApply i32_wms => //.
  - unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate3.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [value_of_int (v + S (length s) * 4)] ⌝ ∗
                                       ↪[frame] f0)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - iApply (wp_binop with "Hf") => //=.
    iPureIntro.
    unfold Wasm_int.Int32.isub, Wasm_int.Int32.sub.
    rewrite Wasm_int.Int32.unsigned_repr.
    rewrite Wasm_int.Int32.unsigned_repr.
    unfold value_of_int.
    unfold Wasm_int.int_of_Z => //=.
    remember (length s) as x.
    rewrite - Heqx.
    clear Heqx Hlen s.
    replace (v + 4 + S x * 4 - 4)%Z with (v + S x * 4)%Z ; first done.
    lia.
    unfold Wasm_int.Int32.max_unsigned.
    unfold Wasm_int.Int32.modulus.
    unfold Wasm_int.Int32.wordsize.
    unfold Integers.Wordsize_32.wordsize.
    replace (two_power_nat 32) with 4294967296%Z ; last done.
    lia.
    remember (length s) as x.
    rewrite - Heqx.
    clear Heqx Hlen s.
    lia.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate2.
    iApply (wp_seq _ _ _ (λ x, (⌜ x = immV [value_of_int (v + S (length s) * 4)] ⌝
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
    remember {| f_locs := set_nth (value_of_int (v + S (length s) * 4)) (f_locs f0) 1
                                  (value_of_int (v + S (length s) * 4)) ;
                f_inst := f_inst f0 |} as f1.
    rewrite - Heqf1.
    iSimpl.

    rewrite separate4.
    iApply wp_seq.
    iSplitR; last iSplitL "Hf".
    2: { iApply (pop_not_empty with "Hf") => //.
         rewrite Heqf1 => /=.
         by destruct (f_locs f0) => //.
       }
    { by iIntros "(%H & _)". }
    
    iIntros (w) "(-> & Hf)".
    simpl.

    rewrite (separate1 (AI_basic (BI_get_local 1))).

    iApply wp_seq.
    iSplitR; last iSplitL "Hf".
    2: { iApply (wp_get_local with "[] [Hf]") => //.
         rewrite Heqf1 => /=.
         by rewrite set_nth_read.
         instantiate (1 := λ w, ⌜ w = immV [_] ⌝%I).
         done.
       }
    { by iIntros "(%H & _)". }

    iIntros (w) "(-> & Hf)".
    simpl.
    
    rewrite separate2.
    iApply wp_seq.
    iDestruct "Hstack" as "(_ & _ & Hp & Hs & Hrest)".
    iSplitR ; last first.
    iSplitR "HΦ".
  - iApply wp_load ; last first.
    iFrame.
    rewrite separate1.
    iDestruct (big_sepL_app with "Hs") as "[Ha Hs]".
    iSplitR "Ha" ; last first.
    instantiate (1 := VAL_int32 _) => /=.
    iApply i32_wms.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq Z.mod_small.
    rewrite N.add_0_r Z.mul_0_r Z.sub_0_r.
    iDestruct "Ha" as "[Ha _]".
    remember (length s) as x.
    rewrite - Heqx.
    clear Heqx Hlen s.
    replace (v + 4 + S x * 4 - 4)%Z with (v + S x * 4)%Z.
    done.
    lia.
    unfold Wasm_int.Int32.max_unsigned in Hv. 
    remember (length s) as x.
    rewrite - Heqx.
    clear Heqx Hlen s.
    lia.
    by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ N.of_nat n
                                          ↦[i32][ Z.to_N v] Wasm_int.Int32.repr (v + 4 + length ([a] ++ s)%list * 4) ∗
                                          ( ∃ bs : seq.seq byte,
                                              ⌜Z.of_nat (length bs) = (two16 - 4 - length ([a] ++ s)%list * 4)%Z⌝ ∗
                                                                                                              N.of_nat n↦[wms][Z.to_N (v + 4 + length ([a] ++ s)%list * 4)]bs) ∗
                                          ([∗ list] k↦y ∈ s, N.of_nat n
                           ↦[i32][ Z.to_N
                                     (v + 4 + length ([a] ++ s)%list * 4 - 4 -
                                        4 * (length [a] + k)%nat)] y))%I) ; iFrame.
    subst f1.
    done.
    done.
  - iIntros (w) "[[(-> & Hp & Hrest & Hs) Ha] Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate2.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [VAL_int32 a ; value_of_int v] ⌝ ∗ ↪[frame] f1)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    subst.
    iApply (wp_get_local with "[] [$Hf]") => //=.
    unfold set_nth.
    destruct (f_locs f0) => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate3.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV [VAL_int32 a ; value_of_int v ;
                                        value_of_int (v + S (length s) * 4)] ⌝ ∗
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
    unfold of_val, fmap, list_fmap.
    iSimpl.
    iApply wp_wand_r.
    iSplitL "Hp Hf".
  - rewrite (separate1 (AI_basic _)).
    iApply wp_val_app => //.
    instantiate (1 := λ x, ((⌜ x = immV [VAL_int32 a] ⌝ ∗
                                       N.of_nat n↦[wms][Wasm_int.N_of_uint i32m
                                                                           (Wasm_int.int_of_Z i32m v) + N.zero]bits (value_of_int (v + S (length s) * 4))) ∗
                                                                                                                                                           ↪[frame] f1)%I).
    iSplit ; first by iIntros "!> [[%Habs _] _]".
    iApply wp_store => //.
    instantiate (1 := bits (value_of_int (v + 4 + length (a :: s) * 4))) => //=.
    subst f1 => //=.
    iSimpl.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    rewrite N.add_0_r.
    iFrame.
    iSplitR => //=.
    iDestruct (i32_wms with "Hp") as "Hp" => //.
  - iIntros (w) "[[-> Hp] Hf]".
    iApply "HΦ".
    iSplitR => //.
    unfold isStack.
    simpl in Hlen.
    iSplitR "Hf".
    repeat iSplit => //.
    iPureIntro.
    remember (length s) as x. rewrite - Heqx in Hlen ; clear Heqx s ; lia.
    iFrame.
    iSplitL "Hp".
  - simpl. rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
    rewrite N.add_0_r.
    iApply i32_wms => //.
    unfold value_of_int => /=.
    remember (length s) as x. rewrite - Heqx ; clear Heqx Hlen s.
    replace (v + S (x) * 4)%Z with (v + 4 + x * 4)%Z ; last lia.
    done.
  - iDestruct "Hrest" as (bs) "[%Hbs Hrest]".
    iSplitL "Hs".
    iApply (big_sepL_impl with "Hs").
    iIntros "!>" (k y) "% H".
    simpl.
    remember (length s) as x ; rewrite - Heqx ; clear Heqx Hbs H Hlen s.
    replace ( v + 4 + S x * 4 - 4 - 4 * S k)%Z with
      (v + 4 + x * 4 - 4 - 4 * k)%Z.
    done.
    lia.
    iExists (serialise_i32 a ++ bs).
    iFrame.
    iSplitR.
    iPureIntro.
    rewrite app_length.
    simpl in Hbs.
    rewrite - (Nat2Z.id (length bs)).
    rewrite Hbs.
    remember (serialise_i32 a) as l.
    repeat (destruct l ; first done).
    destruct l ; last done.
    simpl.
    lia.
    unfold mem_block_at_pos.
    rewrite big_sepL_app.
    iSplitL "Ha".
    iApply (big_sepL_impl with "Ha").
    iIntros "!>" (k x) "%Hbits H".
    rewrite of_nat_to_nat_plus.
    rewrite N.add_0_r.
    rewrite of_nat_to_nat_plus.
    unfold Wasm_int.N_of_uint => //=.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq.
    rewrite Z.mod_small ; last by unfold Wasm_int.Int32.max_unsigned in Hv ; remember (length s) as y ; rewrite - Heqy ; clear Heqy Hbs Hlen s ; lia.
    remember (length s) as y ; rewrite - Heqy ; clear Heqy Hbs Hlen s.
    replace (v + S (y) * 4)%Z with (v + 4 + y * 4)%Z ; last lia.
    done.
    iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (k x) "%Hbits H".
    repeat rewrite of_nat_to_nat_plus.
    remember (serialise_i32 a) as l.
    repeat (destruct l => //).
    simpl.
    remember (length s) as y ; rewrite - Heqy ; clear Heqy Hbs Hlen s.
    replace (Z.to_N (v + 4 + S y * 4) + N.of_nat k)%N
      with (Z.to_N (v + 4 + y * 4) + N.of_nat (4+k))%N ; first done.
    simpl.
    lia.
    iExists _ ; by subst ; iFrame.
    all : try by iIntros "[[[% _] _] _]".
Qed.    
    
End specs.


End stack.    
      
