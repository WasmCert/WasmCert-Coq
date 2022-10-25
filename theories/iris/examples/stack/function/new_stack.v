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

Close Scope byte_scope.



Section stack.


 Context `{!wasmG Σ}. 

Section code.

Definition new_stack :=
  [
    i32const 1 ;
    BI_grow_memory ;
    BI_tee_local 0 ;
    i32const (-1) ;
    BI_relop T_i32 (Relop_i ROI_eq) ;  
    BI_if (Tf [] [T_i32]) [
        i32const (-1)
      ] [
        BI_get_local 0 ;
        i32const 65536 ;
        BI_binop T_i32 (Binop_i BOI_mul) ;
        BI_tee_local 0 ;
        BI_get_local 0 ;
        i32const 4 ;
        BI_binop T_i32 (Binop_i BOI_add) ;
        BI_store T_i32 None N.zero N.zero ;
        BI_get_local 0 
      ]                             
  ].

End code.

Section specs.

  Definition overflow : N -> Prop :=
    λ len, (Wasm_int.Int32.modulus - 1)%Z <> Wasm_int.Int32.Z_mod_modulus (ssrnat.nat_of_bin (len `div` page_size)).

Lemma spec_new_stack f0 n len E: 
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ length (f_locs f0) >= 1 ⌝ ∗
        ⌜ overflow len ⌝ ∗
        ⌜ (len + 4 < Z.to_N (two_power_nat 32))%N ⌝ ∗
        ⌜ (page_size | len)%N ⌝ ∗
        ↪[frame] f0 ∗
        N.of_nat n ↦[wmlength] len }}}
    to_e_list new_stack @ E
    {{{ v , (∃ (k : Z), ⌜ v = immV [value_of_int k] ⌝ ∗
                                   (⌜ (k = -1)%Z ⌝ ∗
                                      N.of_nat n↦[wmlength] len ∨
                                      ⌜ (0 <= k)%Z /\ (k + Z.of_N page_size + 4 < two32)%Z ⌝ ∗
                                      ⌜ (k = N.to_nat len) ⌝ ∗
                                      ⌜ overflow (len + page_size)%N ⌝ ∗
                                     isStack k [] n ∗
                                     N.of_nat n ↦[wmlength] (len + page_size)%N) ∗
            ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f1 = f_inst f0 ⌝)%I }}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hflocs & %Hmod & %Hlenoverflow4 & %Hlendiv & Hframe & Hlen) HΦ".
  assert (page_size | len)%N as Hlenmod => //=.
  apply divide_and_multiply in Hlenmod => //=.
  assert (len < Z.to_N (two_power_nat 32))%N as Hlenoverflow ; first lia.
  assert (len `div` page_size < Z.to_N (two_power_nat 32))%N.
  { destruct len ; first done.
    remember (N.pos p) as len.
    assert (len `div`page_size < len)%N.
    apply N.div_lt.
    subst. lia.
    unfold page_size. lia.
    lia. }
  rewrite separate2.
  iApply wp_seq => /=.
  iSplitR.
  - instantiate (1 := λ x,
                   (((⌜ x = immV [VAL_int32 (Wasm_int.int_of_Z
                                            i32m (ssrnat.nat_of_bin
                                                    (len `div` page_size)))] ⌝ ∗
                               (N.of_nat n ↦[wms][ len ]
                                              repeat #00%byte (N.to_nat page_size)) ∗
                              N.of_nat n↦[wmlength] (len + page_size)%N)
                              
                   ∨ (⌜ x = immV [VAL_int32 int32_minus_one] ⌝%I ∗
                N.of_nat n↦[wmlength] len)) ∗ ↪[frame] f0)%I).
    iIntros "[[(%Habs & _ & _) | (%Habs & _)] Hf]" ; inversion Habs.
  - iSplitR "HΦ".
    unfold i32const.
    iApply (wp_grow_memory
              NotStuck E n f0 len
              (λ x, ⌜ x = immV [VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin
                                                                     (len `div`
                                                                          page_size)))] ⌝%I)
              (λ x, ⌜ x = immV [VAL_int32 int32_minus_one] ⌝%I) (Wasm_int.int_of_Z i32m 1)).
    + exact Hinst.
    + iFrame. 
      iSplit ; by iPureIntro.
  - iIntros (w) "H".
    unfold of_val.
    destruct w ; try by iDestruct "H" as "[[[%Habs _ ]| [%Habs _]] _]" ; inversion Habs.
    destruct l ; try by iDestruct "H" as "[[[%Habs _ ]| [%Habs _]] _]" ; inversion Habs.
    destruct l ; try by iDestruct "H" as "[[[%Habs _ ]| [%Habs _]] _]" ; inversion Habs.
    unfold fmap, list_fmap.
    rewrite - separate1.
    rewrite separate2.
    iApply (wp_seq _ E _ (λ x, (⌜ x = immV [v] ⌝
                                      ∗ ↪[frame] {|
                                            f_locs := set_nth v (f_locs f0) 0 v;
                                            f_inst := f_inst f0
                                          |} )%I) ).
    iDestruct "H" as "[H Hf]".
    iSplitR.
  - iIntros "[%Habs _]" ; done.
  - iSplitL "Hf". 
    iApply (wp_tee_local with "Hf").
    iIntros "!> Hf".
    rewrite list_extra.cons_app.
    iApply wp_val_app => //=.
    iSplitR => //=.
    iIntros "!> [%Habs _]" ; done.
    iApply (wp_set_local with "[] [$Hf]") => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    rewrite - separate1.
    rewrite separate3.
    iApply wp_seq.
    iSplitR.
  - instantiate (1 := (λ x, (⌜ if v == value_of_int (-1) then
                                 x = immV [value_of_int 1]
                               else x = immV [value_of_int 0] ⌝ ∗
                                             ↪[frame] {| f_locs := set_nth v
                                                                           (f_locs f0) 0 v ;
                                                        f_inst := f_inst f0 |})%I)).
    iIntros "[%Habs _]".
    by destruct (v == value_of_int (-1)).
  - iSplitL "Hf".
    iApply (wp_relop with "Hf") => //=.
    iPureIntro.
    destruct (v == value_of_int (-1)) eqn:Hv.
    move/eqP in Hv.
    by rewrite Hv.
    destruct v => //=.
    unfold value_of_int in Hv.
    unfold value_of_int.
    unfold wasm_bool.
    destruct (Wasm_int.Int32.eq s (Wasm_int.Int32.repr (-1))) eqn:Hv' => //=.
    apply Wasm_int.Int32.same_if_eq in Hv'.
    rewrite Hv' in Hv.
    rewrite eq_refl in Hv.
    inversion Hv.
  - iIntros (w) "[%Hw Hf]".
    destruct w ; try by destruct (v == value_of_int (-1)).
    destruct l ; first by destruct (v == value_of_int (-1)).
    destruct l ; last by destruct (v == value_of_int (-1)).
    unfold of_val, fmap, list_fmap.
    iSimpl.
    destruct (v == value_of_int (-1)) eqn:Hv.
    + (* grow_memory failed *)
      move/eqP in Hv ; subst v.
      inversion Hw ; subst v0.
      iApply (wp_if_true with "Hf").
      intro.
      done.
      iIntros "!> Hf".
      rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
      iApply wp_wand_r. 
      iSplitL "Hf".
      iApply (wp_block with "Hf") => //=.
      iIntros "!> Hf".
      iApply (wp_label_value with "Hf") => //=.
      instantiate (1 := λ x, ⌜ x = immV [VAL_int32 (Wasm_int.Int32.repr (-1))] ⌝%I ).
      done.
      iIntros (v) "[%Hv Hf]".
      iApply "HΦ".
      iExists _.
      iSplit.
      done.
      iDestruct "H" as "[(%Hm1 & Hb & Hlen) | [_ Hlen]]".
      inversion Hm1.
      exfalso. done.
      iSplitR "Hf".
      iLeft.
      by iSplit.
      iExists _ ; by iFrame.
    + (* grow_memory succeeded *)
      inversion Hw ; subst v0.
      iApply (wp_if_false with "Hf").
      done.
      iIntros "!> Hf".
      rewrite - (app_nil_l [AI_basic (BI_block _ _)]).

      iDestruct "H" as "[ (%Hvv & Hb & Hlen) | [%Hvv Hlen]]" ; inversion Hvv ; subst ;
        last by rewrite eq_refl in Hv ; inversion Hv.
      unfold page_size at 3.
      replace (N.to_nat (64 * 1024)) with (4 + N.to_nat (65532)) ; last done.
      rewrite repeat_app.
      unfold repeat at 1.
      rewrite - separate4.
      iDestruct (wms_append with "Hb") as "[H1 Hb]".
      iDestruct (wms_append with "Hb") as "[H2 Hb]".
      iDestruct (wms_append with "Hb") as "[H3 Hb]".
      iDestruct (wms_append with "Hb") as "[H4 Hb]".
      iAssert (N.of_nat n↦[wms][ len ] [(#00%byte) ; (#00%byte) ; (#00%byte) ; (#00%byte)])%I with "[H1 H2 H3 H4]" as "Hbs".
      { unfold mem_block_at_pos, big_opL.
        repeat rewrite of_nat_to_nat_plus ; rewrite N.add_0_r.
        replace (len + 1 + 1)%N with (len + 2)%N ; last lia.
        replace ( len + 2+ 1)%N with (len + 3)%N ; last lia.
        iFrame. }
      remember (Wasm_int.Int32.repr (ssrnat.nat_of_bin (len `div` page_size))) as c.
      iApply wp_wand_r.        
      instantiate (1 := λ x, ((⌜ x = immV [value_of_int (N.to_nat len)] ⌝ ∗ N.of_nat n↦[i32][ len ] (Wasm_int.Int32.repr (N.to_nat len + 4))) ∗ ↪[frame] {| f_locs := set_nth (VAL_int32 c) (f_locs f0) 0
                                                                                                                                                                       (VAL_int32 (Wasm_int.Int32.imul c (Wasm_int.Int32.repr 65536))); f_inst := f_inst f0 |} )%I).
      iSplitL "Hf Hbs".
      * { iApply wp_wasm_empty_ctx.
          iApply (wp_block_ctx with "Hf") => //=.
          iIntros "!> Hf".
          iApply (wp_label_push_nil _ _ _ _ 0 (LH_base [] []) with "[Hf Hbs]") ;
            last unfold lfilled, lfill => //=.
          simpl.
          rewrite (separate1 (AI_basic (BI_get_local 0))).
          iApply wp_seq_ctx; eauto.
          iSplitL ""; last first.
          - iSplitL "Hf".
            iApply (wp_get_local with "[] [$Hf]") => /=; first by rewrite set_nth_read.
            instantiate (1 := (λ x, ( ⌜x = immV [VAL_int32 c] ⌝)%I)) => //=.
          - 2: { simpl. by iIntros "(%HContra & _ )". }
            iIntros (w) "[-> Hf]".
            unfold of_val, fmap, list_fmap.
            rewrite - separate1.
            rewrite (separate3 (AI_basic _)).
            iApply wp_seq_ctx.
            iSplitL ""; last first.
          - iSplitL "Hf".
            iApply (wp_binop with "Hf").
            unfold app_binop, app_binop_i. done.
            instantiate (1 := λ x,
                           ⌜ x = immV [VAL_int32 (Wasm_int.int_mul Wasm_int.Int32.Tmixin
                                                                   c (Wasm_int.int_of_Z i32m
                                                                                        65536))
                                   ] ⌝%I ) => //=.
          - 2: { simpl. by iIntros "(%HContra & _ )". }
            iIntros (w) "[-> Hf]".
            unfold of_val, fmap, list_fmap.
            rewrite - separate1.
            rewrite (separate2 (AI_basic _)).
            iApply wp_seq_ctx.
            iSplitL ""; last first.
            iSplitL "Hf".
            iApply (wp_tee_local with "Hf").
            iIntros "!> Hf".
            rewrite separate1.
        instantiate (1 :=  ( λ x,  (⌜ x = immV [(VAL_int32 (
                                                    Wasm_int.int_mul
                                                      Wasm_int.Int32.Tmixin
                                                      c (Wasm_int.int_of_Z
                                                           i32m 65536))
                                           )] ⌝
                                              ∗ ↪[frame]
                                              {| f_locs := set_nth
                                                             (VAL_int32 (
                                                                  Wasm_int.int_mul
                                                                    Wasm_int.Int32.Tmixin
                                                                    c (Wasm_int.int_of_Z
                                                                         i32m 65536)))
                                                            (set_nth
                                                               (VAL_int32 c)
                                                               (f_locs f0) 0
                                                               (VAL_int32 c))
                                                            0
                                                             (VAL_int32 (
                                                                  Wasm_int.int_mul
                                                                    Wasm_int.Int32.Tmixin
                                                                    c (Wasm_int.int_of_Z
                                                                         i32m 65536)))
                                              |})%I)).
        iApply wp_val_app => //=.
        iSplit; first by iIntros "!> (%HContra & _)" => //.
        iApply (wp_set_local with "[] [$Hf]") => //=.
        rewrite length_is_size size_set_nth.
        unfold ssrnat.maxn.
        rewrite length_is_size in Hflocs.
        destruct (ssrnat.leq 2 (seq.size (f_locs f0))) ; lia.
        rewrite set_nth_write.
        simpl.
        iIntros (w) "[-> Hf]".
        unfold of_val, fmap, list_fmap.
        rewrite - separate1.
        rewrite (separate2 (AI_basic _)).
        iApply wp_seq_ctx.
        iSplitL ""; last first.
        iSplitL "Hf".
        rewrite separate1.
        iApply wp_val_app => //=.
        instantiate (1 := (λ x, (⌜ x = immV [VAL_int32 (Wasm_int.int_mul
                                                          Wasm_int.Int32.Tmixin
                                                          c (Wasm_int.int_of_Z
                                                               i32m 65536)) ;
                                             VAL_int32 (Wasm_int.int_mul
                                                          Wasm_int.Int32.Tmixin
                                                          c (Wasm_int.int_of_Z
                                                               i32m 65536))] ⌝ 
                                            ∗ ↪[frame]
                                            {| f_locs := set_nth (VAL_int32 c)
                                                                 (f_locs f0) 0
                                                                 (VAL_int32
                                                                    (Wasm_int.Int32.imul
                                                                       c (Wasm_int.int_of_Z
                                                                            i32m 65536))) ;
                                              f_inst := f_inst f0
                                            |})%I )).
        iSplitL ""; first by iIntros "!> (%HContra & _)" => //.
        iApply (wp_get_local with "[] [$Hf]") => //=.
        rewrite set_nth_read => //=.
        iIntros (w) "[-> Hf]".
        unfold of_val, fmap, list_fmap.
        rewrite - separate2.
        rewrite (separate4 (AI_basic _)).
        iApply wp_seq_ctx.
        iSplitL ""; last first.
        iSplitL "Hf".
        rewrite separate1.
        iApply wp_val_app => //=.
        instantiate (1 := (λ x, (⌜ x = immV [VAL_int32 (Wasm_int.Int32.imul
                                                          c (Wasm_int.Int32.repr 65536)) ;
                                             VAL_int32 (Wasm_int.Int32.iadd
                                                          (Wasm_int.Int32.imul
                                                             c (Wasm_int.int_of_Z
                                                                  i32m 65536))
                                                          (Wasm_int.int_of_Z i32m 4))] ⌝
                                            ∗ ↪[frame]
                                            {| f_locs := set_nth
                                                           (VAL_int32 c)
                                                           (f_locs f0)
                                                           0 (VAL_int32 (
                                                                  Wasm_int.Int32.imul
                                                                    c (Wasm_int.Int32.repr
                                                                         65536))) ;
                                              f_inst := f_inst f0 |})%I )).
        iSplitL ""; first by iIntros "!> (%HContra & _)" => //.
        iApply (wp_binop with "Hf") => //=.
        iIntros (w) "[-> Hf]".
        unfold of_val, fmap, list_fmap.
        rewrite - separate2.
        rewrite (separate3 (AI_basic _)).
        iApply wp_seq_ctx.
        iSplitL ""; last first.
        iSplitL.
        iApply (wp_store with "[Hf Hbs]").
        done.
        instantiate (1 := [(#00%byte); (#00%byte); (#00%byte); (#00%byte)]).
        done.
        instantiate (2 := {| f_locs := set_nth (VAL_int32 c) (f_locs f0) 0
                                               (VAL_int32 (Wasm_int.Int32.imul
                                                             c (Wasm_int.Int32.repr
                                                                  65536))) ;
                            f_inst := f_inst f0 |}) => //=.
        instantiate (1 := λ x, ⌜x = immV []⌝%I ) => //=.
        iSplitL "" => //.
        iFrame.
        replace len with (Z.to_N (Wasm_int.Int32.Z_mod_modulus (Wasm_int.Int32.unsigned c * 65536)) + N.zero)%N => //.
        rewrite Heqc.
        unfold Wasm_int.Int32.unsigned.
        rewrite N.add_0_r => /=.
        do 2 rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        rewrite (Z.mod_small (ssrnat.nat_of_bin (len `div` page_size)) (two_power_nat 32)).
        replace (ssrnat.nat_of_bin (len `div` page_size) * 65536)%Z with (Z.of_N len).
        rewrite Z.mod_small.
        lia.
        lia.
        rewrite <- Hlenmod at 1.
        unfold page_size.
        replace (64 * 1024)%N with 65536%N ; last done.
        rewrite - (Z2N.id (_ * _)%Z) ; last lia.
        rewrite Z2N.inj_mul ; try lia.
        rewrite nat_of_bin_to_N.
        lia.
        split.
        lia.
        rewrite - (Z2N.id (ssrnat.nat_of_bin _)) ; last lia.
        rewrite nat_of_bin_to_N.
        lia.
        iIntros (w) "((-> & Hwm) & Hf)".
        unfold of_val, fmap, list_fmap.
        iSimpl.
        rewrite - (app_nil_r ([AI_basic _])).
        iApply wp_seq_ctx.
        iSplitL ""; last first.
        iSplitL "Hf".
        iApply (wp_get_local with "[] [$Hf]").
        simpl.
        rewrite set_nth_read.
        done.
        iModIntro.
        instantiate (1 := λ x, ⌜x = immV [ value_of_int (N.to_nat len) ]⌝%I).
        iPureIntro.
        simpl.
        unfold value_of_int.
        rewrite Heqc.
        unfold Wasm_int.Int32.imul.
        rewrite Wasm_int.Int32.mul_signed => /=.
        repeat f_equal.
        rewrite Wasm_int.Int32.signed_repr.
        rewrite Wasm_int.Int32.signed_repr.
        rewrite <- Hlenmod at 2.
        unfold page_size.
        replace (64 * 1024)%N with 65536%N ; last done.
        rewrite - (Z2N.id (ssrnat.nat_of_bin _)) ; last lia.
        rewrite nat_of_bin_to_N.
        lia.
        unfold Wasm_int.Int32.min_signed.
        unfold Wasm_int.Int32.max_signed.
        unfold Wasm_int.Int32.half_modulus.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        done.
        unfold Wasm_int.Int32.min_signed.
        unfold Wasm_int.Int32.max_signed.
        unfold Wasm_int.Int32.half_modulus.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        rewrite - (Z2N.id (ssrnat.nat_of_bin _)) ; last lia.
        rewrite nat_of_bin_to_N.
        split.
        assert (len >= 0)%N ; first lia.
        assert (page_size > 0)%N ; first by unfold page_size ; lia.
        assert (len `div` page_size >= 0)%N ; first lia.
        assert (two_power_nat 32 >= 2)%Z.
        unfold two_power_nat.
        unfold shift_nat.
        simpl.
        lia.
        assert ( 2 > 0 )%Z ; first lia.
        assert (0 < two_power_nat 32 `div` 2)%Z.
        apply Z.div_str_pos.
        lia.
        lia.
        assert (len `div` 2 < Z.to_N (two_power_nat 32) `div` 2)%N.
        apply div_lt => //=.
        assert (2 | page_size)%N.
        unfold page_size.
        replace (64*1024)%N with 65536%N ; last done.
        unfold N.divide.
        exists 32768%N.
        done.
        eapply N.divide_trans => //=.
        unfold N.divide.
        exists 2147483648%N.
        done.
        assert ( 2 < page_size )%N .
        unfold page_size ; lia.
        assert (len `div` page_size <= len `div` 2)%N.
        apply N.div_le_compat_l.
        done.
        eapply Z.le_trans.
        instantiate (1 := Z.of_N (len `div` 2)).
        lia.
        assert (len `div`2 <= Z.to_N (two_power_nat 32) `div` 2 - 1)%N ; first lia.
        apply N2Z.inj_le in H3.
        rewrite N2Z.inj_sub in H3.
        rewrite (N2Z.inj_div (Z.to_N _)) in H3.
        rewrite Z2N.id in H3.
        lia.
        lia.
        unfold two_power_nat.
        simpl.
        replace (4294967296 `div` 2)%N with 2147483648%N ; last done.
        lia.
        iIntros (w) "[-> Hf]".
        unfold of_val, fmap, list_fmap.
        rewrite app_nil_r.
        iApply (wp_val_return with "Hf").
        done.
        iIntros "Hf".
        rewrite app_nil_r app_nil_l.
        iApply wp_value.
        unfold IntoVal.
        apply language.of_to_val.
        done.
        iFrame.
        iSplit => //=.
        replace (Z.to_N (Wasm_int.Int32.Z_mod_modulus
                           (Wasm_int.Int32.unsigned c * 65536)) + N.zero)%N
          with len.
        subst c.
        unfold Wasm_int.Int32.imul.
        unfold Wasm_int.Int32.mul.
        rewrite - (Z2N.id (ssrnat.nat_of_bin _)) ; last lia.
        rewrite nat_of_bin_to_N.
        rewrite Wasm_int.Int32.unsigned_repr.
        rewrite Wasm_int.Int32.unsigned_repr.
        replace (Z.of_N (len `div` page_size) * 65536)%Z with (Z.of_N len).
        unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
        rewrite Wasm_int.Int32.unsigned_repr.
        rewrite Wasm_int.Int32.unsigned_repr.
        unfold serialise_i32.
        rewrite Wasm_int.Int32.unsigned_repr.
        unfold value_of_int.
        iApply i32_wms => //.
        unfold bits, serialise_i32.
        simpl.
        rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        rewrite Z.mod_small.
        replace (Z.of_N len + 4)%Z with (N.to_nat len + 4)%Z ; last lia.
        done.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        lia.
        unfold Wasm_int.Int32.max_unsigned.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        lia.
        unfold Wasm_int.Int32.max_unsigned.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        lia.
        unfold Wasm_int.Int32.max_unsigned.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        lia.
        rewrite <- Hlenmod at 1.
        unfold page_size.
        lia.
        unfold Wasm_int.Int32.max_unsigned.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        unfold two_power_nat => //=.
        unfold Wasm_int.Int32.max_unsigned.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        split ; last lia.
        assert (len >= 0)%N ; first lia.
        assert (page_size > 0)%N ; first by unfold page_size.
        lia.
        subst c.
        rewrite Wasm_int.Int32.unsigned_repr.
        rewrite - (Z2N.id (ssrnat.nat_of_bin _)).
        rewrite nat_of_bin_to_N.
        rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        rewrite Z.mod_small.
        rewrite <- Hlenmod at 1.
        unfold page_size.
        replace (64 * 1024)%N with 65536%N ; last done.
        rewrite - (Z2N.id 65536%Z).
        rewrite - N2Z.inj_mul.
        rewrite N2Z.id.
        unfold N.zero.
        lia.
        lia.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        rewrite - (Z2N.id 65536).
        rewrite - N2Z.inj_mul.
        unfold page_size.
        unfold page_size in Hlenmod.
        replace (64 * 1024)%N with 65536%N ; last done.
        replace (64 * 1024)%N with 65536%N in Hlenmod ; last done.
        rewrite Hlenmod.
        lia.
        lia.
        lia.
        unfold Wasm_int.Int32.max_unsigned.
        unfold Wasm_int.Int32.modulus.
        unfold Wasm_int.Int32.wordsize.
        unfold Integers.Wordsize_32.wordsize.
        rewrite - (Z2N.id (ssrnat.nat_of_bin _)).
        rewrite nat_of_bin_to_N.
        split ; last lia.
        assert (len >= 0)%N ; first lia.
        assert (page_size > 0)%N ; first by unfold page_size ; lia.
        lia.
        lia.
        all: try by iIntros "(%HContra & _)".
        by iIntros "((%HContra & _) & _)". } 
      * iIntros (w) "[[-> Hn] Hf]".
        iApply "HΦ".
        iExists _.
        iSplit ; first done.
        iSplitR "Hf".
        iRight.
        iSplit.
        iPureIntro.
        split ; first lia.
        { destruct Hlendiv as [k ->].
          unfold page_size.
          unfold two32.
          replace (Z.to_N (two_power_nat 32)) with 4294967296%N in Hlenoverflow ; last done.
          unfold page_size in Hlenoverflow.
          assert (k < 65536)%N.
          lia.
          assert (k + 1 <= 65536)%N ; first lia.
          replace (N.to_nat (k * (64 * 1024)) + Z.pos (64 * 1024))%Z
            with (N.to_nat (k + 1)%N * (64 * 1024))%Z ; last lia.
          admit. }
        iSplit;[auto|].
        iSplit;[admit|].
        iSplitR "Hlen". 
        unfold isStack.
        replace (Z.to_N (N.to_nat len)) with len ; last lia.
        iSimpl.
        replace (N.to_nat len + 4 + 0%nat * 4)%Z with (N.to_nat len + 4)%Z ; last lia.
        iSplitR.
        iPureIntro.
        unfold page_size in Hlendiv.
        replace (64 * 1024)%N with 65536%N in Hlendiv ; last done.
        unfold Z.divide.
        unfold N.divide in Hlendiv.
        destruct Hlendiv as [r ->].
        exists (Z.of_N r).
        unfold two16 ; lia.
        iSplitR.
        iPureIntro.
        unfold two14 ; lia.
        iSplitL "Hn" ; first done.
        iSplit ; first done.
        iExists (repeat #00%byte ( N.to_nat 65532)).
        iSplit ; first by rewrite repeat_length.
        replace (Z.to_N (N.to_nat len + 4)) with (len + 1 + 1 + 1 + 1)%N ; last lia.
        done.
        done.
        iExists _ ; iFrame.
        done.
Admitted.

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
    interp_closure_native i0 [] [T_i32] [T_i32] (to_e_list new_stack) [].
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
    iDestruct (big_sepL2_length with "Hws") as %Hlen. inversion Heq. destruct ws;[|done]. simpl.
    iApply fupd_wp.
    iMod (na_inv_acc with "Hstk Hown") as "(>Hstkres & Hown & Hcls)";[solve_ndisj..|].
    iDestruct "Hstkres" as (len) "[% [% [% [Hlen Hstkres]]]]".
    iApply (spec_new_stack with "[$Hf $Hlen]");[auto|].
    iModIntro.
    iIntros (v) "HH".
    iDestruct "HH" as (k) "[-> [Hcases Hf]]".
    iDestruct "Hf" as (f') "[Hf %Hfinst]". simpl in Hfinst.
    iApply (wp_val_return with "[$]");auto.
    iIntros "Hf /=".
    iApply wp_value;[eapply of_to_val;eauto|].
    iExists _. iFrame. iIntros "Hf".
    iApply fupd_wp.
    iMod ("Hcls" with "[$Hown Hcases Hstkres]").
    { iNext.
      iDestruct "Hcases" as "[[Heq Hm] | [[% %] [% [% [Hs Hm]]]]]".
      - iExists _. iFrame. auto.
      - iExists _.
        rewrite <- (N2Nat.id page_size), <- Nat2N.inj_add.
        iFrame "Hm". repeat iSplit.
        + iPureIntro. rewrite (N2Nat.id page_size) Nat2N.inj_add N2Nat.id. auto.
        + iPureIntro. subst k.
          rewrite Nat2N.inj_add. unfold page_size.
          clear -H4. rewrite N2Nat.id. unfold two32 in H4.
          replace (Z.to_N (two_power_nat 32)) with 4294967296%N;[|done].
          lia.
        + iPureIntro. rewrite N2Nat.id Nat2N.inj_add N2Nat.id.
          apply N.divide_add_r;auto. apply N.divide_refl.
        + admit. }
    admit.
  Admitted.    

End valid.


End stack.    
      
