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

Definition stack_map :=
  validate_stack 1 ++
  [
    BI_get_local 1 ;
    BI_load T_i32 None N.zero N.zero ;
    BI_set_local 3 ;
    BI_get_local 1 ;
    i32const 4 ;
    BI_binop T_i32 (Binop_i BOI_add) ;
    BI_set_local 2 ;
    BI_block (Tf [] [])
             [BI_loop (Tf [] [])
                      [BI_get_local 2 ;
                       BI_get_local 3 ;
                       BI_relop T_i32 (Relop_i (ROI_ge SX_U)) ;
                       BI_br_if 1 ;
                       BI_get_local 2 ;
                       BI_get_local 2 ;
                       BI_get_local 2 ;
                       BI_load T_i32 None N.zero N.zero ;
                       BI_get_local 0 ;
                       BI_call_indirect 1 ;
                       BI_store T_i32 None N.zero N.zero ;
                       i32const 4 ;
                       BI_binop T_i32 (Binop_i BOI_add) ;
                       BI_set_local 2 ;
                       BI_br 0]
             ]
  ].



End code.



Section specs.

Lemma spec_stack_map (f0 : frame) (n : immediate) (f : i32) (v : Z) (s : seq.seq i32) E
      j0 a cl 
      (Φ : i32 -> iPropI Σ) (Ψ : i32 -> i32 -> iPropI Σ) :
  ⊢ {{{  ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝  ∗
            ⌜ f0.(f_locs) !! 0 = Some (VAL_int32 f) ⌝  ∗
            ⌜ f0.(f_locs) !! 1 = Some (value_of_int v) ⌝ ∗
            ⌜ length f0.(f_locs) >= 4 ⌝ ∗
            ⌜ (0 <= v)%Z ⌝ ∗                                   
            ⌜ (v + 4 + length s * 4 ≤ Wasm_int.Int32.max_unsigned)%Z ⌝ ∗
            isStack v s n ∗
            stackAll s Φ ∗
            ⌜ f0.(f_inst).(inst_types) !! 1 = Some (Tf [T_i32] [T_i32]) ⌝ ∗

            ⌜ f0.(f_inst).(inst_tab) !! 0 = Some j0 ⌝ ∗
            (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
            (N.of_nat a) ↦[wf] cl ∗
            ⌜ match cl with FC_func_native _ t _ _ => t | FC_func_host t _ => t end
         = Tf [T_i32] [T_i32] ⌝ ∗ 
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
  iIntros "!>" (Ξ) "(%Hinstmem & %Hlocs0 & %Hlocs1 & %Hlocs & %Hvb & %Hv & Hs & HΦ & %Htypes & %Htab & Htab & Hcl & %Hclt & #Hspec & Hf) HΞ" => /=.
  rewrite separate4.
  iApply wp_seq.
  instantiate (1 := λ x,  (⌜ x = immV [] ⌝ ∗ isStack v s n ∗ ↪[frame] f0)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hs Hf"; first by iApply (is_stack_valid with "[$Hs $Hf]").
  iIntros (w) "(-> & Hs & Hf)".
  simpl.
  rewrite (separate1 (AI_basic (BI_get_local 1))).
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply wp_get_local => //.
  instantiate (1 := λ x, ⌜x = immV [value_of_int v]⌝%I) => //.
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (i32const v))).
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf Hs".
  iApply wp_load => // ; last first.
  unfold isStack.
  iDestruct "Hs" as "(% & % & Hn & ?)".
  iDestruct (i32_wms with "Hn") as "Hn".
  rewrite N.add_0_r.
  simpl.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  unfold bits.
  instantiate (1 := VAL_int32 _) => /=.
  iFrame.
  iNext.
  instantiate ( 1 := λ x, (⌜ x = immV [value_of_int (v + 4 + length s * 4)] ⌝ ∗
                                     ⌜(two16 | v)%Z⌝ ∗
                                     ⌜(length s < two14)%Z⌝ ∗
                                     ([∗ list] i↦w ∈ s, N.of_nat n ↦[i32][ Z.to_N (v + 4 + length s * 4 - 4 - 4 * i)] w) ∗
      (∃ bs : seq.seq byte, ⌜Z.of_nat (length bs) = (two16 - 4 - length s * 4)%Z⌝ ∗
                                                                              N.of_nat n↦[wms][Z.to_N (v + 4 + length s * 4)]bs))%I).
  iFrame.
  done.
  unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
  done.
  iIntros (w) "[[[-> Hs] Hn] Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (i32const (v + _ + _)))).
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply wp_set_local => //.
  by instantiate (1 := λ x, ⌜x = immV []⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate1 (AI_basic (BI_get_local 1))).
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_get_local with "[] [$Hf]") => //=.
  unfold set_nth.
  destruct (f_locs f0) ; first by inversion Hlocs0.
  destruct l ; first by inversion Hlocs1.
  simpl in Hlocs1.
  inversion Hlocs1 ; subst.
  done.
  by instantiate (1 := λ x, ⌜x = immV [value_of_int v]⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite separate3.
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_binop with "Hf") => //.
  by instantiate (1 := λ x, ⌜ x = immV [_] ⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 _ (AI_basic (BI_set_local 2))).
  iApply wp_seq.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply wp_set_local => //=.
  simpl.
  rewrite length_is_size size_set_nth.
  rewrite length_is_size in Hlocs.
  unfold ssrnat.maxn.
  destruct (ssrnat.leq _ _) ; lia.
  by instantiate (1 := λ x, ⌜x = immV []⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
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
  rewrite - (cats0 [AI_basic _;_;_;_;_;_;_;_;_;_;_;_;_;_;_]). 
  iApply wp_label_push ; first done.
  unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
  rewrite Wasm_int.Int32.unsigned_repr ; last lia.
  rewrite Wasm_int.Int32.unsigned_repr ; last by unfold Wasm_int.Int32.max_unsigned,
      Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
  iAssert (∀ (j :nat) s', ⌜ j <= length s ⌝ -∗ ⌜ length s' = length s - j ⌝ -∗ ↪[frame] {|
                    f_locs :=
                      set_nth (VAL_int32 (Wasm_int.Int32.repr (v + 4 )))
                        (set_nth
                           (VAL_int32 (Wasm_int.Int32.repr (v + 4 + length s * 4)))
                           (f_locs f0) 3
                           (VAL_int32 (Wasm_int.Int32.repr (v + 4 + length s * 4)))) 2
                        (VAL_int32 (Wasm_int.Int32.repr (v + 4 + (length s - j%Z) * 4)));
                    f_inst := f_inst f0
                    |} -∗
                    isStack v (take j s ++ s') n -∗ 
                    stackAll (take j s) Φ -∗
                    stackAll2 (drop j s) s' Ψ -∗
                    N.of_nat j0 ↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))]Some a -∗
                    N.of_nat a↦[wf] cl -∗
                    (∀ w : val,
                        ⌜w = immV []⌝ ∗ (∃ s' : seq.seq i32, isStack v s' n ∗ stackAll2 s s' Ψ) ∗
                                  (∃ f1 : frame,  ↪[frame]f1 ∗ ⌜f_inst f0 = f_inst f1⌝) ∗
              N.of_nat j0↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))]
              Some a ∗ N.of_nat a↦[wf]cl -∗ 
                                  Ξ w) -∗
                    WP [AI_basic (BI_get_local 2); AI_basic (BI_get_local 3);
     AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_U))); AI_basic (BI_br_if 1);
     AI_basic (BI_get_local 2); AI_basic (BI_get_local 2); AI_basic (BI_get_local 2);
     AI_basic (BI_load T_i32 None N.zero N.zero); AI_basic (BI_get_local 0);
     AI_basic (BI_call_indirect 1); AI_basic (BI_store T_i32 None N.zero N.zero);
     AI_basic (i32const 4); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_set_local 2); AI_basic (BI_br 0)] @  E
  CTX
  2;
  push_base (LH_rec [] 0 [] (LH_base [] []) []) 0
    [AI_basic
       (BI_loop (Tf [] [])
          [BI_get_local 2; BI_get_local 3; BI_relop T_i32 (Relop_i (ROI_ge SX_U));
          BI_br_if 1; BI_get_local 2; BI_get_local 2; BI_get_local 2;
          BI_load T_i32 None N.zero N.zero; BI_get_local 0; 
          BI_call_indirect 1; BI_store T_i32 None N.zero N.zero; 
          i32const 4; BI_binop T_i32 (Binop_i BOI_add); BI_set_local 2; 
          BI_br 0])] [] []
    {{ v0, Ξ v0 }})%I as "H".
  { iIntros (j).
    iInduction j as [|j] "IHj".
  { iIntros (s') "%Hj %Hs' Hf Hs HΦ HΨ Htab Hcl HΞ".
    rewrite (separate1 (AI_basic (BI_get_local 2))).
    iApply wp_seq_ctx.
    iSplitR ; last first.
    iSplitL "Hf".
    iApply (wp_get_local with "[] [$Hf]").
    simpl. by rewrite set_nth_read.
    by instantiate ( 1 := λ x, ⌜x = immV _⌝%I).
    iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite (separate2 _ (AI_basic (BI_get_local 3))).
    iApply wp_seq_ctx.
    iSplitR ; last first.
    iSplitL "Hf".
    rewrite (separate1 _ [AI_basic (BI_get_local 3)]).
    iApply wp_val_app => //.
    iSplitR ; last first.
    iApply wp_wand_r.
    iSplitL.
    iApply (wp_get_local with "[] [$Hf]").
    simpl.
    destruct (f_locs f0) ; first by inversion Hlocs.
    destruct l ; first by inversion Hlocs1.
    destruct l ; first by simpl in Hlocs ; lia.
    simpl.
    by rewrite set_nth_read.
    by instantiate (1 := λ x, ⌜x = immV _⌝%I).
    iIntros (w) "[-> Hf]".
    rewrite Z.sub_0_r.
    iSimpl.
    instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
    iFrame.
    done.
    by iIntros "!> [% _]".
    iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite (separate3 _ _ (AI_basic (BI_relop _ _))).
    iApply wp_seq_ctx.
    iSplitR ; last first.
    iSplitL "Hf".
    iApply (wp_relop with "Hf").
    simpl.
    unfold Wasm_int.Int32.ltu.
    rewrite Wasm_int.Int32.unsigned_repr.
    rewrite Coqlib.zlt_false.
    simpl.
    done.
    lia.
    split ; try lia.
    exact Hv.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite - (app_nil_l (AI_basic (i32const 1) :: _)).
    rewrite (separate2 _ (AI_basic (BI_br_if 1))).
    iApply wp_base_push ; first done.
    iApply (wp_br_if_true_ctx with "Hf").
    done.
    iIntros "!> Hf".
    rewrite - (app_nil_l [AI_basic (BI_br 1)]).
    iApply (wp_br_ctx with "Hf") => //.
    iIntros "!> Hf".
    iApply wp_value.
    unfold IntoVal.
    by apply of_to_val.
    iApply "HΞ".
    iSplit ; first done.
    iFrame. iSplitR "Hf".
    iExists s'.
    unfold take.
    unfold drop.
    iFrame.
    iExists _.
    iFrame.
    done.
    all : try by iIntros "[% _]". }
  iIntros (s') "%Hj %Hs' Hf Hs HΦ HΨ Htab Hcl HΞ".
  destruct s as [|v0 s]; first by inversion Hj.
  cut (exists ys y, v0 :: take j s = ys ++ [y]) ;
  [ intro Htail ; destruct Htail as (ys & y & Htail) |
    exists (removelast (v0 :: take j s)) ;
    exists (List.last (v0 :: take j s) (Wasm_int.Int32.repr 1)) ;
    apply app_removelast_last ;
    apply not_eq_sym ; apply nil_cons ].
  simpl in Hv.
  simpl in Hj.
  assert (j `min` length s = j) as Hjmin.
  { remember (length s) as x. rewrite - Heqx in Hj.
    lia. } 
  rewrite (separate1 (AI_basic (BI_get_local 2))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_get_local with "[] [$Hf]").
  simpl. by rewrite set_nth_read.
  by instantiate ( 1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 _ (AI_basic (BI_get_local 3))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate1 _ [AI_basic (BI_get_local 3)]).
  iApply wp_val_app => //.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "[] [$Hf]").
  simpl.
  destruct (f_locs f0) ; first by inversion Hlocs.
  destruct l ; first by inversion Hlocs1.
  destruct l ; first by simpl in Hlocs ; lia.
  simpl.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
  iFrame.
  done.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate3 _ _ (AI_basic (BI_relop _ _))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_relop with "Hf").
  simpl.
  unfold Wasm_int.Int32.ltu.
  rewrite Wasm_int.Int32.unsigned_repr.
  rewrite Wasm_int.Int32.unsigned_repr.
  rewrite Coqlib.zlt_true.
  simpl.
  done.
  lia.
  lia.
  lia.
  by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (BI_const (VAL_int32 _)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_br_if_false with "Hf").
  done.
  iNext.
  by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate1 (AI_basic (BI_get_local 2)) [_;_;_;_;_;_;_;_;_;_]).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_get_local with "[] [$Hf]") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate1 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app. done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "[] [$Hf]") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate3 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "[] [$Hf]") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate4 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf Hs".
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
 
  iApply wp_wand_r.
  iSplitL.

  iApply wp_load ; last first.
  iFrame.
  unfold isStack.
  iDestruct "Hs" as "(Hdiv & Hlen & Hn & Hl & Hbs)".
  rewrite cat_app.
  iDestruct (big_sepL_app with "Hl") as "[Hs Hs']".
  rewrite app_length.
  rewrite Hs'.
  rewrite take_length.
  replace (S j `min` length (v0 :: s)) with (S j) ; last by simpl ; lia.
  unfold take ; fold (take (A := value)).
  rewrite Htail.
  iDestruct (big_sepL_app with "Hs") as "[Hs H]".
  iDestruct "H" as "[H _]".
  iDestruct (i32_wms with "H") as "H" => //.
  rewrite Nat.add_0_r.
  rewrite N.add_0_r.
  replace (Wasm_int.N_of_uint i32m (Wasm_int.Int32.repr (v + 4 + (S (length s) - S j) * 4)))
    with (Z.to_N (v + 4 + (S (length s) - S j) * 4)).
  replace (S j + (length (v0 :: s) - S j)) with (length (v0 :: s)) ; last by simpl ; lia.
  replace (v + 4 + length (v0 :: s) * 4 - 4 - 4 * length ys)%Z
    with (v + 4 + length (v0 :: s) * 4 - S (length ys) * 4)%Z ; last lia.
  replace (S (length ys)) with (length (ys ++ [y])) ;
    last by rewrite app_length ; simpl ; lia.
  rewrite (cat_app ys [y]).
  rewrite - Htail.
  simpl.
  rewrite firstn_length.
  rewrite Hjmin.
  rewrite (Z.mul_sub_distr_r (S (length s)) (S j) 4).
  simpl in Hj.
  remember (length s) as x.
  rewrite - Heqx.
  replace (v + 4 + S x * 4 - S j * 4)%Z
    with (v + 4 + (S x * 4 - S j * 4))%Z ;
    last lia.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq Z.mod_small.
  instantiate (1 := VAL_int32 _).
  iSplitR "H" ; last iExact "H".
  iNext.
  subst x.
  instantiate ( 1 := λ x, (⌜ x = immV [VAL_int32 y] ⌝ ∗ ⌜ (two16 | v)%Z ⌝ ∗ ⌜ (S (length s) < two14)%Z ⌝ ∗ N.of_nat n ↦[i32][ Z.to_N v] Wasm_int.Int32.repr (v + 4 + S (length s) * 4) ∗  (∃ bs : seq.seq byte, ⌜ Z.of_nat (length bs) = (two16 - 4 - S (length s) * 4)%Z⌝ ∗
            N.of_nat n↦[wms][Z.to_N (v + 4 + S (length s) * 4)]bs) ∗ ([∗ list] k↦y0 ∈ s', N.of_nat n
                              ↦[i32][ Z.to_N
                                        (v + 4 + S (length s) * 4 - 4 - 4 * S (j + k))] y0) ∗ [∗ list] k↦y0 ∈ ys, N.of_nat n
                             ↦[i32][ Z.to_N (v + 4 + S (length s) * 4 - 4 - 4 * k)] y0)%I).
  iFrame.
  done.
  simpl.
  unfold Wasm_int.Int32.max_unsigned in Hv ; rewrite - Heqx in Hv ; lia.
  simpl.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  done.
  unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
  done.
  done.
  iIntros (w) "[[[-> H1] H2] Hf]".
  iSimpl.
  instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗
                                     ( ⌜(two16 | v)%Z⌝ ∗ ⌜(S (length s) < two14)%Z⌝ ∗ N.of_nat n ↦[i32][ Z.to_N v] Wasm_int.Int32.repr (v + 4 + S (length s) * 4) ∗
         (∃ bs : seq.seq byte, ⌜Z.of_nat (length bs) = (two16 - 4 - S (length s) * 4)%Z⌝ ∗
            N.of_nat n↦[wms][Z.to_N (v + 4 + S (length s) * 4)]bs) ∗
         ([∗ list] k↦y0 ∈ s', N.of_nat n
                              ↦[i32][ Z.to_N
                                        (v + 4 + S (length s) * 4 - 4 - 4 * S (j + k))] y0) ∗
         ([∗ list] k↦y0 ∈ ys, N.of_nat n
                                       ↦[i32][ Z.to_N (v + 4 + S (length s) * 4 - 4 - 4 * k)] y0))
                                     ∗ N.of_nat n↦[wms][Wasm_int.N_of_uint i32m
                            (Wasm_int.Int32.repr (v + 4 + (length (v0 :: s) - S j) * 4)) +
                                                          N.zero]bits (VAL_int32 y)
                                     ∗ ↪[frame] {|
                    f_locs :=
                      set_nth
                        (VAL_int32
                           (Wasm_int.Int32.repr (v + 4)))
                        (set_nth
                           (VAL_int32
                              (Wasm_int.Int32.repr (v + 4 + length (v0 :: s) * 4)))
                           (f_locs f0) 3
                           (VAL_int32
                              (Wasm_int.Int32.repr (v + 4 + length (v0 :: s) * 4)))) 2
                        (VAL_int32
                           (Wasm_int.Int32.repr (v + 4 + (length (v0 :: s) - S j) * 4)));
                    f_inst := f_inst f0
                                     |})%I).
  iFrame.
  done.
  by iIntros "!> [% _]".
  iIntros (w) "(-> & (Hdiv & Hlen & Hv & Hbs & Hs' & Hs) & H & Hf)".
  iSimpl.
  rewrite (separate4 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  rewrite (separate3 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply (wp_get_local with "[] [$Hf]") => /=.
  destruct (f_locs f0) ; inversion Hlocs0.
  simpl. done.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate5 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "HΦ Hf Htab Hcl".
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r ; iSplitL.
  unfold take ; fold (take (A := value)).
  rewrite Htail.
  iDestruct (stackAll_app with "HΦ") as "(HΦ & Hy & _)".
  rewrite (separate1 _ [_;AI_basic (BI_call_indirect 1)]).
  rewrite - (app_nil_r [_ ; AI_basic (BI_call_indirect 1)]).
  iApply wp_wasm_empty_ctx.
  iApply wp_base_push ; first done.
  iApply (wp_call_indirect_success_ctx with "Htab Hcl Hf").
  simpl.
  unfold cl_type.
  rewrite Hclt.
  done.
  simpl.
  done.
  iIntros "!> (Htab & Hcl & Hf)".
  iApply wp_base_pull.
  iApply wp_wasm_empty_ctx.
  simpl.
  iApply ("Hspec" with "[Hy Hf Htab Hcl]").
  iFrame.
  iPureIntro => //=.
  iIntros (w) "(H & Hf & ?)".
  iDestruct "H" as (v1) "[-> Hv1]".
  instantiate (1 := λ x, ((∃ v1, ⌜ x = immV _ ⌝ ∗ stackAll ys Φ ∗ Ψ y v1 ∗
                         N.of_nat j0↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))]
                         Some a ∗
                         N.of_nat a↦[wf]cl)∗ ↪[frame] _)%I) ;
    iFrame.
  iExists  _; by iFrame.
  iIntros (w) "[H Hf]".
  iDestruct "H" as (v1) "[-> H]".
  iSimpl.
  instantiate (1 := λ x, (∃ v1, ⌜ x = immV _ ⌝ ∗ stackAll ys Φ ∗ Ψ y v1 ∗
                                           N.of_nat j0↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))]
                                            Some a ∗ N.of_nat a↦[wf]cl
                                           ∗ ↪[frame] _)%I).
  iExists _ ; by iFrame.
  iIntros "!> H".
  by iDestruct "H" as (v1) "[% _]".
  iIntros (w) "Hf".
  iDestruct "Hf" as (v1) "(-> & HΦ & Hv1 & Htab & Hcl & Hf)".
  iSimpl.
  rewrite (separate4 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf H".
  rewrite (separate1 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_app ; first done.
  iSplitR ; last first.
  iApply wp_wand_r.
  iSplitL.
  iApply wp_store ; last first.
  simpl.
  iFrame.
  iNext.
  by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
  done.
  done.
  done.
  iIntros (w) "[[-> H] Hf]".
  iSimpl.
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ N.of_nat n↦[wms][ _ ] _ ∗ ↪[frame] _)%I) ;
  iFrame.
  by iIntros "!> [% _]".
  iIntros (w) "(-> & H & Hf)".
  iSimpl.
  rewrite (separate3 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_binop with "Hf").
  done.
  by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (AI_basic (BI_const (VAL_int32 (Wasm_int.Int32.iadd _ _))))).
  iApply wp_seq_ctx.
  iSplitR ; last first.
  iSplitL "Hf".
  iApply (wp_set_local with "[] [$Hf]") => /=.
  destruct (f_locs f0) ; first done.
  destruct l ; first done.
  destruct l ; first by simpl in Hlocs ; lia.
  destruct l ; first by simpl in Hlocs ; lia.
  simpl.
  lia.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  simpl.
  rewrite set_nth_write.
  all : try by iIntros "[% _]".
  all : try by iIntros "Habs" ; iDestruct "Habs" as (?) "[% _]".
  rewrite - (app_nil_l [AI_basic (BI_br 0)]).
  iApply (wp_br_ctx_nested with "Hf").
  lia.
  done.
  instantiate (1 := LH_rec [] 0 [] (LH_base [] []) []) => //=.
  done.
  done.
  iIntros "!> Hf".
  iSimpl.
  rewrite - (app_nil_l [AI_basic (BI_loop _ _)]).
  iApply (wp_loop_ctx with "Hf") => //.
  iIntros "!> Hf".
  simpl.
  rewrite - (cat0s (AI_basic (BI_get_local 2) :: _)).
  rewrite - (cats0 [AI_basic _;_;_;_;_;_;_;_;_;_;_;_;_;_;_]). 
  iApply wp_label_push ; first done.
  iApply ("IHj" with "[] [] [Hf] [Hv Hbs Hs' Hs H Hlen Hdiv] [HΦ] [HΨ Hv1] Htab Hcl").
  iPureIntro.
  lia.
  instantiate (1 := v1 :: s').
  iPureIntro.
  simpl.
  rewrite Hs' => //=.
  lia.
  unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
  rewrite Wasm_int.Int32.unsigned_repr.
  rewrite Wasm_int.Int32.unsigned_repr.
  remember (length s) as x. rewrite - Heqx.
  replace (v + 4 + (S x - S j) * 4 + 4)%Z
    with (v + 4 + (S x - j) * 4)%Z.
  iExact "Hf".
  lia.
  lia.
  lia.
  unfold isStack.
  iFrame.
  iDestruct "Hlen" as "%".
  iSplit ; first iPureIntro.
  rewrite app_length.
  rewrite firstn_length.
  replace (j `min` length (v0 :: s)) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  lia.
  iSplitL "Hv".
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x. rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  rewrite - Heqx.
  replace (j + S (x - j)) with (S (x)) ; last lia.
  iExact "Hv".
  iSplitR "Hbs".
  iApply big_sepL_app.
  iSplitL "Hs".
  replace j with (j `min` S j) ; last lia.
  rewrite - take_take.
  simpl.
  rewrite Htail.
  replace j with (length ys).
  rewrite take_app.
  iApply (big_sepL_impl with "Hs").
  iIntros "!>" (k x) "% H".
  remember (length s) as z ; rewrite - Heqz.
  replace (S z) with (length (ys ++ v1 :: s')) ; first done.
  rewrite app_length.
  simpl.
  rewrite Hs'.
  simpl.
  rewrite - Heqz.
  remember (length ys) as zz ; rewrite - Heqzz.
  replace zz with j ; first lia.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  subst z. rewrite Hjmin in Hl. rewrite - Heqzz in Hl. lia.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  rewrite Hjmin in Hl.
  remember (length ys) as zz.
  rewrite - Heqzz in Hl.
  lia.
  iSplitL "H".
  iApply i32_wms.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  rewrite N.add_0_r.
  rewrite Nat.add_0_r.
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x ; rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  rewrite Hs'.
  simpl.
  rewrite - Heqx.
  replace (j + S (x - j)) with (S (x)) ; last lia.
  replace (v + 4 + S x *4 - 4 -4 * j)%Z
    with  (v + 4 + ( S x - S j) * 4)%Z ; last lia.
  iExact "H".
  unfold Wasm_int.Int32.max_unsigned in Hv.
  lia.
  iApply (big_sepL_impl with "Hs'").
  iIntros "!>" (k x) "% H".
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as z ; rewrite - Heqz.
  replace (j `min` S z) with j ; last by simpl ; lia.  
  rewrite Hs'.
  simpl.
  rewrite - Heqz.
  replace (j + S (z - j)) with (S z) ; last lia.
  replace (S ( j + k)) with (j + S k) ; last lia.
  iExact "H".
  iDestruct "Hbs" as (bs) "[% H]".
  iExists bs.
  iSplit ; first iPureIntro.
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x ; rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  lia.
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x ; rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  rewrite - Heqx.
  replace (j + S (x - j)) with (S x) ; last lia.
  iExact "H".
  replace j with (j `min` S j) ; last lia.
  rewrite - take_take.
  simpl.
  rewrite Htail.
  replace j with (length ys).
  rewrite take_app.
  done.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  rewrite Hjmin in Hl.
  remember (length ys) as zz ; rewrite - Heqzz in Hl ;
    lia.
  rewrite - (take_drop j s).
  rewrite app_comm_cons.
  rewrite Htail.
  rewrite take_drop.
  rewrite drop_app_le.
  replace j with (length ys).
  rewrite drop_app.
  simpl.
  iFrame.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
   rewrite Hjmin in Hl.
  remember (length ys) as zz ; rewrite - Heqzz in Hl ;
    lia.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  rewrite app_length.
  rewrite - Hl.
  lia.
  iExact "HΞ". }
  iApply ("H" with "[] [] [Hf] [Hn Hs] [HΦ] [] Htab Hcl").
  instantiate (1 := length s).
  iPureIntro ; lia.
  instantiate (1 := []).
  iPureIntro ; simpl ; lia.
  rewrite Z.sub_diag.
  rewrite Z.mul_0_l.
  rewrite Z.add_0_r.
  done.
  iDestruct "Hs" as "(% & % & Hs & Hbs)".
  iSplit ; first done.
  iSplit ; first iPureIntro.
  rewrite cats0 firstn_length.
  rewrite Nat.min_id.
  exact H0.
  iSplitL "Hn".
  iApply i32_wms.
  rewrite N.add_0_r.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  rewrite cats0 firstn_length.
  rewrite Nat.min_id.
  done.
  unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
  iSplitL "Hs".
  rewrite cats0 firstn_length.
  rewrite firstn_all.
  rewrite Nat.min_id.
  done.
  rewrite cats0 firstn_length.
  rewrite Nat.min_id.
  done.
  rewrite firstn_all.
  done.
  rewrite drop_all.
  done.
  done.
  all : try by iIntros "[% _]".
  by iIntros "[[[% _] _] _]".
Qed.



Lemma spec_stack_map_trap `{!logrel_na_invs Σ} (f0 : frame) (n : immediate) (f : i32) (v : Z) (s : seq.seq i32) E
      j0 a cl γ 
      (Φ : i32 -> iPropI Σ) (Ψ : i32 -> i32 -> iPropI Σ) :
  ↑γ ⊆ E ->
  ⊢ {{{  ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝  ∗
            ⌜ f0.(f_locs) !! 0 = Some (VAL_int32 f) ⌝  ∗
            ⌜ f0.(f_locs) !! 1 = Some (value_of_int v) ⌝ ∗
            ⌜ length f0.(f_locs) >= 4 ⌝ ∗
            ⌜ (0 <= v)%Z ⌝ ∗                                   
            ⌜ (v + 4 + length s * 4 ≤ Wasm_int.Int32.max_unsigned)%Z ⌝ ∗
            isStack v s n ∗
            stackAll s Φ ∗
            ⌜ f0.(f_inst).(inst_types) !! 1 = Some (Tf [T_i32] [T_i32]) ⌝ ∗

            ⌜ f0.(f_inst).(inst_tab) !! 0 = Some j0 ⌝ ∗
            (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
            na_inv logrel_nais γ ((N.of_nat a) ↦[wf] cl) ∗
             ⌜ match cl with FC_func_native _ t _ _ => t | FC_func_host t _ => t end 
          = Tf [T_i32] [T_i32] ⌝ ∗  
            (∀ (u : i32) (fc : frame),
                {{{ Φ u ∗
                      ⌜ f_inst f0 = f_inst fc ⌝ ∗
                       ↪[frame] fc ∗
                       na_own logrel_nais ⊤
                  }}}
                  [ AI_basic (BI_const (VAL_int32 u)) ;
                    AI_invoke a ] @ E
                  {{{ w, (⌜ w = trapV ⌝ ∨ ((∃ v, ⌜ w = immV [VAL_int32 v] ⌝ ∗ Ψ u v)))
                           ∗ na_own logrel_nais ⊤ ∗ ↪[frame] fc}}}) ∗
            na_own logrel_nais ⊤ ∗ ↪[frame] f0 }}}
    to_e_list stack_map @ E
    {{{ w, (⌜ w = trapV ⌝ ∨ (⌜ w = immV [] ⌝ ∗
                                        (∃ s', isStack v s' n ∗ stackAll2 s s' Ψ)))
             ∗ (N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a)
             ∗ (∃ f1, ↪[frame] f1 ∗ na_own logrel_nais ⊤ ∗ ⌜ f_inst f0 = f_inst f1 ⌝ )
    }}}.
Proof.
  intros Hsub.
  iIntros "!>" (Ξ) "(%Hinstmem & %Hlocs0 & %Hlocs1 & %Hlocs & %Hvb & %Hv & Hs & HΦ & %Htypes & %Htab & Htab & #Hcl & %Hcl & #Hspec & Hinv & Hf) HΞ" => /=.
  rewrite separate4.
  iApply wp_seq.
  instantiate (1 := λ x,  (⌜ x = immV [] ⌝ ∗ isStack v s n ∗ ↪[frame] f0)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hs Hf"; first by iApply (is_stack_valid with "[$Hs $Hf]").
  iIntros (w) "(-> & Hs & Hf)".
  simpl.
  iApply wp_wand_r.
  iSplitR "HΞ" ; last first.
  iIntros (w) "H".
  iApply "HΞ".
  iExact "H".
  iApply wp_wasm_empty_ctx.
  rewrite (separate1 (AI_basic _)).
  iApply wp_seq_can_trap_ctx.
  iSplitR; last first.
  iFrame "Hf".
  iSplitR; last first.
  iSplitR "Hs HΦ".
  iIntros "Hf".
  iApply wp_wand_r. iSplitL "Hf". iApply wp_get_local => //.
  instantiate (1 := λ x, ⌜x = immV [value_of_int v]⌝%I) => //.
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iExists f0 ; iFrame.
  iCombine "Htab Hinv" as "H".
  instantiate (1 := λ x, (⌜ x = f0 ⌝ ∗ _)%I).
  iSplit ; first done. iExact "H". 
  iIntros (w f2) "(-> & Hf & [-> HΦf])".
  iSimpl.
  rewrite (separate2 (AI_basic _)).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first. 
  iFrame "Hf".
  iSplitR ; last first.
  iSplitL "Hs HΦf".
  iIntros "Hf". iApply wp_wand_r. iSplitR "HΦf". iApply wp_load => // ; last first.
  unfold isStack.
  iDestruct "Hs" as "(% & % & Hn & ?)".
  iDestruct (i32_wms with "Hn") as "Hn".
  rewrite N.add_0_r.
  simpl.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  unfold bits.
  instantiate (1 := VAL_int32 _) => /=.
  iFrame.
  iNext.
  instantiate ( 1 := λ x, (⌜ x = immV [value_of_int (v + 4 + length s * 4)] ⌝ ∗
                                     ⌜(two16 | v)%Z⌝ ∗
                                     ⌜(length s < two14)%Z⌝ ∗
                                     ([∗ list] i↦w ∈ s, N.of_nat n ↦[i32][ Z.to_N (v + 4 + length s * 4 - 4 - 4 * i)] w) ∗
      (∃ bs : seq.seq byte, ⌜Z.of_nat (length bs) = (two16 - 4 - length s * 4)%Z⌝ ∗
                                                                              N.of_nat n↦[wms][Z.to_N (v + 4 + length s * 4)]bs))%I).
  iFrame.
  done.
  unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
  done.
  iIntros (w) "[[[-> Hs] Hn] Hf]".
  iSplitR "Hf HΦf". iRight. instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _ ∗ _)%I).
  iSplitR ; first done. iSplitL "Hs". iExact "Hs". iExact "Hn".
  iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = f0 ⌝ ∗ _ )%I).
  iSplit ; first done. iExact "HΦf".
  iIntros (w f1) "((-> & H & Hn) & Hf & [-> HΦf])".
  iSimpl. rewrite (separate2 (AI_basic _)).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf". iSplitR ; last first.
  iSplitL "HΦf".
  iIntros "Hf".
  iApply wp_wand_r ; iSplitL "Hf". iApply wp_set_local => //.
  by instantiate (1 := λ x, ⌜x = immV []⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
  iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := f_inst f0 |} ⌝∗ _)%I).
  iSplit ; first done. iExact "HΦf".
  iIntros (w f1) "(-> & Hf & [-> HΦf])". iSimpl.
  rewrite (separate1 (AI_basic _)).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf". iSplitR ; last first.
  iSplitL "HΦf". 
  iIntros "Hf". iApply wp_wand_r. iSplitL "Hf".
  iApply (wp_get_local with "[] [$Hf]") => //=.
  unfold set_nth.
  destruct (f_locs f0) ; first by inversion Hlocs0.
  destruct l ; first by inversion Hlocs1.
  simpl in Hlocs1.
  inversion Hlocs1 ; subst.
  done.
  by instantiate (1 := λ x, ⌜x = immV [value_of_int v]⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝ ∗ _)%I).
  iSplit ; first done. iExact "HΦf".
  iIntros (w f1) "(-> & Hf & [-> HΦf])". iSimpl.
  rewrite (separate3 (AI_basic _)).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf".
  iSplitR ; last first.
  iSplitL "HΦf".
  iIntros "Hf". iApply wp_wand_r ; iSplitL "Hf".
  iApply (wp_binop with "Hf") => //.
  by instantiate (1 := λ x, ⌜ x = immV [_] ⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight.
  by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := _ |}⌝ ∗ _)%I).
  iSplit ; first done. iExact "HΦf". iIntros (w f1) "(-> & Hf & [-> HΦf])". iSimpl.
  rewrite (separate2 (AI_basic _)).
  iApply wp_seq_can_trap_ctx. 
  iSplitR ; last first.
  iFrame "Hf".
  iSplitR ; last first.
  iSplitL "HΦf".
  iIntros "Hf". iApply wp_wand_r ; iSplitL "Hf".
  iApply wp_set_local => //=.
  simpl.
  rewrite length_is_size size_set_nth.
  rewrite length_is_size in Hlocs.
  unfold ssrnat.maxn.
  destruct (ssrnat.leq _ _) ; lia.
  by instantiate (1 := λ x, ⌜x = immV []⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
  iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝∗ _)%I).
  iSplit ; first done. iExact "HΦf".
  iIntros (w f1) "(-> & Hf & [-> HΦf])". simpl.
  rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
  iApply (wp_block_ctx with "Hf") => //.
  iIntros "!> Hf".
  iSimpl.
  rewrite - (cat0s [AI_basic (BI_loop _ _)]) - (cats0 [AI_basic (BI_loop _ _)]).
  iApply wp_label_push ; first done.
  rewrite - (app_nil_l [AI_basic (BI_loop _ _)]).
  iApply (wp_loop_ctx with "Hf") => //.
  iIntros "!> Hf".
  simpl.
  rewrite - (cat0s (AI_basic (BI_get_local 2) :: _)).
  rewrite - (cats0 [AI_basic _;_;_;_;_;_;_;_;_;_;_;_;_;_;_]). 
  iApply wp_label_push ; first done.
  unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
  rewrite Wasm_int.Int32.unsigned_repr ; last lia.
  rewrite Wasm_int.Int32.unsigned_repr ; last by unfold Wasm_int.Int32.max_unsigned,
      Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
  iAssert (∀ (j :nat) s', ⌜ j <= length s ⌝ -∗ ⌜ length s' = length s - j ⌝ -∗ ↪[frame] {|
                    f_locs :=
                      set_nth (VAL_int32 (Wasm_int.Int32.repr (v + 4 )))
                        (set_nth
                           (VAL_int32 (Wasm_int.Int32.repr (v + 4 + length s * 4)))
                           (f_locs f0) 3
                           (VAL_int32 (Wasm_int.Int32.repr (v + 4 + length s * 4)))) 2
                        (VAL_int32 (Wasm_int.Int32.repr (v + 4 + (length s - j%Z) * 4)));
                    f_inst := f_inst f0
                    |} -∗
                    isStack v (take j s ++ s') n -∗ 
                    stackAll (take j s) Φ -∗
                    stackAll2 (drop j s) s' Ψ -∗
                    na_own logrel_nais ⊤ -∗
                    N.of_nat j0 ↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))]Some a -∗
                    WP [AI_basic (BI_get_local 2); AI_basic (BI_get_local 3);
     AI_basic (BI_relop T_i32 (Relop_i (ROI_ge SX_U))); AI_basic (BI_br_if 1);
     AI_basic (BI_get_local 2); AI_basic (BI_get_local 2); AI_basic (BI_get_local 2);
     AI_basic (BI_load T_i32 None N.zero N.zero); AI_basic (BI_get_local 0);
     AI_basic (BI_call_indirect 1); AI_basic (BI_store T_i32 None N.zero N.zero);
     AI_basic (i32const 4); AI_basic (BI_binop T_i32 (Binop_i BOI_add));
     AI_basic (BI_set_local 2); AI_basic (BI_br 0)] @  E
  CTX
  2;
  push_base (LH_rec [] 0 [] (LH_base [] []) []) 0
    [AI_basic
       (BI_loop (Tf [] [])
          [BI_get_local 2; BI_get_local 3; BI_relop T_i32 (Relop_i (ROI_ge SX_U));
          BI_br_if 1; BI_get_local 2; BI_get_local 2; BI_get_local 2;
          BI_load T_i32 None N.zero N.zero; BI_get_local 0; 
          BI_call_indirect 1; BI_store T_i32 None N.zero N.zero; 
          i32const 4; BI_binop T_i32 (Binop_i BOI_add); BI_set_local 2; 
          BI_br 0])] [] []
    {{ v0, (⌜v0 = trapV⌝ ∨ ⌜v0 = immV []⌝ ∗
      (∃ s' : seq.seq Wasm_int.Int32.T, isStack v s' n ∗ stackAll2 s s' Ψ)) ∗
     N.of_nat j0↦[wt][N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned f))]
     Some a ∗
     (∃ f1 : frame,  ↪[frame]f1 ∗ na_own logrel_nais ⊤ ∗ ⌜f_inst f0 = f_inst f1⌝)  }})%I as "Hloop".
  { iIntros (j).
    iInduction j as [|j] "IHj".
    { iIntros (s') "%Hj %Hs' Hf Hs HΦ HΨ Hown Htab".
      rewrite (separate1 (AI_basic (BI_get_local 2))).
      iApply wp_seq_can_trap_ctx. 
      iSplitR ; last first.
      iFrame "Hf".
      iSplitR ; last first.
      iSplitL "Htab Hcl Hown".
      iIntros "Hf".
      iApply wp_wand_r ; iSplitL "Hf".
      iApply (wp_get_local with "[] [$Hf]").
      simpl. by rewrite set_nth_read.
      by instantiate ( 1 := λ x, ⌜x = immV _⌝%I).
      iIntros (w) "[-> Hf]".
      iSplitR. iRight.
      by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
      iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝ ∗ _)%I).
      iSplit ; first done. iCombine "Htab Hown" as "H". iExact "H".
      iIntros (w f1) "(-> & Hf & [-> HΦf])". iSimpl.
      rewrite (separate2 _ (AI_basic (BI_get_local 3))).
      iApply wp_seq_can_trap_ctx.
      iSplitR ; last first.
      iFrame "Hf".
      iSplitR ; last first.
      iSplitL "HΦf".
      iIntros "Hf". rewrite (separate1 _ [AI_basic (BI_get_local 3)]).
      iApply wp_val_can_trap => //.
      iSplitR ; last first.
      iFrame "Hf". iIntros "Hf".
      iApply wp_wand_r.
      iSplitL "Hf".
      iApply (wp_get_local with "[] [$Hf]").
      simpl.
      destruct (f_locs f0) ; first by inversion Hlocs.
      destruct l ; first by inversion Hlocs1.
      destruct l ; first by simpl in Hlocs ; lia.
      simpl.
      by rewrite set_nth_read.
      by instantiate (1 := λ x, ⌜x = immV _⌝%I).
      iIntros (w) "[-> Hf]".
      iSplitR. iRight.
      by instantiate (1 := λ x, ⌜ x = immV _⌝%I).
      iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝ ∗ _)%I).
      iSplit ; first done. iExact "HΦf".
      by iIntros "%".
      iIntros (w f1) "(-> & Hf & [-> HΦf])". rewrite Z.sub_0_r.
      iSimpl.
      rewrite (separate3 _ _ (AI_basic (BI_relop _ _))).
      iApply wp_seq_can_trap_ctx.
      iSplitR ; last first.
      iFrame "Hf". iSplitR ; last first.
      iSplitL "HΦf".
      iIntros "Hf".
      iApply wp_wand_r ; iSplitL "Hf".
      iApply (wp_relop with "Hf").
      simpl.
      unfold Wasm_int.Int32.ltu.
      rewrite Wasm_int.Int32.unsigned_repr.
      rewrite Coqlib.zlt_false.
      simpl.
      done.
      lia.
      split ; try lia.
      exact Hv.
      by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
      iIntros (w) "[-> Hf]".
      iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
      iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝ ∗ _)%I).
      iSplit ; first done. iExact "HΦf".
      iIntros (w f1) "(-> & Hf & (-> & Htab & Hown))". iSimpl.
      rewrite - (app_nil_l (AI_basic (i32const 1) :: _)).
      rewrite (separate2 _ (AI_basic (BI_br_if 1))).
      iApply wp_base_push ; first done.
      iApply (wp_br_if_true_ctx with "Hf").
      done.
      iIntros "!> Hf".
      rewrite - (app_nil_l [AI_basic (BI_br 1)]).
      iApply (wp_br_ctx with "Hf") => //.
      iIntros "!> Hf".
      iApply wp_value.
      unfold IntoVal.
      by apply of_to_val.
      (*      iApply "HΞ". *)
      iFrame. iSplitR "Hf". iRight. iSplit ; first done.
      iExists s'.
      unfold take.
      unfold drop.
      iFrame.
      iExists _.
      iFrame.
      done.
      all : try by iIntros (f1) "(Hf & -> & Htab & Hown)" ; 
      iFrame ; iSplitR ; [by iLeft | by iExists _ ; iFrame]. 
      all : try by iIntros "%".
    }
  iIntros (s') "%Hj %Hs' Hf Hs HΦ HΨ Hown Htab".
  destruct s as [|v0 s]; first by inversion Hj.
  cut (exists ys y, v0 :: take j s = ys ++ [y]) ;
  [ intro Htail ; destruct Htail as (ys & y & Htail) |
    exists (removelast (v0 :: take j s)) ;
    exists (List.last (v0 :: take j s) (Wasm_int.Int32.repr 1)) ;
    apply app_removelast_last ;
    apply not_eq_sym ; apply nil_cons ].
  simpl in Hv.
  simpl in Hj.
  assert (j `min` length s = j) as Hjmin.
  { remember (length s) as x. rewrite - Heqx in Hj.
    lia. } 
  rewrite (separate1 (AI_basic (BI_get_local 2))).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf". iSplitR ; last first.
  iSplitL "Hcl Htab Hown".
  iIntros "Hf". 
  iApply wp_wand_r. iSplitL "Hf". iApply (wp_get_local with "[] [$Hf]").
  simpl. by rewrite set_nth_read.
  by instantiate ( 1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝ ∗ _)%I).
  iSplit ; first done. iCombine "Htab Hown" as "H". iExact "H".
  iIntros (w f1) "(-> & Hf & -> & HΦf)". iSimpl.
  rewrite (separate2 _ (AI_basic (BI_get_local 3))).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf". iSplitR ; last first.
  iSplitL "HΦf".
  rewrite (separate1 _ [AI_basic (BI_get_local 3)]).
  iIntros "Hf". iApply wp_val_can_trap => //.
  iSplitR ; last first.
  iFrame "Hf". iIntros "Hf".
  iApply wp_wand_r.
  iSplitL "Hf".
  iApply (wp_get_local with "[] [$Hf]").
  simpl.
  destruct (f_locs f0) ; first by inversion Hlocs.
  destruct l ; first by inversion Hlocs1.
  destruct l ; first by simpl in Hlocs ; lia.
  simpl.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate ( 1 := λ x, ⌜ x = immV _ ⌝%I).
  iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝ ∗ _ )%I).
  iSplit ; first done. iExact "HΦf".
  by iIntros "%".
  iIntros (w f1) "(-> & Hf & -> & HΦf)". iSimpl.
  rewrite (separate3 _ _ (AI_basic (BI_relop _ _))).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf". iSplitR ; last first.
  iSplitL "HΦf".
  iIntros "Hf". iApply wp_wand_r. iSplitL "Hf".
  iApply (wp_relop with "Hf").
  simpl.
  unfold Wasm_int.Int32.ltu.
  rewrite Wasm_int.Int32.unsigned_repr.
  rewrite Wasm_int.Int32.unsigned_repr.
  rewrite Coqlib.zlt_true.
  simpl.
  done.
  lia.
  lia.
  lia.
  by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝ ∗ _)%I).
  iSplit ; first done. iExact "HΦf".
  iIntros (w f1) "(-> & Hf & -> & HΦf)". iSimpl.
  rewrite (separate2 (AI_basic (BI_const (VAL_int32 _)))).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf". iSplitR ; last first.
  iSplitL "HΦf".
  iIntros "Hf". iApply wp_wand_r ; iSplitL "Hf".
  iApply (wp_br_if_false with "Hf").
  done.
  iNext.
  by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
  iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝ ∗ _ )%I).
  iSplit ; first done. iExact "HΦf".
  iIntros (w f1) "(-> & Hf & -> & HΦf)". iSimpl.
  rewrite (separate1 (AI_basic (BI_get_local 2)) [_;_;_;_;_;_;_;_;_;_]).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf". iSplitR ; last first.
  iSplitL "HΦf".
  iIntros "Hf". 
  iApply wp_wand_r ; iSplitL "Hf".
  iApply (wp_get_local with "[] [$Hf]") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_inst := _ ; f_locs := _ |} ⌝ ∗ _)%I).
  iSplit ; first done. iExact "HΦf".
  iIntros (w f1) "(-> & Hf & -> & HΦf)". iSimpl.
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf". iSplitR ; last first.
  iSplitL "HΦf".
  iIntros "Hf".
  rewrite (separate1 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_can_trap. 
  iSplitR ; last first.
  iFrame "Hf". iIntros "Hf". iApply wp_wand_r.
  iSplitL "Hf".
  iApply (wp_get_local with "[] [$Hf]") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝ ∗ _)%I).
  iSplit ; first done. iExact "HΦf".
  by iIntros "%".
  iIntros (w f1) "(-> & Hf & -> & HΦf)". iSimpl.
  rewrite (separate3 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf". iSplitR ; last first.
  iSplitL "HΦf". iIntros "Hf".
  rewrite (separate2 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_val_can_trap.
  iSplitR ; last first.
  iFrame "Hf". iIntros "Hf".
  iApply wp_wand_r.
  iSplitL.
  iApply wp_val_can_trap.
  iSplitR ; last first.
  iFrame "Hf". iIntros "Hf".
  iApply wp_wand_r.
  iSplitL "Hf". iApply (wp_get_local with "[] [$Hf]") => /=.
  by rewrite set_nth_read.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_inst := _ ; f_locs := _ |} ⌝ ∗ _)%I).
  iSplit ; first done. iExact "HΦf".
  by iIntros "%".
  iIntros (w) "[[-> | ->] Hf]".
  iSplitR. by iLeft. iExact "Hf".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iExact "Hf".
  by iIntros "%".
  iIntros (w f1) "(-> & Hf & -> & HΦf)". iSimpl.
  rewrite (separate4 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf". iSplitR ; last first.
  iSplitL "HΦf Hs".
  iIntros "Hf".
  iApply wp_val_can_trap.
  iSplitR ; last first.
  iFrame "Hf". iIntros "Hf". 
  iApply wp_wand_r ; iSplitL. iApply wp_val_can_trap.
  iSplitR ; last first.
  iFrame "Hf". iIntros "Hf". iApply wp_wand_r.
  iSplitR "HΦf".
  iApply wp_load ; last first.
  iFrame.
  unfold isStack.
  iDestruct "Hs" as "(Hdiv & Hlen & Hn & Hl & Hbs)".
  rewrite cat_app.
  iDestruct (big_sepL_app with "Hl") as "[Hs Hs']".
  rewrite app_length.
  rewrite Hs'.
  rewrite take_length.
  replace (S j `min` length (v0 :: s)) with (S j) ; last by simpl ; lia.
  unfold take ; fold (take (A := value)).
  rewrite Htail.
  iDestruct (big_sepL_app with "Hs") as "[Hs H]".
  iDestruct "H" as "[H _]".
  iDestruct (i32_wms with "H") as "H" => //.
  rewrite Nat.add_0_r.
  rewrite N.add_0_r.
  replace (Wasm_int.N_of_uint i32m (Wasm_int.Int32.repr (v + 4 + (S (length s) - S j) * 4)))
    with (Z.to_N (v + 4 + (S (length s) - S j) * 4)).
  replace (S j + (length (v0 :: s) - S j)) with (length (v0 :: s)) ; last by simpl ; lia.
  replace (v + 4 + length (v0 :: s) * 4 - 4 - 4 * length ys)%Z
    with (v + 4 + length (v0 :: s) * 4 - S (length ys) * 4)%Z ; last lia.
  replace (S (length ys)) with (length (ys ++ [y])) ;
    last by rewrite app_length ; simpl ; lia.
  rewrite (cat_app ys [y]).
  rewrite - Htail.
  simpl.
  rewrite firstn_length.
  rewrite Hjmin.
  rewrite (Z.mul_sub_distr_r (S (length s)) (S j) 4).
  simpl in Hj.
  remember (length s) as x.
  rewrite - Heqx.
  replace (v + 4 + S x * 4 - S j * 4)%Z
    with (v + 4 + (S x * 4 - S j * 4))%Z ;
    last lia.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq Z.mod_small.
  instantiate (1 := VAL_int32 _).
  iSplitR "H" ; last iExact "H".
  iNext.
  subst x.
  instantiate ( 1 := λ x, (⌜ x = immV [VAL_int32 y] ⌝ ∗ ⌜ (two16 | v)%Z ⌝ ∗ ⌜ (S (length s) < two14)%Z ⌝ ∗ N.of_nat n ↦[i32][ Z.to_N v] Wasm_int.Int32.repr (v + 4 + S (length s) * 4) ∗  (∃ bs : seq.seq byte, ⌜ Z.of_nat (length bs) = (two16 - 4 - S (length s) * 4)%Z⌝ ∗
            N.of_nat n↦[wms][Z.to_N (v + 4 + S (length s) * 4)]bs) ∗ ([∗ list] k↦y0 ∈ s', N.of_nat n
                              ↦[i32][ Z.to_N
                                        (v + 4 + S (length s) * 4 - 4 - 4 * S (j + k))] y0) ∗ [∗ list] k↦y0 ∈ ys, N.of_nat n
                             ↦[i32][ Z.to_N (v + 4 + S (length s) * 4 - 4 - 4 * k)] y0)%I).
  iFrame.
  done.
  simpl.
  unfold Wasm_int.Int32.max_unsigned in Hv ; rewrite - Heqx in Hv ; lia.
  simpl.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  done.
  unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
  done.
  done.
  iIntros (w) "[[[-> H1] H2] Hf]".
  iSplitR "Hf HΦf". 
  iRight. iSimpl.
  instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗
                                     ( ⌜(two16 | v)%Z⌝ ∗ ⌜(S (length s) < two14)%Z⌝ ∗ N.of_nat n ↦[i32][ Z.to_N v] Wasm_int.Int32.repr (v + 4 + S (length s) * 4) ∗
         (∃ bs : seq.seq byte, ⌜Z.of_nat (length bs) = (two16 - 4 - S (length s) * 4)%Z⌝ ∗
            N.of_nat n↦[wms][Z.to_N (v + 4 + S (length s) * 4)]bs) ∗
         ([∗ list] k↦y0 ∈ s', N.of_nat n
                              ↦[i32][ Z.to_N
                                        (v + 4 + S (length s) * 4 - 4 - 4 * S (j + k))] y0) ∗
         ([∗ list] k↦y0 ∈ ys, N.of_nat n
                                       ↦[i32][ Z.to_N (v + 4 + S (length s) * 4 - 4 - 4 * k)] y0))
                                     ∗ N.of_nat n↦[wms][Wasm_int.N_of_uint i32m
                            (Wasm_int.Int32.repr (v + 4 + (length (v0 :: s) - S j) * 4)) +
                                                          N.zero]bits (VAL_int32 y)
                                 )%I).
  iFrame.
  done.
  iExists _ ; iFrame.
  instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝ ∗ _)%I).
  iSplit ; first done. iExact "HΦf".
  by iIntros "[% _]".
  iIntros (w) "[[ -> | [-> H]] Hf]".
  iSplitR. by iLeft. iExact "Hf".
  iSplitL "H". iRight. instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
  iSplit ; first done. iExact "H".
  iExact "Hf".
  by iIntros "[% _]".
  iIntros (w f1) 
          "((-> & (Hdiv & Hlen & Hv & Hbs & Hs' & Hs) & H) & Hf & -> & HΦf)".
  iSimpl.
  rewrite (separate4 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf". iSplitR ; last first.
  iSplitL "HΦf". iIntros "Hf". 
  iApply wp_val_can_trap.
  iSplitR ; last first.
  iFrame "Hf". iIntros "Hf".
  iApply wp_wand_r. iSplitL.
  iApply wp_val_can_trap.
  iSplitR ; last first.
  iFrame "Hf". iIntros "Hf".
  iApply wp_wand_r. iSplitL.
  iApply wp_val_can_trap.
  iSplitR ; last first.
  iFrame "Hf".
  iIntros "Hf".
  iApply wp_wand_r.
  iSplitL "Hf".
  iApply (wp_get_local with "[] [$Hf]") => /=.
  destruct (f_locs f0) ; inversion Hlocs0.
  simpl. done.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝ ∗ _)%I).
  iSplit ; first done. iExact "HΦf".
  by iIntros "%".
  iIntros (w) "[[-> | ->] Hf]".
  iSplitR. by iLeft. iExact "Hf".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iExact "Hf".
  by iIntros "%".
  iIntros (w) "[[ -> | ->] Hf]".
  iSplitR. by iLeft. iExact "Hf".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iExact "Hf".
  by iIntros "%".
  iIntros (w f1) "(-> & Hf & -> & Htab & Hown)". iSimpl.
  rewrite (separate5 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf". iSplitR ; last first.
  iSplitL "HΦ Htab Hown".
  iIntros "Hf". 
  iApply wp_val_can_trap.
  iSplitR ; last first.
  iFrame "Hf". iIntros "Hf".
  iApply wp_wand_r. iSplitL.
  iApply wp_val_can_trap.
  iSplitR ; last first.
  iFrame "Hf". iIntros "Hf".
  iApply wp_wand_r ; iSplitL.
  unfold take ; fold (take (A := value)).
  rewrite Htail.
  iDestruct (stackAll_app with "HΦ") as "(HΦ & Hy & _)".
  rewrite (separate1 _ [_;AI_basic (BI_call_indirect 1)]).
  rewrite - (app_nil_r [_ ; AI_basic (BI_call_indirect 1)]).
  iApply fupd_wp. iMod (na_inv_acc with "Hcl Hown") as "(>Ha & Hown & Hcls)";[auto|solve_ndisj|].
  iApply wp_wasm_empty_ctx.
  iApply wp_base_push ; first done.
  iApply (wp_call_indirect_success_ctx with "Htab Ha Hf").
  simpl.
  unfold cl_type.
  rewrite Hcl.
  done.
  simpl.
  done. iModIntro.
  iIntros "!> (Htab & Ha & Hf)".
  iApply wp_base_pull.
  iApply wp_wasm_empty_ctx.
  iApply fupd_wp. iMod ("Hcls" with "[$]") as "Hown". simpl.
  iApply ("Hspec" with "[Hy Hf Hown]").
  iFrame.
  iPureIntro => //=.
  iModIntro. iIntros (w) "H".
  iCombine "HΦ Htab H" as "H".
  iExact "H".
  iIntros (w) "(HΦ & Htab & H & Hown & Hf)".
  iDestruct "H" as "[-> | H]".
  iSplitL "HΦ". by iLeft.
  iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := _ |}⌝ ∗ _)%I).
  iSplit ; first done. iCombine "Htab Hown" as "H".
  iExact "H".
  iSplitL "HΦ H". iRight. instantiate (1 := λ x, (∃ v1, ⌜ x = immV _ ⌝ ∗ stackAll ys Φ ∗ Ψ y v1)%I).
  iDestruct "H" as (v1) "[-> H]".
  iSimpl.
  iExists _ ; by iFrame.
  iExists _ ; iFrame. done.
  by iIntros "H" ; iDestruct "H" as (v1) "[% _]".
  iIntros (w) "[[-> | H] Hf]".
  iSplitR. by iLeft. iExact "Hf".
  iSplitR "Hf". iRight.
  iDestruct "H" as (v1) "[-> H]".
  instantiate (1 := λ x, (∃ v1, ⌜ x = immV _ ⌝ ∗ _)%I).
  iExists _. iSplit ; first done. iExact "H".
  iExact "Hf".
  by iIntros "H" ; iDestruct "H" as (v1) "[% _]".
  iIntros (w f1) "(H' & Hf & -> & HΦf)". 
  iDestruct "H'" as (v1) "(-> & HΦ & Hv1)".
  iSimpl.
  rewrite (separate4 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf". iSplitR ; last first.
  iSplitL "HΦf H".
  iIntros "Hf". 
  iApply wp_val_can_trap.
  iSplitR ; last first.
  iFrame "Hf". iIntros "Hf". iApply wp_wand_r.
  iSplitR "HΦf".
  iApply wp_store ; last first.
  simpl.
  iFrame.
  iNext.
  by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
  done.
  done.
  done.
  iIntros (w) "[[-> H] Hf]".
  iSplitL "H". iRight. 
  by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ N.of_nat n↦[wms][ _ ] _)%I) ;
  iFrame.
  iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝ ∗ _)%I).
  iSplit ; first done. iExact "HΦf".
  by iIntros "[% _]".
  iIntros (w f1) "([-> H] & Hf & -> & HΦf)".
  iSimpl.
  rewrite (separate3 (AI_basic (i32const (v + 4 + _ * 4)))).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf". iSplitR ; last first.
  iSplitL "HΦf". iIntros "Hf". 
  iApply wp_wand_r. iSplitL "Hf". iApply (wp_binop with "Hf").
  done.
  by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝ ∗ _)%I).
  iSplit ; first done. iExact "HΦf".
  iIntros (w f1) "(-> & Hf & -> & HΦf)". iSimpl.
  rewrite (separate2 (AI_basic (BI_const (VAL_int32 (Wasm_int.Int32.iadd _ _))))).
  iApply wp_seq_can_trap_ctx.
  iSplitR ; last first.
  iFrame "Hf". iSplitR ; last first.
  iSplitL "HΦf". iIntros "Hf". 
  iApply wp_wand_r. iSplitL "Hf".
  iApply (wp_set_local with "[] [$Hf]") => /=.
  destruct (f_locs f0) ; first done.
  destruct l ; first done.
  destruct l ; first by simpl in Hlocs ; lia.
  destruct l ; first by simpl in Hlocs ; lia.
  simpl.
  lia.
  by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iIntros (w) "[-> Hf]".
  iSplitR. iRight. by instantiate (1 := λ x, ⌜x = immV _⌝%I).
  iExists _ ; iFrame. instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst := _ |} ⌝ ∗ _)%I).
  iSplit ; first done. iExact "HΦf".
  iIntros (w f1) "(-> & Hf & -> & Htab & Hown)". simpl.
  rewrite set_nth_write.
  all : try by iIntros (f1) "(Hf & -> & Htab & Hown)" ; 
    iFrame ; iSplitR ; [by iLeft | by iExists _ ; iFrame]. 
  all : try by iIntros "%".
  all : try by iIntros "[% _]".
  all : try by iIntros "H" ; iDestruct "H" as (v1) "[% _]".
  rewrite - (app_nil_l [AI_basic (BI_br 0)]).
  iApply (wp_br_ctx_nested with "Hf").
  lia.
  done.
  instantiate (1 := LH_rec [] 0 [] (LH_base [] []) []) => //=.
  done.
  done.
  iIntros "!> Hf".
  iSimpl.
  rewrite - (app_nil_l [AI_basic (BI_loop _ _)]).
  iApply (wp_loop_ctx with "Hf") => //.
  iIntros "!> Hf".
  simpl.
  rewrite - (cat0s (AI_basic (BI_get_local 2) :: _)).
  rewrite - (cats0 [AI_basic _;_;_;_;_;_;_;_;_;_;_;_;_;_;_]). 
  iApply wp_label_push ; first done.
  iApply ("IHj" with "[] [] [Hf] [Hv Hbs Hs' Hs H Hlen Hdiv] [HΦ] [HΨ Hv1] Hown Htab").
  iPureIntro.
  lia.
  instantiate (1 := v1 :: s').
  iPureIntro.
  simpl.
  rewrite Hs' => //=.
  lia.
  unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
  rewrite Wasm_int.Int32.unsigned_repr.
  rewrite Wasm_int.Int32.unsigned_repr.
  remember (length s) as x. rewrite - Heqx.
  replace (v + 4 + (S x - S j) * 4 + 4)%Z
    with (v + 4 + (S x - j) * 4)%Z.
  iExact "Hf".
  lia.
  lia.
  lia.
  unfold isStack.
  iFrame.
  iDestruct "Hlen" as "%".
  iSplit ; first iPureIntro.
  rewrite app_length.
  rewrite firstn_length.
  replace (j `min` length (v0 :: s)) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  lia.
  iSplitL "Hv".
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x. rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  rewrite - Heqx.
  replace (j + S (x - j)) with (S (x)) ; last lia.
  iExact "Hv".
  iSplitR "Hbs".
  iApply big_sepL_app.
  iSplitL "Hs".
  replace j with (j `min` S j) ; last lia.
  rewrite - take_take.
  simpl.
  rewrite Htail.
  replace j with (length ys).
  rewrite take_app.
  iApply (big_sepL_impl with "Hs").
  iIntros "!>" (k x) "% H".
  remember (length s) as z ; rewrite - Heqz.
  replace (S z) with (length (ys ++ v1 :: s')) ; first done.
  rewrite app_length.
  simpl.
  rewrite Hs'.
  simpl.
  rewrite - Heqz.
  remember (length ys) as zz ; rewrite - Heqzz.
  replace zz with j ; first lia.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  subst z. rewrite Hjmin in Hl. rewrite - Heqzz in Hl. lia.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  rewrite Hjmin in Hl.
  remember (length ys) as zz.
  rewrite - Heqzz in Hl.
  lia.
  iSplitL "H".
  iApply i32_wms.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  rewrite N.add_0_r.
  rewrite Nat.add_0_r.
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x ; rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  rewrite Hs'.
  simpl.
  rewrite - Heqx.
  replace (j + S (x - j)) with (S (x)) ; last lia.
  replace (v + 4 + S x *4 - 4 -4 * j)%Z
    with  (v + 4 + ( S x - S j) * 4)%Z ; last lia.
  iExact "H".
  unfold Wasm_int.Int32.max_unsigned in Hv.
  lia.
  iApply (big_sepL_impl with "Hs'").
  iIntros "!>" (k x) "% H".
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as z ; rewrite - Heqz.
  replace (j `min` S z) with j ; last by simpl ; lia.  
  rewrite Hs'.
  simpl.
  rewrite - Heqz.
  replace (j + S (z - j)) with (S z) ; last lia.
  replace (S ( j + k)) with (j + S k) ; last lia.
  iExact "H".
  iDestruct "Hbs" as (bs) "[% H]".
  iExists bs.
  iSplit ; first iPureIntro.
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x ; rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  lia.
  rewrite app_length.
  rewrite firstn_length.
  simpl.
  remember (length s) as x ; rewrite - Heqx.
  replace (j `min` S x) with j ; last by simpl ; lia.
  simpl.
  rewrite Hs'.
  simpl.
  rewrite - Heqx.
  replace (j + S (x - j)) with (S x) ; last lia.
  iExact "H".
  replace j with (j `min` S j) ; last lia.
  rewrite - take_take.
  simpl.
  rewrite Htail.
  replace j with (length ys).
  rewrite take_app.
  done.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  rewrite Hjmin in Hl.
  remember (length ys) as zz ; rewrite - Heqzz in Hl ;
    lia.
  rewrite - (take_drop j s).
  rewrite app_comm_cons.
  rewrite Htail.
  rewrite take_drop.
  rewrite drop_app_le.
  replace j with (length ys).
  rewrite drop_app.
  simpl.
  iFrame.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  rewrite Hjmin in Hl.
  remember (length ys) as zz ; rewrite - Heqzz in Hl ;
    lia.
  specialize (f_equal length Htail) as Hl.
  simpl in Hl.
  rewrite app_length in Hl ; simpl in Hl.
  rewrite firstn_length in Hl.
  rewrite app_length.
  rewrite - Hl.
  lia. }
  iDestruct "HΦf" as "(Htab & Hown)".
  iApply ("Hloop" with "[] [] [Hf] [Hn H] [HΦ] [] Hown Htab").
  instantiate (1 := length s).
  iPureIntro ; lia.
  instantiate (1 := []).
  iPureIntro ; simpl ; lia.
  rewrite Z.sub_diag.
  rewrite Z.mul_0_l.
  rewrite Z.add_0_r.
  done.
  iDestruct "H" as "(% & % & Hs & Hbs)".
  iSplit ; first done.
  iSplit ; first iPureIntro.
  rewrite cats0 firstn_length.
  rewrite Nat.min_id.
  exact H0.
  iSplitL "Hn".
  iApply i32_wms.
  rewrite N.add_0_r.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite Z.mod_small.
  rewrite cats0 firstn_length.
  rewrite Nat.min_id.
  done.
  unfold Wasm_int.Int32.max_unsigned in Hv ; lia.
  iSplitL "Hs".
  rewrite cats0 firstn_length.
  rewrite firstn_all.
  rewrite Nat.min_id.
  done.
  rewrite cats0 firstn_length.
  rewrite Nat.min_id.
  done.
  rewrite firstn_all.
  done.
  rewrite drop_all.
  done.
  all : try by iIntros (f1) "(Hf & -> & Htab & Hown)" ; 
    iFrame ; iSplitR ; [by iLeft | by iExists _ ; iFrame]. 
  all : try by iIntros "%".
  by iIntros "[% _]".
Qed. 

End specs.


End stack.    
      
