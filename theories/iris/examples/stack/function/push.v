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
    
    Lemma spec_push_op f0 n (v: N) (a : i32) s E :
      ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝
          ∗ ⌜ f0.(f_locs) !! 0 = Some (value_of_uint v) ⌝
          ∗ ⌜ f0.(f_locs) !! 1 = Some (VAL_int32 a) ⌝ 
          ∗ ⌜ length f0.(f_locs) >= 3 ⌝
          ∗ ⌜ (N.of_nat (length s) < two14 - 1)%N ⌝
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
           iIntros (w) "H".
           by iApply "H".
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
      
      instantiate (1 := λ x, (⌜ x = immV [value_of_uint v] ⌝ ∗ ↪[frame] f0)%I).
      iSplitR ; first by iIntros "[%Habs _]".
      iSplitL "Hf".
      - iApply (wp_get_local with "[] [$Hf]") => //=.
      - iIntros (w) "[-> Hf]".
        simpl.
        rewrite separate2.
        iApply wp_seq.
        instantiate ( 1 := λ x, ((⌜ x = immV [ value_of_uint (v + N.of_nat (length s) * 4)%N] ⌝ ∗ isStack v s n ∗ ↪[frame] f0)%I)).
        iSplitR ; first by iIntros "(%Habs & _)".
        iSplitR "HΦ".
        { by iApply (stack_load_0 with "[] [$] [$]") => //. }

      - iIntros (w) "(-> & Hstack & Hf)" => /=.
        rewrite separate3.
        iApply (wp_seq _ _ _ (λ x, (⌜ x = immV [value_of_uint (v + 4 + N.of_nat (length s) * 4)] ⌝
                                            ∗ ↪[frame] _)%I)).
        iSplitR ; first by iIntros "[%Habs _]".
        iSplitL "Hf".
        iApply (wp_binop with "Hf") => //.
        iIntros "!>".
        iPureIntro.
        unfold value_of_int, value_of_uint => /=.
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
        instantiate (1 := λ w, (⌜ w = immV [value_of_uint (v + 4 + N.of_nat (length s) * 4)] ⌝ ∗ ↪[frame] _) %I).
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

        remember {| f_locs := set_nth (value_of_uint (v + 4 + N.of_nat (length s) * 4))
                                (f_locs f0) 2 (value_of_uint (v + 4 + N.of_nat (length s) * 4)) ;
                   f_inst := f_inst f0 |} as f1.
        rewrite - Heqf1.
        rewrite separate2.
        iApply wp_seq.
        instantiate (1 := λ x, (⌜ x = immV [value_of_uint (v + 4 + N.of_nat (length s) * 4) ;
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
        instantiate (1 := λ x, (⌜ x = immV [] ⌝ ∗ (N.of_nat n
        ↦[i32][ v] Wasm_int.Int32.repr (Z.of_N (v + N.of_nat (length s) * 4)) ∗
        (([∗ list] i↦w ∈ s, N.of_nat n
                            ↦[i32][ v + N.of_nat (length s) * 4 -
                                    4 * N.of_nat i] w) ∗
         (∃ bs, ⌜ N.of_nat (length bs) = (two16 - 4 - N.of_nat (length s) * 4 - 4)%N ⌝ ∗ [∗ list] k↦y ∈ bs, N.of_nat n↦[wm][N.of_nat
                                               (N.to_nat
                                                  (v + N.of_nat (length s) * 4 +
                                                  4) +
                                                (4 + k))]y)) ∗
        N.of_nat n↦[wms][Wasm_int.N_of_uint i32m
                           (Wasm_int.int_of_Z i32m
                              (Z.of_N (v + 4 + N.of_nat (length s) * 4))) + N.zero]
        bits (VAL_int32 a) ∗  ↪[frame]f1))%I).
        iSplitR ; first by iIntros " [%Habs _]".
        iDestruct "Hstack" as "(_ & _ & _ & Hp & Hs & Hrest)".
        iDestruct "Hrest" as (bs) "[%Hbs Hrest]".
        unfold two16 in Hbs.
        unfold two14 in Hlens.
        remember (length s) as x.
        rewrite - Heqx.
        assert ((65536-4-N.of_nat x * 4)%N >= 4)%N as Hlen; first lia.
        do 4 (destruct bs; first by exfalso; rewrite - Hbs in Hlen; lias).
        rewrite separate4.
        unfold mem_block_at_pos at 1.
        rewrite big_sepL_app.
        iDestruct "Hrest" as "[Ha Hrest]".
        iSplitR "HΦ".
      - iApply wp_wand_r. iSplitL. iApply wp_store ; last first.
        iFrame.
        iSplitR "Ha".
        iNext.
        subst x.
        iCombine "Hp Hs Hrest" as "H".
        instantiate (1 := λ x, (⌜ x = immV [] ⌝ ∗ _)%I).
        iSplit => //.
        by iApply "H".
        3: instantiate (1 := [b ; b0 ; b1 ; b2]) => //. 
        3: done.
        2: subst f1 => //.
        iApply (big_sepL_impl with "Ha").
        iIntros "!>" (k y) "% H".
        rewrite of_nat_to_nat_plus.
        simpl.
        rewrite Wasm_int.Int32.Z_mod_modulus_eq Z.mod_small; last first.
        { unfold ffff0000 in Hvb; rewrite u32_modulus; lia. }
        rewrite of_nat_to_nat_plus N2Z.id N.add_0_r.
        iApply (points_to_wm_eq with "H") => //; lia.

      - iIntros (w) "(((-> & (H0 & H1 & H1')) & H2) & H3)".
        iSplit => //.
        rewrite - Heqx.
        iFrame.
        iExists bs.
        iSplit; last by iFrame.
        unfold two16.
        repeat rewrite cons_length in Hbs.
        remember (length bs) as x'.
        iPureIntro.
        lia.
        
      - iIntros (w) "(-> & H)".
        iDestruct "H" as "(Hp & (Hs & Hrest) & Ha & Hf)".
        iSimpl.
        rewrite (separate1 (AI_basic _)).
        iApply wp_seq.
        instantiate (1 := λ x, ( ⌜ x = immV [value_of_uint v] ⌝ ∗ ↪[frame]f1)%I).
        iSplitR ; first by iIntros "[%Habs _]".
        iSplitL "Hf".
      - iApply (wp_get_local with "[] [$Hf]") => //.
        subst f1 => //.
        rewrite - fmap_insert_set_nth; last by lias.
        by rewrite list_lookup_insert_ne => //.
          
      - iIntros (w) "[-> Hf]".
        iSimpl.
        rewrite separate2.
        iApply wp_seq.
        instantiate (1 := λ x, ( ⌜ x = immV [value_of_uint v ;
                                             value_of_uint ( v + 4 + N.of_nat (length s) * 4 ) ] ⌝
                                         ∗ ↪[frame] f1)%I).
        iSplitR ; first by iIntros "[%Habs _]".
        iSplitL "Hf".
      - rewrite separate1.
        iApply wp_val_app => //.
        iSplitR ; first by iIntros "!> [%Habs _]".
        iApply (wp_get_local with "[] [$Hf]") => //.
        subst f1 => //.
        rewrite set_nth_read => //=.
        by subst x.
          
      - iIntros (w) "[-> Hf]".
        iSimpl.
        iApply wp_wand_r.
        iSplitL "Hf Hp".
      - iApply wp_store.
        done.
        instantiate (1 := bits (value_of_uint (v + N.of_nat (length s) * 4))) => //=.
        instantiate (2 := f1).
        subst f1 => //.
        instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
        iFrame.
        iSplit => //=.
        rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        rewrite Z.mod_small ; last by unfold ffff0000 in Hvb ; rewrite u32_modulus; lia.
        iDestruct (i32_wms with "Hp") as "Hp" => //.
        rewrite N.add_0_r N2Z.id.
        by subst x.
      - iIntros (w) "[[-> Hp] Hf]".
        iApply "HΦ".
        iSplit => //.
        unfold isStack.
        iSplitR "Hf"; last by iExists f1; subst f1; iFrame.
        repeat iSplit => //.
        iPureIntro=> /= ; rewrite - Heqx ; clear Heqx s ; unfold two14 ; lia.
        iSplitL "Hp".
        simpl.
        rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        rewrite Z.mod_small ; last by unfold ffff0000 in Hvb ; rewrite u32_modulus; lia.
        iApply i32_wms => //.
        rewrite N.add_0_r N2Z.id.
        rewrite -Heqx.
        iApply (points_to_wms_eq with "Hp") => //; do 3 f_equal; lia.
        
        iSplitR "Hrest".
        iSplitL "Ha".
        iApply i32_wms => //=.
        rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        rewrite Z.mod_small ; last by unfold ffff0000 in Hvb ; rewrite u32_modulus; lia.
        rewrite N.add_0_r N.sub_0_r N2Z.id.
        rewrite - Heqx.
        iApply (points_to_wms_eq with "Ha") => //; lia.
        
        iApply (big_sepL_impl with "Hs").
        iIntros "!>" (k y) "%Hbits H".
        iApply (points_to_i32_eq with "H") => //.
        rewrite cons_length - Heqx.
        lia.
        
        iDestruct "Hrest" as (bs0) "(%Hbslen & Hrest)".
        iExists bs0.
        iSplit => //.
        iPureIntro.
        rewrite cons_length.
        repeat rewrite cons_length in Hbs.
        rewrite - Heqx.
        lias.
        rewrite cons_length -Heqx.
        unfold mem_block_at_pos.
        iApply (big_sepL_impl with "Hrest").
        iIntros "!>" (k y) "%Hl Hy".
        do 2 rewrite of_nat_to_nat_plus.
        iApply (points_to_wm_eq with "Hy") => //; lia.
    Qed.

    Lemma spec_push f0 n (v: N) (a : i32) s E :
      ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝
          ∗ ⌜ f0.(f_locs) !! 0 = Some (value_of_uint v) ⌝
          ∗ ⌜ f0.(f_locs) !! 1 = Some (VAL_int32 a) ⌝ 
          ∗ ⌜ length f0.(f_locs) >= 3 ⌝
         ∗ ⌜ (N.of_nat (length s) < two14 - 1)%N ⌝
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

    Lemma valid_push m t funcs :
    let i0 := {| inst_types := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
                     inst_funcs := funcs;
                     inst_tab := [t];
                     inst_memory := [m];
                     inst_globs := []
              |} in
    na_inv logrel_nais stkN (stackModuleInv (λ (a : N) (b : seq.seq i32), isStack a b m) (λ n : nat, N.of_nat m↦[wmlength]N.of_nat n)) -∗
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
    pose proof (value_of_uint_repr z0) as [v ->]. iSimpl in "Hf".
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
      iApply fupd_wp.
      iMod (na_inv_acc with "Hstk Hown") as "(>Hstkres & Hown & Hcls)";[solve_ndisj..|].
      iModIntro.
      iDestruct "Hstkres" as (l Hmul) "[Hlen Hstkres]".
      iDestruct "Hstkres" as (l' Hmultiple) "Hl'".
      match goal with | |- context [ (WP ?e @ _; _ {{ _ }} )%I ] => set (e0:=e) end.
      match goal with | |- context [ (↪[frame] ?f0)%I ] => set (f':=f0) end.
      match goal with | |- context [ (?P ={⊤}=∗ ?Q)%I ] => set (CLS:=(P ={⊤}=∗ Q)%I) end.
      
      set (k:=Wasm_int.N_of_uint i32m ((Wasm_int.int_of_Z i32m (Z.of_N v)))).
      destruct (decide (k < N.of_nat l)%N).
      + apply div_mod_i32 in Hdiv as Hdiv'.
        eapply multiples_upto_in in Hmultiple as Hin;[..|apply Hdiv'];[|lia].
        apply elem_of_list_lookup_1 in Hin as [i Hi].
        iDestruct (big_sepL_lookup_acc with "Hl'") as "[Hv Hl']";[eauto|].
        iDestruct "Hv" as (stk) "Hv".
        iApply (wp_seq _ _ _ (λ v, ⌜v = immV []⌝ ∗ _)%I).
        iSplitR;[by iIntros "[%Hcontr _]"|].
        iSplitL "Hf Hv".
        { iApply is_stack_bound_valid. iFrame "Hf Hv". iSplit;auto.
          iPureIntro. subst f'. simpl. unfold value_of_uint.
          f_equal. f_equal. apply int_of_Z_mod. }
        iIntros (w) "(-> & Hstack & Hf) /=".
        destruct (decide (N.of_nat (length stk) < two14 - 1)%N).
        * iApply (spec_push_op with "[$Hstack $Hf]").
          { repeat iSplit;auto. subst f';simpl. iPureIntro.
            unfold value_of_uint. f_equal. f_equal. apply int_of_Z_mod. }
          iIntros (w) "[-> [Hstack Hf]]".
          iDestruct "Hf" as (f1) "[Hf %Hfeq]".
          iDestruct ("Hl'" with "[Hstack]") as "Hl'".
          { iExists _. iFrame. }
          deconstruct_ctx.
          iApply fupd_wp.
          iMod ("Hcls" with "[Hlen Hl' $Hown]") as "Hown".
          { iExists _. iFrame. iNext. iSplit;auto. }
          iModIntro.
          iApply (wp_wand _ _ _ (λ v, ⌜v = immV []⌝ ∗ _)%I with "[Hf]").
          iApply (wp_label_value with "Hf");eauto.
          iIntros (v0) "[-> Hf]".
          iExists _. iFrame.
          iIntros "Hf".
          iApply (wp_frame_value with "Hf");eauto.
          iNext. iLeft. iRight. iExists []. simpl. done.
        * iDestruct (stack_pure with "Hstack") as "(_ & _ & %Hstkbound & Hstack)".
          take_drop_app_rewrite (length (is_full_op)).
          iApply wp_seq.
          iSplitR;[|iSplitL "Hf Hstack"];cycle 1.
          { iApply (spec_is_full_op with "[$Hf $Hstack]").
            - repeat iSplit;auto.
              iPureIntro. subst f';simpl. unfold value_of_uint.
              f_equal. f_equal. apply int_of_Z_mod.
            - iIntros (w) "H". iExact "H". }
          2: iIntros "H";by iDestruct "H" as (? ?) "_".
          iIntros (w) "H".
          iDestruct "H" as (k0) "(-> & Hstack & [[-> %Hcond]|[-> %Hcond]] & Hf)";[|lia].
          simpl.
          iDestruct ("Hl'" with "[Hstack]") as "Hl'".
          { iExists _. iFrame. }
          iApply fupd_wp.
          iMod ("Hcls" with "[Hlen Hl' $Hown]") as "Hown".
          { iExists _. iFrame. iNext. iSplit;auto. }
          iModIntro.
          take_drop_app_rewrite 2.
          iApply (wp_wand _ _ _ (λ v, ⌜v = trapV⌝ ∗ _)%I with "[Hf]").
          iApply wp_seq_trap. iFrame.
          iIntros "Hf". iApply (wp_if_true with "[$]");auto.
          iNext. iIntros "Hf".
          take_drop_app_rewrite 0.
          iApply (wp_block with "[$]");auto.
          iNext. iIntros "Hf".
          build_ctx [AI_basic BI_unreachable].
          take_drop_app_rewrite 1.
          iApply wp_seq_trap_ctx. iFrame. iIntros "Hf".
          iApply (wp_unreachable with "[$]"). auto.
          iIntros (v') "[-> Hf]".
          deconstruct_ctx.
          iApply (wp_wand _ _ _ (λ v, ⌜v = trapV⌝ ∗ _)%I with "[Hf]").
          iApply (wp_label_trap with "[$]");eauto.
          iIntros (v0) "[-> Hf]".
          iExists _. iFrame. iIntros "Hf".
          iApply (wp_frame_trap with "[$]").
          iNext. iLeft. iLeft. auto.          
      + iApply (wp_wand with "[Hlen Hf]").
        iApply (fail_stack_bound_valid with "[$Hlen $Hf]").
        eauto.
        iIntros (v0) "(-> & Hlen & Hf)".
        deconstruct_ctx.
        iApply fupd_wp.
        iMod ("Hcls" with "[$Hown Hl' Hlen]") as "Hown".
        { iNext. iExists _. iFrame. auto. }
        iModIntro.
        iApply (wp_wand _ _ _ (λ v, ⌜v = trapV⌝ ∗ _)%I with "[Hf]").
        iApply (wp_label_trap with "Hf");eauto.
        iIntros (v0) "[-> Hf]".
        iExists _. iFrame. iIntros "Hf".
        iApply (wp_frame_trap with "[$]").
        iNext. iLeft. iLeft. auto.
    - iIntros "[%Hcontr _]";done.
  Qed.
    
  End valid.

End stack.    

