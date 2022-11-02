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

(*
  new_stack: [] -> [i32]
  locals declared: [i32]

  Attempts to create a new stack of i32s, at the end of memory 0 by allocating a new page of memory.

  Can fail non-deterministically if grow_memory fails.
  Upon successful grow_memory, store a pointer to the top element of the stack at the start of stack (0th cell).
  The maximum number of elements that can be stored is therefore 2^14-1.

  Returns the pointer to the start of stack as i32, or -1 if memory allocation fails. Cannot trap.

  Parameters/Locals:
  0     local variable, storing the address to the start of the page for return
*)
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
        BI_store T_i32 None N.zero N.zero ;
        BI_get_local 0 
      ]                             
  ].

End code.

Section specs.

Lemma spec_new_stack f0 n len E: 
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ length (f_locs f0) >= 1 ⌝ ∗
        ⌜ (page_size | len)%N ⌝ ∗
        ↪[frame] f0 ∗
        N.of_nat n ↦[wmlength] len }}}
    to_e_list new_stack @ E
    {{{ v , ((⌜ v = immV [value_of_int (-1)%Z] ⌝ ∗
              N.of_nat n↦[wmlength] len) ∨
             (⌜ v = immV [value_of_uint len]⌝ ∗
                   isStack len [] n ∗
                   N.of_nat n ↦[wmlength] (len + page_size)%N)) ∗
            ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f1 = f_inst f0 ⌝ }}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hflocs & %Hlendiv & Hframe & Hlen) HΦ".
  assert (page_size | len)%N as Hlenmod => //=.
  apply divide_and_multiply in Hlenmod => //=.
  rewrite separate2.
  iApply wp_seq => /=.
  iDestruct (wp_grow_memory with "[$Hframe $Hlen]") as "HWP" => //.
  { iSplitL; by instantiate (1 := λ v, ⌜ v = immV _ ⌝%I ). }
  iSplitR; last iSplitL "HWP".
  2: { by iApply "HWP". }
  { iIntros "[[((%Habs & _ & _) & _) | (%Habs & _)] Hf]" ; by inversion Habs. }
  - iIntros (w) "(H & Hf)".
    unfold of_val.
    destruct w ; try by iDestruct "H" as "[[[%Habs _] _ ]| [%Habs _]]" ; inversion Habs.
    destruct l ; try by iDestruct "H" as "[[[%Habs _] _ ]| [%Habs _]]" ; inversion Habs.
    destruct l ; try by iDestruct "H" as "[[[%Habs _] _ ]| [%Habs _]]" ; inversion Habs.
    rewrite - separate1.
    rewrite separate2.
    iApply (wp_seq _ E _ (λ x, (⌜ x = immV [v] ⌝
                                      ∗ ↪[frame] {|
                                            f_locs := set_nth v (f_locs f0) 0 v;
                                            f_inst := f_inst f0
                                      |} )%I) ).
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
    instantiate (1 := (λ x, (⌜ if v == value_of_int (-1) then
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
  (* If *)
  - iIntros (w) "[%Hw Hf]".
    destruct w ; try by destruct (v == value_of_int (-1)).
    destruct l ; first by destruct (v == value_of_int (-1)).
    destruct l ; last by destruct (v == value_of_int (-1)).
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
      iDestruct "H" as "[((%Hm1 & Hb & Hlen) & %Hbound) | [_ Hlen]]".
      inversion Hm1.
      exfalso.
      unfold mem_in_bound in Hbound.
      simpl in Hbound.
      unfold page_limit in Hbound.
      remember (len `div` page_size)%N as pagenum.
      assert (pagenum <= 65535)%N as Hbound'; first by lias.
      clear - H0 Hbound'.
      rewrite Wasm_int.Int32.Z_mod_modulus_eq in H0.
      rewrite u32_modulus in H0.
      rewrite nat_bin in H0.
      rewrite Zmod_small in H0; last first.
      split; try by lias.
      lia.
      iSplitR "Hf";eauto.
    + (* grow_memory succeeded *)
      inversion Hw ; subst v0.
      iApply (wp_if_false with "Hf"). done.
      iIntros "!> Hf".
      rewrite - (app_nil_l [AI_basic (BI_block _ _)]).

      iDestruct "H" as "[ ((%Hvv & Hb & Hlen) & %Hbound) | [%Hvv Hlen]]" ; inversion Hvv ; subst ;
        last by rewrite eq_refl in Hv ; inversion Hv.
      (* len bound *)
      assert (len `div` page_size <= 65535)%N as Hpagebound.
      { unfold mem_in_bound, page_limit in Hbound.
        simpl in Hbound.
        by lias.
      }
      assert (len <= ffff0000)%N as Hlenbound.
      { rewrite <- Hlenmod.
        remember (len `div` page_size)%N as pagenum.
        replace page_size with 65536%N => //.
        unfold ffff0000.
        by lias.
      }
      unfold page_size at 3.
      replace (N.to_nat (_ * (64 * 1024))) with (4 + N.to_nat (65532)) ; last done.
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
      instantiate (1 := λ x, ((⌜ x = immV [value_of_uint len] ⌝ ∗ N.of_nat n↦[i32][ len ] (Wasm_int.Int32.repr (Z.of_N len))) ∗ ↪[frame] {| f_locs := set_nth (VAL_int32 c) (f_locs f0) 0 (VAL_int32 (Wasm_int.Int32.imul c (Wasm_int.Int32.repr 65536))); f_inst := f_inst f0 |} )%I).
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
            instantiate (1 := λ x,  ⌜ x = immV _ ⌝%I ) => //=.
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
            instantiate (1 := (λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I)). 
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
        instantiate (1 := (λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I)).
        iSplitL ""; first by iIntros "!> (%HContra & _)" => //.
        iApply (wp_get_local with "[] [$Hf]") => //=.
        rewrite set_nth_read => //=.
        iIntros (w) "[-> Hf]".
        simpl.
        rewrite (separate3 (AI_basic _)).
        iApply wp_seq_ctx; iSplitR; last iSplitL.
        2: { iApply (wp_store with "[Hf Hbs]") => /=.
             { done. }
             { by instantiate (1 := [(#00%byte); (#00%byte); (#00%byte); (#00%byte)]) => //. }
             2: { iFrame "Hf".
                  instantiate (2 := λ x, ⌜x = immV []⌝%I ) => //=.
                  iSplit => //.
                  rewrite N.add_0_r => /=.
                  instantiate (1 := n).
                  iApply (points_to_wms_eq with "Hbs") => //.
                  rewrite Heqc.
                  unfold Wasm_int.Int32.unsigned => /=.
                  do 2 rewrite Wasm_int.Int32.Z_mod_modulus_eq.
                  rewrite u32_modulus nat_bin.
                  unfold mem_in_bound in Hbound.
                  simpl in Hbound.
                  remember (len `div` page_size)%N as pagenum.
                  unfold page_limit in Hbound.
                  assert (pagenum <= 65535)%N; first by lias.
                  rewrite (Zmod_small (N.to_nat pagenum) _); last by lias.
                  rewrite Zmod_small; last by lias.
                  rewrite - Hlenmod.
                  unfold page_size.
                  replace (64*1024)%N with (65536)%N; by lias.
             }
             { done. }
        }
        { by iIntros "((%Hcontra & _)&_)". }
        iIntros (w) "((-> & Hwm) & Hf)".
        iSimpl.
        rewrite - (app_nil_r ([AI_basic _])).
        iApply wp_seq_ctx.
        iSplitL ""; last first.
        iSplitL "Hf".
        iApply (wp_get_local with "[] [$Hf]").
        simpl.
        rewrite set_nth_read.
        done.
        { iModIntro.
          instantiate (1 := λ x, ⌜x = immV [ value_of_uint len ]⌝%I).
          iPureIntro.
          unfold value_of_uint.
          rewrite Heqc.
          unfold Wasm_int.Int32.imul.
          rewrite Wasm_int.Int32.mul_signed => /=.
          repeat f_equal.
          rewrite nat_bin.
          clear - Hlenmod Hpagebound.
          remember (len `div` page_size)%N as pagenum.
          repeat (rewrite wasm_int_signed; last by lias).
          replace page_size with 65536%N in Hlenmod; by lias.
        }
        
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
        { iFrame "Hf".
          iSplit => //=.
          rewrite Wasm_int.Int32.Z_mod_modulus_eq.
          unfold Wasm_int.Int32.imul.
          unfold Wasm_int.Int32.mul.
          rewrite wasm_int_unsigned; last by lias.
          rewrite N.add_0_r.
          rewrite nat_bin in Heqc.
          replace (Z.to_N _) with len; last first.
          { 
            subst c.
            remember (len `div` page_size)%N as pagenum.
            rewrite wasm_int_unsigned; last by lias.
            rewrite - Hlenmod.
            replace (page_size) with (65536)%N; last by lias.
            rewrite Z.mod_small; first by lias.
            split; first by lias.
            rewrite u32_modulus.
            by lias.
          }
          iApply i32_wms.
          subst c.
          remember (len `div` page_size)%N as pagenum.
          rewrite wasm_int_unsigned; last by lias.
          rewrite - Hlenmod.
          replace (page_size) with 65536%N; last by lias.
          repeat rewrite N_nat_Z.
          iApply (points_to_wms_eq with "Hwm") => //.
          repeat f_equal.
          lia.
        }
        all: try by iIntros "(%HContra & _)".
      }
      * iIntros (w) "[[-> Hn] Hf]".
        iApply "HΦ".
        iSplitR "Hf"; last first.
        { iExists _.
          by iSplitL "Hf" => //.
        }
        iRight.
        
        iSplit => //.
        iSplitR "Hlen". 
        unfold isStack.
        iSimpl.
        iSplitR.
        iPureIntro.
        unfold page_size in Hlendiv.
        replace (64 * 1024)%N with 65536%N in Hlendiv ; last done.
        by unfold two16.
        rewrite N.add_0_r.
        iSplitR.
        iPureIntro.
        unfold ffff0000; by lias.
        iSplit => //.
        iSplitL "Hn" => //.
        iSplit => //.
        iExists (repeat #00%byte ( N.to_nat 65532)).
        rewrite repeat_length N2Nat.id.
        iSplit; first done.
        iApply (points_to_wms_eq with "Hb") => //; lia.
        done.
Qed.
        
End specs.

Section valid.
  Context `{!logrel_na_invs Σ}.
  Set Bullet Behavior "Strict Subproofs".

  Lemma interp_value_of_int i :
    ⊢ @interp_value Σ T_i32 (value_of_int i).
  Proof.
    iIntros "". unfold interp_value. simpl.
    iExists _. eauto. Qed.

  Lemma interp_value_of_uint i :
    ⊢ @interp_value Σ T_i32 (value_of_uint i).
  Proof.
    iIntros "". unfold interp_value. simpl.
    iExists _. eauto. Qed.

  Lemma valid_new_stack m t funcs :
    let i0 := {| inst_types := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
                     inst_funcs := funcs;
                     inst_tab := [t];
                     inst_memory := [m];
                     inst_globs := []
              |} in
    na_inv logrel_nais stkN (stackModuleInv (λ (a : N) (b : seq.seq i32), isStack a b m) (λ n : nat, N.of_nat m↦[wmlength]N.of_nat n)) -∗
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
    iDestruct "Hstkres" as (len) "[% [Hlen Hstkres]]".
    iApply (spec_new_stack with "[$Hf $Hlen]") ;[auto|].
    iModIntro.
    iIntros (v) "HH".
    iDestruct "HH" as "[Hcases Hf]".
    iDestruct "Hf" as (f') "[Hf %Hfinst]". simpl in Hfinst.
    iAssert (⌜const_list (iris.of_val v)⌝)%I as %Hval.
    { iDestruct "Hcases" as "[[-> Hm] | [-> [Hs Hm]]]";auto. }
    apply const_list_to_val in Hval as Hvs. destruct Hvs as [vs Hvs].
    rewrite to_of_val in Hvs.
    iAssert (⌜length vs = 1⌝)%I as %Hlenvs.
    { inversion Hvs;subst v.
      iDestruct "Hcases" as "[[%eq1 Hm] | [%eq1 [Hs Hm]]]";inversion eq1;auto. }
    iAssert (interp_values [T_i32] v) as "#Hv".
    { iDestruct "Hcases" as "[[-> Hm] | [-> [Hs Hm]]]"; iSimpl.
      iExists _. iSplit;eauto. iSplit =>//. iApply interp_value_of_int.
      iExists _. iSplit;eauto. iSplit =>//. iApply interp_value_of_uint.
    }
    iApply (wp_val_return with "[$]");auto.
    iIntros "Hf /=".
    iApply wp_value;[rewrite app_nil_r;eapply of_to_val;eauto;eapply to_of_val|].
    iExists _. iFrame. iIntros "Hf".
    
    iApply fupd_wp.
    iMod ("Hcls" with "[$Hown Hcases Hstkres]") as "Hown".
    { iNext.
      iDestruct "Hcases" as "[[Heq Hm] | [% [Hs Hm]]]".
      - iExists _. iFrame. auto.
      - iExists _.
        rewrite <- (N2Nat.id page_size), <- Nat2N.inj_add.
        iFrame "Hm". repeat iSplit.
        + iPureIntro. rewrite N2Nat.id Nat2N.inj_add N2Nat.id.
          apply N.divide_add_r;auto. apply N.divide_refl.
        + iDestruct "Hstkres" as (l Hmul) "Hstkres".
          rewrite N2Nat.id in Hmul. iExists (N.of_nat len :: l).
          iSplit.
          { iPureIntro. rewrite Nat2N.inj_add N2Nat.id. constructor. auto. }
          iSimpl. iFrame. iExists _. iFrame. }
    iModIntro.
    inversion Hvs;subst v.
    iApply (wp_wand _ _ _ (λ v, ⌜v = immV vs⌝ ∗ _)%I with "[Hf]").
    { iApply (wp_frame_value with "[$]");eauto. apply to_of_val. simpl.
      rewrite v_to_e_length. auto. }
    iIntros (v) "[-> Hf]". iFrame.
    iLeft. iRight. iFrame "#". 
  Qed.

End valid.


End stack.    
      
