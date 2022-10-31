From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export stack_common stack_map iris_fundamental proofmode.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

Section stack.

 Context `{!wasmG Σ, logrel_na_invs Σ}. 

Section specs.

Lemma spec_map_loop_body_continue_trap f (s: list i32) (v: N) n E j fn (sv: i32) j0 a cl
  (Φ : i32 -> iPropI Σ) (Ψ: i32 -> i32 -> iPropI Σ) (γ1 : namespace) :
  ↑γ1 ⊆ E ->
  ⊢ {{{ ⌜ f.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ f.(f_locs) !! 0 = Some (value_of_uint v) ⌝ ∗
        ⌜ f.(f_locs) !! 1 = Some (VAL_int32 fn) ⌝  ∗
        ⌜ f.(f_locs) !! 2 = Some (value_of_uint (v + N.of_nat (length s) * 4 - 4 * j - 4)) ⌝ ∗
        ⌜ f.(f_locs) !! 3 = Some (value_of_uint (v + N.of_nat (length s) * 4)) ⌝ ∗
        ⌜ length f.(f_locs) >= 4 ⌝ ∗
        ⌜ (0 <= j < N.of_nat (length s))%N ⌝ ∗
        ⌜ s !! (N.to_nat j) = Some sv ⌝ ∗
        isStack v s n ∗
        Φ sv ∗
            ⌜ f.(f_inst).(inst_types) !! 1 = Some (Tf [T_i32] [T_i32]) ⌝ ∗

            ⌜ f.(f_inst).(inst_tab) !! 0 = Some j0 ⌝ ∗
            na_inv logrel_nais γ1 ((N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m fn) ] a) ∗
            (match a with
             | Some a => ∃ γ2, ⌜↑γ2 ⊆ E ∧ @up_close _ coPset _ γ2 ⊆ ⊤ ∖ ↑γ1⌝ ∗ na_inv logrel_nais γ2 ((N.of_nat a) ↦[wf] cl) ∗
                          ⌜ cl_type cl = Tf [T_i32] [T_i32] ⌝ ∗ 
                                           (∀ (u : i32) (fc : frame),
                                               {{{ Φ u ∗
                                                     ⌜ f_inst f = f_inst fc ⌝ ∗
                                                                    ↪[frame] fc ∗
                                                                    na_own logrel_nais ⊤
                                               }}}
                                                 [ AI_basic (BI_const (VAL_int32 u)) ;
                                                   AI_invoke a ] @ E
                                                 {{{ w, (⌜ w = trapV ⌝ ∨ ((∃ v, ⌜ w = immV [VAL_int32 v] ⌝ ∗ Ψ u v)))
                                                          ∗ na_own logrel_nais ⊤ ∗ ↪[frame] fc}}})
             | None => True
             end) ∗ 
        na_own logrel_nais ⊤ ∗ ↪[frame] f }}}
    to_e_list map_loop_body @ E
    {{{ w, (⌜ w = trapV ⌝ ∨ ⌜ w = brV (VH_base 0 [] []) ⌝ ∗
           (∃ (sv': i32), isStack v (<[N.to_nat j := sv']> s) n ∗ Ψ sv sv')) ∗
             na_own logrel_nais ⊤ ∗
            ↪[frame]
            {| f_locs := <[ 2 := value_of_uint (v + N.of_nat (length s) * 4 - 4 * j) ]> f.(f_locs);
               f_inst := f.(f_inst)
            |}
    }}}.
Proof.
  intros Hsub1.
  iIntros "!>" (Ξ) "(%Hinstmem & %Hlocs0 & %Hlocs1 & %Hlocs2 & %Hlocs3 & %Hlocs & %Hjbound & %Hslookup & Hs & HΦ & %Htypes & %Htab & #Htab & Hcl & Hown & Hf) HΞ" => /=.

  iDestruct (stack_pure with "Hs") as "(%Hdiv & %Hvb & %Hlens & Hs)".

  assert (0 <= j < 16383)%N as Hjb.
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
  instantiate (1 := λ w, (⌜ w = immV [value_of_uint (v + N.of_nat (length s) * 4 - 4 * j - 4); value_of_uint (v + N.of_nat (length s) * 4)] ⌝ ∗ ↪[frame] f)%I).
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
       instantiate (1 := λ w, ⌜ w = immV [value_of_uint (v + N.of_nat (length s) * 4 - 4 * j)]⌝%I) => /=.
       iIntros "!>".
       iPureIntro.
       unfold value_of_uint.
       repeat f_equal.
       unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
       f_equal.
       simpl.
       rewrite Wasm_int.Int32.Z_mod_modulus_eq.
       rewrite Z.mod_small; last first.
       { remember (length s) as x; rewrite - Heqx.
         unfold ffff0000 in Hvb; rewrite u32_modulus; unfold two14 in Hlens.
         lia.
       }
       remember (N.of_nat (length s)) as x; rewrite - Heqx.
       by destruct j => //; lias.
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜ w = immV [value_of_uint (v + N.of_nat (length s) * 4 - 4 * j)] ⌝ ∗ ↪[frame] _)%I).
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
  instantiate (1 := λ w, (⌜ w = immV [value_of_uint (v + N.of_nat (length s) * 4 - 4 * j); value_of_uint (v + N.of_nat (length s) * 4 - 4 * j)] ⌝ ∗ ↪[frame] _)%I).
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
  instantiate (1 := λ w, (⌜ w = immV [value_of_uint (v + N.of_nat (length s) * 4 - 4 * j); VAL_int32 sv] ⌝ ∗ isStack v s n ∗ ↪[frame] _)%I).
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
  instantiate (1 := λ w, (⌜ w = immV [value_of_uint (v + N.of_nat (length s) * 4 - 4 * j); VAL_int32 sv; VAL_int32 fn] ⌝ ∗ ↪[frame] _)%I).
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
  iApply (wp_wand with "[-HΞ] HΞ").
  set (f' := {| f_locs := <[2:=value_of_uint (v + N.of_nat (length s) * 4 - match j with
                                                                          | 0%N => 0
                                                                          | N.pos q => N.pos (4 * q)
                                                                            end)]> (f_locs f); f_inst := f_inst f |}).
  iApply wp_wasm_empty_ctx.  
  iApply wp_seq_can_trap_ctx.
  instantiate (1 := λ f, (⌜ f = f'⌝ ∗ na_own logrel_nais ⊤)%I).
  instantiate (2 := λ w, (∃ v0, ⌜ w = immV [value_of_uint (v + N.of_nat (length s) * 4 - 4 * j); VAL_int32 v0] ⌝ ∗ Ψ sv v0 ∗ isStack v s n)%I).  
  iSplitR; last iSplitR.
  { by iIntros "H"; iDestruct "H" as (v0) "(%Habs & _)". }
  { iIntros (f0) "[Hf [-> Hown]]". subst f'. iFrame. iLeft. done. }
  iFrame "Hf". iSplitL.
  { rewrite (separate1 (AI_basic _)).
    iIntros "Hf".
    iApply wp_val_can_trap_app => //. iFrame "Hf".
    iSplit; first by iIntros "!> H" => /=; iDestruct "H" as (v0) "(%Habs & _)".
    iIntros "Hf".
    iApply fupd_wp.
    iMod (na_inv_acc with "Htab Hown") as "(>Htab' & Hown & Hcls')";[solve_ndisj..|].
    destruct a.
    - iDestruct "Hcl" as (γ2) "(%Hsub & #Hcl & %Hclt & #Hspec)".
      destruct Hsub as [Hsub2 Hdiff].
      iMod (na_inv_acc with "Hcl Hown") as "(>Hcl' & Hown & Hcls)";[auto|solve_ndisj|].      
      iApply (wp_call_indirect_success_ctx with "[$Htab'] [$Hcl'] [$Hf] [HΦ Hs Hcls Hown Hcls']") => /=.
      { by rewrite Hclt. }
      { done. }
      2: { iPureIntro.
           instantiate (1 := (LH_base [AI_basic (BI_const (VAL_int32 sv))] [])).
           instantiate (1 := 0).
           unfold lfilled, lfill.
           simpl.
           by apply/eqP.
      }
      { iIntros "!> (Htab' & Hcl' & Hf)".
        iApply wp_base_pull.
        iApply wp_wasm_empty_ctx.
        iApply fupd_wp.
        iMod ("Hcls" with "[$]") as "Hown".
        iMod ("Hcls'" with "[$]") as "Hown".
        iModIntro.
        iApply ("Hspec" with "[$HΦ $Hown $Hf]"); first done.
        iIntros (w) "(Hret & Hown & Hf)".
        iSplitR "Htab Hf Hown";[|iExists _;iFrame;subst f';simpl;auto].
        iDestruct "Hret" as "[-> | Hret]";auto.
        iDestruct "Hret" as (v0) "(-> & HΨ)".
        iRight. iExists v0.
        iSplit => //. iFrame.
        rewrite - fmap_insert_set_nth;auto.
        lia.
      }
    - take_drop_app_rewrite 1.
      iApply (wp_val_can_trap_app);auto.
      iFrame "Hf".
      iSplitR.
      { simpl. iModIntro. iModIntro. iIntros "HH";iDestruct "HH" as (v0 Hcontr) "_";done. }
      iModIntro. iIntros "Hf".
      iApply wp_fupd.
      iApply (wp_wand _ _ _ (λ v, (⌜v = trapV⌝ ∗ _) ∗ _)%I with "[Hf Htab']").
      iApply (wp_call_indirect_failure_noindex with "Htab' Hf");auto.
      iIntros (v0) "[[-> Htab'] Hf]".
      iMod ("Hcls'" with "[$]") as "Hown". iModIntro.
      iSplitR "Hf Hown";[|iExists _; iFrame;subst f';rewrite - fmap_insert_set_nth;auto;lia].
      iLeft. auto.
  }

  iIntros (w f0) "[H [Hf [-> Hown]]]".
  iDestruct "H" as (v0) "(-> & HΨ & Hs)" => /=.
  deconstruct_ctx.
  iApply (wp_wand _ _ _
            (λ v1, (⌜v1 = brV (VH_base 0 [] [])⌝ ∗ (∃ sv' : Wasm_int.Int32.T, isStack v (<[N.to_nat j:=sv']> s) n ∗ Ψ sv sv')) ∗ _)%I
           with "[-]").
  2: { iIntros (v') "[? HH]". iSplitR "HH"; [|iExact "HH"]. iRight. iFrame. }
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
  iFrame.
  iSplit => //.
  iExists _. iFrame.
Qed.

Lemma spec_map_loop_j_trap f (s: list i32) (v: N) n E j fn j0 a cl
  (Φ : i32 -> iPropI Σ) (Ψ: i32 -> i32 -> iPropI Σ) (s': list i32) γ1 :
  ↑γ1 ⊆ E ->
  ⊢ ( ⌜ f.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ f.(f_locs) !! 0 = Some (value_of_uint v) ⌝ ∗
        ⌜ f.(f_locs) !! 1 = Some (VAL_int32 fn) ⌝  ∗
        ⌜ f.(f_locs) !! 2 = Some (value_of_uint (v + N.of_nat (length s) * 4 - 4 * j)) ⌝ ∗
        ⌜ f.(f_locs) !! 3 = Some (value_of_uint (v + N.of_nat (length s) * 4)) ⌝ ∗
        ⌜ length f.(f_locs) >= 4 ⌝ ∗
        ⌜ (0 <= j <= N.of_nat (length s))%N ⌝ ∗
        ⌜ (j + N.of_nat (length s') = N.of_nat (length s))%N ⌝ ∗
        isStack v (take (N.to_nat j) s ++ s') n ∗
        stackAll (take (N.to_nat j) s) Φ ∗
        stackAll2 (drop (N.to_nat j) s) s' Ψ ∗
            ⌜ f.(f_inst).(inst_types) !! 1 = Some (Tf [T_i32] [T_i32]) ⌝ ∗
            ⌜ f.(f_inst).(inst_tab) !! 0 = Some j0 ⌝ ∗
            na_inv logrel_nais γ1 ((N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m fn) ] a) ∗
            (match a with
             | Some a => ∃ γ2, ⌜↑γ2 ⊆ E ∧ @up_close _ coPset _ γ2 ⊆ ⊤ ∖ ↑γ1⌝ ∗ na_inv logrel_nais γ2 ((N.of_nat a) ↦[wf] cl) ∗
                          ⌜ cl_type cl = Tf [T_i32] [T_i32] ⌝ ∗ 
                                           (∀ (u : i32) (fc : frame),
                                               {{{ Φ u ∗
                                                     ⌜ f_inst f = f_inst fc ⌝ ∗
                                                                    ↪[frame] fc ∗
                                                                    na_own logrel_nais ⊤
                                               }}}
                                                 [ AI_basic (BI_const (VAL_int32 u)) ;
                                                   AI_invoke a ] @ E
                                                 {{{ w, (⌜ w = trapV ⌝ ∨ ((∃ v, ⌜ w = immV [VAL_int32 v] ⌝ ∗ Ψ u v)))
                                                          ∗ na_own logrel_nais ⊤ ∗ ↪[frame] fc}}})
             | None => True
             end)  ∗   
            na_own logrel_nais ⊤ ∗ ↪[frame] f) -∗
  WP (to_e_list map_loop_body) @ E CTX 2;
  push_base (LH_rec [] 0 [] (LH_base [] []) []) 0
    [AI_basic
       (BI_loop (Tf [] [])
          map_loop_body)] [] []
    {{ w, (⌜ w = trapV ⌝ ∨ (⌜ w = immV [] ⌝ ∗
                                        (∃ s', isStack v s' n ∗ stackAll2 s s' Ψ)))
             ∗ (∃ f1, ↪[frame] f1 ∗ na_own logrel_nais ⊤ ∗ ⌜ f_inst f = f_inst f1 ⌝ )
    }}.
Proof.
  remember (N.to_nat j) as k.
  iRevert (Heqk).
  iRevert (j s' s f).
  iInduction k as [|k] "IHk".
  
  { iIntros (j s' s f Habs Hsub1).
    iIntros "(%Hinstmem & %Hlocs0 & %Hlocs1 & %Hlocs2 & %Hlocs3 & %Hlocs & %Hjbound & %Hlen & Hs & HΦ & HΨ & %Htypes & %Htab & #Htab & Hcl & Hown & Hf)" => /=.

    iDestruct (stack_pure with "Hs") as "(%Hdiv & %Hvb & %Hlens & Hs)".
    
    assert (j=0)%N as ->; first lia.
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
    iFrame. iSplitR "Hf";eauto.
    iRight. iSplit => //.
    iExists s'.
    rewrite drop_0.
    by iFrame.
  }
  
  { iIntros (j s' s f Habs Hsub1).
    iIntros "(%Hinstmem & %Hlocs0 & %Hlocs1 & %Hlocs2 & %Hlocs3 & %Hlocs & %Hjbound & %Hlen & Hs & HΦ & HΨ & %Htypes & %Htab & #Htab & #Hcl & Hown & Hf)" => /=.
    
    iDestruct (stack_pure with "Hs") as "(%Hdiv & %Hvb & %Hlens & Hs)".

    assert (j = N.of_nat (k+1)) as ->; first lia.

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
    iApply (spec_map_loop_body_continue_trap with "[Hs HsvΦ Hf Hown Hcl]");[apply Hsub1|..].
    { iFrame "Htab Hcl". iFrame.
      repeat rewrite app_length take_length.
      replace (S k `min` length s) with (S k); last lia.
      replace (S k + length s') with (length s); last lia.
      instantiate (4 := N.of_nat k).
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
        rewrite Nat2N.id.
        replace (take _ _ !! k) with (Some sv) => //.
        rewrite lookup_take; last lia.
        done.
      }
    }
    
    iIntros (w) "(Hres & Hown & Hf)" => /=.
    iDestruct "Hres" as "[-> | Hres]".
    { iApply (wp_wand_ctx _ _ _ (λ w, ⌜w = trapV⌝ ∗ _)%I with "[Hf]"). iClear "IHk".
      take_drop_app_rewrite_twice 0 0. iApply (wp_trap_ctx with "[$]");auto.
      iIntros (v0) "[-> Hf]". iFrame.
      iSplitR "Hf";eauto. }    

    iDestruct "Hres" as "(-> & HsvΨ)".
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
    remember ({| f_locs := <[2:=value_of_uint (v + N.of_nat (length (take (S k) s ++ s')) * 4 - 4 * N.of_nat k)]> (f_locs f);
                 f_inst := f_inst f |}) as f'.
    rewrite -Heqf'.
    replace (f_inst f) with (f_inst f'); last by rewrite Heqf'.

    iApply "IHk"; auto; first by iPureIntro; instantiate (1 := N.of_nat k); rewrite Nat2N.id.
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
    { iPureIntro. clear H.
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
      rewrite - Heqx Nat2N.id.
      replace (k `min` x) with k; last lia.
      replace (k - k) with 0; last lia.
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
  
Lemma spec_stack_map_op_trap (f0 : frame) (n : immediate) (f : i32) (v : N) (s : seq.seq i32) E
      j0 a cl γ1
      (Φ : i32 -> iPropI Σ) (Ψ : i32 -> i32 -> iPropI Σ) :
  ↑γ1 ⊆ E ->
  ⊢ {{{  ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝  ∗
            ⌜ f0.(f_locs) !! 0 = Some (value_of_uint v) ⌝ ∗
            ⌜ f0.(f_locs) !! 1 = Some (VAL_int32 f) ⌝  ∗
            ⌜ length f0.(f_locs) >= 4 ⌝ ∗
            isStack v s n ∗
            stackAll s Φ ∗
            ⌜ f0.(f_inst).(inst_types) !! 1 = Some (Tf [T_i32] [T_i32]) ⌝ ∗

            ⌜ f0.(f_inst).(inst_tab) !! 0 = Some j0 ⌝ ∗
            na_inv logrel_nais γ1 ((N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] a) ∗
            match a with
            | Some a => ∃ γ2, ⌜↑γ2 ⊆ E ∧ @up_close _ coPset _ γ2 ⊆ ⊤ ∖ ↑γ1⌝ ∗ na_inv logrel_nais γ2 ((N.of_nat a) ↦[wf] cl) ∗
             ⌜ cl_type cl = Tf [T_i32] [T_i32] ⌝ ∗  
            (∀ (u : i32) (fc : frame),
                {{{ Φ u ∗
                      ⌜ f_inst f0 = f_inst fc ⌝ ∗
                       ↪[frame] fc ∗
                       na_own logrel_nais ⊤
                  }}}
                  [ AI_basic (BI_const (VAL_int32 u)) ;
                    AI_invoke a ] @ E
                  {{{ w, (⌜ w = trapV ⌝ ∨ ((∃ v, ⌜ w = immV [VAL_int32 v] ⌝ ∗ Ψ u v)))
                           ∗ na_own logrel_nais ⊤ ∗ ↪[frame] fc}}})
            | None => True
            end ∗
            na_own logrel_nais ⊤ ∗ ↪[frame] f0 }}}
    to_e_list map_op @ E
    {{{ w, (⌜ w = trapV ⌝ ∨ (⌜ w = immV [] ⌝ ∗
                                        (∃ s', isStack v s' n ∗ stackAll2 s s' Ψ)))
             ∗ (∃ f1, ↪[frame] f1 ∗ na_own logrel_nais ⊤ ∗ ⌜ f_inst f0 = f_inst f1 ⌝ )
    }}}.
Proof.
  intros Hsub1.
  iIntros "!>" (Ξ) "(%Hinstmem & %Hlocs0 & %Hlocs1 & %Hlocs & Hs & HΦ & %Htypes & %Htab & #Htab & #Hcl & Hinv & Hf) HΞ" => /=.
  
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
  iApply (wp_wand_ctx with "[HΦ Htab Hs Hf Hinv]").
  { iApply spec_map_loop_j_trap;[apply Hsub1|].
    iFrame "∗ #".
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
      instantiate (1 := N.of_nat (length s)).
      instantiate (1 := s).
      simpl.
      iPureIntro.
      do 2 f_equal.
      remember (N.of_nat (length s)) as x; rewrite - Heqx.
      by destruct x => //; lia.
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
    { rewrite Nat2N.id.
      rewrite firstn_all cats0.
      iFrame.
      rewrite drop_all.
      repeat iSplit => //.
    }
  }
  iFrame.
Qed.

Lemma spec_stack_map_trap (f0 : frame) (n : immediate) (f : i32) (v : N) (s : seq.seq i32) E
      j0 a cl γ1
      (Φ : i32 -> iPropI Σ) (Ψ : i32 -> i32 -> iPropI Σ) :
  ↑γ1 ⊆ E ->
  ⊢ {{{  ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝  ∗
            ⌜ f0.(f_locs) !! 0 = Some (value_of_uint v) ⌝ ∗
            ⌜ f0.(f_locs) !! 1 = Some (VAL_int32 f) ⌝  ∗
            ⌜ length f0.(f_locs) >= 4 ⌝ ∗
            isStack v s n ∗
            stackAll s Φ ∗
            ⌜ f0.(f_inst).(inst_types) !! 1 = Some (Tf [T_i32] [T_i32]) ⌝ ∗

            ⌜ f0.(f_inst).(inst_tab) !! 0 = Some j0 ⌝ ∗
            na_inv logrel_nais γ1 ((N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] a) ∗
            match a with
            | Some a => ∃ γ2, ⌜↑γ2 ⊆ E ∧ @up_close _ coPset _ γ2 ⊆ ⊤ ∖ ↑γ1⌝ ∗ na_inv logrel_nais γ2 ((N.of_nat a) ↦[wf] cl) ∗
             ⌜ cl_type cl = Tf [T_i32] [T_i32] ⌝ ∗  
            (∀ (u : i32) (fc : frame),
                {{{ Φ u ∗
                      ⌜ f_inst f0 = f_inst fc ⌝ ∗
                       ↪[frame] fc ∗
                       na_own logrel_nais ⊤
                  }}}
                  [ AI_basic (BI_const (VAL_int32 u)) ;
                    AI_invoke a ] @ E
                  {{{ w, (⌜ w = trapV ⌝ ∨ ((∃ v, ⌜ w = immV [VAL_int32 v] ⌝ ∗ Ψ u v)))
                           ∗ na_own logrel_nais ⊤ ∗ ↪[frame] fc}}})
            | None => True
            end ∗
            na_own logrel_nais ⊤ ∗ ↪[frame] f0 }}}
    to_e_list stack_map @ E
    {{{ w, (⌜ w = trapV ⌝ ∨ (⌜ w = immV [] ⌝ ∗
                                        (∃ s', isStack v s' n ∗ stackAll2 s s' Ψ)))
             ∗ (∃ f1, ↪[frame] f1 ∗ na_own logrel_nais ⊤ ∗ ⌜ f_inst f0 = f_inst f1 ⌝ )
    }}}.
Proof.
  intros Hsub1.
  iIntros "!>" (Ξ) "(%Hinstmem & %Hlocs0 & %Hlocs1 & %Hlocs & Hs & HΦ & %Htypes & %Htab & #Htab & #Hcl & Hinv & Hf) HΞ" => /=.
  
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
  iApply (spec_stack_map_op_trap with "[$HΦ $Htab $Hinv $Hs $Hf $Hcl]");eauto.
Qed.

End specs.

(*
Section valid.
  Set Bullet Behavior "Strict Subproofs".

  Global Instance interp_table_persistent n t : Persistent (interp_table n (λ n, interp_closure []) t).
  Proof. apply big_sepL_persistent. intros. repeat (apply bi.exist_persistent;intros).
         apply bi.sep_persistent;try apply _. apply bi.from_option_persistent; try apply _.
         intros. apply interp_function_persistent. intros.
         unfold interp_closure. simpl. destruct cl,f; apply _.
  Qed.
  
  Lemma valid_push m t funcs :
    let i0 := {| inst_types := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
                     inst_funcs := funcs;
                     inst_tab := [t];
                     inst_memory := [m];
                     inst_globs := []
              |} in
    na_inv logrel_nais stkN (stackModuleInv (λ (a : N) (b : seq.seq i32), isStack a b m) (λ n : nat, N.of_nat m↦[wmlength]N.of_nat n)) -∗
    interp_table 1 (λ n, interp_closure []) (N.of_nat t) -∗
    interp_closure_native i0 [T_i32;T_i32] [] [T_i32;T_i32] (to_e_list stack_map) [].
  Proof.
    iIntros "#Hstk #Htab".
    iIntros (vcs f) "#Hv Hown Hf".
    iIntros (LI HLI%lfilled_Ind_Equivalent);inversion HLI;inversion H9;subst;simpl.
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
        * iDestruct "Htab" as "[Htab _]".
          iDestruct "Htab" as (τf fe) "[Htab Hfe]".
          assert (0%N = N.of_nat (Wasm_int.nat_of_uint i32m (Wasm_int.int_of_Z i32m 0))) as ->;[lias|].

          iApply (spec_stack_map_op_trap with "[$Hstack $Hf $Htab]");[solve_ndisj|..].
          { repeat iSplit;auto. subst f';simpl. iPureIntro.
            unfold value_of_uint. f_equal. f_equal. apply int_of_Z_mod.
            lia. }
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
*)

End stack.    
      
