From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_host iris_fundamental_helpers stack_specs stack_instantiation iris_interp_instance_alloc.
Require Export iris_example_helper.
Require Export datatypes operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.
   

Section Client.
  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ}.

  Definition main :=
    [ BI_call 0 ;
      BI_tee_local 0 ;
      i32const (-1) ;
      BI_relop T_i32 (Relop_i ROI_eq) ;
      (* If new_stack failed, set global v0 to -1 and return *)
      BI_if (Tf [] []) [i32const (-1) ; BI_set_global 0 ; BI_return] [] ;
      i32const 4 ;
      BI_get_local 0 ;
      BI_call 4 ;
      i32const 2 ;
      BI_get_local 0 ;
      BI_call 4 ;
      i32const 0 ;
      BI_get_local 0 ;
      BI_call 5 ;
      BI_get_local 0 ;
      BI_call 3 ;
      BI_set_global 0
    ].

  Definition client_module :=
    {|
      mod_types := [ Tf [] [] ; Tf [] [T_i32] ; Tf [T_i32] [T_i32] ;
                     Tf [T_i32 ; T_i32] [] ] ;
      mod_funcs :=
      [ {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := [T_i32] ;
          modfunc_body := main
        |} ] ;
      mod_tables := [] ; 
      mod_mems := [] ;
      mod_globals := [] ;
      mod_elem := [ {| modelem_table := Mk_tableidx 0 ;
                      modelem_offset := [i32const 0] ;
                      modelem_init := [Mk_funcidx 6] |} ] ;
      mod_data := [] ;
      mod_start := Some {| modstart_func := Mk_funcidx 7 |} ;
      mod_imports := [
        {|
          imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "new_stack" ;
          imp_desc := ID_func 1
        |} ;
        {|
          imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "is_empty" ;
          imp_desc := ID_func 2
        |} ;
        {|
          imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "is_full" ;
          imp_desc := ID_func 2
        |} ;
        {|
          imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "pop" ;
          imp_desc := ID_func 2
        |} ;
        {|
          imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "push" ;
          imp_desc := ID_func 3
        |} ;
        {| imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "stack_map" ;
          imp_desc := ID_func 3
        |} ;
        {| imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "table" ;
          imp_desc := ID_table {| tt_limits := {| lim_min := 1%N ; lim_max := None |} ;
                                 tt_elem_type := ELT_funcref |}
        |} ;
        {| imp_module := list_byte_of_string "Adv";
          imp_name := list_byte_of_string "adv_call";
          imp_desc := ID_func 2
        |} ;
        {| imp_module := list_byte_of_string "Ret";
          imp_name := list_byte_of_string "ret_glob";
          imp_desc := ID_global {| tg_mut := MUT_mut; tg_t := T_i32 |} |}
      ] ;
      mod_exports := []
    |}.

  Definition client_func_impts : seq.seq extern_t := expts ++ [ET_func (Tf [T_i32] [T_i32])].
  Definition client_glob_impts : seq.seq extern_t := [ET_glob {| tg_mut := MUT_mut; tg_t := T_i32 |} ].

  Ltac type_next_rewrite :=
  match goal with
  | |- context [ be_typing _ ?e _  ] =>
      rewrite -(list.take_drop (length e - 1) e);simpl take; simpl drop
  end.
  Ltac type_next :=
  match goal with
  | |- context [ be_typing _ ?e _  ] =>
      rewrite -(list.take_drop (length e - 1) e);simpl take; simpl drop;
      eapply bet_composition;[|econstructor;eauto];simpl
  end.
  
  Lemma client_module_typing :
    module_typing client_module (client_func_impts ++ client_glob_impts) [].
  Proof.
    exists [Tf [] []],[]. simpl.
    repeat split;eauto.
    { apply Forall2_cons. split;auto. cbn.
      repeat split;auto. repeat type_next.
      type_next_rewrite.
      eapply bet_composition.
      instantiate (1:=[T_i32]).
      2: { rewrite <- (app_nil_r [T_i32]).
           rewrite -(list.take_drop (1) [T_i32;T_i32]);simpl take; simpl drop.
           eapply bet_weakening. econstructor;eauto. }
      repeat type_next.
      type_next_rewrite.
      eapply bet_composition.
      instantiate (1:=[T_i32]).
      2: { rewrite <- (app_nil_r [T_i32]).
           rewrite -(list.take_drop (1) [T_i32;T_i32]);simpl take; simpl drop.
           eapply bet_weakening. econstructor;eauto. }
      repeat type_next.
      type_next_rewrite.
      eapply bet_composition.
      instantiate (1:=[T_i32]).
      2: { rewrite <- (app_nil_r [T_i32]).
           rewrite -(list.take_drop (1) [T_i32;T_i32]);simpl take; simpl drop.
           eapply bet_weakening. econstructor;eauto. }
      type_next. type_next.
      3: constructor.
      { type_next;[|constructor].
      type_next_rewrite.
      eapply bet_composition.
      instantiate (1:=[T_i32]).
      2: { rewrite <- (app_nil_r [T_i32]).
           rewrite -(list.take_drop (1) [T_i32;T_i32]);simpl take; simpl drop.
           eapply bet_weakening. econstructor;eauto. }
      repeat type_next. constructor. }
      { type_next. instantiate (1:=[]).
        type_next. constructor. }
    }
    { apply Forall_cons. split;auto. cbn. repeat split;auto. constructor. }
    { repeat (apply Forall2_cons;split;auto). }
  Qed.

End Client.

Ltac take_drop_app_rewrite n :=
  match goal with
  | |- context [ WP ?e @ _; _ CTX _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  | |- context [ WP ?e @ _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  | |- context [ WP ?e @ _; _ FRAME _; _ CTX _; _  {{ _, _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  | |- context [ WP ?e @ _; _ FRAME _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  end.
  
Ltac take_drop_app_rewrite_twice n m :=
  take_drop_app_rewrite n;
  match goal with
  | |- context [ WP _ ++ ?e @ _; _ CTX _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop (length e - m) e);simpl take; simpl drop
  | |- context [ WP _ ++ ?e @ _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop (length e - m) e);simpl take; simpl drop
  end.

Section Client_main.

  Context `{!wasmG Σ, !logrel_na_invs Σ }.

  Lemma main_spec C k idt locs es f a i idf0 l0 f0 idf3 l3 f3 idf4 l4 f4 idf5 l5 f5
        istack isStack newStackAddrIs stacktab :
    (tc_label C) = [] ∧ (tc_return C) = None ->

    f.(f_inst).(inst_globs) !! 0 = Some k ->
    f.(f_inst).(inst_tab) !! 0 = Some idt ->
    inst_funcs (f_inst f) !! 0 = Some idf0 ->
    inst_funcs (f_inst f) !! 4 = Some idf4 ->
    inst_funcs (f_inst f) !! 3 = Some idf3 ->
    inst_funcs (f_inst f) !! 5 = Some idf5 ->
    f.(f_locs) = n_zeros [T_i32] ->
    length (table_data stacktab) >= 1 ->
    
    be_typing (upd_local_label_return C (T_i32 :: locs) [[T_i32]] (Some [T_i32])) es (Tf [] [T_i32]) ->
    
    ⊢ {{{ ↪[frame] f
         ∗ na_own logrel_nais ⊤
         ∗ na_inv logrel_nais (wfN (N.of_nat a)) ((N.of_nat a) ↦[wf] (FC_func_native i (Tf [T_i32] [T_i32]) locs es))
         ∗ interp_instance C [] i
         ∗ (∃ gv, N.of_nat k ↦[wg] {| g_mut := MUT_mut; g_val := gv |})
         (* new stack *)
         ∗ N.of_nat idf0 ↦[wf]FC_func_native istack (Tf [] [T_i32]) l0 f0
         ∗ spec0_new_stack idf0 istack l0 f0 isStack newStackAddrIs ⊤
         (* push *)
         ∗ N.of_nat idf4↦[wf]FC_func_native istack (Tf [T_i32; T_i32] []) l4 f4
         ∗ spec4_push idf4 istack l4 f4 isStack ⊤
         (* pop *)
         ∗ N.of_nat idf3↦[wf]FC_func_native istack (Tf [T_i32] [T_i32]) l3 f3
         ∗ spec3_pop idf3 istack l3 f3 isStack ⊤
         (* map *)
         ∗ N.of_nat idf5↦[wf]FC_func_native istack (Tf [T_i32; T_i32] []) l5 f5
         ∗ spec5_stack_map_trap idf5 istack l5 f5 isStack idt ⊤
         (* table *)
         ∗ N.of_nat idt↦[wtblock]table_init_replace_single stacktab (nat_of_int (Wasm_int.Int32.repr 0)) [Some a]
         (* new stack predicate *)
         ∗ newStackAddrIs 0
      }}}
      to_e_list main
      {{{ w, (⌜w = trapV⌝ ∨ ((∃ vh, ⌜w = retV vh⌝ ∗ (N.of_nat k) ↦[wg] {| g_mut := MUT_mut; g_val := xx (-1) |} )
                          ∨ (⌜w = immV []⌝ ∗ ∃ v, (N.of_nat k) ↦[wg] {| g_mut := MUT_mut; g_val := VAL_int32 v |}
                                                               ∗ na_own logrel_nais ⊤)))
               ∗ ∃ f', ↪[frame] f' ∗ ∃ r, ⌜f' = Build_frame (set_nth r (f_locs f) 0 r) (f_inst f)⌝ }}}.
  Proof.
    iIntros (HC Hglob Htab Hidf0 Hidf4 Hidf3 Hidf5 Hflocs Htablen Htyp Φ)
            "!> (Hf & Hown & #Hadv & #Hi & Hg & Hidf0 & #Hnewstack & 
                 Hidf4 & #Hpush & Hidf3 & #Hpop & Hidf5 & #Hmap & Hidt & Hnewstackaddr) HΦ".
    take_drop_app_rewrite 1.
    iApply wp_seq.
    (* new stack *)
    iSplitR;[|iSplitL "Hidf0 Hf Hnewstackaddr"];cycle 1.
    { iApply (wp_call with "Hf");[apply Hidf0|].
      iNext. iIntros "Hf". iApply ("Hnewstack" with "[$Hf $Hnewstackaddr $Hidf0]").
      { iPureIntro. repeat split; try lias. exists 0%N. lia. }
      iIntros (v) "[Hres [Hidf Hf]]".
      instantiate (1:= (λ vs, _ ∗ ↪[frame] _)%I). iFrame "Hf".
      iCombine "Hres" "Hidf" as "Hres". iExact "Hres". }
    2: iIntros "[[Hcontr _] _]";iDestruct "Hcontr" as (? Hcontr) "_";done.
    iIntros (w) "[[Hres Hidf] Hf]".
    iDestruct "Hres" as (r Hweq) "Hres". subst w. iSimpl.
    (* tee_local + set_local *)
    take_drop_app_rewrite 2.
    iApply wp_seq. iSplitR;[|iSplitL "Hf"];cycle 1.
    { iApply (wp_tee_local with "[$]").
      iIntros "!> Hf".
      take_drop_app_rewrite 1.
      iApply wp_val.
      iSplitR;cycle 1.
      { iApply (wp_wand _ _ _ (λ v, ⌜v = immV []⌝ ∗ _)%I with "[Hf]").
        iApply (wp_set_local with "[] [$Hf]");[rewrite Hflocs;simpl;lia|done|..].
        iIntros (v) "[-> Hf]". iSimpl.
        instantiate (1:=(λ v, ⌜v = immV _⌝ ∗ _)%I).
        iSplitR;eauto. iExact "Hf". }
      iIntros "[%Hcontr _]";done. }
    2: iIntros "[%Hcontr _]";done.
    iIntros (w) "[-> Hf]". iSimpl.
    (* relop *)
    take_drop_app_rewrite 3.
    iApply wp_seq. iSplitR;[|iSplitL "Hf"];cycle 1.
    { iApply (wp_relop with "[$]");eauto.
      iNext. instantiate (1:=(λ v, ⌜v = immV _⌝)%I);eauto. }
    2: iIntros "[%Hcontr _]";done.
    iIntros (w) "[-> Hf]". iSimpl.

    (* CASES: new stack succeeded/failed *)
    iDestruct "Hres" as "[[-> Hnewstackaddr]|[[%Hpos %Hle] [HisStack Hnewstackaddr]]]".
    { (* failure *)
      iSimpl.
      iApply wp_wasm_empty_ctx.
      (* if *)
      take_drop_app_rewrite_twice 0 (length main - 5).
      iApply wp_base_push;auto.
      iApply (wp_if_true_ctx with "Hf");[lias|..].
      iNext. iIntros "Hf".
      (* block *)
      take_drop_app_rewrite 0.
      iApply (wp_block_ctx with "Hf");[auto..|].
      iNext. iIntros "Hf".
      iApply wp_label_push_nil. iSimpl.
      iApply wp_ctx_bind;[simpl;auto|].
      (* set_global to -1 *)
      iDestruct "Hg" as (gv) "Hg".
      take_drop_app_rewrite 2.
      iApply wp_seq. iSplitR;[|iSplitL "Hf Hg"];cycle 1.
      { iApply (wp_set_global with "[] Hf Hg");auto.
        iNext. instantiate (1:=(λ v, ⌜v = immV _⌝)%I);eauto. }
      2: iIntros "[%Hcontr _]";done.
      iIntros (w) "[-> [Hg Hf]]". iSimpl.
      assert (iris.to_val [AI_basic BI_return] = Some (retV (SH_base [] []))) as Hval.
      { cbn. eauto. }
      iApply iris_wp.wp_value;[unfold IntoVal;by eapply iris.of_to_val|].
      iIntros (LI HLI%lfilled_Ind_Equivalent);inversion HLI;subst. iSimpl.
      inversion H8;subst. iSimpl.
      match goal with |- context [ WP ?e @ _ {{ _ }}%I ] => set (v:=e) end.
      eassert (iris.to_val v = Some (retV (SH_rec _ _ _ (SH_base [] []) _))) as Hval'.
      { cbn. eauto. }
      iApply iris_wp.wp_value;[unfold IntoVal;by eapply iris.of_to_val|].
      iApply "HΦ".
      iSplitR "Hf";[|iExists _;iFrame;iExists _;eauto].
      iRight. iLeft. iExists _. iSplit;eauto.
    }

    { (* success *)
      assert (VAL_int32 (wasm_bool (Wasm_int.Int32.eq (Wasm_int.Int32.repr r) (Wasm_int.Int32.repr (-1))))
              = VAL_int32 Wasm_int.Int32.zero) as ->.
      { unfold wasm_bool.
        assert (Wasm_int.Int32.eq (Wasm_int.Int32.repr r) (Wasm_int.Int32.repr (-1)) = false) as ->;auto.
        apply Wasm_int.Int32.eq_false. intros Hcontr.
        rewrite Wasm_int.Int32.repr_m1 in Hcontr.
        inversion Hcontr. rewrite Wasm_int.Int32.Z_mod_modulus_id in H0;simplify_eq. lias. split;try lia.
        unfold Wasm_int.Int32.modulus,Wasm_int.Int32.wordsize,Integers.Wordsize_32.wordsize,two_power_nat. simpl.
        unfold two32 in Hle. unfold page_size in Hle. lia. }

      iSimpl.
      iApply wp_wasm_empty_ctx.
      (* if *)
      take_drop_app_rewrite_twice 0 (length main - 5).
      iApply wp_base_push;auto.
      iApply (wp_if_false_ctx with "Hf");[auto|..].
      iNext. iIntros "Hf".
      (* block *)
      take_drop_app_rewrite 0.
      iApply (wp_block_ctx with "Hf");[auto..|].
      iNext. iIntros "Hf". iSimpl.
      iApply wp_label_push_nil. iSimpl.
      iApply (wp_val_return with "Hf");auto.
      iIntros "Hf". iSimpl.
      (* get_local *)
      take_drop_app_rewrite 2.
      rewrite Hflocs. iSimpl in "Hf".
      iApply (wp_seq _ _ _ (λ v, ⌜v = immV _⌝ ∗ _)%I).
      iSplitR;[|iSplitL "Hf"];[by iIntros "[%Hcontr _]"|..].
      { take_drop_app_rewrite 1.
        iApply wp_val. iSplitR;[by iIntros "[%Hcontr _]"|].
        iApply (wp_get_local with "[] [$Hf]");simpl;eauto. }
      iIntros (w) "[-> Hf]".
      iSimpl.
      (* push *)
      take_drop_app_rewrite 3.
      iApply wp_seq. iSplitR;[|iSplitL "HisStack Hf Hidf4"];cycle 1.
      { take_drop_app_rewrite_twice 2 0.
        iApply wp_wasm_empty_ctx.
        iApply wp_base_push;auto.
        iApply (wp_call_ctx with "Hf");[simpl;apply Hidf4|].
        iNext. iIntros "Hf".
        iApply wp_base_pull. iApply wp_wasm_empty_ctx.
        iSimpl. iApply ("Hpush" with "[$Hf $Hidf4 $HisStack]").
        { iPureIntro. simpl. unfold two14,Wasm_int.Int32.max_unsigned,Wasm_int.Int32.modulus.
          unfold two_power_nat, Wasm_int.Int32.wordsize.
          unfold page_size,two32 in Hle. simpl. lia. }
        iIntros (w). rewrite (bi.sep_assoc _ _ (↪[frame] _)%I).
        iIntros "[-> [HH Hf]]".
        instantiate (1:=(λ v, ⌜v = immV []⌝ ∗ ↪[frame] _ ∗ _)%I).
        iFrame "Hf".
        iSplit;[auto|]. iExact "HH". }
      iIntros (w) "( -> & Hf & HisStack & Hidf4)".
      iSimpl. 2: by iIntros "[%Hcontr _]".
      (* get_local *)
      take_drop_app_rewrite 2.
      iApply (wp_seq _ _ _ (λ v, ⌜v = immV _⌝ ∗ _)%I).
      iSplitR;[|iSplitL "Hf"];[by iIntros "[%Hcontr _]"|..].
      { take_drop_app_rewrite 1.
        iApply wp_val. iSplitR;[by iIntros "[%Hcontr _]"|].
        iApply (wp_get_local with "[] [$Hf]");simpl;eauto. }
      iIntros (w) "[-> Hf]".
      iSimpl.
      (* push *)
      take_drop_app_rewrite 3.
      iApply wp_seq. iSplitR;[|iSplitL "HisStack Hf Hidf4"];cycle 1.
      { take_drop_app_rewrite_twice 2 0.
        iApply wp_wasm_empty_ctx.
        iApply wp_base_push;auto.
        iApply (wp_call_ctx with "Hf");[simpl;apply Hidf4|].
        iNext. iIntros "Hf".
        iApply wp_base_pull. iApply wp_wasm_empty_ctx.
        iSimpl. iApply ("Hpush" with "[$Hf $Hidf4 $HisStack]").
        { iPureIntro. simpl. unfold two14,Wasm_int.Int32.max_unsigned,Wasm_int.Int32.modulus.
          unfold two_power_nat, Wasm_int.Int32.wordsize.
          unfold page_size,two32 in Hle. simpl. lia. }
        iIntros (w). rewrite (bi.sep_assoc _ _ (↪[frame] _)%I).
        iIntros "[-> [HH Hf]]".
        instantiate (1:=(λ v, (⌜v = immV []⌝ ∗ _ ) ∗ ↪[frame] _)%I). iFrame "Hf".
        iSplit;[auto|]. iExact "HH". }
      iIntros (w) "[[-> [HisStack Hidf4]] Hf]".
      iSimpl. 2: by iIntros "[[%Hcontr _] _]".
      (* get_local *)
      take_drop_app_rewrite 2.
      iApply (wp_seq _ _ _ (λ v, ⌜v = immV _⌝ ∗ _)%I).
      iSplitR;[|iSplitL "Hf"];[by iIntros "[%Hcontr _]"|..].
      { take_drop_app_rewrite 1.
        iApply wp_val. iSplitR;[by iIntros "[%Hcontr _]"|].
        iApply (wp_get_local with "[] [$Hf]");simpl;eauto. }
      iIntros (w) "[-> Hf]".
      iSimpl.
      (* map *)
      iDestruct "Hidt" as "[Ht _]". iSimpl in "Ht".
      destruct (length (table_data stacktab));[lia|].
      rewrite firstn_cons. iDestruct "Ht" as "[Ht _]".
      
      take_drop_app_rewrite 3.
      iApply (wp_wand with "[-HΦ]").
      { iApply wp_wasm_empty_ctx.
        iApply wp_seq_can_trap_same_ctx. iFrame "Hf".
        iSplitR;[|iSplitR];cycle 2.
        iSplitL "HisStack Hidf5 Ht Hown".
        { iIntros "Hf". iApply (wp_wand with "[-]").
          { take_drop_app_rewrite_twice 2 0.
            iApply wp_wasm_empty_ctx.
            iApply wp_base_push;auto.
            iApply (wp_call_ctx with "Hf");[simpl;apply Hidf5|].
            iNext. iIntros "Hf".
            iApply wp_base_pull. iApply wp_wasm_empty_ctx.
            iSimpl.
            iDestruct (be_fundamental_local _ _ [] _ (T_i32 :: locs) with "Hi") as "Hl";eauto.
            unfold interp_expression_closure.
            
            iApply ("Hmap" with "[] [$HisStack $Hf $Hidf5 Ht $Hown $Hadv]");[iPureIntro;solve_ndisj|..].
            iSimpl. iFrame "Ht".
            instantiate (2:=(λ _, True)%I).
            instantiate (1:=(λ _ _, True)%I).
            
            repeat iSplit;[auto| |auto..|].
            { iPureIntro. unfold page_size, two32 in Hle.
              unfold Wasm_int.Int32.max_unsigned,Wasm_int.Int32.modulus,
                Wasm_int.Int32.wordsize,Integers.Wordsize_32.wordsize,two_power_nat. simpl. lia. }
            { (* This is the most interesting part of the proof: since we do not assume a spec for the 
             imported function, we apply the ftlr to get a specifiction for the function *)
              iIntros (u fc). iModIntro.
              iIntros (Ψ) "(_ & %Histack & Hf & Hown) HΨ".
              iApply fupd_wp.
              iMod (na_inv_acc with "Hadv Hown") as "(>Ha & Hown & Hcls)";[solve_ndisj..|].
              take_drop_app_rewrite 1.
              iApply (wp_wand with "[-HΨ] [HΨ]");cycle 1.
              { iIntros (v). iSpecialize ("HΨ" $! v). rewrite bi.sep_assoc. iExact "HΨ". }
              iApply (wp_invoke_native with "Hf Ha");[eauto..|].
              iNext. iIntros "[Hf Ha]".
              iApply fupd_wp.
              iMod ("Hcls" with "[$]") as "Hown". iModIntro.
              
              rewrite -wp_frame_rewrite.
              iApply wp_wasm_empty_ctx_frame.
              take_drop_app_rewrite 0.
              iApply (wp_block_local_ctx with "Hf");[eauto..|].
              iNext. iIntros "Hf".
              iApply wp_wasm_empty_ctx_frame.
              rewrite wp_frame_rewrite.
              iDestruct ("Hl" $! _ ([VAL_int32 u] ++ n_zeros locs) with "Hf Hown []") as "Hcont".
              { iSimpl. iRight. iExists _. iSplit;[eauto|].
                iSplit. iExists _. eauto.
                iApply n_zeros_interp_values. }
              iApply (wp_wand with "Hcont").
              iIntros (v) "[[Hv ?] ?]". iFrame.
              iDestruct "Hv" as "[? | Hv]";[by iLeft|iRight].
              iDestruct "Hv" as (ws ->) "Hw".
              iDestruct (big_sepL2_length with "Hw") as %Hwlen.
              destruct ws as [|w ws];[done|destruct ws;[|done]].
              iDestruct "Hw" as "[Hw _]". iDestruct "Hw" as (z) "->". unfold interp_value. eauto.
            }
            { iIntros (w) "[H [Htab [Hown Hf]]]".
              iCombine "H Htab Hown" as "H". instantiate (1:=(λ vs, _ ∗ ↪[frame] _)%I). iFrame "Hf". iExact "H". }
          }
          iIntros (v) "[[Hv [Htab Hown]] Hf]".
          iSplitR "Hf".
          iDestruct "Hv" as "[Htrap | [-> [Hs Hidf]]]";[by iLeft|].
          iRight. iCombine "Hs Hidf Htab Hown" as "H".
          instantiate (1:=(λ v, ⌜v = immV []⌝ ∗ _ )%I). iSplit;auto. iExact "H".
          iFrame.
        }
        2: by iIntros "[%Hcontr _]".
        { iIntros (w) "[[-> [Hs [Hidf5 [Htab Hown]]]] Hf]".
          iSimpl. iApply wp_wasm_empty_ctx.
          (* get_local *)
          take_drop_app_rewrite 1.
          iApply (wp_seq _ _ _ (λ v, ⌜v = immV _⌝ ∗ _)%I).
          iSplitR;[|iSplitL "Hf"];[by iIntros "[%Hcontr _]"|..].
          { iApply (wp_get_local with "[] [$Hf]");simpl;eauto. }
          iIntros (w) "[-> Hf]".
          iSimpl.
          (* pop *)
          (* we can infer the size of the new stack state *)
          iDestruct "Hs" as (s') "[HisStack Hstackall]".
          do 2 (destruct s';try done). { iDestruct "Hstackall" as "[? ?]";done. }
          destruct s';try done. 2: { iDestruct "Hstackall" as "[? [? ?]]";done. }
          take_drop_app_rewrite 2.
          
          iApply wp_seq. iSplitR;[|iSplitL "HisStack Hf Hidf3"];cycle 1.
          { take_drop_app_rewrite_twice 1 0.
            iApply wp_wasm_empty_ctx.
            iApply wp_base_push;auto.
            iApply (wp_call_ctx with "Hf");[simpl;apply Hidf3|].
            iNext. iIntros "Hf".
            iApply wp_base_pull. iApply wp_wasm_empty_ctx.
            iSimpl. unfold spec3_pop. unfold i32const. iApply ("Hpop" with "[$Hf $Hidf3 $HisStack]").
            { iPureIntro. simpl. unfold two14,Wasm_int.Int32.max_unsigned,Wasm_int.Int32.modulus.
              unfold two_power_nat, Wasm_int.Int32.wordsize.
              unfold page_size,two32 in Hle. simpl. lia. }
            iIntros (w). rewrite (bi.sep_assoc _ _ (↪[frame] _)%I).
            iIntros "[-> [HH Hf]]". instantiate (1:=(λ vs, ⌜vs = immV [_]⌝ ∗ _ ∗ ↪[frame] _)%I). iFrame "Hf".
            iSplit;[auto|]. iExact "HH". }
          iIntros (w) "(-> & [HisStack Hidf3] & Hf)".
          iSimpl. 2: by iIntros "[%Hcontr _]".
          instantiate (1:=(λ v, ⌜v = trapV⌝
                                ∨ (∃ vh : simple_valid_holed, ⌜v = retV vh⌝ ∗
                                   N.of_nat k↦[wg] {| g_mut := MUT_mut; g_val := xx (-1) |})
                                ∨ ⌜v = immV []⌝ ∗
                                            (∃ v0, N.of_nat k↦[wg] {| g_mut := MUT_mut; g_val := VAL_int32 v0 |} ∗
                                                                na_own logrel_nais ⊤))%I).
          iSimpl.
          iDestruct "Hg" as (gv) "Hg".
          iApply (wp_wand with "[Hf Hg]").
          { iApply (wp_set_global with "[] Hf Hg");[simpl;auto|].
            instantiate (1:=(λ v, ⌜ v = immV [] ⌝)%I). iNext. auto. }
          iIntros (v) "[-> [Hg Hf]]". iFrame. iRight. iRight. iSplitR "Hg Hown";[auto|].
          iExists _. iFrame.
        }
        { by iLeft. }
      }
      iIntros (v) "[Hv Hf]".
      iApply "HΦ". iFrame. iExists _. iFrame. eauto. }
  Qed.
      
    
End Client_main.

Ltac simplify_map_lookup H :=
  repeat lazymatch H with
  | <[ _ := _]> _ !! _ = _ => rewrite lookup_insert in H
  | <[ _ := _]> _ !! _ = _ => rewrite lookup_insert_ne in H => //
  end.
    

Section Client_instantiation.

  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ,
      !logrel_na_invs Σ, !hasG Σ}.

  Notation "{{{ P }}} es {{{ v , Q }}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).

  Notation " n ↪[vis]{ q } v" := (ghost_map_elem (V := module_export) visGName n q v%V)
                           (at level 20, q at level 5, format " n ↪[vis]{ q } v") .
  Notation " n ↪[vis] v" := (ghost_map_elem (V := module_export) visGName n (DfracOwn 1) v%V)
                              (at level 20, format " n ↪[vis] v").
  
  Notation " n ↪[mods]{ q } v" := (ghost_map_elem (V := module) msGName n q v%V)
                           (at level 20, q at level 5, format " n ↪[mods]{ q } v") .
  Notation " n ↪[mods] v" := (ghost_map_elem (V := module) msGName n (DfracOwn 1) v%V)
                               (at level 20, format " n ↪[mods] v").

  Definition stack_adv_client_instantiate :=
    [ ID_instantiate [0%N ; 1%N ; 2%N ; 3%N ; 4%N ; 5%N ; 6%N] 0 [] ;
      ID_instantiate [7%N] 1 [] ;
      ID_instantiate [] 2 [0%N;1%N;2%N;3%N;4%N;5%N;6%N;7%N;8%N] ].

  Lemma wp_wand_host s E (e : host_expr) (Φ Ψ : host_val -> iProp Σ) :
    WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
  Proof. iApply (weakestpre.wp_wand). Qed.

  Lemma instantiate_client adv_module g_ret wret  :
    module_typing adv_module [] [ET_func (Tf [T_i32] [T_i32])] -> (* we assume the adversary module has an export of the () → () *)
    mod_start adv_module = None -> (* that it does not have a start function *)
    module_restrictions adv_module -> (* that it adheres to the module restrictions (i.e. only constant initializers for globals) *)
    module_elem_bound_check_gmap ∅ [] adv_module -> (* if the adversary module declares a table, there cannot be more initializers that its size *)
    module_data_bound_check_gmap ∅ [] adv_module -> (* if the adversary module declares a memory, there cannot be more initializers that its size *)
    typeof wret = T_i32 -> (* the imported return global has type i32 *)

    ⊢ {{{ g_ret ↦[wg] {| g_mut := MUT_mut; g_val := wret |} ∗
          0%N ↪[mods] stack_module ∗
          1%N ↪[mods] adv_module ∗
          2%N ↪[mods] client_module ∗
          na_own logrel_nais ⊤ ∗
          (∃ name, 8%N ↪[vis] {| modexp_name := name; modexp_desc := MED_global (Mk_globalidx (N.to_nat g_ret)) |}) ∗
          (∃ vs0 vs1 vs2 vs3 vs4 vs5 vs6, [∗ list] v↦vs∈[vs0;vs1;vs2;vs3;vs4;vs5;vs6], N.of_nat v ↪[vis] vs) ∗
          (∃ vs, 7%N ↪[vis] vs) ∗
          ↪[frame] empty_frame
      }}}
        ((stack_adv_client_instantiate,[]) : host_expr) 
      {{{ v, ⌜v = (trapHV : host_val)⌝ ∨ ∃ v, g_ret ↦[wg] {| g_mut := MUT_mut; g_val := VAL_int32 v|} }}} .
  Proof.
    iIntros (Htyp Hnostart Hrestrict Hboundst Hboundsm Hgrettyp).
    iModIntro. iIntros (Φ) "(Hgret & Hmod_stack & Hmod_adv & Hmod_lse & Hown & Hvis8 & 
                        Hvisvst & Hvis7 & Hemptyframe) HΦ".
    iDestruct "Hvisvst" as (vs0 vs1 vs2 vs3 vs4 vs5 vs6) "Hvis".
    iApply (wp_seq_host_nostart NotStuck with "[] [$Hmod_stack] [Hvis] ") => //.
    2: { iIntros "Hmod_stack".
      iApply weakestpre.wp_mono;cycle 1.
      iApply (instantiate_stack_spec with "[$]").
      { iFrame "Hvis". }
      iIntros (v) "[Hvsucc [$ Hv]]".
      iCombine "Hvsucc Hv" as "Hv".
      iExact "Hv". }
    { by iIntros "(% & ?)". }
    iIntros (w) "Hstack Hmod_stack".
    iApply (wp_seq_host_nostart NotStuck with "[] [$Hmod_adv] [Hvis7] ") => //.
    2: { iIntros "Hmod_adv".
      iApply weakestpre.wp_mono.
      2: iApply (instantiation_spec_operational_no_start _ _ _ [] [] _ _ _ _ ∅ ∅ ∅ ∅);eauto;iFrame.
      2: cbn; repeat iSplit =>//.
      { iIntros (v) "[Hvsucc [$ Hv]]".
        iCombine "Hvsucc Hv" as "Hv".
        by iExact "Hv". }
      { by unfold import_func_resources. }
      { by unfold func_typecheck. }
      { by unfold import_tab_resources. }
      { by unfold tab_typecheck. }
      { by unfold import_mem_resources. }
      { by unfold mem_typecheck. }
      { by unfold import_glob_resources. }
      { by unfold glob_typecheck. }
      iPureIntro. destruct Htyp as [fts [gts Htyp]].
      destruct adv_module;simpl in *.
      destruct Htyp as (_&_&_&_&_&_&_&_&Htyp).
      apply Forall2_length in Htyp. auto. }
    { by iIntros "(% & ?)". }

    iIntros (w') "(-> & [Himps Hinst_adv]) Hmod_adv".
    iDestruct "Hinst_adv" as (inst_adv) "[Hinst_adv Hadv_exports]".
    iDestruct "Hinst_adv" as (g_adv_inits t_adv_inits m_adv_inits glob_adv_inits wts' wms')
                               "(Himpstyp & %HH & %Htyp_inits & %Hwts' & %Hbounds_elem & %Hmem_inits 
                               & %Hwms' & %Hbounds_data & %Hglob_inits_vals & %Hglob_inits & Hinst_adv_res)".
    destruct HH as (?&?&?&?&?&?).
    iDestruct (big_sepL2_length with "Hadv_exports") as %Hexp_len.
    destruct (mod_exports adv_module) eqn:Hexp;[done|].
    destruct l;[|done].
    iDestruct "Hadv_exports" as "[Hn _]".
    revert Htyp. rewrite module_typing_body_eq =>Htyp.
    destruct Htyp as [fts [gts Htyp]].
    assert (Hmod:=Htyp).
    remember adv_module as advm.
    destruct adv_module. rewrite Heqadvm in Hexp.
    rewrite Heqadvm in Hmod.
    
    simpl in Hexp. subst mod_exports.
    destruct Hmod as (Hmod&_&_&_&_&_&_&Himpts&Hexpts).
    apply Forall2_length in Himpts. destruct mod_imports;[|done].
    simpl in Hexpts.
    apply Forall2_cons in Hexpts as [He _].
    unfold module_export_typing in He. simpl in He.
    destruct (modexp_desc m) eqn:Hm;[destruct f|by destruct t|by destruct m0|by destruct g].
    apply andb_true_iff in He as [Hle He].
    destruct (nth_error fts n) eqn:Hn;[|done].
    revert He. move/eqP=>He. subst f.
    iDestruct "Hn" as (name) "Hn".

    rewrite Heqadvm.
    iDestruct "Hinst_adv_res" as "(Hresf & Hrest & Hresm & Hresg) /=".
    rewrite /get_import_func_count
            /get_import_mem_count
            /get_import_table_count
            /get_import_global_count /=.
    rewrite !drop_0 -Heqadvm.
    rewrite nth_error_lookup in Hn.
    eapply Forall2_lookup_r in Hmod as [mf [Hmf Htypf]];[|eauto].
    destruct mf. simpl in Htypf.
    destruct modfunc_type. destruct Htypf as (Hlef & Hnthf & Htypf).
    revert Hlef. move/ssrnat.leP=>Hlef.
    assert (n0 < length mod_types) as Hlt;[lia|].
    rewrite Heqadvm /= in H.
    apply lookup_lt_is_Some in Hlt as [t Ht].
    rewrite - nth_error_lookup in Ht.
    erewrite nth_error_nth in Hnthf;eauto.
    revert Hnthf;move/eqP=>heq. subst t.
    iDestruct (big_sepL2_length with "Hresf") as %Hinstf_len.
    apply lookup_lt_Some in Hmf as Hlt'.
    rewrite Hinstf_len in Hlt'.
    apply lookup_lt_is_Some in Hlt' as [advf Hadv].
    iDestruct (big_sepL2_lookup_acc with "Hresf") as "[Hadvf Hcls]";[eauto..|].
    simpl.
    rewrite - nth_error_lookup in Hadv.
    rewrite H.
    erewrite !nth_error_nth;eauto.
    
    iDestruct "Hvis8" as (gr) "Hvis8".

    iDestruct "Hstack" as "(-> & Hstack)".
    
    iDestruct "Hstack" as (idf0 idf1 idf2 idf3 idf4 idf5 idt) "Hstack".
    iDestruct "Hstack" as (nm0 nm1 nm2 nm3 nm4 nm5 nm6 f0 f1 f2) "Hstack".
    iDestruct "Hstack" as (f3 f4 f5 istack l0 l1 l2 l3 l4 l5) "Hstack".
    iDestruct "Hstack" as (stacktab isStack newStackAddrIs) "Hstack".
    iDestruct "Hstack" as "(HimpsH & HimpsW & %Hnodup & %Htablen & HnewStackAddrIs 
    & #Hnewstack & #Hisempty & #Hisfull & #Hpop & #Hpush & #Hmap & #Hmaptrap)".

    rewrite irwt_nodup_equiv; last by apply NoDup_nil.
    iDestruct "HimpsW" as "(_ & Hidf0 & Hidf1 & Hidf2 & Hidf3 & Hidf4 & Hidf5 & Hidtab & _) /=".
     repeat (rewrite lookup_insert + (rewrite lookup_insert_ne;[|done])).
    iDestruct "Hidf0" as (cl0) "[Himpfcl0 Hcl0]".
    iDestruct "Hidf1" as (cl1) "[Himpfcl1 Hcl1]".
    iDestruct "Hidf2" as (cl2) "[Himpfcl2 Hcl2]".
    iDestruct "Hidf3" as (cl3) "[Himpfcl3 Hcl3]".
    iDestruct "Hidf4" as (cl4) "[Himpfcl4 Hcl4]".
    iDestruct "Hidf5" as (cl5) "[Himpfcl5 Hcl5]".
    iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl1") as "%H01" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl2") as "%H02" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl3") as "%H03" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl4") as "%H04" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl5") as "%H05" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl1 Himpfcl2") as "%H12" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl1 Himpfcl3") as "%H13" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl1 Himpfcl4") as "%H14" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl1 Himpfcl5") as "%H15" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl2 Himpfcl3") as "%H23" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl2 Himpfcl4") as "%H24" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl2 Himpfcl5") as "%H25" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl3 Himpfcl4") as "%H34" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl3 Himpfcl5") as "%H35" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl4 Himpfcl5") as "%H45" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Hadvf Himpfcl0") as "%Hadv0" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Hadvf Himpfcl1") as "%Hadv1" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Hadvf Himpfcl2") as "%Hadv2" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Hadvf Himpfcl3") as "%Hadv3" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Hadvf Himpfcl4") as "%Hadv4" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Hadvf Himpfcl5") as "%Hadv5" ; first by eauto.
    repeat (rewrite lookup_insert + (rewrite lookup_insert_ne;[|done])).
    iDestruct "Hcl0" as %[Heq1 Heq2];inversion Heq1;inversion Heq2;clear Heq1 Heq2.
    iDestruct "Hcl1" as %[Heq1 Heq2];inversion Heq1;inversion Heq2;clear Heq1 Heq2.
    iDestruct "Hcl2" as %[Heq1 Heq2];inversion Heq1;inversion Heq2;clear Heq1 Heq2.
    iDestruct "Hcl3" as %[Heq1 Heq2];inversion Heq1;inversion Heq2;clear Heq1 Heq2.
    iDestruct "Hcl4" as %[Heq1 Heq2];inversion Heq1;inversion Heq2;clear Heq1 Heq2.
    iDestruct "Hcl5" as %[Heq1 Heq2];inversion Heq1;inversion Heq2;clear Heq1 Heq2.
    subst cl0 cl1 cl2 cl3 cl4 cl5.
    iDestruct "Hidtab" as (tab tt) "[Hidtab [%Heq %Htt]]". inversion Heq;subst tab.

    iApply (wp_wand_host _ _ _ (λ v, _ ∗ ↪[frame]empty_frame)%I with "[-HΦ] [HΦ]");cycle 1.
    { iIntros (v) "[Hv Hframe]". iApply "HΦ". iExact "Hv". }

    iApply (instantiation_spec_operational_start with "[$Hemptyframe] [Hmod_lse HimpsH Himpfcl0 Himpfcl1 Himpfcl2 Himpfcl3 Himpfcl4 Himpfcl5 Hadvf Hidtab Hn Hgret Hvis8]")
    ; try exact client_module_typing;[eauto|..].
    { unfold module_restrictions.
      simpl.
      split; first by exists [].
      split; first by exists ([Wasm_int.int_of_Z i32m 0]).
      by exists [].
    }
    { iFrame. 
      instantiate (5:=[_;_;_;_;_;_;_;_;_]).
      iDestruct "HimpsH" as "($&$&$&$&$&$&$&_)". iFrame "Hn Hvis8".
      iSplitR;[done|].
      unfold instantiation_resources_pre_wasm.
      rewrite irwt_nodup_equiv => /=; last first.
      { clear - H01 H02 H03 H04 H05 H12 H13 H14 H15 H23 H24 H25 H34 H35 H45 Hadv0 Hadv1 Hadv2 Hadv3 Hadv4 Hadv5.
        repeat (apply NoDup_cons; split; cbn; first by set_solver).
        by apply NoDup_nil.
      }
      iSplitL;[|auto]. iSplitL.
      { iSplit.
        { iPureIntro.
          instantiate (1:={[g_ret := {| g_mut := MUT_mut; g_val := wret |} ]}).
          instantiate (1:=∅).
          instantiate (1:={[N.of_nat idt := stacktab]}).
          instantiate (1:= {[ N.of_nat idf0 := FC_func_native istack (Tf [] [T_i32]) l0 f0 ;
                          N.of_nat idf1 := FC_func_native istack (Tf [T_i32] [T_i32]) l1 f1 ;
                          N.of_nat idf2 := FC_func_native istack (Tf [T_i32] [T_i32]) l2 f2 ;
                          N.of_nat idf3 := FC_func_native istack (Tf [T_i32] [T_i32]) l3 f3 ;
                          N.of_nat idf4 := FC_func_native istack (Tf [T_i32; T_i32] []) l4 f4 ;
                          N.of_nat idf5 := FC_func_native istack (Tf [T_i32; T_i32] []) l5 f5 ;
                          N.of_nat advf := (FC_func_native inst_adv (Tf [T_i32] [T_i32]) modfunc_locals modfunc_body)]}).
          cbn. rewrite !dom_insert_L !dom_empty_L.
          rewrite N2Nat.id. auto. }
        cbn. repeat (rewrite lookup_insert + (rewrite lookup_insert_ne;[|done])).
        iSplitL "Himpfcl0";[iExists _;iFrame;auto|].
        iSplitL "Himpfcl1";[iExists _;iFrame;auto|].
        iSplitL "Himpfcl2";[iExists _;iFrame;auto|].
        iSplitL "Himpfcl3";[iExists _;iFrame;auto|].
        iSplitL "Himpfcl4";[iExists _;iFrame;auto|].
        iSplitL "Himpfcl5";[iExists _;iFrame;auto|].
        iSplitL "Hidtab";[iExists _,_;iFrame;eauto|].
        iSplitL "Hadvf";[iExists _;iFrame;auto|].
        iSplitL;[|done]. iExists _,_. rewrite N2Nat.id. iFrame.
        rewrite lookup_insert. repeat iSplit;eauto.
        iPureIntro. unfold global_agree. simpl. apply/eqP. auto.
      }
      unfold module_elem_bound_check_gmap,module_data_bound_check_gmap. cbn.
      iSplit;[|iPureIntro;apply Forall_nil].
      iPureIntro. apply Forall_cons.
      split;[|apply Forall_nil].
      simpl. rewrite lookup_insert;auto. done. done. cbn. done. }

    iIntros (idnstart) "Hf [Hmod_lse Hr]".
    iDestruct "Hr" as "((Himpf0 & Himpf1 & Himpf2 & Himpf3 & Himpf4 & Himpf5 & Htab & Hadvf & Hg) & Hr)".
    iDestruct "Hr" as (?) "[Hr' _]".
    unfold instantiation_resources_post_wasm.
    iDestruct "Hr'" as (? ? ? ? ? ?) "Hr'".
    rewrite irwt_nodup_equiv => /=; last first.
    { clear - H01 H02 H03 H04 H05 H12 H13 H14 H15 H23 H24 H25 H34 H35 H45 Hadv0 Hadv1 Hadv2 Hadv3 Hadv4 Hadv5.
      repeat (apply NoDup_cons; split; cbn; first by set_solver).
      by apply NoDup_nil.
    }
    iDestruct "Hr'" as "([%Hdom (Himpr0 & Himpr1 & Himpr2 & Himpr3 & Himpr4 & Himpr5 & Htabr & Hadv & Hgret & _)] & %Htypr & %Htab_inits & %Hwts'0 & %Hbounds_elemr & 
        %Hmem_initsr & %Hwms0' & %Hbounds_datar & %Hglobsr & %Hglob_initsr & Hr )".
    iDestruct "Hr" as "(Hr&_&_&_)".
    destruct Htypr as (Heq1&[? Heq2]&[? Heq3]&[? Heq4]&[? Heq6]&Heq5).
    rewrite Heq2.
    iSimpl in "Himpr0 Himpr1 Himpr2 Himpr3 Himpr4 Himpr5 Hadv Hgret Htabr".
    rewrite N2Nat.id. repeat (rewrite lookup_insert + (rewrite lookup_insert_ne;[|done])).

    iDestruct "Himpr0" as (cl0) "[Himpr0 [%Hcleq _]]";inversion Hcleq;clear Hcleq.
    iDestruct "Himpr1" as (cl1) "[Himpr1 [%Hcleq _]]";inversion Hcleq;clear Hcleq.
    iDestruct "Himpr2" as (cl2) "[Himpr2 [%Hcleq _]]";inversion Hcleq;clear Hcleq.
    iDestruct "Himpr3" as (cl3) "[Himpr3 [%Hcleq _]]";inversion Hcleq;clear Hcleq.
    iDestruct "Himpr4" as (cl4) "[Himpr4 [%Hcleq _]]";inversion Hcleq;clear Hcleq.
    iDestruct "Himpr5" as (cl5) "[Himpr5 [%Hcleq _]]";inversion Hcleq;clear Hcleq.
    subst cl0 cl1 cl2 cl3 cl4 cl5.
    iDestruct "Hadv" as (cladv) "[Hadv [%Hcleq %]]";inversion Hcleq;clear Hcleq.
    iDestruct "Hgret" as (g gt) "(Hgret & %Hlookg & %Hgteq & %Hagree)". inversion Hlookg;clear Hlookg.
    iDestruct (big_sepL2_length with "Hr") as %Himprlen.
    destruct x;[done|destruct x;[|done]].
    iDestruct "Hr" as "[Hr _] /=". rewrite Heq1 /=.
    iDestruct ("Hcls" with "Hadv") as "Hresf".
    iDestruct "Htabr" as (tab tt0) "(Htabr & %Hwts'look & %Htt0 & %Htabtyp)".
    inversion Htt0;subst tt0;clear Htt0.
    rewrite Hwts'0 in Hwts'look.
    apply module_import_init_tabs_Some in Hwts'look as HH; destruct HH as [? Hwtslook].
    eapply module_import_init_tabs_lookup in Hwtslook as Heqtab;[|eauto].
    rewrite lookup_singleton in Hwtslook. inversion Hwtslook;subst x.
    cbn in Heqtab. rewrite Heq3 in Heqtab. cbn in Heqtab.
    rewrite Nat2N.id decide_True /= // Heq2 /= in Heqtab.
    subst tab.
    
    iApply weakestpre.fupd_wp.
    iMod (interp_instance_alloc with "[] [] [] [] [Hrest Hresm Hresg Hresf]") as "[#Hi [[#Hires _] _]]";
      [apply Htyp|repeat split;eauto|eauto|..].
    3,4,5: by instantiate (1:=∅).
    { rewrite Heqadvm /=. auto. }
    { destruct Hglob_inits_vals as [? ?];eauto. }
    { instantiate (1:=∅).
      rewrite irwt_nodup_equiv; last by apply NoDup_nil.
      repeat iSplit;auto.
      rewrite module_import_init_tabs_dom. auto.
      rewrite module_import_init_mems_dom. auto.
    }
    { rewrite Htyp_inits Hmem_inits Hglob_inits
                  /module_inst_resources_wasm Heqadvm /=
                  /get_import_table_count
                  /get_import_mem_count
                  /get_import_global_count
                  /get_import_func_count /= !drop_0 -H.
      iFrame. 
    }
    cbn in Heq5. rewrite Heq2 /= in Heq5.
    revert Heq5;move/eqP=>Heq5. subst n1.
    iModIntro.

    iApply wp_lift_wasm.
    take_drop_app_rewrite 0.
    iApply (wp_invoke_native with "Hf Hr");[eauto|eauto..|].
    iNext. iIntros "[Hf Hidnstart]".
    iApply (wp_frame_bind with "Hf"). { cbn. auto. } iIntros "Hf".
    take_drop_app_rewrite 0. iApply (wp_block with "Hf");[auto..|].
    iNext. iIntros "Hf".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.
    iApply wp_ctx_bind;[simpl;auto|]. repeat erewrite app_nil_l.

    iApply (wp_wand with "[Hf Hgret Himpr0 Himpr3 Himpr4 Himpr5 Hown Htabr HnewStackAddrIs]").
    { iApply (main_spec with "[$Hi $Hf $Hown Himpr0 Himpr3 Himpr4 Himpr5 Htabr Hgret HnewStackAddrIs]").
      { simpl. auto. }
      { simpl. rewrite Heq6. simpl. eauto. }
      { simpl. rewrite Heq3. simpl. eauto. }
      1,2,3,4: rewrite /= Heq2 /=;eauto.
      { eauto. }
      { apply Htablen. }
      { unfold upd_local_label_return. simpl.
        rewrite Heqadvm /=.
        apply Htypf. }
      { iFrame. iSplit.
        { iDestruct (big_sepL2_lookup with "Hires") as "Ha".
          { rewrite Heqadvm /=. eauto. }
          { rewrite Heqadvm /= /get_import_func_count /= drop_0 /= -nth_error_lookup. eauto. }
          iSimpl in "Ha". erewrite H, nth_error_nth;eauto. }
        iSplitL "Hgret";[iExists _;rewrite N2Nat.id;iFrame|].
        iSplit. iExact "Hnewstack".
        iSplit. iExact "Hpush".
        iSplit. iExact "Hpop".
        iSplit. iExact "Hmaptrap".
        iFrame. }
      iIntros (v) "HH". iExact "HH".
    }
    iIntros (v) "[HH Hf]".
    iDestruct "Hf" as (f) "[Hf %Hfeq]".
    iDestruct "HH" as "[-> | [Hret | Hres]]".
    { take_drop_app_rewrite_twice 0 0.
      iApply (wp_wand_ctx with "[Hf]").
      { iApply (wp_trap_ctx with "Hf"). auto. }
      iIntros (v) "[-> Hf]".
      iExists f;iFrame.
      iIntros "Hf".
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗ _)%I with "[Hf]").
      { iApply (wp_frame_trap with "Hf"). iNext. auto. }
      iIntros (v) "[-> Hf]". iFrame.
      iApply weakestpre.wp_value. eapply of_to_val. eauto.
      by iLeft. }
    { iDestruct "Hret" as (vh) "[-> Hgret]".
      iSimpl.
      iIntros (LI HLI%lfilled_Ind_Equivalent). inversion HLI;inversion H30.
      iSimpl. erewrite app_nil_r. rewrite sfill_label.
      iApply iris_wp.wp_value.
      { unfold IntoVal. instantiate (1:=retV _). simpl of_val. eauto. }
      iExists _;iFrame. iIntros "Hf". iSimpl.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = immV []⌝ ∗ _)%I with "[Hf]").
      { iApply wp_frame_return.
        { instantiate (2:=[]). eauto. }
        1:auto.
        { erewrite <- (app_nil_l [AI_label _ _ _]).
          erewrite <- (app_nil_r [AI_label _ _ _]).
          apply lfilled_Ind_Equivalent. constructor. auto.
          apply lfilled_Ind_Equivalent.
          erewrite app_nil_l.
          apply sfill_to_lfilled. }
        iApply iris_wp.wp_value;[eapply iris.of_to_val;eauto|].
        iFrame. eauto. }
      iIntros (v) "[-> Hf]". iFrame.
      iApply weakestpre.wp_value. eapply of_to_val. eauto.
      iRight. iExists _. rewrite N2Nat.id. iFrame. }
    { iDestruct "Hres" as "[-> Hgret]".
      iSimpl. iApply (wp_val_return with "Hf");[auto..|].
      iIntros "Hf".
      iSimpl. iApply iris_wp.wp_value;[eapply iris.of_to_val;eauto|].
      iExists _;iFrame.
      iIntros "Hf".
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = immV []⌝ ∗ _)%I with "[Hf]").
      { iApply (wp_frame_value with "Hf");[eauto|auto|..].
        iNext. auto. }
      iIntros (v) "[-> Hf]". iFrame.
      iApply weakestpre.wp_value. eapply of_to_val. eauto.
      iRight. iDestruct "Hgret" as (v) "[Hgret Hown]".
      iExists v. rewrite N2Nat.id. iFrame "Hgret".
    }
  Qed.
  
End Client_instantiation.
