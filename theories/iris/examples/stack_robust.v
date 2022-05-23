From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_host iris_fundamental_helpers stack_specs stack_instantiation iris_interp_instance_alloc.
Require Export datatypes host operations properties opsem.

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
    exists [Tf [] []],[ (* {| tg_mut := MUT_mut; tg_t := T_i32 |} *)]. simpl.
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

Section Client_instantiation.
  Import DummyHost.

  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ,
        !logrel_na_invs Σ, HWP:host_program_logic,!hvisG Σ, !hmsG Σ}.

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

  Lemma instantiate_client adv_module g_ret wret :
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
          (∃ vs, 7%N ↪[vis] vs)
      }}}
        ((stack_adv_client_instantiate,[]) : host_expr)
      {{{ v, ⌜v = (trapV : host_val)⌝ ∨ ∃ v, g_ret ↦[wg] {| g_mut := MUT_mut; g_val := xx v|} }}} .
  Proof.
    iIntros (Htyp Hnostart Hrestrict Hboundst Hboundsm Hgrettyp).
    iModIntro. iIntros (Φ) "(Hgret & Hmod_stack & Hmod_adv & Hmod_lse & Hown & Hvis8 & 
                        Hvisvst & Hvis7) HΦ".
    iDestruct "Hvisvst" as (vs0 vs1 vs2 vs3 vs4 vs5 vs6) "Hvis".
    iApply (wp_seq_host_nostart with "[$Hmod_stack] [Hvis] ") => //.
    { iIntros "Hmod_stack".
      iApply weakestpre.wp_mono;cycle 1.
      iApply (instantiate_stack_spec with "[$]").
      { iFrame "Hvis". }
      iIntros (v) "[$ Hv]". iExact "Hv". }
    iIntros (w) "Hstack Hmod_stack".
    iApply (wp_seq_host_nostart with "[$Hmod_adv] [Hvis7] ") => //.
    { iIntros "Hmod_adv".
      iApply weakestpre.wp_mono.
      2: iApply (instantiation_spec_operational_no_start _ _ _ [] [] _ _ _ _ ∅ ∅ ∅ ∅);eauto;iFrame.
      2: cbn; repeat iSplit =>//.
      iIntros (v) "[$ Hv]". iExact "Hv".
      iPureIntro. destruct Htyp as [fts [gts Htyp]].
      destruct adv_module;simpl in *.
      destruct Htyp as (_&_&_&_&_&_&_&_&Htyp).
      apply Forall2_length in Htyp. auto. }

    iIntros (w') "[Himps Hinst_adv] Hmod_adv".
    iDestruct "Hinst_adv" as (inst_adv g_adv_inits t_adv_inits m_adv_inits glob_adv_inits wts' wms')
                               "(Himpstyp & %HH & %Htyp_inits & %Hwts' & %Hbounds_elem & %Hmem_inits 
                               & %Hwms' & %Hbounds_data & %Hglob_inits_vals & %Hglob_inits & Hinst_adv_res & Hadv_exports)".
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
    
    iDestruct "Hstack" as (idf0 idf1 idf2 idf3 idf4 idf5 idt) "Hstack".
    iDestruct "Hstack" as (nm0 nm1 nm2 nm3 nm4 nm5 nm6 f0 f1 f2) "Hstack".
    iDestruct "Hstack" as (f3 f4 f5 istack l0 l1 l2 l3 l4 l5) "Hstack".
    iDestruct "Hstack" as (stacktab isStack newStackAddrIs) "Hstack".
    iDestruct "Hstack" as "(HimpsH & HimpsW & %Htablen & HnewStackAddrIs 
    & #Hnewstack & #Hisempty & #Hisfull & #Hpop & #Hpush & #Hmap)".

    iDestruct "HimpsW" as "(_ & Hidf0 & Hidf1 & Hidf2 & Hidf3 & Hidf4 & Hidf5 & Hidtab & _) /=".
    repeat (rewrite lookup_insert + (rewrite lookup_insert_ne;[|done])).
    iDestruct "Hidf0" as (cl0) "[Himpfcl0 Hcl0]".
    iDestruct "Hidf1" as (cl1) "[Himpfcl1 Hcl1]".
    iDestruct "Hidf2" as (cl2) "[Himpfcl2 Hcl2]".
    iDestruct "Hidf3" as (cl3) "[Himpfcl3 Hcl3]".
    iDestruct "Hidf4" as (cl4) "[Himpfcl4 Hcl4]".
    iDestruct "Hidf5" as (cl5) "[Himpfcl5 Hcl5]".
    (* TODO: find solution to avoid the following *)
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
    { iIntros (v) "[Hv ?]". iApply "HΦ". iExact "Hv". }

    iApply (instantiation_spec_operational_start with "[Hmod_lse HimpsH Himpfcl0 Himpfcl1 Himpfcl2 Himpfcl3 Himpfcl4 
                                                 Himpfcl5 Hadvf Hidtab Hn Hgret Hvis8]")
    ; try exact client_module_typing;[eauto|..].
    { iFrame. 
      instantiate (1:=[_;_;_;_;_;_;_;_;_]).
      iDestruct "HimpsH" as "($&$&$&$&$&$&$&_)". iFrame "Hn Hvis8".
      iSplitR;[done|].
      instantiate (3:={[g_ret := {| g_mut := MUT_mut; g_val := wret |} ]}).
      instantiate (3:=∅).
      instantiate (2:={[N.of_nat idt := stacktab]}).
      instantiate (1:= {[ N.of_nat idf0 := FC_func_native istack (Tf [] [T_i32]) l0 f0 ;
                          N.of_nat idf1 := FC_func_native istack (Tf [T_i32] [T_i32]) l1 f1 ;                 
                          N.of_nat idf2 := FC_func_native istack (Tf [T_i32] [T_i32]) l2 f2 ;
                          N.of_nat idf3 := FC_func_native istack (Tf [T_i32] [T_i32]) l3 f3 ;
                          N.of_nat idf4 := FC_func_native istack (Tf [T_i32; T_i32] []) l4 f4 ;
                          N.of_nat idf5 := FC_func_native istack (Tf [T_i32; T_i32] []) l5 f5 ;
                          N.of_nat advf := (FC_func_native inst_adv (Tf [T_i32] [T_i32]) modfunc_locals modfunc_body)]}).
      cbn.  unfold client_glob_impts.
      iSplitL.
      { iSplit.
        { iPureIntro. cbn. rewrite !dom_insert_L !dom_empty_L.
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
      do 2 (iSplit;[done|]).
      unfold module_elem_bound_check_gmap,module_data_bound_check_gmap. cbn.
      iSplit;[|iPureIntro;apply Forall_nil].
      iPureIntro. apply Forall_cons.
      split;[|apply Forall_nil].
      simpl. rewrite lookup_insert;auto. done. done. }

    iIntros (idnstart) "Hf [Hmod_lse Hr]".
    iDestruct "Hr" as "((Himpf0 & Himpf1 & Himpf2 & Himpf3 & Himpf4 & Himpf5 & Htab & Hadvf & Hg) & Hr)".
    iDestruct "Hr" as (? ? ? ? ? ? ?) "([%Hdom (Himpr0 & Himpr1 & Himpr2 & Himpr3 & Himpr4 & Himpr5 & Htabr & Hadv & Hgret & _)] & %Htypr & %Htab_inits & %Hwts'0 & %Hbounds_elemr & 
        %Hmem_initsr & %Hwms0' & %Hbounds_datar & %Hglobsr & %Hglob_initsr & Hr & _)".
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
    iMod (interp_instance_alloc with "[] [] [] [] [Hrest Hresm Hresg Hresf]") as "[#Hi [#Hires _]]";
      [apply Htyp|repeat split;eauto|eauto|..].
    3,4,5: by instantiate (1:=∅).
    { rewrite Heqadvm /=. auto. }
    { destruct Hglob_inits_vals as [? ?];eauto. }
    { instantiate (1:=∅). repeat iSplit;auto.
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

    iApply wp_host_wasm;[apply HWEV_invoke|].
    take_drop_app_rewrite 0.
    iApply (wp_invoke_native with "Hf Hr");[eauto|eauto..|].
    iNext. iIntros "[Hf Hidnstart]".
    iApply (wp_frame_bind with "Hf"). iIntros "Hf".
    take_drop_app_rewrite 0. iApply (wp_block with "Hf");[auto..|].
    iNext. iIntros "Hf".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.
    iApply wp_ctx_bind;[simpl;auto|]. repeat erewrite app_nil_l.
    
    (* Next step: spec of the main function *)

  Admitted.
  
End Client_instantiation.
