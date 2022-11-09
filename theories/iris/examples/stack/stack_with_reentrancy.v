From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export stack_instantiation.
Require Export type_checker_reflects_typing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Client2.

 Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ, !logrel_na_invs Σ}. 

  
(* Functions from the stack module are : 
     0 - new_stack
     1 - is_empty
     2 - is_full
     3 - pop
     4 - push 
     5 - map
     6 - length *)
 (* Function 7 is a call_host that modifies the table *)
 (* Function 8 is main *)
 (* Function 9 is the square function *)
 (* Function 10 is the *2 function *)
 
  Definition main :=
    [ BI_call 0 ;
      BI_tee_local 0 ;
      i32const (-1) ;
      BI_relop T_i32 (Relop_i ROI_eq) ;
      (* If new_stack failed, set global v0 to -1 and return *)
      BI_if (Tf [] []) [i32const (-1) ; BI_set_global 0 ; BI_return] [] ;
      BI_get_local 0 ;
      i32const 4 ;
      BI_call 4 ; (* Push 4 onto the stack *)
      BI_get_local 0 ;
      i32const 6 ;
      BI_call 4 ; (* Push 6 onto the stack *)
      BI_get_local 0 ;
      i32const 0 ;
      BI_call 5 ; (* Map square onto the stack *)
      i32const 0 ;
      i32const 10 ;
      BI_call 7 ; (* Modify the table to now have *2 as the 0th function *)
      BI_get_local 0 ;
      i32const 0 ;
      BI_call 5 ; (* Map *2 onto the stack *)
      BI_get_local 0 ;
      BI_call 3 ; (* Pop 72 *)
      BI_get_local 0 ;
      BI_call 3 ; (* Pop 32 *)
      BI_binop T_i32 (Binop_i BOI_sub) ; (* Subtract the two, to get 40 *)
      BI_set_global 0 (* Assign the 0th gloabl to 40 *)
    ].

  Definition square :=
    [ BI_get_local 0 ;
      BI_get_local 0 ;
      BI_binop T_i32 (Binop_i BOI_mul) ].

  Definition times_two :=
    [ BI_get_local 0 ;
      i32const 2 ;
      BI_binop T_i32 (Binop_i BOI_mul) ]. 

  
  Definition client_module :=
    {|
      mod_types := [ Tf [] [] ; Tf [] [T_i32] ; Tf [T_i32] [T_i32] ;
                     Tf [T_i32 ; T_i32] [] ] ;
      mod_funcs :=
      [ {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := [T_i32] ;
          modfunc_body := main
        |} ;
        {|
          modfunc_type := Mk_typeidx 2 ;
          modfunc_locals := [] ;
          modfunc_body := square
        |} ;
        {|
          modfunc_type := Mk_typeidx 2 ;
          modfunc_locals := [] ;
          modfunc_body := times_two
        |}] ;
      mod_tables := [] ; (* the table is imported, and thus only mentioned later *)
      mod_mems := [] ;
      mod_globals := [ {| modglob_type := {| tg_t := T_i32 ;
                                            tg_mut := MUT_mut |} ;
                         modglob_init := [i32const 0] |} ] ;
      mod_elem := [ {| modelem_table := Mk_tableidx 0 ;
                      modelem_offset := [i32const 0] ;
                      modelem_init := [Mk_funcidx 9] |} ] ; (* the (imported) table originally contains the square function *)
      mod_data := [] ;
      mod_start := Some {| modstart_func := Mk_funcidx 8 |} ;
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
          imp_name := list_byte_of_string "stack_length" ;
          imp_desc := ID_func 2
        |} ;
        {| imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "table" ;
          imp_desc := ID_table {| tt_limits := {| lim_min := 1%N ; lim_max := None |} ;
                                 tt_elem_type := ELT_funcref |} |} ;
        {| imp_module := list_byte_of_string "Host" ;
          imp_name := list_byte_of_string "modify_table" ;
          imp_desc := ID_func 3 |} 
      ] ;
      mod_exports := [
        {|
          modexp_name := list_byte_of_string "answer" ;
          modexp_desc := MED_global (Mk_globalidx 0)
        |}
      ]
    |}.

  Lemma module_typing_client :
    module_typing client_module (expts ++ [ET_func (Tf [T_i32 ; T_i32] [])]) [ET_glob {| tg_t := T_i32 ; tg_mut := MUT_mut |} ].
  Proof.
    unfold module_typing => /=.
    exists [ Tf [] [] ; Tf [T_i32] [T_i32] ; Tf [T_i32] [T_i32] ],
      [ {| tg_t := T_i32 ; tg_mut := MUT_mut |} ].
    repeat split => //.
    repeat (apply Forall2_cons ; repeat split => //) => /=.
    { unfold main.
      rewrite (separate9 (BI_call _)).
      eapply bet_composition'.
      { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. }
      {
        rewrite (separate9 (i32const _)).
        eapply bet_composition'.
        { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. }
        { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. }
      }
    }
    { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. }
    { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. }
    - apply Forall2_cons.
      repeat split => //.
      by apply bet_const.
    - unfold module_elem_typing.
      apply Forall_cons.
      repeat split => //.
      apply bet_const.
    - unfold module_import_typing.
      repeat (apply Forall2_cons ; repeat split => //) => //=.
    - apply Forall2_cons.
      repeat split => //.
  Qed.

  Lemma module_restrictions_client:
    module_restrictions client_module.
  Proof.
    unfold module_restrictions.
    repeat split => //=.
    { by exists [VAL_int32 (Wasm_int.int_of_Z i32m 0)]. }
    { by exists [Wasm_int.int_of_Z i32m 0]. }
    { by exists []. }
  Qed.
  
  Definition stack_instantiate (exp_addrs : list N) (stack_mod_addr client_mod_addr : N) :=
    [ ID_instantiate (take 8 exp_addrs) stack_mod_addr [] ;
      ID_instantiate [exp_addrs !!! 8] client_mod_addr ((take 8 exp_addrs) ++ [(exp_addrs !!! 9)]) ].
  (* the 7th element is the host import *)

  Lemma instantiate_stack_client_spec (s: stuckness) E name idmodtab (exp_addrs: list N) (stack_mod_addr client_mod_addr: N) (ha_mod_table_addr: nat) :
    length exp_addrs = 10 -> 
  ↪[frame] empty_frame -∗
  stack_mod_addr%N ↪[mods] stack_module -∗
  client_mod_addr%N ↪[mods] client_module -∗
  own_vis_pointers (take 9 exp_addrs) -∗
     (* The next lines assert that the host import does indeed point to the desired
        modify_table host-instruction *)
     (exp_addrs !!! 9) ↪[vis] {| modexp_name := name ;
                  modexp_desc := MED_func (Mk_funcidx idmodtab) |} -∗
     N.of_nat idmodtab ↦[wf] FC_func_host (Tf [T_i32 ; T_i32] []) (Mk_hostfuncidx ha_mod_table_addr) -∗
     (N.of_nat ha_mod_table_addr) ↦[ha] HA_modify_table -∗

     
     WP ((stack_instantiate exp_addrs stack_mod_addr client_mod_addr , []) : host_expr)
     @ E
     {{ v, ⌜ v = immHV [] ⌝ ∗
              ↪[frame] empty_frame ∗
                stack_mod_addr ↪[mods] stack_module ∗
                 client_mod_addr ↪[mods] client_module ∗
                 ∃ idg name,
                   (exp_addrs !!! 8) ↪[vis] {| modexp_name := name ;
                                modexp_desc := MED_global (Mk_globalidx idg) |} ∗
                    (N.of_nat idg ↦[wg] {| g_mut := MUT_mut ; g_val := value_of_int 40%Z |} ∨
                       N.of_nat idg ↦[wg] {| g_mut := MUT_mut ; g_val := value_of_int (-1)%Z |}) }}.
Proof.
  iIntros (Hvisaddrlen) "Hemptyframe Hmod0 Hmod1 Hvis Hvishost Hwfcallhost Hha".
  
  do 11 (destruct exp_addrs => //); clear Hvisaddrlen.
  simpl.
  
  rewrite separate8.
  iDestruct (big_sepL_app with "Hvis") as "(Hvis & (Hvisglob & _))".
    iApply (wp_seq_host_nostart NotStuck
              with "[] [$Hmod0] [Hvis]") => //.
    2: { iIntros "Hmod0".
      iApply weakestpre.wp_mono ;
        last iApply (instantiate_stack_spec with "Hmod0 [Hvis]") => //.
      iIntros (v) "[Hvsucc [? H]]".
      iFrame.
      iCombine "Hvsucc H" as "H".
      by iApply "H".
    }
    { by iIntros "(% & ?)". }
    
    - iIntros (w) "Hes1 Hmod0".
      iDestruct "Hes1" as "(-> & Hes1)".
      iDestruct "Hes1" as (idf0 idf1 idf2 idf3 idf4 idf5 idf6 idt) "Hes1".
      iDestruct "Hes1" as (name0 name1 name2 name3 name4 name5 name6 name7) "Hes1".
      iDestruct "Hes1" as (f0 f1 f2 f3 f4 f5 f6) "Hes1".
      iDestruct "Hes1" as (i0) "Hes1".  
      iDestruct "Hes1" as (l0 l1 l2 l3 l4 l5 l6) "Hes1".
      iDestruct "Hes1" as (tab isStack nextStackAddrIs)
                            "(Himport & Himp_type & %Hnodup & %Hfnodup & %Htab & Hnextaddr & #Hspec0 & #Hspec1 & #Hspec2 & #Hspec3 & #Hspec4 & #Hspec5 & #Hspec6 & #Hspec7)".

      iFrame "Hmod0".
      iDestruct "Himp_type" as "(_ & Himpw0 & Himpw1 & Himpw2 & Himpw3 & Himpw4 & Himpw5 & Himpw6 & Htab & _)".
      iDestruct "Himpw0" as (cl0) "[Himpfcl0 %Hcltype0]".
      iDestruct "Himpw1" as (cl1) "[Himpfcl1 %Hcltype1]".
      iDestruct "Himpw2" as (cl2) "[Himpfcl2 %Hcltype2]".
      iDestruct "Himpw3" as (cl3) "[Himpfcl3 %Hcltype3]".
      iDestruct "Himpw4" as (cl4) "[Himpfcl4 %Hcltype4]".
      iDestruct "Himpw5" as (cl5) "[Himpfcl5 %Hcltype5]".
      iDestruct "Himpw6" as (cl6) "[Himpfcl6 %Hcltype6]".
      iDestruct "Htab" as (tab0 tt) "[Htab %Htab0]".

      apply (NoDup_fmap_2 N.of_nat) in Hfnodup; simpl in Hfnodup.
      
      remember (list_to_map _) as mtmp.
      rewrite -> Heqmtmp in *.
      rewrite -> list_to_map_zip_lookup in Hcltype0, Hcltype1, Hcltype2, Hcltype3, Hcltype4, Hcltype5, Hcltype6 => //.
      invert_cllookup Hcltype0 0.
      invert_cllookup Hcltype1 1.
      invert_cllookup Hcltype2 2.
      invert_cllookup Hcltype3 3.
      invert_cllookup Hcltype4 4.
      invert_cllookup Hcltype5 5.
      invert_cllookup Hcltype6 6.
      iDestruct (mapsto_ne with "Himpfcl0 Hwfcallhost") as "%Hne0".
      iDestruct (mapsto_ne with "Himpfcl1 Hwfcallhost") as "%Hne1".
      iDestruct (mapsto_ne with "Himpfcl2 Hwfcallhost") as "%Hne2".
      iDestruct (mapsto_ne with "Himpfcl3 Hwfcallhost") as "%Hne3".
      iDestruct (mapsto_ne with "Himpfcl4 Hwfcallhost") as "%Hne4".
      iDestruct (mapsto_ne with "Himpfcl5 Hwfcallhost") as "%Hne5".
      iDestruct (mapsto_ne with "Himpfcl6 Hwfcallhost") as "%Hne6".
      assert (NoDup (fmap N.of_nat [idf0; idf1; idf2; idf3; idf4; idf5; idf6; idmodtab])) as Hfnodup2.
      { simpl.
        rewrite separate7.
        apply NoDup_app; repeat split => //; last by apply NoDup_singleton.
        move => x Hin.
        by set_solver.
      }
      
      remember ((list_to_map
                     (zip
                        [N.of_nat idf0; N.of_nat idf1; N.of_nat idf2; N.of_nat idf3; N.of_nat idf4; 
                        N.of_nat idf5; N.of_nat idf6; N.of_nat idmodtab]
                        [FC_func_native i0 (Tf [] [T_i32]) l0 f0; FC_func_native i0 (Tf [T_i32] [T_i32]) l1 f1;
                        FC_func_native i0 (Tf [T_i32] [T_i32]) l2 f2; FC_func_native i0 (Tf [T_i32] [T_i32]) l3 f3;
                        FC_func_native i0 (Tf [T_i32; T_i32] []) l4 f4; FC_func_native i0 (Tf [T_i32; T_i32] []) l5 f5;
                        FC_func_native i0 (Tf [T_i32] [T_i32]) l6 f6; FC_func_host (Tf [T_i32; T_i32] []) (Mk_hostfuncidx ha_mod_table_addr) ]): gmap N function_closure)) as mtmp.
      
      iApply (instantiation_spec_operational_start with "[$Hemptyframe] [Hwfcallhost Hmod1 Himport Himpfcl0 Himpfcl1 Himpfcl2 Himpfcl3 Himpfcl4 Himpfcl5 Himpfcl6 Htab Hvisglob Hvishost]") ; try exact module_typing_client.
    - by unfold client_module.
    - by apply module_restrictions_client.
      (* Because of the extra host import, a lot of the clever work done 
         in stack_instantiation.v is now unusable, so we must destruct the 
         hypotheses that were useful in the no-reentrancy example *)
    - Opaque list_to_map.
      Opaque zip_with.
      unfold instantiation_resources_pre.
      unfold import_resources_host.
      instantiate (5 := [_;_;_;_;_;_;_;_;_]).
      iSplitL "Hmod1" ; first done.
      iSplitL "Himport Hvishost".
      iDestruct "Himport" as "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & _)".
      iFrame.
      done. 
    - unfold instantiation_resources_pre_wasm.
      unfold export_ownership_host => /=.
      instantiate ( 1 := ∅) .
      instantiate ( 1 := <[ N.of_nat idt := tab ]> ∅) .
      instantiate ( 1 := ∅) .
      iFrame "Hvisglob".
      instantiate (1 := mtmp).
      rewrite -> Heqmtmp.
      iSplitL. 2: { done. }
      rewrite irwt_nodup_equiv => //=.
      unfold import_resources_wasm_typecheck_sepL2. 
      repeat iSplit.
      { iPureIntro. rewrite dom_list_to_map. by rewrite fst_zip => //=. }
      simpl. by rewrite dom_insert.
      done. done.
      cbn.
      
      iSplitL "Himpfcl0"; first by resolve_cl_lookup 0. 
      iSplitL "Himpfcl1"; first by resolve_cl_lookup 1. 
      iSplitL "Himpfcl2"; first by resolve_cl_lookup 2. 
      iSplitL "Himpfcl3"; first by resolve_cl_lookup 3. 
      iSplitL "Himpfcl4"; first by resolve_cl_lookup 4. 
      iSplitL "Himpfcl5"; first by resolve_cl_lookup 5. 
      iSplitL "Himpfcl6"; first by resolve_cl_lookup 6. 
      iSplitL "Htab". {iExists _, _; iFrame. done. }
      iSplitL "Hwfcallhost"; first by resolve_cl_lookup 7. 
      done.
      iPureIntro ; unfold module_elem_bound_check_gmap ; simpl.
      apply Forall_cons.
      split ; last done.
      simpl.
      rewrite lookup_insert.
      done.
      iPureIntro ; unfold module_data_bound_check_gmap ; simpl ; done.
    - apply NoDup_fmap in Hfnodup2; last by lias.
      eapply (NoDup_fmap_2 (λ x, (MED_func (Mk_funcidx x)))) in Hfnodup2; simpl in Hfnodup2.
      { rewrite separate8.
        apply NoDup_app; repeat split => //; last by apply NoDup_singleton.
        intros; by set_solver.
      }
      Unshelve.
      2: { move => x y Heq. by inversion Heq. }
      
    - iIntros (idnstart) "Hf Hres".
      unfold instantiation_resources_post.
      iDestruct "Hres" as "(Hmod1 & Himphost & Hres)".
      iDestruct "Hres" as (inst) "[Hres Hexphost]".
      iDestruct "Hres" as (g_inits t_inits m_inits gms wts wms) "(Himpwasm & %Hinst & -> & -> & %Hbound & -> & -> & %Hbound' & Hginit & -> & Hexpwasm)".
      destruct Hinst as (Hinsttype & Hinstfunc & Hinsttab & Hinstmem & Hinstglob & Hstart).
      unfold module_inst_resources_wasm, module_export_resources_host => /=.
      destruct inst => /=.
      iDestruct "Hexpwasm" as "(Hexpwf & Hexpwt & Hexpwm & Hexpwg)".
      unfold module_inst_resources_func, module_inst_resources_tab,
        module_inst_resources_mem, module_inst_resources_glob => /=.
      unfold big_sepL2 => /=.
      do 9 (destruct inst_funcs as [| ? inst_funcs] ; first by iExFalso ; iExact "Hexpwf").
      simpl.
      iDestruct "Hexpwf" as "[Hwfcl Hexpwf]".
      destruct inst_funcs ; first by iExFalso ; iExact "Hexpwf".
      iDestruct "Hexpwf" as "[Hwfsq Hexpwf]".
      destruct inst_funcs ; first by iExFalso ; iExact "Hexpwf".
      iDestruct "Hexpwf" as "[Hwfdbl Hexpwf]".
      destruct inst_funcs ; last by iExFalso ; iExact "Hexpwf".
      destruct inst_memory ; last by iExFalso ; iExact "Hexpwm".

      destruct inst_globs as [| g inst_globs] ; 
        first by destruct g_inits ; iExFalso ; iExact "Hexpwg".
      destruct inst_globs ;
        last by destruct g_inits ; iExFalso ; iDestruct "Hexpwg" as "[_ Habs]" ;
        iExact "Habs".

      (* For inst_tab, we cannot rely on the same technique as for inst_funcs, 
         inst_memory and inst_globs, because we are importing one table and not 
         creating any table in this module. In other words "Hexpwt" is telling us
         [ drop 1 inst_tab ] should be [], but this only tells un inst_tab has length
         less than 1. We must rely on the Hinsttab hypothesis which tells us that
         the singleton list [idt] is a prefix of inst_tab. Now combined with "Hexpwt",
         we know inst_tab has length exactly one, *and* it is singleton list [idt]. *)
      (* It may seam here like we are getting more information than we did for
         inst_funcs, for which we currently only know its length but not its elements.
         In fact we will indeed need to use Hinstfunc later to get the exact value of
         the elements of inst_funcs, but because we both create and import functions, 
         "Hexpwf" was enough to get the length of inst_funcs. Furthermore, we will
         not need to know the exact elements of inst_func until further on, whereas
         to populate the table using elem, we will need to know that inst_tab contains
         exactly idt right at the next step.
       *)
       
      unfold ext_tab_addrs in Hinsttab ; simpl in Hinsttab.
      unfold prefix in Hinsttab.
      destruct Hinsttab as [ll Hinsttab].
      destruct inst_tab ; first done.
      inversion Hinsttab ; subst.
      destruct ll ; last by iExFalso ; iExact "Hexpwt".

      
      iDestruct "Hexphost" as "[Hexphost _]".
      iDestruct "Hexphost" as (nameh) "Hexphost" => /=.
      rewrite irwt_nodup_equiv => //; last first.
      { simpl.
        apply NoDup_fmap in Hfnodup2; last by lias.
        eapply (NoDup_fmap_2 (λ x, (MED_func (Mk_funcidx x)))) in Hfnodup2; simpl in Hfnodup2.
        { rewrite separate8.
          apply NoDup_app; repeat split => //; last by apply NoDup_singleton.
          intros; by set_solver.
        }
        Unshelve.
        move => x y Heq. by inversion Heq.
      }
      
      unfold import_resources_wasm_typecheck_sepL2 => /=.
      iDestruct "Himpwasm" as "(% & Himpw0 & Himpw1 & Himpw2 & Himpw3 & Himpw4 & Himpw5 & Himpw6 & Htab & Himpw7 & _)".
      iDestruct "Himpw0" as (cl0) "[Himpfcl0 %Hcltype0]".
      iDestruct "Himpw1" as (cl1) "[Himpfcl1 %Hcltype1]".
      iDestruct "Himpw2" as (cl2) "[Himpfcl2 %Hcltype2]".
      iDestruct "Himpw3" as (cl3) "[Himpfcl3 %Hcltype3]".
      iDestruct "Himpw4" as (cl4) "[Himpfcl4 %Hcltype4]".
      iDestruct "Himpw5" as (cl5) "[Himpfcl5 %Hcltype5]".
      iDestruct "Himpw6" as (cl6) "[Himpfcl6 %Hcltype6]".
      iDestruct "Himpw7" as (cl7) "[Himpfcl7 %Hcltype7]".
      remember (list_to_map _) as mtmp.
      rewrite -> Heqmtmp in *.
      rewrite -> list_to_map_zip_lookup in Hcltype0, Hcltype1, Hcltype2, Hcltype3, Hcltype4, Hcltype5, Hcltype6, Hcltype7 => //.
      invert_cllookup Hcltype0 0.
      invert_cllookup Hcltype1 1.
      invert_cllookup Hcltype2 2.
      invert_cllookup Hcltype3 3.
      invert_cllookup Hcltype4 4.
      invert_cllookup Hcltype5 5.
      invert_cllookup Hcltype6 6.
      invert_cllookup Hcltype7 7.
      
      (* Now for our last export (the table), we have a little more work to do,
         because we are populating it. This is where the knowledge of the exact
         elements of inst_tab (not just its length) is important *)
      clear Htab0.
      clear tab0 tt.
      iDestruct "Htab" as (tab0 tt) "[Htab %Htab0]".
      unfold module_import_init_tabs in Htab0.
      simpl in Htab0.
      do 2 rewrite lookup_insert in Htab0.
      destruct Htab0 as [Htab0 _] ; inversion Htab0 ; subst ; clear Htab0.
      
      simpl in * ; subst.

      (* And now we invoke Hinstfunc to get the exact values in list inst_func *)
      unfold ext_func_addrs in Hinstfunc ; simpl in Hinstfunc.
      unfold prefix in Hinstfunc.
      destruct Hinstfunc as [ll Hinstfunc].
      inversion Hinstfunc ; subst ; clear Hinstfunc.
    
      unfold table_init_replace_single.
      simpl.
      iDestruct "Htab" as "[Htab _]".
      simpl.
      replace (length (table_data tab)) with (length (Some f15 :: drop 1 (table_data tab))) ; last first => /=.
      rewrite drop_length.
      destruct (table_data tab) ; first by simpl in Htab ; clear - Htab ; lia.
      simpl.
      by rewrite Nat.sub_0_r.
      rewrite firstn_all.
      iDestruct "Htab" as "[Ht0 _]".

      iAssert (∃ v, N.of_nat g ↦[wg] {| g_mut := MUT_mut ; g_val := v |})%I
        with "[Hexpwg]" as "Hwg".
      { destruct g_inits ; iDestruct "Hexpwg" as "[?_]" ; by iExists _. }
      iDestruct "Hwg" as (vg) "Hwg".
        
      unfold check_start in Hstart.
      simpl in Hstart.
      move/eqP in Hstart.
      inversion Hstart ; subst ; clear Hstart.
      iApply wp_lift_wasm.
      
      iApply wp_wand_r.
      iSplitR "Hmod1 Hha Himpfcl1 Himpfcl2 Himpfcl3". 
      rewrite - (app_nil_l [AI_invoke idnstart]).
      iApply (wp_invoke_native with "Hf Hwfcl").
      done. done. done.
      iIntros "!> [Hf Hwfcl]".
      iApply (wp_frame_bind with "Hf").
      done. iIntros "Hf".
      rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
      iApply (wp_block with "Hf").
      done. done. done. done.
      iIntros "!> Hf".
      iApply (wp_label_bind with
               "[Hwg Ht0 Hwfsq Hwfdbl Hf Himpfcl0 Himpfcl4 Himpfcl5 Hexphost Hnextaddr Himpfcl7]") ; last first.
      iPureIntro.
      unfold lfilled, lfill => /=.
      instantiate (5 := []) => /=.
      rewrite app_nil_r.
      done.

      (* Clearing away some premises to improve compilation time *)
      all: clear Hinstmem Hinstglob H Hnodup Hfnodup Hfnodup2 Hne0 Hne1 Hne2 Hne3 Hne4 Hne5 Hne6 Hbound Hbound' Htab Hinsttab name0 name1 name2 name3 name4 name5 name6 name7 n n0 n1 n2 n3 n4 n5 n6.
      all: iClear "Hspec1 Hspec2 Hspec6 Hspec7".
      
      (* Proving spec of the client main *)
      { rewrite (separate1 (AI_basic (BI_call 0)) (_ :: _)).
        iApply wp_seq.
        iSplitR ; last first.
        iSplitL "Hnextaddr Hf Himpfcl0".
        { iApply (wp_call with "Hf").
          done.
          iIntros "!> Hf".
          iApply ("Hspec0" with "[Hf Hnextaddr Himpfcl0]").
          iFrame.
          repeat iSplit ; iPureIntro => //.
          unfold page_size. unfold N.divide.
          exists 0%N. 
          done.
          iIntros (v0) "(H & Himpfcl0 & Hf)".
          iFrame.
          instantiate (1 := λ v0, (((⌜v0 = immV [value_of_int (-1)%Z]⌝ ∗
                                    (nextStackAddrIs 0)) ∨  (∃ k, ⌜ v0 = immV [value_of_uint k] ⌝ ∗ ⌜ (0 <= k <= ffff0000)%N ⌝ ∗ isStack k [] ∗ nextStackAddrIs (0+N.to_nat page_size))) ∗ 
                                     N.of_nat idf0↦[wf]FC_func_native i0 (Tf [] [T_i32]) l0 f0 ∗ ↪[frame] _)%I). 
          by iFrame. }
        2:{ iIntros "([(%Habs & ?) | (%k & %Habs & ?)] & ? & ?)"; by inversion Habs. }

        iIntros (w) "(H & (Hcl & Hf))".
        
        iDestruct "H" as "[(-> & Hnextaddr) | (%k & -> & %Hkb & Hstack & Hnextaddr)]".
        (* new_stack failed *)
        { iSimpl.
          rewrite (separate2 (AI_basic _)).
          iApply wp_seq; iSplitR; last iSplitL "Hf".
          2: { iApply (wp_tee_local with "Hf").
               iIntros "!> Hf".
               instantiate (1 := λ w, (⌜ w = immV [value_of_int (-1)] ⌝ ∗ ↪[frame] _)%I).
               rewrite (separate1 (AI_basic (i32const _))).
               iApply wp_val_app => //.
               iSplitR.
               2: { 
                 iApply (wp_set_local with "[] [$Hf]") => /=; first lia.
                 iIntros "!>".
                 iPureIntro.
                 done.
               }
               { iIntros "!> (%Habs & _)"; by inversion Habs. }
          }
          { iIntros "(%Habs & _)"; by inversion Habs. }
          iSimpl.
          
          iIntros (w) "(-> & Hf)".
          iSimpl.
          rewrite (separate3 (AI_basic (BI_const _))).
          iApply wp_seq.
          iSplitR; last iSplitL "Hf".
          2: {
            iApply (wp_relop with "Hf") => //=.
            instantiate (1 := λ v, ⌜ v = immV _⌝%I).
            iIntros "!>".
            iPureIntro.
            done.
          }
          { iIntros "(%Habs & _)"; by inversion Habs. }
          
          iIntros (w) "[-> Hf]".
          iSimpl.
        
          rewrite (separate2 _ (AI_basic (BI_if _ _ _))).
          iApply wp_seq.
          iSplitR; last iSplitL "Hf Hwg".
          2: {
            iApply (wp_if_true with "Hf"); first clear => //.
            iIntros "!> Hf".
            instantiate (1:= λ v1, ((⌜ exists sh, v1 = retV sh ⌝ ∗ N.of_nat g↦[wg] {| g_mut := MUT_mut ; g_val := value_of_int (-1)%Z |}) ∗ ↪[frame] _)%I ).         
            rewrite - (app_nil_l [AI_basic _]).
            iApply (wp_block with "Hf"); try by clear.
            
            iIntros "!> Hf".
            iSimpl.
            iApply (wp_label_bind with "[Hf Hwg]") ; last first.
            iPureIntro.
            unfold lfilled, lfill.
            instantiate (4 := []) => /=.
            rewrite app_nil_r.
            done.
            rewrite (separate2 (AI_basic (i32const _))).
            iApply wp_seq.
            iSplitR ; last first.
            iSplitL.
            iApply (wp_set_global with "[] Hf Hwg").
            done.
            instantiate (1 := λ v, ⌜ v = immV [] ⌝%I ).
            done.
            iIntros (w0) "[-> [Hwg Hf]]".
            iSimpl.
            iApply wp_value.
            unfold IntoVal.
              by apply of_to_val.
              iIntros (lh) "%Hfill".
              unfold lfilled, lfill in Hfill ; simpl in Hfill.
              move/eqP in Hfill; subst.
              iApply wp_value.
              unfold IntoVal.
                by apply of_to_val.
                iFrame.
                iPureIntro ; by eexists _.
                  by iIntros "[%Habs _]".
          }
          {
            iIntros "((%Habs & _) & _)"; by inversion Habs.
          }
          
          iIntros (w).
          iIntros "((%Habs & Hwg) & Hf)".
          destruct Habs as [sh ->].
          iSimpl.
          iApply wp_value.
          unfold IntoVal.
          apply iris.of_to_val.
          rewrite extend_retV.
          done.
          iIntros (lh) "%Hfill".
          unfold lfilled, lfill in Hfill.
          simpl in Hfill.
          move/eqP in Hfill; subst.
          iApply wp_value.
          unfold IntoVal.
          remember (sh_append sh _) as shret.
          apply iris.of_to_val.
          unfold iris.to_val => /=.
          specialize (iris.to_of_val (retV shret)) as Hv.
          unfold iris.to_val, iris.to_val, iris.of_val in Hv.
          rewrite app_nil_r.
          destruct (merge_values_list _); by subst; inversion Hv.
          iExists _.
          iFrame.
          iIntros "Hf".
          iApply wp_return.
          3:{ unfold of_val.
              instantiate (1 := []).
              apply sfill_to_lfilled. } 
          done.
          done.
          iApply wp_value.
          unfold IntoVal.
          by apply of_to_val.
          iFrame.
          instantiate (1 := λ x, (( _ ∗
                                      ((∃ k, ⌜ (0 <= k <= ffff0000)%N ⌝ ∗ ⌜ x = callHostV _ _ _ _ ⌝ ∗ nextStackAddrIs _ ∗  _ ↦[wg] _ ∗ isStack k _)
                                            ∨ ⌜ x = immV [] ⌝ ∗ _ ↦[wg] {| g_mut := MUT_mut; g_val := value_of_int (-1) |})))%I).
          iIntros "!>".
          iCombine "Hwfdbl Hexphost Hcl Himpfcl4 Himpfcl5 Himpfcl7 Ht0 Hwfsq" as "H".
          iSplitL "H"; first by iApply "H".
          iRight.
          by iFrame.
        }
        (* new_stack succeeded *)
        {
          iSimpl.
          rewrite (separate2 (AI_basic _)).
          iApply wp_seq; iSplitR; last iSplitL "Hf".
          2: { iApply (wp_tee_local with "Hf").
               iIntros "!> Hf".
               instantiate (1 := λ w, (⌜ w = immV [value_of_uint k] ⌝ ∗ ↪[frame] _)%I).
               rewrite (separate1 (AI_basic (BI_const _))).
               iApply wp_val_app => //.
               iSplitR.
               2: { 
                 iApply (wp_set_local with "[] [$Hf]") => /=; first lia.
                 iIntros "!>".
                 iPureIntro.
                 done.
               }
               { iIntros "!> (%Habs & _)"; by inversion Habs. }
          }
          { iIntros "(%Habs & _)"; by inversion Habs. }
          iSimpl.
          
          iIntros (w) "(-> & Hf)".
          iSimpl.
          rewrite (separate3 (AI_basic (BI_const _))).
          iApply wp_seq.
          iSplitR; last iSplitL "Hf".
          2: {
            iApply (wp_relop with "Hf") => //=.
            instantiate (1 := λ v, ⌜ v = immV _⌝%I).
            iIntros "!>".
            iPureIntro.
            done.
          }
          { iIntros "(%Habs & _)"; by inversion Habs. }
          
          iIntros (w) "[-> Hf]".
          iSimpl.
        
          rewrite (separate2 _ (AI_basic (BI_if _ _ _))).
          iApply wp_seq.
          iSplitR; last iSplitL "Hf Hwg".
          2: {
            iApply (wp_if_false with "Hf").
            rewrite Wasm_int.Int32.eq_false => //.
            move => H.
            clear - Hkb H.
            rewrite (Wasm_int.Int32.repr_add_modulus (-1)) in H.
            rewrite u32_modulus in H.
            apply Wasm_int.Int32.repr_inv in H; (try by unfold ffff0000 in Hkb; lias); (by rewrite u32_modulus; unfold ffff0000 in Hkb; lias).
            iIntros "!> Hf".
            instantiate (1:= λ v1, ((⌜ v1 = immV [] ⌝ ∗ N.of_nat g↦[wg] {| g_mut := MUT_mut ; g_val := vg |}) ∗ ↪[frame] _)%I ).         
            rewrite - (app_nil_l [AI_basic _]).
            iApply (wp_block with "Hf"); try by clear.
            
            iIntros "!> Hf".
            simpl.
            iApply (wp_label_bind with "[Hf Hwg]") ; last first.
            iPureIntro ; unfold lfilled, lfill.
            instantiate (4 := []) => /=.
            rewrite app_nil_r.
            done.
            iApply wp_value.
            unfold IntoVal ; by apply of_to_val.
            iSimpl.
            iIntros (lh) "%Hfill".
            unfold lfilled, lfill in Hfill ; simpl in Hfill.
            move/eqP in Hfill; subst.
            iApply (wp_label_value with "Hf").
            done.
            { iIntros "!>".
              iFrame.
              iPureIntro.
              done.
            }
          }
          { iIntros "((%Habs & _) & _)"; clear - Habs; by inversion Habs. }
          
          iIntros (w0) "[[-> Hwg] Hf]".
          iSimpl.
          rewrite (separate1 (AI_basic _)).
          iApply wp_seq; iSplitR; last iSplitL "Hf".
          2: { iApply wp_get_local => //.
               { done. }
               { instantiate (1 := λ v, ⌜ v = immV _⌝%I). iIntros "!>"; iPureIntro => //. }
          }
          { iIntros "(%Habs & _)"; by inversion Habs. }
          
          iIntros (w0) "[-> Hf]".
          iSimpl.
          rewrite (separate3 (AI_basic _)).
          iApply wp_seq.
          iSplitR; last iSplitL "Himpfcl4 Hf Hstack".
          2: {
            rewrite (separate2 (AI_basic _)).
            rewrite - (app_nil_r [AI_basic (BI_call 4)]).
            iApply wp_wasm_empty_ctx.
            iApply wp_base_push => //.
            iApply (wp_call_ctx with "Hf") => //=.
            iIntros "!> Hf".
            iApply wp_base_pull.
            rewrite app_nil_r.
            iApply wp_wasm_empty_ctx.
            iApply ("Hspec4" with "[Hf Himpfcl4 Hstack]").
            iFrame.
            iSimpl.
            repeat iSplit ; iPureIntro => //.
            
            iIntros (w0) "(-> & Hs & Himpfcl4 & Hf)".
            instantiate (1 := λ v, ((⌜ v = immV [] ⌝ ∗
                                             isStack k [ (Wasm_int.int_of_Z i32m 4)] ∗
                                             N.of_nat idf4↦[wf]FC_func_native i0 (Tf [T_i32 ; T_i32] []) l4 f4) ∗ ↪[frame] _)%I).
            by iFrame.
          }
          { iIntros "((%Habs & _) & _)". by inversion Habs. }
        
          iIntros (w0) "[(-> & Hs & Himpfcl4) Hf]".
          iSimpl.
          rewrite (separate1 (AI_basic _)).
          iApply wp_seq; iSplitR; last iSplitL "Hf".
          2: { iApply wp_get_local => //.
               { done. }
               { instantiate (1 := λ v, ⌜ v = immV _⌝%I). iIntros "!>"; iPureIntro => //. }
          }
          { iIntros "(%Habs & _)"; by inversion Habs. }
          
          iIntros (w0) "[-> Hf]".
          iSimpl.
          rewrite (separate3 (AI_basic _)).
          iApply wp_seq.
          iSplitR; last iSplitL "Himpfcl4 Hf Hs".
          2: {
            rewrite (separate2 (AI_basic _)).
            rewrite - (app_nil_r [AI_basic (BI_call 4)]).
            iApply wp_wasm_empty_ctx.
            iApply wp_base_push => //.
            iApply (wp_call_ctx with "Hf") => //=.
            iIntros "!> Hf".
            iApply wp_base_pull.
            rewrite app_nil_r.
            iApply wp_wasm_empty_ctx.
            iApply ("Hspec4" with "[Hf Himpfcl4 Hs]").
            iFrame.
            iSimpl.
            repeat iSplit ; iPureIntro => //.
            
            iIntros (w0) "(-> & Hs & Himpfcl4 & Hf)".
            instantiate (1 := λ v, ((⌜ v = immV [] ⌝ ∗
                                             isStack k _ ∗
                                             N.of_nat idf4↦[wf]FC_func_native i0 (Tf [T_i32 ; T_i32] []) l4 f4) ∗ ↪[frame] _)%I).
            by iFrame.
          }
          { iIntros "((%Habs & _) & _)". by inversion Habs. }
          

          iIntros (w0) "[(-> & Hs & Himpfcl4) Hf]".
          iSimpl.
          rewrite (separate1 (AI_basic _)).
          iApply wp_seq; iSplitR; last iSplitL "Hf".
          2: { iApply wp_get_local => //.
               { done. }
               { instantiate (1 := λ v, ⌜ v = immV _⌝%I). iIntros "!>"; iPureIntro => //. }
          }
          { iIntros "(%Habs & _)"; by inversion Habs. }

          
          iIntros (w0) "[-> Hf]".
          iSimpl.
          rewrite (separate3 (AI_basic _)).
          iApply wp_seq.
          iSplitR; last iSplitL "Himpfcl5 Hf Hs Ht0 Hwfsq".
          2: {
            rewrite (separate2 (AI_basic _)).
            rewrite - (app_nil_r [AI_basic (BI_call 5)]).
            iApply wp_wasm_empty_ctx.
            iApply wp_base_push => //.
            iApply (wp_call_ctx with "Hf"); first done.
            iIntros "!> Hf".
            iApply wp_base_pull.
            rewrite app_nil_r.
            iApply wp_wasm_empty_ctx.
            iApply ("Hspec5" with "[Hf Himpfcl5 Hs Ht0 Hwfsq]").
            iFrame.
            instantiate (2 := λ x, True%I).
            iSimpl.
            repeat iSplit => //.
            iIntros (u fc) "!>".
            iIntros (?) "(_ & -> & Hf & Ht & Hcl)".
            iIntros "HΦ".
            rewrite (separate1 _ [AI_invoke _]).
            iApply wp_wand_r.
            iSplitL "Hf Hcl".
            iApply (wp_invoke_native with "Hf Hcl") => //.
            iIntros "!> [Hf Hcl]".
          iApply (wp_frame_bind with "Hf").
          done. iIntros "Hf".
          rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
          iApply (wp_block with "Hf") => //.
          
          iIntros "!> Hf".
          iApply (wp_label_bind with "[Hf Hcl]") ; last first.
          iPureIntro.
          unfold lfilled, lfill.
          instantiate (4 := []) => /=.
          by rewrite app_nil_r.
          rewrite (separate1 (AI_basic _)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf".
          iApply (wp_get_local with "[] [$Hf]").
          done.
          by instantiate (1 := λ x, ⌜x = immV _⌝%I).
          iIntros (w0) "[-> Hf]".
          iSimpl.
          rewrite (separate2 (AI_basic _)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf".
          rewrite (separate1 (AI_basic _)).
          iApply wp_val_app ; first done.
          iSplitR ; last first.
          iApply wp_wand_r.
          iSplitL.
          iApply (wp_get_local with "[] [$Hf]").
          done.
          by instantiate (1 := λ x, ⌜x = immV _⌝%I).
          iIntros (v0) "[-> Hf]".
          by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
          by iIntros "!> [% _]".
          iIntros (w0) "[-> Hf]".
          iSimpl.
          iApply wp_wand_r.
          iSplitL "Hf".
          iApply (wp_binop with "Hf").
          done.
          by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
          iIntros (v0) "[-> Hf]".
          iSimpl.
          iIntros (lh) "%Hlh".
          unfold lfilled, lfill in Hlh ; simpl in Hlh.
          move/eqP in Hlh.
          subst lh.
          iApply wp_wand_r.
          iSplitL "Hf".
          iApply (wp_label_value with "Hf") ; first done.
          by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
          iIntros (v0) "[-> Hf]".
          iExists _.
          iFrame.
          iIntros "Hf".
          iSimpl.
          iApply (wp_frame_value with "Hf") ; first done.
          done.
          iNext.
          by instantiate (1 := λ x, (⌜ x = immV _⌝ ∗ N.of_nat f15 ↦[wf] _)%I) ; iFrame.
          all : try by iIntros "[% _]".

          
          instantiate (1 := (λ x y, ⌜y = Wasm_int.Int32.imul x x⌝%I)).
          iIntros (v0) "[[-> Hcl] Hf]".
          iApply "HΦ".
          iFrame.
          iExists _.
          iSplit => //.
          
          iIntros (w0) "(-> & H & Hwimpcl5 & Hf & Ht & Ha)".
          iDestruct "H" as (s') "[Hs Hs']".
          destruct s' ; first by iExFalso ; iExact "Hs'".
          iDestruct "Hs'" as "[-> Hs']".
          destruct s' ; first by iExFalso ; iExact "Hs'".
          iDestruct "Hs'" as "[-> Hs']".
          destruct s' ; last by iExFalso ; iExact "Hs'".
          by instantiate (1 := λ x, ((⌜ x = immV _ ⌝ ∗ isStack _ _ ∗ N.of_nat idf5 ↦[wf] _ ∗ (N.of_nat idt) ↦[wt][_] _ ∗ N.of_nat f15 ↦[wf] _) ∗ ↪[frame] _)%I) ; iFrame.
          }
          { iIntros "((%Habs & _) & _)"; by inversion Habs. }
        
          iIntros (w0) "[(-> & Hs & Himpfcl5 & Ht & Hfsquare) Hf]".
          iSimpl.
          rewrite (separate3 (AI_basic _)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf Himpfcl7".
          rewrite (separate2 (AI_basic _)).
          rewrite - (app_nil_r [AI_basic (BI_call _)]).
          iApply wp_wasm_empty_ctx.
          iApply wp_base_push => //.
          iApply (wp_call_ctx with "Hf") => //.
          iIntros "!> Hf".
          iApply wp_base_pull.
          rewrite app_nil_r.
          iApply wp_wasm_empty_ctx.
          iApply (wp_invoke_host with "Himpfcl7 Hf").
          instantiate (1 := [_;_]) => //.
          done.
          done.
          iIntros "!> Himpfcl6 Hf".
          iApply wp_value.
          unfold IntoVal.
          apply of_to_val => //.
          iFrame.
          by instantiate (1 := λ x, (⌜ x = callHostV _ _ _ _ ⌝ ∗ _ ↦[wf] _∗ ↪[frame] _)%I) ; iFrame.
            
          iIntros (w0) "(-> & Himpfcl7 & Hf)".
          iApply wp_value.
          unfold IntoVal.
          apply of_to_val => //=.
          simpl.
          iIntros (lh) "%Hfill".
          unfold lfilled, lfill in Hfill ; simpl in Hfill.
          move/eqP in Hfill.
          subst lh.
          
          iApply wp_value.
          unfold IntoVal ; apply of_to_val => //=.
          simpl.
          iExists _.
          iFrame.
          iIntros "Hf".
          iApply wp_value.
          unfold IntoVal ; apply of_to_val => //=.
          simpl.
          iFrame.
          iLeft.
          iExists k.
          by iFrame.
          by iIntros "[% _]".
        }
      }
      
      
      iIntros (w0) "(((Hf16 & Hvis8 & Himpfcl0 & Himpfcl4 & Himpfcl5 & Hmodtab & Himpidt & Hf15) & H) & Hf)".
      iDestruct "H" as "[[%k (% & -> & Hnextaddr & Hwg & Hs)] | [-> Hwg]]".
      simpl.
      iApply wp_call_host_modify_table ; last first.
      rewrite <- (N2Nat.id 0). iFrame.
      instantiate (3 := Wasm_int.int_of_Z i32m 0%Z).
      simpl. iFrame.
      iIntros "!> (Hf & Ha & Hwt)".
      5:{ instantiate (3 := LL_local [] _ _ (LL_label [] _ _ (LL_base [] _) []) []).
          simpl. done. }
      all: try done. 
      simpl. 
      iApply wp_lift_wasm.
      iApply (wp_frame_bind with "Hf"). done.
      iIntros "Hf".
      iApply (wp_label_bind with "[Hf Hwg Himpfcl5 Himpfcl3 Hs Hwt Hf16 Hvis8]") ; last first.
      iPureIntro.
      unfold lfilled, lfill => //=.
      instantiate (5 := []) => //=.
      by rewrite app_nil_r.

      rewrite (separate1 (AI_basic _)).
      iApply wp_seq.
      iSplitR; last iSplitL "Hf".
      2: { iApply wp_get_local => //.
           { by simpl. }
           { iNext. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I). }
      }
      { iIntros "(%Habs & _)"; by inversion Habs. }

      iIntros (w) "(-> & Hf)".
      iSimpl.
      
      rewrite (separate3 (AI_basic _)).
      iApply wp_seq.
      iSplitR ; last first.
      rewrite (separate2 (AI_basic _)).
      iSplitR "Hvis8 Himpfcl3 Hwg".
      rewrite (separate2 (AI_basic _)).
      rewrite - (app_nil_r [AI_basic (BI_call _)]).
      iApply wp_wasm_empty_ctx.
      iApply wp_base_push => //.
      iApply (wp_call_ctx with "Hf") => //.
      iIntros "!> Hf".
      iApply wp_base_pull.
      rewrite app_nil_r.
      iApply wp_wasm_empty_ctx.
      simpl. 
      iApply ("Hspec5" with "[Himpfcl5 Hf Hs Hf16 Hwt]"). iFrame.
      repeat iSplit => //.
      instantiate (1 := λ x, ⌜ (0 <= (Wasm_int.Int32.intval x) < 65536%Z)%Z ⌝%I).
      done.
      
      iIntros (u f) "!>".
      iIntros (Φ) "(% & -> & Hf & Hwt & Hf16) HΦ".
      rewrite (separate1 (AI_basic _)).
      iApply (wp_invoke_native with "Hf Hf16"). done.
      done. done.
      iIntros "!> [Hf Hf16]".
      iApply (wp_frame_bind with "Hf"). done.
      iIntros "Hf".
      rewrite - (app_nil_l [AI_basic _]).
      iApply (wp_block with "Hf") => //.
      iIntros "!> Hf".
      iApply (wp_label_bind with "[Hf HΦ Hwt Hf16]") ; last first.
      iPureIntro. unfold lfilled, lfill.
      instantiate (6 := []) => /=.
      by rewrite app_nil_r.
      rewrite (separate1 (AI_basic _)).
      iApply wp_seq.
      iSplitR ; last first.
      iSplitL "Hf".
      iApply (wp_get_local with "[] [$Hf]").
      done. by instantiate (1 := λ x, ⌜x = immV _⌝%I).
      iIntros (w0) "[-> Hf]".
      iApply wp_wand_r. iSplitL "Hf". iApply (wp_binop with "Hf").
      done. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
      iIntros (v) "[-> Hf]".
      simpl.
      iIntros (lh) "%".
      unfold lfilled, lfill in H1. simpl in H1.
      move/eqP in H1; subst lh.
      iApply wp_wand_r. iSplitL "Hf". iApply (wp_label_value with "Hf").
      done. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
      iIntros (v) "[-> Hf]".
      iExists _ ; iFrame ; iIntros "Hf".
      simpl. iApply wp_wand_r. iSplitL "Hf".
      iApply (wp_frame_value with "Hf"). done.
      done. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
      iIntros (v) "[-> Hf]".
      iApply "HΦ".
      iFrame. iExists _. iSplit ; first done.
      unfold spec5_stack_map. 
      instantiate ( 1 := λ x y, ⌜ (Wasm_int.Int32.intval y = 2 * Wasm_int.Int32.intval x)%Z ⌝%I ).
      simpl. iPureIntro. 
      rewrite Wasm_int.Int32.Z_mod_modulus_eq.
      rewrite Z.mod_small.
      unfold Wasm_int.Int32.unsigned. 
      lia.
      unfold Wasm_int.Int32.unsigned.
      remember (Wasm_int.Int32.intval u) as x.
      clear - H0.
      unfold two16 in H0.
      destruct H0.
      rewrite u32_modulus.
      split; try lias.
      iIntros "(%Habs & _)"; by inversion Habs.
      
      iIntros (w0) "[-> H]".
      instantiate (1 := λ x, (⌜ x = immV [] ⌝ ∗ _)%I).
      iSplitR ; first done.
      iExact "H".
      iIntros (w0) "(-> & H & Himpfcl5 & Hf & Hwt & Hf16)".
      iDestruct "H" as (s') "[Hs Hs']".
      destruct s'; first by iExFalso ; iExact "Hs'".
      destruct s'; first iExFalso.
      by iDestruct "Hs'" as "[_ %]".
      destruct s' ; last first. 
      simpl. by iDestruct "Hs'" as "(_ & _ & %)".
      iDestruct "Hs'" as "(% & % & _)".
      simpl in H0. simpl in H1. simpl. 
      rewrite (separate1 (AI_basic _)).
      iApply wp_seq.
      iSplitR ; last first.
      iSplitL "Hf".
      iApply (wp_get_local with "[] [$Hf]").
      done.
      by instantiate (1 := λ x, ⌜x = immV _⌝%I).
      iIntros (w0) "[-> Hf]". simpl.
      rewrite (separate2 (AI_basic _)).
      iApply wp_seq. iSplitR ; last first.
      iSplitL "Hf Himpfcl3 Hs".
      rewrite (separate1 (AI_basic _)).
      rewrite - (app_nil_r [AI_basic (BI_call _)]).
      iApply wp_wasm_empty_ctx.
      iApply wp_base_push. done.
      iApply (wp_call_ctx with "Hf").
      done. 
      iIntros "!> Hf".
      iApply wp_base_pull.
      simpl.
      iApply wp_wasm_empty_ctx.
      iApply ("Hspec3" with "[Himpfcl3 Hs Hf]").
      iFrame.
      
      iIntros (w0) "(-> & H)".
      instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
      iSplitR. done. iExact "H".
      iIntros (w0) "(-> & Hs & Himpfcl3 & Hf)".
      iSimpl.
      rewrite (separate2 (AI_basic _)).
      iApply wp_seq.
      iSplitR ; last first.
      iSplitL "Hf".
      rewrite (separate1 (AI_basic _)).
      iApply wp_val_app.
      done.
      iSplitR ; last first.
      iApply wp_wand_r.
      iSplitL.
      iApply (wp_get_local with "[] [$Hf]").
      done.
      instantiate (1 := λ v, ⌜v = immV [value_of_uint k]⌝%I).
      done.
      iIntros (v0) "[-> Hf]".
      iSimpl.
      instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗ ↪[frame] _)%I). 
      by iFrame.
      by iIntros "!> [% _]".
      iIntros (w0) "[-> Hf]".
      iSimpl.
      rewrite (separate3 (AI_basic _)).
      iApply wp_seq.
      iSplitR ; last first.
      iSplitL "Hf Hs Himpfcl3".
      rewrite (separate1 (AI_basic _)).
      iApply wp_val_app.
      done.
      iSplitR ; last first.
      rewrite (separate1 (AI_basic (i32const _))).
      rewrite - (app_nil_r [AI_basic (BI_call 3)]).
      iApply wp_wasm_empty_ctx.
      iApply wp_base_push => //.
      iApply (wp_wand_ctx with "[Hf Hs Himpfcl3]"). 
      iApply (wp_call_ctx with "Hf") => //.
      iIntros "!> Hf".
      iApply wp_base_pull.
      rewrite app_nil_r.
      iApply wp_wasm_empty_ctx.
      iApply ("Hspec3"  with "[Hs Hf Himpfcl3]").
      by iFrame.
        
      iIntros (w0) "(-> & H)".
      instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗ _)%I).
      iSplitR. done. iExact "H". 
      iIntros (w0) "(-> & H)".
      iSimpl.
      instantiate (1:= λ v, (⌜ v = immV _ ⌝ ∗ _)%I).
      iSplitR. done. iExact "H". 
      by iIntros "!> [% _]".
      iIntros (w0) "(-> & Hs & Himpfcl3 & Hf)".
      iSimpl.
      rewrite (separate3 (AI_basic _) (AI_basic _)).
      iApply wp_seq.
      iSplitR ; last first.
      iSplitL "Hf".
      iApply (wp_binop with "Hf").
      done.
      iSimpl.
      unfold Wasm_int.Int32.isub, Wasm_int.Int32.sub.
      unfold Wasm_int.Int32.unsigned.
      rewrite H0 H1.
      instantiate (1 := λ v, ⌜ v = immV _ ⌝%I).
      done.
      iIntros (w0) "[-> Hf]".
      iSimpl.
      iApply wp_wand_r.
      iSplitL "Hf Hwg".
      iApply (wp_set_global with "[] Hf Hwg").
      done.
      instantiate (1 := λ v, ⌜ v = immV [] ⌝%I).
      by iNext.
      iIntros (v0) "[ -> [Hwg Hf]]".
      iSimpl.
      iIntros (lh) "%Hfill".
      unfold lfilled, lfill in Hfill ; simpl in Hfill.
      move/eqP in Hfill; subst lh.
      iApply wp_wand_r.
      iSplitL "Hf".
      iApply (wp_label_value with "Hf").
      done.
      instantiate (1 := λ v, ⌜ v = immV [] ⌝%I).
      done.
      iIntros (v0) "[-> Hf]".
      iExists _.
      iFrame.
      iIntros "Hf".
      iSimpl.
      iApply wp_wand_r.
      iSplitL "Hf". iApply (wp_frame_value with "Hf").
      done.
      done.
      by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
      all: try by iIntros "[% _]".
      iIntros (v) "[-> Hf]".
      iApply iris_host.wp_value. done.
      iSplit => //.
      iFrame "Hf".
      iExists _, _.
      iFrame.
      iApply iris_host.wp_value. done.
      iSplit => //.
      iFrame "Hf Hmod1".
      iExists _, _. by iFrame.
Qed.

End Client2.
  
