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


Section Client.

 Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ, !logrel_na_invs Σ}. 

(* Functions from the stack module are : 
     0 - new_stack
     1 - is_empty
     2 - is_full
     3 - pop
     4 - push 
     5 - map
     6 - length *)
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
      BI_get_local 0 ;
      BI_call 3 ; (* Pop 36 *)
      BI_get_local 0 ;
      BI_call 3 ; (* Pop 16 *)
      BI_binop T_i32 (Binop_i BOI_sub) ; (* Subtract those two, to get 20 *)
      BI_set_global 0 (* Assign the 0th global the value 20 *)
    ].

  Definition square :=
    [ BI_get_local 0 ;
    BI_get_local 0 ;
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
      |} ] ;
    mod_tables := [] ; 
    mod_mems := [] ;
    mod_globals := [ {| modglob_type := {| tg_t := T_i32 ;
                                           tg_mut := MUT_mut |} ;
                        modglob_init := [i32const 0] |} ] ;
    mod_elem := [ {| modelem_table := Mk_tableidx 0 ;
                     modelem_offset := [i32const 0] ;
                     modelem_init := [Mk_funcidx 8] |} ] ;
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
                     imp_name := list_byte_of_string "stack_length" ;
                     imp_desc := ID_func 2
                  |} ;
                  {| imp_module := list_byte_of_string "Stack" ;
                     imp_name := list_byte_of_string "table" ;
                     imp_desc := ID_table {| tt_limits := {| lim_min := 1%N ; lim_max := None |} ;
                                             tt_elem_type := ELT_funcref |} |}
                  ] ;
    mod_exports := [
                    {|
                      modexp_name := list_byte_of_string "answer" ;
                      modexp_desc := MED_global (Mk_globalidx 0)
                    |}
                  ]
    |}.

  Lemma module_typing_client :
    module_typing client_module expts [ET_glob {| tg_t := T_i32 ; tg_mut := MUT_mut |} ].
  Proof.
    unfold module_typing => /=.
    exists [ Tf [] [] ; Tf [T_i32] [T_i32] ],
    [ {| tg_t := T_i32 ; tg_mut := MUT_mut |} ].
    repeat split => //.
    (* Functions *)
    { repeat (apply Forall2_cons ; repeat split => //) => /=.
      - unfold main.
        rewrite (separate9 (BI_call _)).
        eapply bet_composition'.
        { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. }
        { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. }
      - apply/b_e_type_checker_reflects_typing => /=; by apply/eqP.
    }
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

  Definition stack_instantiate (vis_addrs: list N) (stack_mod_addr client_mod_addr: N) :=
    [ ID_instantiate (take 8 vis_addrs) stack_mod_addr [] ;
    ID_instantiate (drop 8 vis_addrs) client_mod_addr (take 8 vis_addrs) ].

  Lemma instantiate_stack_client_spec E (vis_addrs: list N) (stack_mod_addr client_mod_addr: N) :
    length vis_addrs = 9 ->
   ↪[frame] empty_frame -∗
    stack_mod_addr ↪[mods] stack_module -∗
    client_mod_addr ↪[mods] client_module -∗
    own_vis_pointers vis_addrs -∗
     WP ((stack_instantiate vis_addrs stack_mod_addr client_mod_addr, []) : host_expr)
     @ E
            {{ v, ⌜ v = immHV [] ⌝ ∗ 
               ↪[frame] empty_frame ∗
                stack_mod_addr ↪[mods] stack_module ∗
                 client_mod_addr ↪[mods] client_module ∗
                 ∃ idg name,
                   (vis_addrs !!! 8) ↪[vis] {| modexp_name := name ;
                                modexp_desc := MED_global (Mk_globalidx idg) |} ∗
                    (N.of_nat idg ↦[wg] {| g_mut := MUT_mut ; g_val := value_of_int 20%Z |} ∨
                       N.of_nat idg ↦[wg] {| g_mut := MUT_mut ; g_val := value_of_int (-1)%Z |}) }}.
Proof.
  iIntros (Hvisaddrlen) "Hemptyframe Hmod0 Hmod1 Hvis".
  do 10 (destruct vis_addrs => //); clear Hvisaddrlen.
  
  rewrite separate8.
  iDestruct (big_sepL_app with "Hvis") as "(Hvis & (Hvis8 & _))".
  unfold own_vis_pointers.
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
    { by iIntros "(% & _)". }
    
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
      iApply (instantiation_spec_operational_start with "[$Hemptyframe] [Hmod1 Himport Himp_type Hvis8]") ; try exact module_typing_client.
    - by unfold client_module.
    - by apply module_restrictions_client.
    - unfold instantiation_resources_pre.
      iFrame.
    - Opaque list_to_map.
      Opaque zip_with.
      unfold export_ownership_host => /=.
      unfold instantiation_resources_pre_wasm.
      rewrite irwt_nodup_equiv => //.
      iFrame "Himp_type".
      repeat iSplit.
    
      iPureIntro ; unfold module_elem_bound_check_gmap ; simpl.
      apply Forall_cons.
      split ; last done.
      simpl.
      rewrite lookup_insert.
      done.
      iPureIntro ; unfold module_data_bound_check_gmap ; simpl ; done.
      done.
      done.
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
      do 8 (destruct inst_funcs as [| ? inst_funcs] ; first by iExFalso ; iExact "Hexpwf").
      simpl.
      iDestruct "Hexpwf" as "[Hwfcl Hexpwf]".
      destruct inst_funcs ; first by iExFalso ; iExact "Hexpwf".
      iDestruct "Hexpwf" as "[Hwfsq Hexpwf]".
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
      iDestruct "Hexphost" as (name) "Hexphost" => /=.

      rewrite irwt_nodup_equiv; last by [].

      iDestruct "Himpwasm" as "(%Hdom & Himpw0 & Himpw1 & Himpw2 & Himpw3 & Himpw4 & Himpw5 & Himpw6 & Htab & _)".
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
      
      (* Now for our last export (the table), we have a little more work to do,
         because we are populating it. This is where the knowledge of the exact
         elements of inst_tab (not just its length) is important *)
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
      replace (length (table_data tab)) with (length (Some f14 :: drop 1 (table_data tab))) ; last first => /=.
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
      iApply weakestpre.wp_wand_l. iSplitR ; last iApply wp_lift_wasm.
      iIntros (v).
      instantiate ( 1 := λ v, (⌜ v = immHV [] ⌝ ∗ ↪[frame] empty_frame ∗ client_mod_addr↪[mods]client_module ∗
  (∃ (idg : nat) (name8: datatypes.name),
      n7↪[vis] {| modexp_name := name8; modexp_desc := MED_global (Mk_globalidx idg) |} ∗
     (N.of_nat idg↦[wg] {| g_mut := MUT_mut; g_val := value_of_int 20 |}
      ∨ N.of_nat idg↦[wg] {| g_mut := MUT_mut; g_val := value_of_int (-1) |})))%I) => //=.
      iIntros "H" ; done. 
      
      iApply wp_wand_r.
      iSplitR "Hmod1".
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
               "[Hwg Ht0 Hwfsq Hf Himpfcl0 Himpfcl1 Himpfcl2 Himpfcl3 Himpfcl4 Himpfcl5 Himpfcl6 Hexphost Hnextaddr]") ; last first.
      iPureIntro.
      unfold lfilled, lfill => /=.
      instantiate (5 := []) => /=.
      rewrite app_nil_r.
      done.

      clear Hdom Hbound Hbound' Hinsttab Hinstmem Hinstglob Hnodup Hfnodup Htab.
      clear n n0 n1 n2 n3 n4 n5 n6 name0 name1 name2 name3 name4 name5 name6.
      
      (* Proving the spec of main *)
     
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
            move/eqP in Hfill ; subst.
            iApply wp_value.
            unfold IntoVal.
            by apply of_to_val.
            iFrame.
            iPureIntro ; by eexists _.
            by iIntros "[%H _]".
          }
          { iIntros "((%Habs & _) & _)"; by inversion Habs. }
          
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
          apply iris.of_to_val.
          remember (sh_append sh _) as shret.
          unfold iris.to_val => /=.
          specialize (iris.to_of_val (retV shret)) as H.
          unfold iris.to_val, iris.to_val, iris.of_val in H.
          rewrite app_nil_r.
          destruct (merge_values_list _).
          inversion H; subst => //. done.
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
          instantiate ( 1 := λ v, (⌜ v = immV [] ⌝ ∗ ∃ g, (N.of_nat g↦[wg] {| g_mut := MUT_mut ; g_val := value_of_int 20 |} ∨ N.of_nat g↦[wg] {| g_mut := MUT_mut ; g_val := value_of_int (-1) |}) ∗ n7%N ↪[vis] {|
                                                                                                                                                                                                     modexp_name := name;
                           modexp_desc := MED_global (Mk_globalidx g)
                                                                                                                                                                                                    |} )%I ).
          iIntros "!>".
          iSplit => //.
          iExists g.
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
            iApply (wp_call_ctx with "Hf") => //=.
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
          by instantiate (1 := λ x, (⌜ x = immV _⌝ ∗ N.of_nat f14 ↦[wf] _)%I) ; iFrame.
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
          by instantiate (1 := λ x, ((⌜ x = immV _ ⌝ ∗ isStack _ _ ∗ N.of_nat idf5 ↦[wf] _) ∗ ↪[frame] _)%I) ; iFrame.
          }
          { iIntros "((%Habs & _) & _)"; by inversion Habs. }
        
          iIntros (w0) "[(-> & Hs & Himpfcl5) Hf]".
          iSimpl.
          rewrite (separate1 (AI_basic _)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf".
          iApply (wp_get_local with "[] [$Hf]") => //.
          by instantiate (1 := λ v, ⌜v = immV [value_of_uint k]⌝%I).
            
          iIntros (v0) "[-> Hf]".
          iSimpl.
          rewrite (separate2 (AI_basic (i32const _))).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Himpfcl3 Hf Hs".
          rewrite (separate1 (AI_basic (i32const _))).
          rewrite - (app_nil_r [AI_basic (BI_call 3)]).
          iApply wp_wasm_empty_ctx.
          iApply wp_base_push => //.
          iApply (wp_call_ctx with "Hf") => //.
          iIntros "!> Hf".
          iApply wp_base_pull.
          rewrite app_nil_r.
          iApply wp_wasm_empty_ctx.
          iApply ("Hspec3"  with "[Hs Hf Himpfcl3]").
          by iFrame.
            
          iIntros (w0) "(-> & Hs & Himpfcl3 & Hf)".
          iFrame.
          instantiate (1 := λ v, ((⌜ v = immV _ ⌝ ∗
                                             isStack k _ ∗
                                             N.of_nat idf3 ↦[wf] FC_func_native i0 (Tf [T_i32] [T_i32]) l3 f3)∗ ↪[frame] _)%I).
          by iFrame.
          iIntros (w0) "[(-> & Hs & Himpfcl3) Hf]".
          iSimpl.
          rewrite (separate2 (AI_basic (i32const _))).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf".
          rewrite (separate1 (AI_basic (i32const _))).
          iApply wp_val_app.
          done.
          iSplitR ; last first.
          iApply wp_wand_r.
          iSplitL.
          iApply (wp_get_local with "[] [$Hf]") => //.
          instantiate (1 := λ v, ⌜v = immV [value_of_uint k]⌝%I).
          done.
          iIntros (v0) "[-> Hf]".
          iSimpl.
          instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗
                                             ↪[frame] _)%I). 
          by iFrame.
          by iIntros "!> [%H _]".
          iIntros (w0) "[-> Hf]".
          iSimpl.
          rewrite (separate3 (AI_basic (i32const _))).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf Hs Himpfcl3".
          rewrite (separate1 (AI_basic (i32const _))).
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
            
          iIntros (w0) "(-> & Hs & Himpfcl3 & Hf)".
          iFrame.
          instantiate (1 := λ v, ((⌜ v = immV _ ⌝ ∗
                                             isStack k [] ∗
                                             N.of_nat idf3 ↦[wf] FC_func_native i0 (Tf [T_i32] [T_i32]) l3 f3)∗ ↪[frame] _)%I).
          by iFrame.
          iIntros (w0) "[(-> & Hs & Himpfcl3) Hf]".
          iSimpl.
          instantiate (1:= λ v, (⌜ v = immV _ ⌝ ∗
                                            isStack k [] ∗
                                            N.of_nat idf3 ↦[wf] FC_func_native i0 (Tf [T_i32] [T_i32]) l3 f3 ∗
                                            ↪[frame] _)%I ). 
          by iFrame.
          by iIntros "!> [%H _]".
          iIntros (w0) "(-> & Hs & Himpfcl3 & Hf)".
          iSimpl.
          rewrite (separate3 (AI_basic (i32const _)) (AI_basic (i32const _))).
          iSimpl.
          rewrite (separate3 (AI_basic (i32const _)) (AI_basic (i32const _))).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf".
          iApply (wp_binop with "Hf").
          done.
          iSimpl.
          unfold Wasm_int.Int32.isub, Wasm_int.Int32.sub.
          rewrite Wasm_int.Int32.unsigned_repr.
          rewrite Wasm_int.Int32.unsigned_repr.
          instantiate (1 := λ v, ⌜ v = immV _ ⌝%I).
          done.
          unfold Wasm_int.Int32.max_unsigned; rewrite u32_modulus; lia.
          unfold Wasm_int.Int32.max_unsigned; rewrite u32_modulus; lia.
          
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
          move/eqP in Hfill; subst.
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
          iApply (wp_frame_value with "Hf").
          done.
          done.
          all: try by iIntros "[% _]".
          all: try by iIntros "[[% _] _]".
          iNext.
          iSplit ; first done.
          iExists g.
          by iFrame.
        }
      }
      
      iIntros (w) "((-> & H) & Hf)".
      iDestruct "H" as (ga) "(H & ?)".
      iSimpl.
      iApply iris_host.wp_value.
      unfold iris_host.to_val => //.

      iSplit => //.
      iFrame.

      iExists ga, _.
      by iFrame.
  Qed.
      
End Client.
  
