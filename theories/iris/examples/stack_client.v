


From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_host iris_fundamental_helpers stack_specs stack_instantiation.
Require Export datatypes host operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.
   

Section Client.

 Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ, !logrel_na_invs Σ}. 


  
(* Functions from the stack module are : 
     0 - new_stack
     1 - is_empty
     2 - is_full
     3 - pop
     4 - push 
     5 - map *)
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
      i32const 6 ;
      BI_get_local 0 ;
      BI_call 4 ;
      i32const 0 ;
      BI_get_local 0 ;
      BI_call 5 ;
      BI_get_local 0 ;
      BI_call 3 ;
      BI_get_local 0 ;
      BI_call 3 ;
      BI_binop T_i32 (Binop_i BOI_sub) ;
      BI_set_global 0
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
                      modelem_init := [Mk_funcidx 7] |} ] ;
      mod_data := [] ;
      mod_start := Some {| modstart_func := Mk_funcidx 6 |} ;
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
                                 tt_elem_type := ELT_funcref |} |}
      ] ;
      mod_exports := [
        {|
          modexp_name := list_byte_of_string "answer" ;
          modexp_desc := MED_global (Mk_globalidx 0)
        |}
      ]
    |}.



  Ltac bet_first f :=
  eapply bet_composition_front ; first eapply f => //=.


  Lemma module_typing_client :
    module_typing client_module expts [ET_glob {| tg_t := T_i32 ; tg_mut := MUT_mut |} ].
  Proof.
    unfold module_typing => /=.
    exists [ Tf [] [] ; Tf [T_i32] [T_i32] ],
      [ {| tg_t := T_i32 ; tg_mut := MUT_mut |} ].
    repeat split => //.
    repeat (apply Forall2_cons ; repeat split => //) => /=.
    - bet_first bet_call.
      bet_first bet_tee_local.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 []).
      apply bet_weakening.
      apply bet_const.
      bet_first bet_relop.
      apply Relop_i32_agree.
      bet_first bet_if_wasm.
      bet_first bet_const.
      bet_first bet_set_global.
      replace (Tf [] []) with (Tf (app ([] : list value_type) []) []) ; last done.
      eapply bet_return => //.
      apply bet_empty.
      bet_first bet_const.
      unfold typeof.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 []).
      apply bet_weakening.
      by apply bet_get_local.
      bet_first bet_call.
      bet_first bet_const.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 []).
      apply bet_weakening.
      by apply bet_get_local.
      bet_first bet_call.
      bet_first bet_const.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 []).
      apply bet_weakening.
      by apply bet_get_local.
      bet_first bet_call.
      bet_first bet_get_local.
      bet_first bet_call.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 []).
      apply bet_weakening.
      by apply bet_get_local.
      eapply bet_composition_front.
      apply bet_weakening.
      by apply bet_call.
      bet_first bet_binop.
      apply Binop_i32_agree.
      by eapply bet_set_global.
    - bet_first bet_get_local.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 []).
      apply bet_weakening.
      by apply bet_get_local.
      apply bet_binop.
      apply Binop_i32_agree.
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



    Definition stack_instantiate :=
    [ ID_instantiate [0%N ; 1%N ; 2%N ; 3%N ; 4%N ; 5%N ; 6%N] 0 [] ;
      ID_instantiate [7%N] 1 [0%N ; 1%N ; 2%N ; 3%N ; 4%N ; 5%N ; 6%N] ].



    Notation " n ↪[vis]{ q } v" := (ghost_map_elem (V := module_export) visGName n q v%V)
                                 (at level 20, q at level 5, format " n ↪[vis]{ q } v") .
Notation " n ↪[vis] v" := (ghost_map_elem (V := module_export) visGName n (DfracOwn 1) v%V)
                            (at level 20, format " n ↪[vis] v").

Notation " n ↪[mods]{ q } v" := (ghost_map_elem (V := module) msGName n q v%V)
                                  (at level 20, q at level 5, format " n ↪[mods]{ q } v") .
Notation " n ↪[mods] v" := (ghost_map_elem (V := module) msGName n (DfracOwn 1) v%V)
                             (at level 20, format " n ↪[mods] v").

  

  Lemma instantiate_stack_client_spec (s: stuckness) E hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 :
    0%N ↪[mods] stack_module -∗
     1%N ↪[mods] client_module -∗
     ( [∗ list] k↦hvk ∈ [hv0 ; hv1 ; hv2 ; hv3 ; hv4 ; hv5 ; hv6 ; hv7], N.of_nat k↪[vis] hvk) -∗
     WP ((stack_instantiate , []) : host_expr)
     @ s; E
            {{ v,
                0%N ↪[mods] stack_module ∗
                 1%N ↪[mods] client_module ∗
                 ∃ idg name,
                   7%N ↪[vis] {| modexp_name := name ;
                                modexp_desc := MED_global (Mk_globalidx idg) |} ∗
                    (N.of_nat idg ↦[wg] {| g_mut := MUT_mut ; g_val := value_of_int 20%Z |} ∨
                       N.of_nat idg ↦[wg] {| g_mut := MUT_mut ; g_val := value_of_int (-1)%Z |}) }}.
  Proof.
    iIntros "Hmod0 Hmod1 (Hvis0 & Hvis1 & Hvis2 & Hvis3 & Hvis4 & Hvis5 & Hvis6 & Hvis7 &  _)".
    iApply (wp_seq_host_nostart
             with "[$Hmod0] [Hvis0 Hvis1 Hvis2 Hvis3 Hvis4 Hvis5 Hvis6]") => //.
    - iIntros "Hmod0".
      iApply weakestpre.wp_mono ;
        last iApply (instantiate_stack_spec
                      with "Hmod0 [Hvis0 Hvis1 Hvis2 Hvis3 Hvis4 Hvis5 Hvis6]").
      2:{ iSplitL "Hvis0" ; first done.
          iSplitL "Hvis1" ; first done.
          iSplitL "Hvis2" ; first done.
          iSplitL "Hvis3" ; first done.
          iSplitL "Hvis4" ; first done.
          iSplitL "Hvis5" ; first done.
          by iSplitL. }
      iIntros (v) "[? H]".
      iFrame.
      by iApply "H".
    - iIntros (w) "Hes1 Hmod0".
      iDestruct "Hes1" as (idf0 idf1 idf2 idf3 idf4 idf5 idt) "Hes1".
      iDestruct "Hes1" as (name0 name1 name2 name3 name4 name5 name6) "Hes1".
      iDestruct "Hes1" as (f0 f1 f2 f3 f4 f5) "Hes1".
      iDestruct "Hes1" as (i0) "Hes1".  
      iDestruct "Hes1" as (l0 l1 l2 l3 l4 l5) "Hes1".
      iDestruct "Hes1" as (tab isStack nextStackAddrIs)
                            "(Himport & Himp_type & %Htab & Hnextaddr & #Hspec0 & #Hspec1 & #Hspec2 & #Hspec3 & #Hspec4 & #Hspec5 & #Hspec6)".
      iFrame "Hmod0".
      iApply (instantiation_spec_operational_start with "[Hmod1 Himport Himp_type Hvis7]") ; try exact module_typing_client.
    - by unfold client_module.
    - unfold instantiation_resources_pre.
      iFrame.
    - unfold export_ownership_host => /=.
      repeat iSplit.
    
      iPureIntro ; unfold module_elem_bound_check_gmap ; simpl.
      apply Forall_cons.
      split ; last done.
      simpl.
      rewrite lookup_insert.
      done.
      iPureIntro ; unfold module_data_bound_check_gmap ; simpl ; done.
      by iExists _.
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
      do 7 (destruct inst_funcs as [| ? inst_funcs] ; first by iExFalso ; iExact "Hexpwf").
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
      unfold import_resources_wasm_typecheck => /=.
      iDestruct "Himpwasm" as "(%Hdom & Himpw0 & Himpw1 & Himpw2 & Himpw3 & Himpw4 & Himpw5 & Htab & _)". 
      iDestruct "Himpw0" as (cl0) "[Himpfcl0 %Hcltype0]".
      iDestruct "Himpw1" as (cl1) "[Himpfcl1 %Hcltype1]".
      iDestruct "Himpw2" as (cl2) "[Himpfcl2 %Hcltype2]".
      iDestruct "Himpw3" as (cl3) "[Himpfcl3 %Hcltype3]".
      iDestruct "Himpw4" as (cl4) "[Himpfcl4 %Hcltype4]".
      iDestruct "Himpw5" as (cl5) "[Himpfcl5 %Hcltype5]".
      iDestruct "Htab" as (tab0 tt) "[Htab %Htab0]".
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
      rewrite lookup_insert in Hcltype0.
      destruct Hcltype0 as [Hcl _] ; inversion Hcl ; subst ; clear Hcl.
      rewrite lookup_insert_ne in Hcltype1 ; last assumption.
      rewrite lookup_insert in Hcltype1.
      destruct Hcltype1 as [Hcl _] ; inversion Hcl ; subst ; clear Hcl.
      do 2 (rewrite lookup_insert_ne in Hcltype2 ; last assumption).
      rewrite lookup_insert in Hcltype2.
      destruct Hcltype2 as [Hcl _] ; inversion Hcl ; subst ; clear Hcl.
      do 3 (rewrite lookup_insert_ne in Hcltype3 ; last assumption).
      rewrite lookup_insert in Hcltype3.
      destruct Hcltype3 as [Hcl _] ; inversion Hcl ; subst ; clear Hcl.
      do 4 (rewrite lookup_insert_ne in Hcltype4 ; last assumption).
      rewrite lookup_insert in Hcltype4.
      destruct Hcltype4 as [Hcl _] ; inversion Hcl ; subst ; clear Hcl.
      do 5 (rewrite lookup_insert_ne in Hcltype5 ; last assumption).
      rewrite lookup_insert in Hcltype5.
      destruct Hcltype5 as [Hcl _] ; inversion Hcl ; subst ; clear Hcl.
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
      replace (length (table_data tab)) with (length (Some f12 :: drop 1 (table_data tab))) ; last first => /=.
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
      apply b2p in Hstart.
      inversion Hstart ; subst ; clear Hstart.
      iApply weakestpre.wp_wand_l. iSplitR ; last iApply wp_lift_wasm.
      iIntros (v).
      instantiate ( 1 := λ v, (1%N↪[mods]client_module ∗
  (∃ (idg : nat) (name7 : datatypes.name),
      7%N↪[vis] {| modexp_name := name7; modexp_desc := MED_global (Mk_globalidx idg) |} ∗
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
               "[Hwg Ht0 Hwfsq Hf Himpfcl0 Himpfcl1 Himpfcl2 Himpfcl3 Himpfcl4 Himpfcl5 Hexphost Hnextaddr]") ; last first.
      iPureIntro.
      unfold lfilled, lfill => /=.
      instantiate (5 := []) => /=.
      rewrite app_nil_r.
      done.
       
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
          instantiate (1 := λ v0, (( ∃ k : Z, ⌜v0 = immV [value_of_int k]⌝ ∗
                                                         (⌜k = (-1)%Z⌝ ∗ nextStackAddrIs 0 ∨  ⌜ (0 ≤ k)%Z ∧ (k + Z.pos (64 * 1024) ≤ two32)%Z⌝ ∗ isStack k [] ∗ nextStackAddrIs (0 + Pos.to_nat (64 * 1024)))) ∗ 
                                     N.of_nat idf0↦[wf]FC_func_native i0 (Tf [] [T_i32]) l0 f0)%I). 
          iFrame. }
        iIntros (w0) "[[H Himpfcl0] Hf]". 
        iDestruct "H" as (k) "[-> H]".
        iSimpl.
        rewrite (separate2 (AI_basic (i32const k))).
        iApply wp_seq.
        iSplitR ; last first.
        iSplitL "Hf".
        iApply (wp_tee_local with "Hf").
        iIntros "Hf".
        rewrite (separate1 (AI_basic (i32const _))).
        iApply wp_val_app => //.
        iSplitR ; last first.
        iApply wp_wand_r.
        iSplitL "Hf".
        iApply (wp_set_local with "Hf").
        simpl.
        lia.
        instantiate (1 := λ v, v = immV []) => //.
        iIntros (v0) "[-> Hf]".
        iSimpl.
        iSimpl in "Hf".
        instantiate (1 := λ v, (⌜ v = immV [VAL_int32 (Wasm_int.Int32.repr k)] ⌝
                                           ∗ ↪[frame] _)%I). 
        by iFrame.
        by iIntros "!> [%H _]".
        iIntros (w0) "[-> Hf]".
        iSimpl.
        rewrite (separate3 (AI_basic (i32const k))).
        iApply wp_seq.
        iSplitR ; last first.
        iSplitL "Hf".
        iApply (wp_relop with "Hf") => //.
        instantiate (1 := λ v, ⌜ v = immV
                                       [VAL_int32
                                          (wasm_bool
                                             (app_relop (Relop_i ROI_eq) (VAL_int32 (Wasm_int.int_of_Z i32m k))
                                                        (VAL_int32 (Wasm_int.Int32.repr (-1)))))]⌝%I ).
        done.
        iIntros (w0) "[-> Hf]".
        iSimpl.
        rewrite (separate2 _ (AI_basic (BI_if _ _ _))).
        iApply wp_seq.
        iSplitR ; last first.
        iAssert (⌜ (-1 <= k < two32 - 1)%Z ⌝%I) with "[H]" as "%Hk".
        { iDestruct "H" as "[[%Hk _] | (%Hk & _)]" ; iPureIntro.
          subst. done.
          destruct Hk.
          lia. }
        iSplitL "Hf Hwg". 
        instantiate (1:= λ v1, (( ⌜ v1 = immV [] ⌝ ∗
                                              ⌜ (k <> -1)%Z ⌝ ∗
                                              N.of_nat g↦[wg] {| g_mut := MUT_mut ; g_val := vg |} ∨
                                    ⌜ exists sh, v1 = retV sh ⌝ ∗
                                                      N.of_nat g↦[wg] {| g_mut := MUT_mut ; g_val := value_of_int (-1)%Z |}) ∗
                                                                                                                             ↪[frame] _)%I ).         
        destruct ( decide ( k = - 1)%Z ).
        + { subst. iSimpl.
            iApply (wp_if_true with "Hf") => //.
            iIntros "!> Hf".
            rewrite - (app_nil_l [AI_basic _]).
            iApply (wp_block with "Hf") => //.
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
            iIntros (w0) "[[-> Hwg] Hf]".
            iSimpl.
            iApply wp_value.
            unfold IntoVal.
            by apply of_to_val.
            iIntros (lh) "%Hfill".
            unfold lfilled, lfill in Hfill ; simpl in Hfill.
            apply b2p in Hfill ; subst.
            iApply wp_value.
            unfold IntoVal.
            by apply of_to_val.
            iFrame.
            iRight.
            iFrame.
            iPureIntro ; by eexists _.
            by iIntros "[[%H _] _]". }
        + { rewrite Wasm_int.Int32.eq_false.
            2:{ intro Habs ; inversion Habs.
                rewrite Wasm_int.Int32.Z_mod_modulus_eq in H0.
                rewrite Z.mod_small in H0.
                subst.
                unfold Wasm_int.Int32.modulus in Hk.
                unfold Wasm_int.Int32.wordsize in Hk.
                unfold Integers.Wordsize_32.wordsize in Hk.
                replace (two_power_nat 32) with two32 in Hk ; last done.
                lia.
                unfold Wasm_int.Int32.modulus.
                unfold Wasm_int.Int32.wordsize.
                unfold Integers.Wordsize_32.wordsize.
                replace (two_power_nat 32) with two32 ; last done.
                lia. }
            iApply (wp_if_false with "Hf").
            done.
            iIntros "!> Hf".
            rewrite - (app_nil_l [AI_basic _]).
            iApply (wp_block with "Hf").
            done. done. done. done.
            iIntros "!> Hf".
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
            apply b2p in Hfill ; subst. 
            iApply (wp_label_value with "Hf").
            done.
            iLeft.
            repeat (iSplit ; try by iPureIntro).
            done. }
         
            iIntros (w0) "[[(-> & %Hk1 & Hwg) | [%Hret Hwg]] Hf]".
          { iDestruct "H" as "[[-> Haddr] | (%Hk2 & Hs & Haddr)]".
            done.
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
            iApply (wp_get_local with "Hf").
            done.
            instantiate (1 := λ v, v = immV [VAL_int32 (Wasm_int.Int32.repr k)]).
            done.
            iIntros (w0) "[-> Hf]".
            iSimpl.
            instantiate (1 := λ v, (⌜ v = immV [value_of_int 4%Z ; value_of_int k] ⌝ ∗
                                               ↪[frame] _)%I ). 
            by iFrame.
          by iIntros "!> [%H _]".
          iIntros (w0) "[-> Hf]".
          iSimpl.
          rewrite (separate3 (AI_basic (i32const 4))).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Himpfcl4 Hf Hs".
          rewrite (separate2 (AI_basic (i32const _))).
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
          by destruct Hk2.
          unfold Wasm_int.Int32.max_unsigned, Wasm_int.Int32.modulus.
          unfold Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
          replace (two_power_nat 32) with two32 ; last done.
          by destruct Hk2 ; lia.
          iIntros (w0) "(-> & Hs & Himpfcl4 & Hf)".
          iFrame.
          instantiate (1 := λ v, (⌜ v = immV [] ⌝ ∗
                                             isStack k [ (Wasm_int.int_of_Z i32m 4)] ∗
                                             N.of_nat idf4↦[wf]FC_func_native i0 (Tf [T_i32 ; T_i32] []) l4 f4)%I).
          by iFrame.
          iIntros (w0) "[(-> & Hs & Himpfcl4) Hf]".
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
          iApply (wp_get_local with "Hf").
          done.
          instantiate (1 := λ v, v = immV [value_of_int k]).
          done.
          iIntros (v0) "[-> Hf]".
          iSimpl.
          instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗
                                             ↪[frame] _)%I).  
          by iFrame.
          by iIntros "!> [%H _]".
          iIntros (w0) "[-> Hf]".
          iSimpl.
          rewrite (separate3 (AI_basic (i32const 6))).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Himpfcl4 Hf Hs".
          rewrite (separate2 (AI_basic (i32const _))).
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
          by destruct Hk2.
          unfold Wasm_int.Int32.max_unsigned, Wasm_int.Int32.modulus.
          unfold Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
          replace (two_power_nat 32) with two32 ; last done.
          by destruct Hk2 ; lia.
          iIntros (w0) "(-> & Hs & Himpfcl4 & Hf)".
          iFrame.
          instantiate (1 := λ v, (⌜ v = immV [] ⌝ ∗
                                             isStack k [_;_] ∗
                                             N.of_nat idf4↦[wf]FC_func_native i0 (Tf [T_i32 ; T_i32] []) l4 f4)%I).
          by iFrame.
          iIntros (w0) "[(-> & Hs & Himpfcl4) Hf]".
          iSimpl.
          rewrite (separate2 (AI_basic _)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf".
          rewrite (separate1 (AI_basic _)).
          iApply wp_val_app ; first done.
          iSplitR ; last first.
          iApply wp_wand_r ; iSplitL.
          iApply (wp_get_local with "Hf").
          done.
          by instantiate (1 := λ v, v = immV _).
          iIntros (v0) "[-> Hf]".
          by instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗ ↪[frame] _)%I) ; iFrame.
          by iIntros "!> [% _]".
          iIntros (v0) "[-> Hf]".
          iSimpl.
          rewrite (separate3 (AI_basic (i32const 0))).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf Himpfcl5 Hs Ht0 Hwfsq".
          rewrite (separate2 (AI_basic (i32const _))).
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
          iSimpl.
          repeat iSplit ; try iPureIntro.
          by destruct Hk2.
          unfold Wasm_int.Int32.max_unsigned, Wasm_int.Int32.modulus.
          unfold Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
          replace (two_power_nat 32) with two32 ; last done.
          by destruct Hk2 ; lia.
          instantiate (2 := λ x, True%I).
          done.
          done.
          instantiate (1 := λ x y, ⌜ y = Wasm_int.Int32.imul x x ⌝%I ).
          iIntros (u fc) "!>". iIntros (Λ) "(_ & -> & Hf & Htab & Hcl) HΛ".
          rewrite (separate1 _ [AI_invoke _]).
          iApply wp_wand_r.
          iSplitL "Hf Hcl".
          iApply (wp_invoke_native with "Hf Hcl").
          done.
          done.
          done.
          iIntros "!> [Hf Hcl]".
          iApply (wp_frame_bind with "Hf").
          done. iIntros "Hf".
          rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
          iApply (wp_block with "Hf").
          done.
          done.
          done.
          done.
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
          iApply (wp_get_local with "Hf").
          done.
          by instantiate (1 := λ x, x = immV _).
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
          iApply (wp_get_local with "Hf").
          done.
          by instantiate (1 := λ x, x = immV _).
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
          apply b2p in Hlh as ->.
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
          by instantiate (1 := λ x, (⌜ x = immV _⌝ ∗ N.of_nat f12 ↦[wf] _)%I) ; iFrame.
          all : try by iIntros "[% _]".
          iIntros (v0) "[[-> Hcl] Hf]".
          iApply "HΛ".
          iFrame.
          by iExists _.
          iIntros (w0) "(-> & H & Hwimpcl5 & Hf)".
          iDestruct "H" as (s') "[Hs Hs']".
          destruct s' ; first by iExFalso ; iExact "Hs'".
          iDestruct "Hs'" as "[-> Hs']".
          destruct s' ; first by iExFalso ; iExact "Hs'".
          iDestruct "Hs'" as "[-> Hs']".
          destruct s' ; last by iExFalso ; iExact "Hs'".
          iFrame.
          by instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ isStack _ _ ∗ N.of_nat idf5 ↦[wf] _)%I) ; iFrame.
          iIntros (w0) "[(-> & Hs & Himpfcl5) Hf]".
          iSimpl.
          rewrite (separate1 (AI_basic _)).
          iApply wp_seq.
          iSplitR ; last first.
          iSplitL "Hf".
          iApply (wp_get_local with "Hf").
          done.
          instantiate (1 := λ v, v = immV [value_of_int k]).
          done.
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
          iFrame.
          iSimpl.
          repeat iSplit ; iPureIntro => //.
          by destruct Hk2.
          unfold Wasm_int.Int32.max_unsigned, Wasm_int.Int32.modulus.
          unfold Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
          replace (two_power_nat 32) with two32 ; last done.
          by destruct Hk2 ; lia.
          iIntros (w0) "(-> & Hs & Himpfcl3 & Hf)".
          iFrame.
          instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗
                                             isStack k _ ∗
                                             N.of_nat idf3 ↦[wf] FC_func_native i0 (Tf [T_i32] [T_i32]) l3 f3)%I).
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
          iApply (wp_get_local with "Hf").
          done.
          instantiate (1 := λ v, v = immV [value_of_int k]).
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
          iFrame.
          iSimpl.
          repeat iSplit ; iPureIntro => //.
          by destruct Hk2.
          unfold Wasm_int.Int32.max_unsigned, Wasm_int.Int32.modulus.
          unfold Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
          replace (two_power_nat 32) with two32 ; last done.
          by destruct Hk2 ; lia.
          iIntros (w0) "(-> & Hs & Himpfcl3 & Hf)".
          iFrame.
          instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗
                                             isStack k [] ∗
                                             N.of_nat idf3 ↦[wf] FC_func_native i0 (Tf [T_i32] [T_i32]) l3 f3)%I).
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
          unfold Wasm_int.Int32.max_unsigned, Wasm_int.Int32.modulus.
          unfold Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
          replace (two_power_nat 32) with two32 ; last done.
          unfold two32.
          lia.
          unfold Wasm_int.Int32.max_unsigned, Wasm_int.Int32.modulus.
          unfold Wasm_int.Int32.wordsize, Integers.Wordsize_32.wordsize.
          replace (two_power_nat 32) with two32 ; last done.
          unfold two32.
          lia.
          iIntros (w0) "[-> Hf]".
          iSimpl.
          iApply wp_wand_r.
          iSplitL "Hf Hwg".
          iApply (wp_set_global with "[] Hf Hwg").
          done.
          instantiate (1 := λ v, ⌜ v = immV [] ⌝%I).
          by iNext.
          iIntros (v0) "[[ -> Hwg] Hf]".
          iSimpl.
          iIntros (lh) "%Hfill".
          unfold lfilled, lfill in Hfill ; simpl in Hfill.
          apply b2p in Hfill ; subst.
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
          instantiate ( 1 := λ v, (⌜ v = immV [] ⌝ ∗ ∃ g, (N.of_nat g↦[wg] {| g_mut := MUT_mut ; g_val := value_of_int 20 |} ∨ N.of_nat g↦[wg] {| g_mut := MUT_mut ; g_val := value_of_int (-1) |}) ∗ 7%N ↪[vis] {|
                                                                                                                                                                                                     modexp_name := name;
                           modexp_desc :=
                             MED_global (Mk_globalidx g)
                         |} )%I ).
          iNext.
          iSplit ; first done.
          iExists g.
          iFrame. }
          destruct Hret as [sh ->].
          iApply wp_value.
          unfold IntoVal.
          apply iris.of_to_val.
          rewrite extend_retV.
          done.
          iIntros (lh) "%Hfill".
          unfold lfilled, lfill in Hfill.
          simpl in Hfill.
          apply b2p in Hfill ; subst.
          iApply wp_value.
          unfold IntoVal.
          apply iris.of_to_val.
          unfold iris.to_val => /=.
          specialize (iris.to_of_val (retV (sh_append sh [AI_basic
                      (BI_const
                         (VAL_int32 (Wasm_int.Int32.repr 4)));
                   AI_basic (BI_get_local 0);
                   AI_basic (BI_call 4);
                   AI_basic
                     (BI_const (VAL_int32 (Wasm_int.Int32.repr 6)));
                   AI_basic (BI_get_local 0);
                   AI_basic (BI_call 4);
                   AI_basic (i32const 0) ; AI_basic (BI_get_local 0) ; AI_basic (BI_call 5) ;                                  
                   AI_basic (BI_get_local 0);
                   AI_basic (BI_call 3);
                   AI_basic (BI_get_local 0);
                   AI_basic (BI_call 3);
                   AI_basic (BI_binop T_i32 (Binop_i BOI_sub));
                                                     AI_basic (BI_set_global 0)]))) as H.
          unfold iris.to_val, iris.to_val, iris.of_val in H.
          rewrite app_nil_r.
          destruct (merge_values_list _).
          inversion H.
          done.
          done.
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
          iSplit ; first done.
          iExists g.
          iFrame.
          by iIntros "[[[%H _] | [%H _]] _]" ; first done ;
            destruct H.
          all : try by iIntros "[%H _]".
          iIntros "[[H _] _]".
          iDestruct "H" as (k) "[%H _]".
          done. }
      iIntros (w0) "[[-> Hwg] Hf]".
      iFrame.
      iDestruct "Hwg" as (g') "[Hwg Hvis7]".
      iApply weakestpre.wp_value.
      instantiate (1 := immHV []) => //=.
      iExists g', _.
      iFrame.
  Qed.


End Client.
  
