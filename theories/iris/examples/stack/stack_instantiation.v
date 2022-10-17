From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_host iris_fundamental_helpers stack_specs.
Require Export datatypes operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.


Notation "{{{ P }}} es {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v : iris.val, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50). 

Section StackModule.

  

  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ}. 




Definition stack_module :=
  {|
    mod_types := [
      Tf [] [T_i32] ;
      Tf [T_i32] [T_i32] ;
      Tf [T_i32 ; T_i32] [] 
    ] ;
    mod_funcs := [
      {|
        modfunc_type := Mk_typeidx 0 ;
        modfunc_locals := [T_i32] ;
        modfunc_body := new_stack
      |} ;
      {|
        modfunc_type := Mk_typeidx 1 ;
        modfunc_locals := [] ;
        modfunc_body := is_empty
      |} ;
      {|
        modfunc_type := Mk_typeidx 1 ;
        modfunc_locals := [] ;
        modfunc_body := is_full
      |} ;
      {|
        modfunc_type := Mk_typeidx 1 ;
        modfunc_locals := [T_i32] ;
        modfunc_body := pop
      |} ;
      {|
        modfunc_type := Mk_typeidx 2 ;
        modfunc_locals := [T_i32] ;
        modfunc_body := push
      |} ;
      {|
        modfunc_type := Mk_typeidx 2 ;
        modfunc_locals := [T_i32 ; T_i32] ;
        modfunc_body := stack_map
      |}
    ] ;
    mod_tables := [ {| modtab_type := {| tt_limits := {| lim_min := 1%N ; lim_max := None |} ;
                                        tt_elem_type := ELT_funcref |} |} ] ;
    mod_mems := [
      {| lim_min := 0%N ; lim_max := None |}
    ] ;
    mod_globals := [] ;
    mod_elem := [] ;
    mod_data := [] ;
    mod_start := None ;
    mod_imports := [] ;
    mod_exports := [
      {|
        modexp_name := list_byte_of_string "new_stack" ;
        modexp_desc := MED_func (Mk_funcidx 0)
      |} ;
      {|
        modexp_name := list_byte_of_string "is_empty" ;
        modexp_desc := MED_func (Mk_funcidx 1)
      |} ;
      {|
        modexp_name := list_byte_of_string "is_full" ;
        modexp_desc := MED_func (Mk_funcidx 2)
      |} ;
      {|
        modexp_name := list_byte_of_string "pop" ;
        modexp_desc := MED_func (Mk_funcidx 3)
      |} ;
      {|
        modexp_name := list_byte_of_string "push" ;
        modexp_desc := MED_func (Mk_funcidx 4)
      |} ;
      {|
        modexp_name := list_byte_of_string "stack_map" ;
        modexp_desc := MED_func (Mk_funcidx 5)
      |} ;
      {|
        modexp_name := list_byte_of_string "table" ;
        modexp_desc := MED_table (Mk_tableidx 0)
      |}
    ]
  |}.


Definition expts := [ET_func (Tf [] [T_i32]) ; ET_func (Tf [T_i32] [T_i32]);
                     ET_func (Tf [T_i32] [T_i32]) ; ET_func (Tf [T_i32] [T_i32]);
                     ET_func (Tf [T_i32 ; T_i32] []) ; ET_func (Tf [T_i32 ; T_i32] []) ;
                     ET_tab {| tt_limits := {| lim_min := 1%N ; lim_max := None |} ;
                              tt_elem_type := ELT_funcref |} ].

Ltac bet_first f :=
  eapply bet_composition_front ; first eapply f => //=.



Lemma validate_stack_typing x tloc tlab tret:
    nth_error tloc x = Some T_i32 ->
    be_typing
    {|
      tc_types_t := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
      tc_func_t := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []; Tf [T_i32; T_i32] []];
      tc_global := [];
      tc_table := [ {| tt_limits := {| lim_min := 1; lim_max := None |}; tt_elem_type := ELT_funcref |}];
      tc_memory := [ {| lim_min := 0; lim_max := None |}];
      tc_local := tloc;
      tc_label := tlab;
      tc_return := tret
    |} (validate_stack x) (Tf [] []).
Proof.
  move => Htloc.
  bet_first bet_get_local => //.
  { rewrite nth_error_lookup in Htloc.
    apply lookup_lt_Some in Htloc.
      by lias. }
  eapply bet_composition_front.
  rewrite (separate1 T_i32 []).
  apply bet_weakening.
  apply bet_const => //.
  simpl.
  bet_first bet_binop; first by apply Binop_i32_agree.
  apply bet_if_wasm => //.
  { by apply bet_unreachable. }
  { by apply bet_empty. }
Qed.

  
Lemma new_stack_typing :
    be_typing
    {|
      tc_types_t := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
      tc_func_t := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []; Tf [T_i32; T_i32] []];
      tc_global := [];
      tc_table := [ {| tt_limits := {| lim_min := 1; lim_max := None |}; tt_elem_type := ELT_funcref |}];
      tc_memory := [ {| lim_min := 0; lim_max := None |}];
      tc_local := [T_i32];
      tc_label := [[T_i32]];
      tc_return := Some [T_i32]
    |} new_stack (Tf [] [T_i32]).
Proof.
  bet_first bet_const.
  bet_first bet_grow_memory.
  bet_first bet_tee_local.
  eapply bet_composition_front.
  rewrite (separate1 T_i32 []).
  apply bet_weakening.
    by apply bet_const.
    bet_first bet_relop.
      by apply Relop_i32_agree.
      apply bet_if_wasm => /=.
      apply bet_const.
      bet_first bet_get_local.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 []).
      apply bet_weakening.
      apply bet_const.
      bet_first bet_binop.
      apply Binop_i32_agree.
      bet_first bet_tee_local.
      eapply bet_composition_front.
      rewrite - (app_nil_r [T_i32]).
      apply bet_weakening.
      apply bet_get_local => //.
      simpl.
      eapply bet_composition_front.
      rewrite - (app_nil_r [T_i32 ; _]).
      apply bet_weakening.
      apply bet_const.
      simpl.
      eapply bet_composition_front.
      rewrite (separate1 T_i32 [_ ; _]). 
      apply bet_weakening.
      apply bet_binop.
      apply Binop_i32_agree.
      bet_first bet_store. 
      apply bet_get_local => //.
Qed.

Lemma is_empty_typing:
  be_typing
    {|
      tc_types_t := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
      tc_func_t := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []; Tf [T_i32; T_i32] []];
      tc_global := [];
      tc_table := [ {| tt_limits := {| lim_min := 1; lim_max := None |}; tt_elem_type := ELT_funcref |}];
      tc_memory := [ {| lim_min := 0; lim_max := None |}];
      tc_local := [T_i32];
      tc_label := [[T_i32]];
      tc_return := Some [T_i32]
    |} is_empty (Tf [] [T_i32]).
Proof.
  unfold is_empty.
  eapply bet_composition'; first by apply validate_stack_typing.
  bet_first bet_get_local.
    eapply bet_composition_front.
    rewrite - (app_nil_r [T_i32]).
    apply bet_weakening.
    apply bet_const.
    bet_first bet_binop.
    apply Binop_i32_agree.
    eapply bet_composition_front.
    rewrite - (app_nil_r [T_i32]).
    apply bet_weakening.
    apply bet_get_local => //.
    eapply bet_composition_front.
    apply bet_weakening.
    apply bet_load => //.
    apply bet_relop.
    apply Relop_i32_agree.
Qed.
    
Lemma is_full_typing :
  be_typing
    {|
      tc_types_t := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
      tc_func_t := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []; Tf [T_i32; T_i32] []];
      tc_global := [];
      tc_table := [ {| tt_limits := {| lim_min := 1; lim_max := None |}; tt_elem_type := ELT_funcref |}];
      tc_memory := [ {| lim_min := 0; lim_max := None |}];
      tc_local := [T_i32];
      tc_label := [[T_i32]];
      tc_return := Some [T_i32]
    |} is_full (Tf [] [T_i32]).
Proof.
  unfold is_empty.
  eapply bet_composition'; first by apply validate_stack_typing.
  bet_first bet_const.
    unfold typeof.
    eapply bet_composition_front.
    rewrite - (app_nil_r [T_i32]).
    apply bet_weakening.
    apply bet_const.
    unfold typeof => /=.
    eapply bet_composition_front.
    rewrite - (app_nil_r [T_i32 ; T_i32]).
    apply bet_weakening.
    apply bet_get_local => //.
    eapply bet_composition_front.
    apply bet_weakening.
    apply bet_load => //.
    simpl.
    eapply bet_composition_front.
    rewrite - (app_nil_r [T_i32;_;_]).
    apply bet_weakening.
    apply bet_const.
    simpl.
    eapply bet_composition_front.
    rewrite (separate2 T_i32 T_i32 [_;_]).
    apply bet_weakening.
    apply bet_binop.
    apply Binop_i32_agree.
    apply bet_select.
Qed.
    
Lemma pop_typing :
   be_typing
    {|
      tc_types_t := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
      tc_func_t := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []; Tf [T_i32; T_i32] []];
      tc_global := [];
      tc_table := [ {| tt_limits := {| lim_min := 1; lim_max := None |}; tt_elem_type := ELT_funcref |}];
      tc_memory := [ {| lim_min := 0; lim_max := None |}];
      tc_local := [T_i32; T_i32];
      tc_label := [[T_i32]];
      tc_return := Some [T_i32]
    |} pop (Tf [] [T_i32]).
Proof.
  unfold is_empty.
  eapply bet_composition'; first by apply validate_stack_typing.
  bet_first bet_get_local. 
    bet_first bet_load.
    eapply bet_composition_front.
    rewrite - (app_nil_r [T_i32]).
    apply bet_weakening.
    apply bet_const.
    bet_first bet_binop.
    apply Binop_i32_agree.
    bet_first bet_tee_local.
    eapply bet_composition_front.
    rewrite - (app_nil_r [T_i32]).
    apply bet_weakening.
    apply bet_get_local => //.
    bet_first bet_relop; first by apply Relop_i32_agree.
    bet_first bet_if_wasm.
    { by apply bet_unreachable. }
    { by apply bet_empty. }
    bet_first bet_get_local.
    bet_first bet_load.
    eapply bet_composition_front.
    rewrite - (app_nil_r [T_i32]).
    apply bet_weakening.
    apply bet_get_local => //.
    simpl.
    eapply bet_composition_front.
    rewrite - (app_nil_r [T_i32 ; _]).
    apply bet_weakening.
    apply bet_get_local => //.
    simpl.
    rewrite (separate1 T_i32 [_;_]).
    rewrite - (app_nil_r [T_i32]).
    apply bet_weakening.
    apply bet_store => //.
Qed.
    
Lemma push_typing:
  be_typing
    {|
      tc_types_t := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
      tc_func_t := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []; Tf [T_i32; T_i32] []];
      tc_global := [];
      tc_table := [ {| tt_limits := {| lim_min := 1; lim_max := None |}; tt_elem_type := ELT_funcref |}];
      tc_memory := [ {| lim_min := 0; lim_max := None |}];
      tc_local := [T_i32; T_i32; T_i32];
      tc_label := [[]];
      tc_return := Some []
    |} push (Tf [] []).
Proof.
  unfold is_empty.
  eapply bet_composition'; first by apply validate_stack_typing.
  bet_first bet_get_local. 
    bet_first bet_load.
    bet_first bet_tee_local.
    eapply bet_composition_front.
    rewrite - (app_nil_r [T_i32]).
    apply bet_weakening.
    apply bet_const.
    simpl.
    bet_first bet_binop; first by apply Binop_i32_agree.
    bet_first bet_if_wasm.
    { by apply bet_empty. }
    { by apply bet_unreachable. }
    bet_first bet_get_local => //.
    eapply bet_composition_front.
    rewrite - (app_nil_r [T_i32]).
    apply bet_weakening.
    apply bet_get_local => //.
    bet_first bet_store.
    bet_first bet_get_local.
    eapply bet_composition_front.
    rewrite - (app_nil_r [T_i32]).
    apply bet_weakening.
    apply bet_get_local => //.
    simpl.
    eapply bet_composition_front.
    rewrite - (app_nil_r [T_i32 ; _]).
    apply bet_weakening.
    apply bet_const.
    unfold typeof => /=.
    eapply bet_composition_front.
    rewrite (separate1 T_i32 [_;_]).
    apply bet_weakening.
    apply bet_binop.
    apply Binop_i32_agree.
    apply bet_store => //.
Qed.
    
Lemma stack_map_typing:
    be_typing
    {|
      tc_types_t := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
      tc_func_t := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []; Tf [T_i32; T_i32] []];
      tc_global := [];
      tc_table := [ {| tt_limits := {| lim_min := 1; lim_max := None |}; tt_elem_type := ELT_funcref |}];
      tc_memory := [ {| lim_min := 0; lim_max := None |}];
      tc_local := [T_i32; T_i32; T_i32; T_i32];
      tc_label := [[]];
      tc_return := Some []
    |} stack_map (Tf [] []).
Proof.
  unfold is_empty.
  eapply bet_composition'; first by apply validate_stack_typing.
  bet_first bet_get_local.
    bet_first bet_load.
    bet_first bet_set_local.
    bet_first bet_get_local.
    eapply bet_composition_front.
    rewrite (separate1 T_i32).
    apply bet_weakening.
    apply bet_const.
    bet_first bet_binop.
    apply Binop_i32_agree.
    bet_first bet_set_local.
    apply bet_block.
    apply bet_loop => /=.
    bet_first bet_get_local.
    eapply bet_composition_front.
    rewrite (separate1 T_i32).
    apply bet_weakening.
    apply bet_get_local => //.
    bet_first bet_relop.
    apply Relop_i32_agree.
    rewrite - (app_nil_l [T_i32]).
    bet_first bet_br_if.
    bet_first bet_get_local.
    eapply bet_composition_front.
    rewrite (separate1 T_i32).
    apply bet_weakening.
    apply bet_get_local => //.
    eapply bet_composition_front.
    simpl ; rewrite (separate2 T_i32).
    apply bet_weakening.
    apply bet_get_local => //.
    eapply bet_composition_front.
    simpl ; rewrite (separate2 T_i32 _ [_]).
    apply bet_weakening.
    apply bet_load => //.
    eapply bet_composition_front.
    simpl ; rewrite (separate3 T_i32 T_i32 T_i32 []).
    apply bet_weakening.
    apply bet_get_local => //.
    eapply bet_composition_front.
    simpl ; rewrite (separate2 T_i32 T_i32 [_;_]).
    apply bet_weakening.
    rewrite (separate1 T_i32 [_]).
    apply bet_call_indirect => //=.
    eapply bet_composition_front.
    simpl ; rewrite (separate1 T_i32 [_;_]).
    apply bet_weakening.
    apply bet_store => //.
    eapply bet_composition_front.
    apply bet_weakening.
    apply bet_const.
    bet_first bet_binop.
    apply Binop_i32_agree.
    bet_first bet_set_local.
    rewrite - (app_nil_l []).
    apply bet_br => //. 
Qed.
    

Lemma module_typing_stack :
  module_typing stack_module [] expts.
Proof.
  unfold module_typing => /=. 
  exists [Tf [] [T_i32] ; Tf [T_i32] [T_i32] ; Tf [T_i32] [T_i32] ;
     Tf [T_i32] [T_i32] ; Tf [T_i32 ; T_i32] [] ; Tf [T_i32 ; T_i32] [] ], [].
  repeat split => //.
  repeat (apply Forall2_cons ; repeat split => //) => /=.
  - by apply new_stack_typing.
  - by apply is_empty_typing.
  - by apply is_full_typing.
  - by apply pop_typing.
  - by apply push_typing.
  - by apply stack_map_typing.
  - unfold module_export_typing.
    repeat (apply Forall2_cons ; repeat split => //) => //=.
Qed.




Definition stack_instantiate :=
  [ ID_instantiate [0%N ; 1%N ; 2%N ; 3%N ; 4%N ; 5%N ; 6%N] 0 []  ].

Notation " n ↪[vis]{ q } v" := (ghost_map_elem (V := module_export) visGName n q v%V)
                                 (at level 20, q at level 5, format " n ↪[vis]{ q } v") .
Notation " n ↪[vis] v" := (ghost_map_elem (V := module_export) visGName n (DfracOwn 1) v%V)
                            (at level 20, format " n ↪[vis] v").

Notation " n ↪[mods]{ q } v" := (ghost_map_elem (V := module) msGName n q v%V)
                                  (at level 20, q at level 5, format " n ↪[mods]{ q } v") .
Notation " n ↪[mods] v" := (ghost_map_elem (V := module) msGName n (DfracOwn 1) v%V)
                             (at level 20, format " n ↪[mods] v").



Definition stack_instance idfs m t :=
  {|
    inst_types := [Tf [] [T_i32] ; Tf [T_i32] [T_i32] ; Tf [T_i32 ; T_i32] []] ;
    inst_funcs := idfs ;
    inst_tab := [t] ;
    inst_memory := [m] ;
    inst_globs := []
  |}.

 


 

Definition spec0_new_stack (idf0 : nat) (i0 : instance) (l0 : seq.seq value_type)
           (f0 : seq.seq basic_instruction) (isStack : Z -> seq.seq i32 -> iPropI Σ)
           (nextStackAddrIs : nat -> iPropI Σ) E : iPropI Σ :=

 (∀ (f : frame) (addr : nat), 
      {{{ ↪[frame] f ∗ 
           N.of_nat idf0 ↦[wf] FC_func_native i0 (Tf [] [T_i32]) l0 f0 ∗
           nextStackAddrIs addr ∗
           ⌜ (Wasm_int.Int32.modulus - 1)%Z <> Wasm_int.Int32.Z_mod_modulus (ssrnat.nat_of_bin (N.of_nat addr `div` page_size)) ⌝ ∗
           ⌜ (N.of_nat addr + 4 < Z.to_N (two_power_nat 32))%N ⌝ ∗
           ⌜ (page_size | N.of_nat addr)%N ⌝  }}}
        [AI_invoke idf0] @ E
        {{{  v, (∃ (k : Z), ⌜ v = immV [value_of_int k] ⌝ ∗
                                       (⌜ (k = -1)%Z ⌝  ∗
                                          nextStackAddrIs addr ∨
                                          ⌜ (0 <= k)%Z /\ (k + Z.of_N page_size <= two32)%Z ⌝ ∗
                                          isStack k []  ∗
                                          nextStackAddrIs (addr + N.to_nat page_size) ))  ∗
                            N.of_nat idf0 ↦[wf] FC_func_native i0 (Tf [] [T_i32]) l0 f0 ∗
                            ↪[frame] f }}} )%I.



  
Definition spec1_is_empty idf1 i1 l1 f1 (isStack : Z -> seq.seq i32 -> iPropI Σ) (E: coPset) :=
  (∀ v s f, {{{ ↪[frame] f  ∗
                 N.of_nat idf1 ↦[wf] FC_func_native i1 (Tf [T_i32] [T_i32]) l1 f1 ∗
                 ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - length s * 4)%Z ⌝ ∗ 
                 isStack v s }}}
              [AI_basic (i32const v) ; AI_invoke idf1] @ E
              {{{ w, (∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s ∗
                                      ⌜ (k = 1 /\ s = []) \/
                             (k = 0 /\ s <> []) ⌝) ∗
                                                 N.of_nat idf1 ↦[wf] FC_func_native i1 (Tf [T_i32] [T_i32]) l1 f1 ∗ 
                                                 ↪[frame] f}}})%I.



Definition spec2_is_full idf2 i2 l2 f2 (isStack : Z -> seq.seq i32 -> iPropI Σ) E :=
  (∀ v s f, {{{ ↪[frame] f ∗
                 N.of_nat idf2 ↦[wf] FC_func_native i2 (Tf [T_i32] [T_i32]) l2 f2 ∗
                 ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - length s * 4 )%Z ⌝ ∗ 
                 isStack v s }}} 
              [AI_basic (i32const v) ; AI_invoke idf2] @ E
              {{{ w, (∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗
                                      isStack v s ∗
                                      ⌜ k = 1 \/ (length s < two14 - 1)%Z ⌝) ∗
                                                                            N.of_nat idf2 ↦[wf] FC_func_native i2 (Tf [T_i32] [T_i32]) l2 f2 ∗ 
                                                                            ↪[frame] f }}})%I.

Definition spec3_pop idf3 i3 l3 f3 (isStack : Z -> seq.seq i32 -> iPropI Σ) E :=
  (∀ a v s f, {{{ ↪[frame] f ∗
                   N.of_nat idf3 ↦[wf] FC_func_native i3 (Tf [T_i32] [T_i32]) l3 f3
                   ∗ ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - S (length s) * 4 )%Z ⌝
                   ∗ isStack v (a :: s) }}}
                [AI_basic (i32const v) ; AI_invoke idf3] @ E
                {{{ w, ⌜ w = immV [VAL_int32 a] ⌝ ∗
                                  isStack v s ∗
                                  N.of_nat idf3 ↦[wf] FC_func_native i3 (Tf [T_i32] [T_i32]) l3 f3 ∗
                                  ↪[frame] f }}})%I.






Definition spec4_push idf4 i4 l4 f4 isStack E :=
  (∀ a v s f, {{{ ↪[frame] f ∗
                   N.of_nat idf4 ↦[wf] FC_func_native i4 (Tf [T_i32 ; T_i32] []) l4 f4 
                   ∗ ⌜ (0 <= v <= Wasm_int.Int32.max_unsigned - 4 - S (length s) * 4 )%Z ⌝
                   ∗ ⌜ (length s < two14 - 1)%Z ⌝
                   ∗ isStack v s }}}
                [ AI_basic (BI_const (VAL_int32 a)) ; AI_basic (i32const v) ;
                  AI_invoke idf4 ] @ E
                {{{ w, ⌜ w = immV [] ⌝ ∗
                                  isStack v (a :: s) ∗
                                  N.of_nat idf4 ↦[wf] FC_func_native i4 (Tf [T_i32 ; T_i32] []) l4 f4 ∗
                                  ↪[frame] f }}})%I.


Definition spec5_stack_map idf5 i5 l5 f5 (isStack : Z -> seq.seq i32 -> iPropI Σ) j0 E :=
  (∀ (f0 : frame) (f : i32) (v : Z) (s : seq.seq i32) a cl
      (Φ : i32 -> iPropI Σ) (Ψ : i32 -> i32 -> iPropI Σ) ,
      {{{  ↪[frame] f0 ∗
            N.of_nat idf5 ↦[wf] FC_func_native i5 (Tf [T_i32 ; T_i32] []) l5 f5 ∗
            ⌜ (0 <= v)%Z ⌝ ∗
            ⌜ (v + 4 + length s * 4 ≤ Wasm_int.Int32.max_unsigned)%Z ⌝ ∗
            isStack v s ∗
            stackAll s Φ ∗
            N.of_nat j0 ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
            (N.of_nat a) ↦[wf] cl ∗
            ⌜ match cl with FC_func_native _ t _ _ => t | FC_func_host t _ => t end
         = Tf [T_i32] [T_i32] ⌝ ∗ 
              (∀ (u : i32) (fc : frame),
                   {{{ Φ u ∗
                      ⌜ i5 = f_inst fc ⌝ ∗
                       ↪[frame] fc ∗
                       N.of_nat j0 ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
                       (N.of_nat a) ↦[wf] cl
                  }}}
                  [ AI_basic (BI_const (VAL_int32 u)) ;
                    AI_invoke a ] @ E
                  {{{ w, (∃ v, ⌜ w = immV [VAL_int32 v] ⌝ ∗ Ψ u v)
                           ∗ ↪[frame] fc
                           ∗ N.of_nat j0 ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) 
                           ∗ (N.of_nat a) ↦[wf] cl }}}
                  )  }}}
    [ AI_basic (BI_const (VAL_int32 f)) ; AI_basic (i32const v) ; AI_invoke idf5 ] @ E
    {{{ w, ⌜ w = immV [] ⌝ ∗
           (∃ s', isStack v s' ∗ stackAll2 s s' Ψ) ∗
           N.of_nat idf5 ↦[wf] FC_func_native i5 (Tf [T_i32 ; T_i32] []) l5 f5 ∗
           ↪[frame] f0 ∗
            N.of_nat j0 ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
            (N.of_nat a) ↦[wf] cl
  }}})%I.

  (* A trap allowing version for code that might trap *)
Definition spec5_stack_map_trap `{!logrel_na_invs Σ} idf5 i5 l5 f5 (isStack : Z -> seq.seq i32 -> iPropI Σ) j0 E :=
  (∀ (f0 : frame) (f : i32) (v : Z) (s : seq.seq i32) a cl γ
     (Φ : i32 -> iPropI Σ) (Ψ : i32 -> i32 -> iPropI Σ) ,
      ⌜↑γ ⊆ E⌝ →
      {{{  ↪[frame] f0 ∗ na_own logrel_nais ⊤ ∗
            N.of_nat idf5 ↦[wf] FC_func_native i5 (Tf [T_i32 ; T_i32] []) l5 f5 ∗
            ⌜ (0 <= v)%Z ⌝ ∗
            ⌜ (v + 4 + length s * 4 ≤ Wasm_int.Int32.max_unsigned)%Z ⌝ ∗
            isStack v s ∗
            stackAll s Φ ∗
            N.of_nat j0 ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
            na_inv logrel_nais γ ((N.of_nat a) ↦[wf] cl) ∗
            ⌜ match cl with FC_func_native _ t _ _ => t | FC_func_host t _ => t end 
           = Tf [T_i32] [T_i32] ⌝ ∗  
              (∀ (u : i32) (fc : frame),
                   {{{ Φ u ∗
                      ⌜ i5 = f_inst fc ⌝ ∗
                       ↪[frame] fc ∗
                       na_own logrel_nais ⊤
                  }}}
                  [ AI_basic (BI_const (VAL_int32 u)) ;
                    AI_invoke a ] @ E
                  {{{ w, (⌜ w = trapV ⌝ ∨ ((∃ v, ⌜ w = immV [VAL_int32 v] ⌝ ∗ Ψ u v)))
                           ∗ na_own logrel_nais ⊤ ∗ ↪[frame] fc }}}
                  )  }}}
    [ AI_basic (BI_const (VAL_int32 f)) ; AI_basic (i32const v) ; AI_invoke idf5 ] @ E
    {{{ w, (⌜ w = trapV ⌝ ∨ (⌜ w = immV [] ⌝ ∗
                              (∃ s', isStack v s' ∗ stackAll2 s s' Ψ) ∗
                              N.of_nat idf5 ↦[wf] FC_func_native i5 (Tf [T_i32 ; T_i32] []) l5 f5)) ∗
      N.of_nat j0 ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
      na_own logrel_nais ⊤ ∗
      ↪[frame] f0
  }}})%I.

  Lemma instantiate_stack_spec `{!logrel_na_invs Σ} (s : stuckness) (E: coPset) (hv0 hv1 hv2 hv3 hv4 hv5 hv6 : module_export) :
  (* Knowing 0%N holds the stack module… *)
  0%N ↪[mods] stack_module -∗
     (* … and we own the vis 0%N thru 4%N … *)
     ([∗ list] k↦hvk ∈ [hv0 ; hv1 ; hv2 ; hv3 ; hv4 ; hv5 ; hv6], N.of_nat k ↪[vis] hvk) -∗
     (* … instantiating the stack-module (by lazyness, this is expressed here with
        a take 1 in order to avoir rewriting the instantiation), yields the following : *)
     WP ((stack_instantiate, []) : host_expr)
     @ s ; E
             {{ λ v : host_val,
                 (* Instantiation succeeds *)
                 ⌜ v = immHV [] ⌝ ∗
                 (* 0%N still owns the stack_module *)
                 0%N ↪[mods] stack_module ∗ 
                  ∃ (idf0 idf1 idf2 idf3 idf4 idf5 idt : nat)
                    (name0 name1 name2 name3 name4 name5 name6 : name)
                    (f0 f1 f2 f3 f4 f5 : list basic_instruction)
                    (i0 : instance)
                    (l0 l1 l2 l3 l4 l5 : list value_type)
                    tab 
                    (isStack : Z -> seq.seq i32 -> iPropI Σ)
                    (nextStackAddrIs : nat -> iPropI Σ), 
                    (* Our exports are in the vis 0%N thru 4%N. Note that everything is 
                       existantially quantified. In fact, all the f_i, i_i and l_i 
                       could be given explicitely, but we quantify them existantially 
                       to show modularity : we do not care what the functions are, 
                       we only care about their spec (see next comment). This also
                       makes this lemma more readable than if we stated explicitely all
                       the codes of the functions *)
                    let inst_vis := (map (λ '(name, idf),
                                                 {| modexp_name := name ;
                                                   modexp_desc := MED_func (Mk_funcidx idf)
                                                 |}) [(name0, idf0) ; (name1, idf1) ;
                                                      (name2, idf2) ; (name3, idf3) ;
                                                      (name4, idf4) ; (name5, idf5) ])
                                        ++ [ {| modexp_name := name6 ;
                                               modexp_desc := MED_table (Mk_tableidx idt) |} ]
                    in 
                    let inst_map := fold_left (λ fs '(idf,i,t,l,f),
                                                <[ N.of_nat idf := FC_func_native i t l f ]> fs)
                                              (rev [(idf0, i0, Tf [] [T_i32], l0, f0) ;
                                               (idf1, i0, Tf [T_i32] [T_i32], l1, f1) ;
                                                    (idf2, i0, Tf [T_i32] [T_i32], l2, f2) ;
                                                    (idf3, i0, Tf [T_i32] [T_i32], l3, f3) ;
                                                    (idf4, i0, Tf [T_i32 ; T_i32] [], l4, f4) ;
                                              (idf5, i0, Tf [T_i32 ; T_i32] [], l5, f5)])
                                              ∅ in 
                    (* These two import functions state that all [vis] and [wf] point 
                       to the correct exports/functions, i.e. a client will be able 
                       to successfully import them *)
                    import_resources_host [0%N; 1%N; 2%N; 3%N; 4%N ; 5%N ; 6%N] inst_vis ∗
                    import_resources_wasm_typecheck_sepL2 inst_vis expts inst_map
                    (<[ N.of_nat idt := tab ]> ∅) 
                    ∅ ∅ ∗
                    ⌜ NoDup (modexp_desc <$> inst_vis) ⌝ ∗
                    ⌜ length tab.(table_data) >= 1 ⌝ ∗
                    (* We own a token that hides ressources needed for the new_stack function *)
                    nextStackAddrIs 0 ∗
                    (* And finally we have specs for all our exports : *)
                    (* Spec for new_stack (call 0) *)
                    spec0_new_stack idf0 i0 l0 f0 isStack nextStackAddrIs E ∗
                    (* Spec for is_empty (call 1) *)
                    spec1_is_empty idf1 i0 l1 f1 isStack E ∗
                    (* Spec for is_full (call 2) *)
                    spec2_is_full idf2 i0 l2 f2 isStack E ∗
                    (* Spec for pop (call 3) *)
                    spec3_pop idf3 i0 l3 f3 isStack E ∗
                    (* Spec for push (call 4) *)
                    spec4_push idf4 i0 l4 f4 isStack E ∗
                    (* Spec of stack_map (call 5) *)
                    spec5_stack_map idf5 i0 l5 f5 isStack idt E ∗
                    spec5_stack_map_trap idf5 i0 l5 f5 isStack idt E
                                          
             }}.
  Proof.
    iIntros "Hmod (Hhv0 & Hhv1 & Hhv2 & Hhv3 & Hhv4 & Hhv5 & Hhv6 & _)".
    iApply (weakestpre.wp_strong_mono s _ E
             with "[Hmod Hhv0 Hhv1 Hhv2 Hhv3 Hhv4 Hhv5 Hhv6]") => //.
    iApply (instantiation_spec_operational_no_start
             with "[Hmod Hhv0 Hhv1 Hhv2 Hhv3 Hhv4 Hhv5 Hhv6]") ;
      try exact module_typing_stack => //.
    - by unfold stack_module.
    - unfold module_restrictions => /=.
      repeat split => //=.
      exists [] => //.
      exists [] => //.
      exists [] => //.
    - unfold instantiation_resources_pre.
      iSplitL "Hmod" ; first done.
      unfold instantiation_resources_pre_wasm.
      rewrite irwt_nodup_equiv.
      repeat iSplit.
    - by unfold import_resources_host.
    - iPureIntro. apply dom_empty.
    - iPureIntro. apply dom_empty.
    - iPureIntro. apply dom_empty.
    - iPureIntro. apply dom_empty.
    - done.
    - iPureIntro. unfold module_elem_bound_check_gmap => //=.
    - iPureIntro. unfold module_data_bound_check_gmap => //=.
    - unfold export_ownership_host.
      iSplitL "Hhv0".
      by iExists _.
      iSplitL "Hhv1".
      by iExists _.
      iSplitL "Hhv2".
      by iExists _.
      iSplitL "Hhv3".
      by iExists _.
      iSplitL "Hhv4".
      by iExists _.
      iSplitL "Hhv5".
      by iExists _.
      iSplitL "Hhv6".
      by iExists _.
      done.
      done.
    - simpl.
      by apply NoDup_nil.
    - iIntros (v) "Hinst".
      unfold instantiation_resources_post.
      iDestruct "Hinst" as "(%Hvsucc & Hmod & Himphost & Hinst)".
      subst v; iSplitR => //.
      iDestruct "Hinst" as (inst) "[Himpwasm Hexphost]".
      iDestruct "Himpwasm" as (g_inits t_inits m_inits gms wts wms) "(Himpwasm & %Hinst & -> & -> & %Hbound & -> & -> & %Hbound' & %Hginit & -> & Hexpwasm)".
      destruct Hinst as (Hinsttype & Hinstfunc & Hinsttab & Hinstmem & Hinstglob).
      unfold module_inst_resources_wasm, module_export_resources_host => /=.
      destruct inst => /=.
      iDestruct "Hexpwasm" as "(Hexpwf & Hexpwt & Hexpwm & Hexpwg)".
      unfold module_inst_resources_func, module_inst_resources_glob,
        module_inst_resources_tab, module_inst_resources_mem => /=.
      unfold big_sepL2 => /=.
      destruct inst_funcs as [|? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf Hexpwf]".
      destruct inst_funcs as [|? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf0 Hexpwf]".
      destruct inst_funcs as [|? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf1 Hexpwf]".
      destruct inst_funcs as [|? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf2 Hexpwf]".
      destruct inst_funcs as [|? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf3 Hexpwf]".
      destruct inst_funcs as [| ? inst_funcs] ; first done ;
        iDestruct "Hexpwf" as "[Hf4 Hexpwf]".
      destruct inst_funcs ; last done.
      destruct inst_tab ; first done.
      iDestruct "Hexpwt" as "[Htab Hexpwt]".
      destruct inst_tab ; last done.
      destruct inst_memory as [|m inst_memory] ; first done.
      iDestruct "Hexpwm" as "[Hexpwm ?]".
      destruct inst_memory ; last done.
      iDestruct "Hexpwm" as "(Hexpwm & Hmemlength & Hmemlim)".
      destruct inst_globs ; last done.
      iDestruct "Hexphost" as "(Hexp0 & Hexp1 & Hexp2 & Hexp3 & Hexp4 & Hexp5 & Hexp6 & _)".
      iDestruct "Hexp0" as (name0) "Hexp0".
      iDestruct "Hexp1" as (name1) "Hexp1".
      iDestruct "Hexp2" as (name2) "Hexp2".
      iDestruct "Hexp3" as (name3) "Hexp3".
      iDestruct "Hexp4" as (name4) "Hexp4".
      iDestruct "Hexp5" as (name5) "Hexp5".
      iDestruct "Hexp6" as (name6) "Hexp6".
      simpl in * ; subst.
      iSplitL "Hmod" ; first done.
      iExists f, f0, f1, f2, f3, f4, t.
      iExists name0, name1, name2, name3, name4, name5, name6.
      iExists _, _, _, _, _, _.
      iExists _.
      iExists _, _, _, _, _, _.
      iExists _.
      iExists (λ a b, isStack a b m).
      iExists (λ n, (N.of_nat m↦[wmlength] N.of_nat n)%I).
      iDestruct (mapsto_frac_ne with "Hf Hf0") as "%H01" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf Hf1") as "%H02" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf Hf2") as "%H03" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf Hf3") as "%H04" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf Hf4") as "%H05" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf0 Hf1") as "%H12" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf0 Hf2") as "%H13" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf0 Hf3") as "%H14" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf0 Hf4") as "%H15" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf1 Hf2") as "%H23" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf1 Hf3") as "%H24" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf1 Hf4") as "%H25" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf2 Hf3") as "%H34" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf2 Hf4") as "%H35" ; first by eauto.
      iDestruct (mapsto_frac_ne with "Hf3 Hf4") as "%H45" ; first by eauto.
      iSplitL "Hexp0 Hexp1 Hexp2 Hexp3 Hexp4 Hexp5 Hexp6".
      unfold import_resources_host.
      iFrame. by iModIntro.
      iSplitL "Hf Hf0 Hf1 Hf2 Hf3 Hf4 Htab".
      iSplitR.
    - iPureIntro.
      simpl.
      repeat rewrite dom_insert.
      done.
    - iSplitL "Hf".
      iExists _.
      iFrame.
      iPureIntro.
      rewrite lookup_insert.
      split => //.
      iSplitL "Hf0".
      iExists _ ; iFrame.
      iPureIntro.
      rewrite lookup_insert_ne ; last assumption.
      rewrite lookup_insert.
      split => //.
      iSplitL "Hf1".
      iExists _ ; iFrame.
      iPureIntro.
      do 2 (rewrite lookup_insert_ne ; last assumption).
      rewrite lookup_insert.
      split => //.
      iSplitL "Hf2".
      iExists _ ; iFrame.
      iPureIntro.
      do 3 (rewrite lookup_insert_ne ; last assumption).
      rewrite lookup_insert.
      split => //.
      iSplitL "Hf3".
      iExists _ ; iFrame.
      iPureIntro.
      do 4 (rewrite lookup_insert_ne ; last assumption).
      rewrite lookup_insert.
      split => //.
      iSplitL "Hf4".
      iExists _ ; iFrame.
      iPureIntro.
      do 5 (rewrite lookup_insert_ne ; last assumption).
      rewrite lookup_insert.
      split => //.
      iSplitL; cbn; last done.
      iExists _, _ ; iFrame.
      iPureIntro.
      rewrite lookup_insert.
      split => //.
      iSplitR.
      { iPureIntro.
        repeat (apply NoDup_cons; split; cbn; first by set_solver).
        by apply NoDup_nil.
      }
      iSplitR.
      iPureIntro.
      simpl.
      lia.
      iSplitL "Hmemlength" ; first done.
    - iSplitR. iIntros "!>" (fr addr Φ) "!> (Hf & Hwf & Hlen & % & % & %) HΦ".
      iApply wp_wand_r.
      iSplitR "HΦ".
      { 
        rewrite - (app_nil_l [AI_invoke f]).
        iApply (wp_invoke_native with "Hf Hwf") => //.
        iIntros "!> [Hf Hf0]".
        iSimpl.
        iApply (wp_frame_bind with "Hf").
        unfold iris.to_val => //=.
        iIntros "Hf".
        rewrite - (app_nil_l [AI_basic _]).
        iApply (wp_block with "Hf") => //.
        iIntros "!> Hf".
        iApply (wp_label_bind with "[Hlen Hf Hf0]") ; last first.
        iPureIntro.
        unfold lfilled, lfill => /=.
        instantiate (5 := []) => /=.
        rewrite app_nil_r.
        done.
        iApply (spec_new_stack with "[Hlen Hf]").
        iFrame.
        repeat iSplit ; iPureIntro => //=.
        lia.
        iIntros (w) "H".
        iDestruct "H" as (k) "(-> & H & Hf)" => /=.
        iDestruct "Hf" as (f5) "[Hf %Hf4]".
        iApply (wp_wand_ctx with "[H Hf Hf0]").
        iApply (wp_val_return with "Hf") => //.
        iIntros "Hf".
        rewrite app_nil_r app_nil_l.
        iApply wp_value => //=.
        unfold IntoVal.
        apply of_to_val => //.
        instantiate (1 := λ v, (⌜ v = immV [value_of_int k] ⌝ ∗
                                           (⌜k = (-1)%Z⌝ ∗N.of_nat m↦[wmlength]N.of_nat addr ∨  ⌜ (0 ≤ k)%Z ∧ (k + Z.pos (64 * 1024) ≤ two32)%Z⌝ ∗ isStack k [] m ∗
                                                                                             N.of_nat m↦[wmlength](N.of_nat addr + page_size)%N) ∗
                                                                                             N.of_nat f↦[wf]FC_func_native
                           {|
                             inst_types :=
                               [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
                             inst_funcs := [f; f0; f1; f2; f3;f4];
                             inst_tab := [t];
                             inst_memory := [m];
                             inst_globs := []
                           |} (Tf [] [T_i32]) [T_i32]
                           new_stack ∗ ↪[frame] f5 )%I).
        iSimpl.
        iFrame.
        done.
        iIntros (w) "(-> & H & Hf0 & Hf)". 
        iExists _.
        iFrame.
        iIntros "Hf".
        iSimpl.         
        iApply (wp_frame_value with "Hf") => //.
        iNext.
        instantiate (1 := λ v, ((∃ k, ⌜ v = immV [value_of_int k] ⌝ ∗
                                           (⌜k = (-1)%Z⌝ ∗ N.of_nat m↦[wmlength]N.of_nat addr ∨  ⌜ (0 ≤ k)%Z ∧ (k + Z.pos (64 * 1024) ≤ two32)%Z⌝ ∗ isStack k [] m ∗
                                                                                             N.of_nat m↦[wmlength](N.of_nat addr + page_size)%N)) ∗
                                                                                             N.of_nat f↦[wf]FC_func_native
                           {|
                             inst_types :=
                               [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
                             inst_funcs := [f; f0; f1; f2; f3; f4];
                             inst_tab := [t];
                             inst_memory := [m];
                             inst_globs := []
                           |} (Tf [] [T_i32]) [T_i32]
                           new_stack)%I).
        iSimpl.
        iFrame.
        iExists k.
        iFrame.
        done. }
      iIntros (w) "[[H Hf0] Hf]".
      iApply "HΦ".
      iFrame.
      iDestruct "H" as (k) "[-> [[-> Hlen] | (% & Hs & Hlen)]]".
      iExists (-1)%Z.
      iSplit ; first done.
      iLeft.
      by iFrame.
      iExists k.
      iSplit ; first done.
      iRight.
      unfold page_size.
      replace (N.of_nat addr + 64 * 1024)%N with
        (N.of_nat (addr + Pos.to_nat (64 * 1024))) ;
        last lia.
      by iFrame.
    - iSplitR.
      iIntros "!>" (v0 s0 vs Φ) "!> (Hf & Hf0 & %H & %Hlen & %Hdiv & Hlen) HΦ".
      iApply wp_wand_r.
      iSplitR "HΦ".
      { rewrite (separate1 (AI_basic (i32const _)) _).
        rewrite - (app_nil_r [AI_basic _]).
        iApply (wp_invoke_native with "Hf Hf0") => //.
        iIntros "!> [Hf Hf0]".
        iSimpl.
        iApply (wp_frame_bind with "Hf").
        done. iIntros "Hf".
        rewrite - (app_nil_l [AI_basic _]).
        iApply (wp_block with "Hf") => //.
        iIntros "!> Hf".
        iApply (wp_label_bind with "[Hlen Hf Hf0]") ; last first.
        iPureIntro.
        unfold lfilled, lfill => /=.
        instantiate (5 := []) => /=.
        rewrite app_nil_r.
        done.
        iApply (spec_is_empty with "[Hlen Hf]").
        iFrame.
        repeat iSplit ; iPureIntro => //=.
        lia.
        by destruct H.
        iIntros (w) "H".
        iDestruct "H" as (k) "(-> & H & %Hk & Hf)" => /=.
        iDestruct "Hf" as (f5) "[Hf %Hf4]".
        iApply (wp_wand_ctx with "[H Hf Hf0]").
        iApply (wp_val_return with "Hf") => //.
        iIntros "Hf".
        rewrite app_nil_r app_nil_l.
        iApply wp_value => //=.
        unfold IntoVal.
        apply of_to_val => //.
        iFrame.
        instantiate (1 := λ v, (⌜ v = immV [value_of_int k] ⌝ ∗
                                           isStack v0 s0 m ∗
                                            N.of_nat f0↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3 ; f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32] [T_i32]) []
                            is_empty ∗ ↪[frame] f5)%I).
        iSimpl.
        iFrame.
        done.
        iIntros (w) "(-> & H &  Hf0 & Hf)".
        iExists _.
        iFrame.
        iIntros "Hf".
        iSimpl.         
        iApply (wp_frame_value with "Hf") => //.
        iNext.
        instantiate (1 := λ v, ((∃ k, ⌜ v = immV [value_of_int k] ⌝ ∗
                                                 ⌜ k = 1 /\ s0 = [] \/ k = 0 /\ s0 <> [] ⌝) ∗
                                                                                        isStack v0 s0 m ∗
                                                                                        N.of_nat f0↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3; f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32] [T_i32]) []
                            is_empty)%I).                            
        iSimpl.
        iFrame.
        iExists k.
        iFrame.
        done. }
      iIntros (w) "[(H & Hs & Hf0) Hf]".
      iDestruct "H" as (k) "%Hk".
      iApply "HΦ".
      iFrame.
      by iExists _.
    - iSplitR.
      iIntros "!>" (v0 s0 vs Φ) "!> (Hf & Hf0 & %H & %Hlen & %Hdiv & Hlen) HΦ".
      iApply wp_wand_r.
      iSplitR "HΦ".
      { rewrite (separate1 (AI_basic (i32const _)) _).
        rewrite - (app_nil_r [AI_basic _]).
        iApply (wp_invoke_native with "Hf Hf0") => //.
        iIntros "!> [Hf Hf0]".
        iSimpl.
        iApply (wp_frame_bind with "Hf").
        done. iIntros "Hf".
        rewrite - (app_nil_l [AI_basic _]).
        iApply (wp_block with "Hf") => //.
        iIntros "!> Hf".
        iApply (wp_label_bind with "[Hlen Hf Hf0]") ; last first.
        iPureIntro.
        unfold lfilled, lfill => /=.
        instantiate (5 := []) => /=.
        rewrite app_nil_r.
        done.
        iApply (spec_is_full with "[Hlen Hf]").
        iFrame.
        repeat iSplit ; iPureIntro => //=.
        lia.
        by destruct H.
        iIntros (w) "H".
        iDestruct "H" as (k) "(-> & H & %Hk & Hf)" => /=.
        iDestruct "Hf" as (f5) "[Hf %Hf4]".
        iApply (wp_wand_ctx with "[H Hf Hf0]").
        iApply (wp_val_return with "Hf") => //.
        iIntros "Hf".
        rewrite app_nil_r app_nil_l.
        iApply wp_value => //=.
        unfold IntoVal.
        apply of_to_val => //.
        iFrame.
        instantiate (1 := λ v, (⌜ v = immV [value_of_int k] ⌝ ∗
                                           isStack v0 s0 m ∗
                                           N.of_nat f1↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3 ; f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32] [T_i32]) []
                            is_full
                            ∗ ↪[frame] f5
                              )%I).
        iSimpl.
        iFrame.
        done.
        iIntros (w) "(-> & H &  Hf0 & Hf)".
        iExists _.
        iFrame.
        iIntros "Hf".
        iSimpl.         
        iApply (wp_frame_value with "Hf") => //.
        iNext.
        instantiate (1 := λ v, ((∃ k, ⌜ v = immV [value_of_int k] ⌝ ∗
                                                 ⌜ k = 1 \/ (length s0 < two14 - 1)%Z ⌝) ∗
                                                                                        isStack v0 s0 m ∗
                                                                                        N.of_nat f1↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3 ; f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32] [T_i32]) []
                            is_full)%I).                            
        iSimpl.
        iFrame.
        iExists k.
        iFrame.
        done. }
      iIntros (w) "[(H & Hs & Hf0) Hf]".
      iDestruct "H" as (k) "%Hk".
      iApply "HΦ".
      iFrame.
      by iExists _.
    - iSplitR.
      iIntros "!>" (a v0 s0 vs Φ) "!> (Hf & Hf0 & %H & %Ha & Hs) HΦ". 
      iApply wp_wand_r.
      iSplitR "HΦ".
      { rewrite (separate1 (AI_basic (i32const _)) _).
        rewrite - (app_nil_r [AI_basic _]).
        iApply (wp_invoke_native with "Hf Hf0") => //.
        iIntros "!> [Hf Hf0]".
        iSimpl.
        iApply (wp_frame_bind with "Hf").
        done. iIntros "Hf".
        rewrite - (app_nil_l [AI_basic _]).
        iApply (wp_block with "Hf") => //.
        iIntros "!> Hf".
        iApply (wp_label_bind with "[Hs Hf Hf0]") ; last first.
        iPureIntro.
        unfold lfilled, lfill => /=.
        instantiate (5 := []) => /=.
        rewrite app_nil_r.
        done.
        iApply (spec_pop with "[Hs Hf]").
        iFrame.
        repeat iSplit ; iPureIntro => //=.
        lia.
        lia.
        by destruct H.
        iIntros (w) "H".
        iDestruct "H" as "(-> & Hs & Hf)" => /=.
        iDestruct "Hf" as (f5) "[Hf %Hf4]".
        iApply (wp_wand_ctx with "[Hs Hf Hf0]").
        iApply (wp_val_return with "Hf") => //.
        iIntros "Hf".
        rewrite app_nil_r app_nil_l.
        iApply wp_value => //=.
        unfold IntoVal.
        apply of_to_val => //.
        iFrame.
        instantiate (1 := λ v, (⌜ v = immV [_] ⌝ ∗
                                           isStack v0 s0 m ∗
                                            N.of_nat f2↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3 ; f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32] [T_i32]) [T_i32]
                            pop ∗ ↪[frame] f5)%I).
        iSimpl.
        iFrame.
        done.
        iIntros (w) "(-> & H &  Hf0 & Hf)".
        iExists _.
        iFrame.
        iIntros "Hf".
        iSimpl.         
        iApply (wp_frame_value with "Hf") => //.
        iNext.
        instantiate (1 := λ v,  (⌜ v = immV [_] ⌝ ∗
                                            isStack v0 s0 m ∗
                                            N.of_nat f2↦[wf]FC_func_native
                                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3 ; f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32] [T_i32]) [T_i32]
                            pop)%I).
        iSimpl.
        iFrame.
        done. }
      iIntros (w) "[(-> & Hs & Hf0) Hf]".
      iApply "HΦ".
      by iFrame.
    - iSplitR. iIntros "!>" (a v0 s0 vs Φ) "!> (Hf & Hf0 & %H & %Ha & %Hlen & Hs) HΦ".
      iApply wp_wand_r.
      iSplitR "HΦ".
      { rewrite (separate2 _ (AI_basic (i32const _)) _).
        rewrite - (app_nil_r [AI_basic _]).
        iApply (wp_invoke_native with "Hf Hf0") => //.
        iIntros "!> [Hf Hf0]".
        iSimpl.
        iApply (wp_frame_bind with "Hf").
        done. iIntros "Hf".
        rewrite - (app_nil_l [AI_basic _]).
        iApply (wp_block with "Hf") => //.
        iIntros "!> Hf".
        iApply (wp_label_bind with "[Hs Hf Hf0]") ; last first.
        iPureIntro.
        unfold lfilled, lfill => /=.
        instantiate (5 := []) => /=.
        rewrite app_nil_r.
        done.
        iApply (spec_push with "[Hs Hf]").
        iFrame.
        repeat iSplit ; iPureIntro => //=.
        lia.
        lia.
        by destruct H.
        iIntros (w) "(-> & Hs & Hf)".
        iDestruct "Hf" as (f5) "[Hf %Hf4]".
        iApply (wp_wand_ctx with "[Hs Hf Hf0]").
        iApply (wp_val_return with "Hf") => //.
        iIntros "Hf".
        iSimpl.
        iApply wp_value => //=.
        unfold IntoVal.
        apply of_to_val => //.
        iFrame.
        instantiate (1 := λ v, (⌜ v = immV [] ⌝ ∗
                                           isStack v0 (a :: s0) m ∗
                                          N.of_nat f3↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3;f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32; T_i32] []) [T_i32]
                            push ∗ ↪[frame] f5)%I).
        iSimpl.
        iFrame.
        done.
        iIntros (w) "(-> & H &  Hf0 & Hf)".
        iExists _.
        iFrame.
        iIntros "Hf".
        iSimpl.         
        iApply (wp_frame_value with "Hf") => //.
        iNext.
         instantiate (1 := λ v, (⌜ v = immV [] ⌝ ∗
                                           isStack v0 (a :: s0) m ∗
                                          N.of_nat f3↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3 ; f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32; T_i32] []) [T_i32]
                            push)%I).
        iSimpl.
        iFrame.
        iFrame.
        done. }
      iIntros (w) "[(-> & Hs & Hf0) Hf]".
      iApply "HΦ".
      by iFrame.
      iSplitR.
    - iIntros "!>" (f5 fi v0 s0 a cl Φ Ψ Ξ)
              "!> (Hf & Hf0 & % & %Hs & Hs & HΦ & Htab & Hcl & %Hclt & #Hspec) HΞ".
      iApply wp_wand_r.
      iSplitR "HΞ".
      { rewrite (separate2 _ (AI_basic (i32const _)) _).
        rewrite - (app_nil_r [AI_basic _]).
        iApply (wp_invoke_native with "Hf Hf0") => //.
        iIntros "!> [Hf Hf0]".
        iSimpl.
        iApply (wp_frame_bind with "Hf").
        done. iIntros "Hf".
        rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
        iApply (wp_block with "Hf") => //.
        iIntros "!> Hf".
        iApply (wp_label_bind with "[Hs Hf Hf0 HΦ Htab Hcl]") ; last first.
        iPureIntro.
        unfold lfilled, lfill => /=.
        instantiate (5 := []) => /=.
        rewrite app_nil_r.
        done.
        iApply (spec_stack_map with "[Hs Hf HΦ Hcl Htab]").        
        iFrame.
        repeat iSplit ; try iPureIntro => //=.
        lia.
        iExact "Hspec".
        iIntros (w) "(-> & Hs & Hf & Ht & Ha)".
        iDestruct "Hf" as (f6) "[Hf %Hf4]".
        iApply (wp_wand_ctx with "[Hs Hf Hf0]").
        iApply (wp_val_return with "Hf") => //.
        iIntros "Hf".
        iSimpl.
        iApply wp_value => //=.
        unfold IntoVal.
        apply of_to_val => //.
        iFrame.
        instantiate (1 := λ v, (⌜ v = immV [] ⌝ ∗
                                           ( ∃ s', isStack v0 s' m ∗ stackAll2 s0 s' Ψ) ∗
                                           N.of_nat f4↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3;f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32; T_i32] []) [T_i32 ; T_i32 ]
                           stack_map ∗ ↪[frame] f6 )%I).
        iSimpl.
        iFrame.
        done.
        iIntros (w) "(-> & H &  Hf0 & Hf)".
        iExists _.
        iFrame.
        iIntros "Hf".
        iSimpl.         
        iApply (wp_frame_value with "Hf") => //.
        iNext.
         instantiate (1 := λ v, (⌜ v = immV [] ⌝ ∗
                                            ( ∃ s', isStack v0 s' m ∗ stackAll2 s0 s' Ψ) ∗
                                            N.of_nat t↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m fi)]Some a ∗
                                            N.of_nat a↦[wf]cl ∗
                                 N.of_nat f4↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3; f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32; T_i32] []) [T_i32; T_i32]
                            stack_map)%I).
        iSimpl.
        iFrame.
        iFrame.
        done. }
      iIntros (w) "[(-> & Hs & Ht & Ha & Hf0) Hf]".
      iApply "HΞ".
      by iFrame.
    - iIntros "!>" (f5 fi v0 s0 a cl γ Φ Ψ Hsub Ξ)
              "!> (Hf & Hown & Hf0 & % & %Hs & Hs & HΦ & Htab & #Hcl & [%Htyp #Hspec]) HΞ".
      iApply wp_wand_r.
      iSplitR "HΞ".
      { rewrite (separate2 _ (AI_basic (i32const _)) _).
        rewrite - (app_nil_r [AI_basic _]).
        iApply (wp_invoke_native with "Hf Hf0") => //.
        iIntros "!> [Hf Hf0]".
        iSimpl.
        iApply (wp_frame_bind with "Hf").
        done. iIntros "Hf".
        rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
        iApply (wp_block with "Hf") => //.
        iIntros "!> Hf".
        iApply (wp_label_bind with "[Hs Hf Hf0 HΦ Htab Hown]") ; last first.
        iPureIntro.
        unfold lfilled, lfill => /=.
        instantiate (5 := []) => /=.
        rewrite app_nil_r.
        done.
        iApply (spec_stack_map_trap _ m _ v0 s0 _ _ _ Φ Ψ
                 with "[Hs Hf HΦ Htab Hown]");[apply Hsub|..].
        iFrame "∗ #".
        repeat iSplit ; try iPureIntro => //=.
        lia.
        iIntros (w) "[[-> | Hs] [Htab Hf]]";
        iDestruct "Hf" as (f6) "[Hf [Hown %Hf4]]".
        { iApply (wp_wand_ctx with "[Hf]").
          iSimpl. take_drop_app_rewrite_twice 0 0.
          iApply wp_trap_ctx;auto.
          iIntros (v1) "[-> Hf]".
          iExists _. iFrame. iIntros "Hf".
          iApply (wp_frame_trap with "Hf").
          instantiate (1:=(λ v, (⌜v = trapV⌝ ∨ ⌜ v = immV [] ⌝ ∗ _) ∗ na_own logrel_nais ⊤ ∗ N.of_nat t↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m fi)]Some a)%I). iNext. iFrame.  eauto.
        }
        iDestruct "Hs" as "[-> Hs]".
        iApply (wp_wand_ctx with "[Hs Hf Hf0]").
        iApply (wp_val_return with "Hf") => //.
        iIntros "Hf".
        iSimpl.
        iApply wp_value => //=.
        unfold IntoVal.
        apply of_to_val => //.
        iFrame.
        instantiate (1 :=  (λ v, ⌜ v = immV [] ⌝ ∗
                                           ( ∃ s', isStack v0 s' m ∗ stackAll2 s0 s' Ψ) ∗
                                           N.of_nat f4↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3;f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32; T_i32] []) [T_i32 ; T_i32 ]
                           stack_map ∗ ↪[frame] f6)%I).
        iSimpl.
        iFrame.
        done.
        iIntros (w) "(-> & H &  Hf0 & Hf)".
        iExists _.
        iFrame.
        iIntros "Hf".
        iSimpl.         
        iApply (wp_frame_value with "Hf") => //.
        iNext. iRight.
         instantiate (1 :=  (( ∃ s', isStack v0 s' m ∗ stackAll2 s0 s' Ψ) ∗
                                 N.of_nat f4↦[wf]FC_func_native
                            {|
                              inst_types :=
                                [Tf [] [T_i32]; Tf [T_i32] [T_i32];
                                Tf [T_i32; T_i32] []];
                              inst_funcs := [f; f0; f1; f2; f3; f4];
                              inst_tab := [t];
                              inst_memory := [m];
                              inst_globs := []
                            |} (Tf [T_i32; T_i32] []) [T_i32; T_i32]
                            stack_map)%I).
        iSimpl. iSplitR;[done|].
        iFrame. }
      iSimpl.
      iIntros (w) "[[[-> | (-> & Hs & Hf0)] [Hown Htab]] Hf]".
      all: iApply "HΞ";iFrame. by iLeft.
      iRight. iSplit;auto. iFrame.
  Qed.


  End StackModule.
