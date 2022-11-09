From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris_host iris_fundamental_helpers stack_specs.
Require Export type_checker_reflects_typing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


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
      |} ;
      {|
        modfunc_type := Mk_typeidx 1 ;
        modfunc_locals := [] ;
        modfunc_body := stack_length
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
        modexp_name := list_byte_of_string "stack_length" ;
        modexp_desc := MED_func (Mk_funcidx 6)
      |} ;
      {|
        modexp_name := list_byte_of_string "table" ;
        modexp_desc := MED_table (Mk_tableidx 0)
      |}
    ]
  |}.

Definition func_types := [Tf [] [T_i32] ; Tf [T_i32] [T_i32] ; Tf [T_i32] [T_i32] ;
     Tf [T_i32] [T_i32] ; Tf [T_i32 ; T_i32] [] ; Tf [T_i32 ; T_i32] []; Tf [T_i32] [T_i32]].

Definition expts := (fmap ET_func func_types) ++ [ET_tab {| tt_limits := {| lim_min := 1%N ; lim_max := None |} ;
                               tt_elem_type := ELT_funcref |}].

Ltac bet_first f :=
  eapply bet_composition_front ; first eapply f => //=.
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
Ltac weaken :=
  match goal with
  | |- context [ be_typing _ ?e (Tf ?t1 ?t)  ] =>
      try rewrite <- (app_nil_r t1);
      rewrite -(list.take_drop (length t - 1) t);simpl take; simpl drop;
      eapply bet_weakening;constructor;auto
  end.
Ltac type_go := repeat (constructor || type_next || weaken || (type_next_rewrite; eapply bet_composition; [constructor|])).


Lemma validate_stack_typing x tt tf tloc tlab tret:
    nth_error tloc x = Some T_i32 ->
    be_typing
    {|
      tc_types_t := tt;
      tc_func_t := tf;
      tc_global := [];
      tc_table := [ {| tt_limits := {| lim_min := 1; lim_max := None |}; tt_elem_type := ELT_funcref |}];
      tc_memory := [ {| lim_min := 0; lim_max := None |}];
      tc_local := tloc;
      tc_label := tlab;
      tc_return := tret
    |} (validate_stack x) (Tf [] []).
Proof.
  move => Htloc.
  apply/b_e_type_checker_reflects_typing => /=.
  rewrite Htloc.
  replace (ssrnat.leq (S x) (length tloc)) with (true); first by apply/eqP.
  assert (x<length tloc); first by eapply nth_error_Some; rewrite Htloc.
  symmetry.
  apply/ssrnat.leP.
  lia.
Qed.

Lemma validate_stack_bound_typing x tt tf tloc tlab tret:
    nth_error tloc x = Some T_i32 ->
    be_typing
    {|
      tc_types_t := tt;
      tc_func_t := tf;
      tc_global := [];
      tc_table := [ {| tt_limits := {| lim_min := 1; lim_max := None |}; tt_elem_type := ELT_funcref |}];
      tc_memory := [ {| lim_min := 0; lim_max := None |}];
      tc_local := tloc;
      tc_label := tlab;
      tc_return := tret
    |} (validate_stack_bound x) (Tf [] []).
Proof.
  move => Htloc.
  bet_first bet_get_local => //.
  { rewrite nth_error_lookup in Htloc.
    apply lookup_lt_Some in Htloc.
      by lias. }
  bet_first bet_load => //.
  bet_first bet_drop => //.
  by apply bet_empty.
Qed.
  
Lemma new_stack_typing tt tf :
    be_typing
    {|
      tc_types_t := tt;
      tc_func_t := tf;
      tc_global := [];
      tc_table := [ {| tt_limits := {| lim_min := 1; lim_max := None |}; tt_elem_type := ELT_funcref |}];
      tc_memory := [ {| lim_min := 0; lim_max := None |}];
      tc_local := [T_i32];
      tc_label := [[T_i32]];
      tc_return := Some [T_i32]
    |} new_stack (Tf [] [T_i32]).
Proof.
  apply/b_e_type_checker_reflects_typing => /=; by apply/eqP.
Qed.

Lemma is_empty_typing tt tf tloc tlab tret:
  nth_error tloc 0 = Some T_i32 ->
  be_typing
    {|
      tc_types_t := tt;
      tc_func_t := tf;
      tc_global := [];
      tc_table := [ {| tt_limits := {| lim_min := 1; lim_max := None |}; tt_elem_type := ELT_funcref |}];
      tc_memory := [ {| lim_min := 0; lim_max := None |}];
      tc_local := tloc;
      tc_label := tlab;
      tc_return := tret
    |} is_empty (Tf [] [T_i32]).
Proof.
  move => Htloc.
  eapply bet_composition'; first by apply validate_stack_typing.
  eapply bet_composition'; first by apply validate_stack_bound_typing.
  apply/b_e_type_checker_reflects_typing => /=; destruct tloc => //=.
  simpl in Htloc. inversion Htloc; subst. by apply/eqP.
Qed.
    
Lemma is_full_typing tt tf tlab tret:
  be_typing
    {|
      tc_types_t := tt;
      tc_func_t := tf;
      tc_global := [];
      tc_table := [ {| tt_limits := {| lim_min := 1; lim_max := None |}; tt_elem_type := ELT_funcref |}];
      tc_memory := [ {| lim_min := 0; lim_max := None |}];
      tc_local := [T_i32];
      tc_label := tlab;
      tc_return := tret
    |} is_full (Tf [] [T_i32]).
Proof.
  eapply bet_composition'; first by apply validate_stack_typing.
  eapply bet_composition'; first by apply validate_stack_bound_typing.
  apply/b_e_type_checker_reflects_typing => /=; by apply/eqP.
Qed.
    
Lemma pop_typing tt tf tlab tret:
   be_typing
    {|
      tc_types_t := tt;
      tc_func_t := tf;
      tc_global := [];
      tc_table := [ {| tt_limits := {| lim_min := 1; lim_max := None |}; tt_elem_type := ELT_funcref |}];
      tc_memory := [ {| lim_min := 0; lim_max := None |}];
      tc_local := [T_i32; T_i32];
      tc_label := tlab;
      tc_return := tret;
    |} pop (Tf [] [T_i32]).
Proof.
  unfold pop, pop_op.
  repeat rewrite app_assoc.
  eapply bet_composition'; first by apply is_empty_typing.
  apply/b_e_type_checker_reflects_typing => /=; by apply/eqP.
Qed.
    
Lemma push_typing tt tf tlab tret:
  be_typing
    {|
      tc_types_t := tt;
      tc_func_t := tf;
      tc_global := [];
      tc_table := [ {| tt_limits := {| lim_min := 1; lim_max := None |}; tt_elem_type := ELT_funcref |}];
      tc_memory := [ {| lim_min := 0; lim_max := None |}];
      tc_local := [T_i32; T_i32; T_i32];
      tc_label := tlab;
      tc_return := tret
    |} push (Tf [] []).
Proof.
  eapply bet_composition'; first by apply validate_stack_typing.
  eapply bet_composition'; first by apply validate_stack_bound_typing.
  unfold push_op.
  (* Type checker is O(n^2), so it's much faster if we split the expression
     up earlier. *)
  eapply bet_composition'.
  { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. }
  { rewrite separate6.
    eapply bet_composition'.
    { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. }
    { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. }
  }
Qed.

Lemma stack_map_typing tf:
    be_typing
    {|
      tc_types_t := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
      tc_func_t := tf;
      tc_global := [];
      tc_table := [ {| tt_limits := {| lim_min := 1; lim_max := None |}; tt_elem_type := ELT_funcref |}];
      tc_memory := [ {| lim_min := 0; lim_max := None |}];
      tc_local := [T_i32; T_i32; T_i32; T_i32];
      tc_label := [[]];
      tc_return := Some []
    |} stack_map (Tf [] []).
Proof.
  eapply bet_composition'; first by apply validate_stack_typing.
  eapply bet_composition'; first by apply validate_stack_bound_typing.
  unfold map_op.
  eapply bet_composition'.
  { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. }
  { apply bet_block => /=.
    apply bet_loop => /=.
    unfold upd_label => /=.
    unfold map_loop_body.
    rewrite separate9.
    eapply bet_composition'.
    { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. }
    { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. }
  }
Qed.

Lemma stack_length_typing tt tf tlab tret:
   be_typing
    {|
      tc_types_t := tt;
      tc_func_t := tf;
      tc_global := [];
      tc_table := [ {| tt_limits := {| lim_min := 1; lim_max := None |}; tt_elem_type := ELT_funcref |}];
      tc_memory := [ {| lim_min := 0; lim_max := None |}];
      tc_local := [T_i32];
      tc_label := tlab;
      tc_return := tret;
    |} stack_length (Tf [] [T_i32]).
Proof.
  eapply bet_composition'; first by apply validate_stack_typing.
  eapply bet_composition'; first by apply validate_stack_bound_typing.
  apply/b_e_type_checker_reflects_typing => /=; by apply/eqP.
Qed.

Lemma module_typing_stack :
  module_typing stack_module [] expts.
Proof.
  unfold module_typing => /=. 
  exists func_types, [].
  repeat split => //.
  repeat (apply Forall2_cons ; repeat split => //) => /=.
  - by apply new_stack_typing.
  - by apply is_empty_typing.
  - by apply is_full_typing.
  - by apply pop_typing.
  - by apply push_typing.
  - by apply stack_map_typing.
  - by apply stack_length_typing.
  - unfold module_export_typing.
    repeat (apply Forall2_cons ; repeat split => //) => //=.
Qed.


Definition stack_instance idfs m t :=
  {|
    inst_types := [Tf [] [T_i32] ; Tf [T_i32] [T_i32] ; Tf [T_i32 ; T_i32] []] ;
    inst_funcs := idfs ;
    inst_tab := [t] ;
    inst_memory := [m] ;
    inst_globs := []
  |}.

 


Definition spec0_new_stack (idf0 : nat) (i0 : instance) (l0 : seq.seq value_type)
           (f0 : seq.seq basic_instruction) (isStack : N -> seq.seq i32 -> iPropI Σ)
           (nextStackAddrIs : nat -> iPropI Σ) E : iPropI Σ :=

 (∀ (f : frame) (addr : nat), 
      {{{ ↪[frame] f ∗ 
           N.of_nat idf0 ↦[wf] FC_func_native i0 (Tf [] [T_i32]) l0 f0 ∗
           nextStackAddrIs addr ∗
           ⌜ (Wasm_int.Int32.modulus - 1)%Z <> Wasm_int.Int32.Z_mod_modulus (ssrnat.nat_of_bin (N.of_nat addr `div` page_size)) ⌝ ∗
           ⌜ (N.of_nat addr + 4 < Z.to_N (two_power_nat 32))%N ⌝ ∗
           ⌜ (page_size | N.of_nat addr)%N ⌝  }}}
        [AI_invoke idf0] @ E
        {{{  v, (( ⌜ v = immV [value_of_int (-1)%Z] ⌝ ∗
                              nextStackAddrIs addr ) ∨
                 (∃ k, (⌜ v = immV [value_of_uint k]⌝ ∗
                     ⌜ (0 <= k <= ffff0000)%N ⌝ ∗
                     isStack k []  ∗
                     nextStackAddrIs (addr + N.to_nat page_size)) ))   ∗
                     N.of_nat idf0 ↦[wf] FC_func_native i0 (Tf [] [T_i32]) l0 f0 ∗
                      ↪[frame] f }}} )%I.

  
Definition spec1_is_empty idf1 i1 l1 f1 (isStack : N -> seq.seq i32 -> iPropI Σ) (E: coPset) :=
  (∀ (v: N) s f, {{{ ↪[frame] f  ∗
                 N.of_nat idf1 ↦[wf] FC_func_native i1 (Tf [T_i32] [T_i32]) l1 f1 ∗
                 isStack v s }}}
              [AI_basic (u32const v) ; AI_invoke idf1] @ E
              {{{ w, (∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s ∗
                                      ⌜ (k = 1 /\ s = []) \/
                             (k = 0 /\ s <> []) ⌝) ∗
                                                 N.of_nat idf1 ↦[wf] FC_func_native i1 (Tf [T_i32] [T_i32]) l1 f1 ∗ 
                                                 ↪[frame] f}}})%I.


Definition spec2_is_full idf2 i2 l2 f2 (isStack : N -> seq.seq i32 -> iPropI Σ) E :=
  (∀ (v: N) s f, {{{ ↪[frame] f ∗
                 N.of_nat idf2 ↦[wf] FC_func_native i2 (Tf [T_i32] [T_i32]) l2 f2 ∗
                 isStack v s }}} 
              [AI_basic (u32const v) ; AI_invoke idf2] @ E
              {{{ w, (∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗
                                      isStack v s ∗
                                      ⌜ (k = 1 /\ (N.of_nat (length s) = two14 - 1)%N) \/ (k = 0 /\ (N.of_nat (length s) < two14 - 1)%N) ⌝) ∗
                                      N.of_nat idf2 ↦[wf] FC_func_native i2 (Tf [T_i32] [T_i32]) l2 f2 ∗ 
                                                                            ↪[frame] f }}})%I.


Definition spec3_pop idf3 i3 l3 f3 (isStack : N -> seq.seq i32 -> iPropI Σ) E :=
  (∀ a (v: N) s f, {{{ ↪[frame] f ∗
                   N.of_nat idf3 ↦[wf] FC_func_native i3 (Tf [T_i32] [T_i32]) l3 f3
                   ∗ isStack v (a :: s) }}}
                [AI_basic (u32const v) ; AI_invoke idf3] @ E
                {{{ w, ⌜ w = immV [VAL_int32 a] ⌝ ∗
                                  isStack v s ∗
                                  N.of_nat idf3 ↦[wf] FC_func_native i3 (Tf [T_i32] [T_i32]) l3 f3 ∗
                                  ↪[frame] f }}})%I.


Definition spec4_push idf4 i4 l4 f4 (isStack: N -> list i32 -> iPropI Σ) E :=
  (∀ a (v: N) s f, {{{ ↪[frame] f ∗
                   N.of_nat idf4 ↦[wf] FC_func_native i4 (Tf [T_i32 ; T_i32] []) l4 f4 
                   ∗ ⌜ (N.of_nat (length s) < two14 - 1)%N ⌝
                   ∗ isStack v s }}}
                [ AI_basic (u32const v); AI_basic (BI_const (VAL_int32 a)); 
                  AI_invoke idf4 ] @ E
                {{{ w, ⌜ w = immV [] ⌝ ∗
                                  isStack v (a :: s) ∗
                                  N.of_nat idf4 ↦[wf] FC_func_native i4 (Tf [T_i32 ; T_i32] []) l4 f4 ∗
                                  ↪[frame] f }}})%I.


Definition spec5_stack_map idf5 i5 l5 f5 (isStack : N -> seq.seq i32 -> iPropI Σ) j0 E :=
  (∀ (f0 : frame) (f : i32) (v : N) (s : seq.seq i32) a cl
      (Φ : i32 -> iPropI Σ) (Ψ : i32 -> i32 -> iPropI Σ) ,
      {{{  ↪[frame] f0 ∗
            N.of_nat idf5 ↦[wf] FC_func_native i5 (Tf [T_i32 ; T_i32] []) l5 f5 ∗
            isStack v s ∗
            stackAll s Φ ∗
            N.of_nat j0 ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
            (N.of_nat a) ↦[wf] cl ∗
            ⌜ cl_type cl = Tf [T_i32] [T_i32] ⌝ ∗ 
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
    [ AI_basic (u32const v); AI_basic (BI_const (VAL_int32 f)) ; AI_invoke idf5 ] @ E
    {{{ w, ⌜ w = immV [] ⌝ ∗
           (∃ s', isStack v s' ∗ stackAll2 s s' Ψ) ∗
           N.of_nat idf5 ↦[wf] FC_func_native i5 (Tf [T_i32 ; T_i32] []) l5 f5 ∗
           ↪[frame] f0 ∗
            N.of_nat j0 ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] (Some a) ∗
            (N.of_nat a) ↦[wf] cl
  }}})%I.


(* A trap allowing version for code that might trap *)
Definition spec5_stack_map_trap `{!logrel_na_invs Σ} idf5 i5 l5 f5 (isStack : N -> seq.seq i32 -> iPropI Σ) j0 E :=
  (∀ (f0 : frame) (f : i32) (v : N) (s : seq.seq i32) a cl γ1
     (Φ : i32 -> iPropI Σ) (Ψ : i32 -> i32 -> iPropI Σ) ,
      ⌜↑γ1 ⊆ E⌝ →
      {{{  N.of_nat idf5 ↦[wf] FC_func_native i5 (Tf [T_i32 ; T_i32] []) l5 f5 ∗
           isStack v s ∗
           stackAll s Φ ∗
           na_inv logrel_nais γ1 ((N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] a) ∗
           match a with
           | Some a => ∃ γ2, ⌜↑γ2 ⊆ E ∧ @up_close _ coPset _ γ2 ⊆ ⊤ ∖ ↑γ1⌝ ∗ na_inv logrel_nais γ2 ((N.of_nat a) ↦[wf] cl) ∗
             ⌜ cl_type cl = Tf [T_i32] [T_i32] ⌝ ∗  
           (∀ (u : i32) (fc : frame),
               {{{ Φ u ∗
                     ⌜ i5 = f_inst fc ⌝ ∗
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
        [ AI_basic (u32const v); AI_basic (BI_const (VAL_int32 f)) ; AI_invoke idf5 ] @ E
      {{{ w, (⌜ w = trapV ⌝ ∨ (⌜ w = immV [] ⌝ ∗
                              (∃ s', isStack v s' ∗ stackAll2 s s' Ψ) ∗
                              N.of_nat idf5 ↦[wf] FC_func_native i5 (Tf [T_i32 ; T_i32] []) l5 f5)) ∗
      na_own logrel_nais ⊤ ∗
      ↪[frame] f0
  }}})%I.


Definition spec6_stack_length idf i l fn (isStack : N -> seq.seq i32 -> iPropI Σ) (E: coPset) :=
  (∀ (v: N) s f len, {{{ ↪[frame] f  ∗
                      N.of_nat idf ↦[wf] FC_func_native i (Tf [T_i32] [T_i32]) l fn ∗
                      ⌜ (N.of_nat (length s) = len)%N ⌝ ∗
                 isStack v s }}}
              [AI_basic (u32const v) ; AI_invoke idf] @ E
              {{{ w, ⌜ w = immV [value_of_uint len] ⌝ ∗ isStack v s ∗
                     N.of_nat idf ↦[wf] FC_func_native i (Tf [T_i32] [T_i32]) l fn ∗ 
                     ↪[frame] f}}})%I.


Definition stack_instantiate_para (exp_addrs: list N) (stack_mod_addr : N) := [ ID_instantiate exp_addrs stack_mod_addr [] ].

Definition own_vis_pointers (exp_addrs: list N): iProp Σ :=
   ([∗ list] exp_addr ∈ exp_addrs, (∃ mexp, exp_addr ↪[vis] mexp)).

Lemma own_vis_pointers_nodup (exp_addrs: list N):
  own_vis_pointers exp_addrs -∗
  ⌜ NoDup exp_addrs ⌝.
Proof.
  iInduction (exp_addrs) as [|e] "IH"; unfold own_vis_pointers => //=; first by iIntros; rewrite NoDup_nil.
  iIntros "(Hexp & Hexps)".
  iDestruct "Hexp" as (?) "Hexp".
  rewrite NoDup_cons.
  iDestruct ("IH" with "Hexps") as "%Hnodup".
  iSplit => //.
  iIntros "%Hin".
  apply elem_of_list_lookup in Hin.
  destruct Hin as [i Hin].
  iDestruct (big_sepL_lookup with "Hexps") as "Hcontra" => //.
  iDestruct "Hcontra" as (?) "Hcontra".
  by iDestruct (ghost_map_elem_ne with "Hexp Hcontra") as "%".
Qed.

(* The similar result does *not* hold for tables and memories, because wtblock and wmblock are not necessarily
   exclusive resources. This is an undesirable feature. *)
Lemma module_inst_resources_func_nodup ms inst addrs:
  module_inst_resources_func ms inst addrs -∗
  ⌜ NoDup addrs ⌝.
Proof.
  move: ms inst.
  iInduction (addrs) as [|a] "IH"; unfold module_inst_resources_func; iIntros (ms inst) "Hw" => //=; first by rewrite NoDup_nil.
  iDestruct (big_sepL2_length with "Hw") as "%Hlen".
  destruct ms => //=.
  iDestruct "Hw" as "(Hf & Hw)".
  rewrite NoDup_cons.
  iDestruct ("IH" with "Hw") as "%Hnodup".
  iSplit => //.
  iIntros "%Hin".
  apply elem_of_list_lookup in Hin.
  destruct Hin as [i Hin].
  assert (exists m', ms !! i = Some m') as Hm.
  { apply lookup_lt_Some in Hin.
    simpl in Hlen.
    replace (length addrs) with (length ms) in Hin; last by inversion Hlen.
    destruct (ms !! i) eqn:Hl; try by eexists.
    apply lookup_ge_None in Hl; lia.
  }
  destruct Hm as [? Hm].
  iDestruct (big_sepL2_lookup with "Hw") as "Hcontra" => //; last by iDestruct (mapsto_ne with "Hf Hcontra") as "%".
Qed.

Lemma instantiate_stack_spec `{!logrel_na_invs Σ} (s : stuckness) (E: coPset) (exp_addrs: list N) (stack_mod_addr : N) :
  length exp_addrs = 8 ->
  (* Knowing that we hold the stack module… *)
  stack_mod_addr ↪[mods] stack_module -∗
     (* … and we own the vis of the export targets … *)
   own_vis_pointers exp_addrs -∗
     (* … instantiating the stack-module, yields the following : *)
     WP ((stack_instantiate_para exp_addrs stack_mod_addr, []) : host_expr)
     @ s ; E
             {{ λ v : host_val,
                 (* Instantiation succeeds *)
                 ⌜ v = immHV [] ⌝ ∗
                 (* we still own the stack_module *)
                 stack_mod_addr ↪[mods] stack_module ∗ 
                  ∃ (idf0 idf1 idf2 idf3 idf4 idf5 idf6 idt : nat)
                    (name0 name1 name2 name3 name4 name5 name6 name7 : name)
                    (f0 f1 f2 f3 f4 f5 f6 : list basic_instruction)
                    (i0 : instance)
                    (l0 l1 l2 l3 l4 l5 l6: list value_type)
                    tab 
                    (isStack : N -> seq.seq i32 -> iPropI Σ)
                    (nextStackAddrIs : nat -> iPropI Σ), 
                    (* Our exports are in the vis stated. Note that everything is 
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
                                                     (name4, idf4) ; (name5, idf5) ;
                                                     (name6, idf6) ])
                                        ++ [ {| modexp_name := name7 ;
                                                modexp_desc := MED_table (Mk_tableidx idt) |} ]
                    in let inst_map := (list_to_map (zip (fmap N.of_nat [idf0; idf1; idf2; idf3; idf4; idf5; idf6])
                                                    [(FC_func_native i0 (Tf [] [T_i32]) l0 f0) ;
                                                     (FC_func_native i0 (Tf [T_i32] [T_i32]) l1 f1) ;
                                                     (FC_func_native i0 (Tf [T_i32] [T_i32]) l2 f2) ;
                                                     (FC_func_native i0 (Tf [T_i32] [T_i32]) l3 f3) ;
                                                     (FC_func_native i0 (Tf [T_i32; T_i32] []) l4 f4) ;
                                                     (FC_func_native i0 (Tf [T_i32; T_i32] []) l5 f5) ;
                                                     (FC_func_native i0 (Tf [T_i32] [T_i32]) l6 f6)])) in
                    (* These two import functions state that all [vis] and [wf] point 
                       to the correct exports/functions, i.e. a client will be able 
                       to successfully import them *)
                    import_resources_host exp_addrs inst_vis ∗
                    import_resources_wasm_typecheck_sepL2 inst_vis expts inst_map
                    (<[ N.of_nat idt := tab ]> ∅) 
                    ∅ ∅ ∗
                    ⌜ NoDup (modexp_desc <$> inst_vis) ⌝ ∗
                    (* This is technically redundant, but is commonly used in other modules that import the stack *)
                    ⌜ NoDup [idf0; idf1; idf2; idf3; idf4; idf5; idf6] ⌝ ∗
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
                    spec5_stack_map_trap idf5 i0 l5 f5 isStack idt E ∗
                    spec6_stack_length idf6 i0 l6 f6 isStack E
                                          
             }}.
Proof.
  move => Hexpaddrlen.
  do 9 (destruct exp_addrs => //).
  iIntros "Hmod Hexps".
  iDestruct (own_vis_pointers_nodup with "Hexps") as "%Hnodupexp".
  iApply (weakestpre.wp_strong_mono s _ E with "[Hmod Hexps]") => //.
  iApply (instantiation_spec_operational_no_start with "[Hmod Hexps]"); (try exact module_typing_stack); auto => //.
  { unfold module_restrictions => /=.
      by repeat split => //=; exists [] => //.
  }
  
  - unfold instantiation_resources_pre.
    iSplitL "Hmod" ; first done.
    unfold instantiation_resources_pre_wasm.
    instantiate (1 := []).
    rewrite irwt_nodup_equiv => /=; last by apply NoDup_nil.
    repeat iSplit => //=; try by (iPureIntro; apply dom_empty).
    { by unfold import_resources_host. }
    { iPureIntro. by unfold module_elem_bound_check_gmap => //=. }
    { iPureIntro. by unfold module_data_bound_check_gmap => //=. }
    
  - iIntros (v) "(-> & Hinst)".
    unfold instantiation_resources_post.
    Opaque list_to_map.
    iDestruct "Hinst" as "(Hmod & _ & (%inst & Himpwasm & Hexphost))".
    iSplitR => //.
    iFrame "Hmod".
    iDestruct "Himpwasm" as (g_inits t_inits m_inits gms wts wms) "(Himpwasm & %Hinst & -> & -> & %Hbound & -> & -> & %Hbound' & %Hginit & -> & Hwasm)".
    destruct Hinst as (Hinsttype & _ & _ & _ & _ & Hstart).
    unfold module_inst_resources_wasm, module_export_resources_host => /=.
    destruct inst => /=.
    iDestruct "Hwasm" as "(Hwf & Hwt & Hwm & _)".
    iDestruct (module_inst_resources_func_nodup with "Hwf") as "%Hnodupwf".
    unfold module_inst_resources_func, module_inst_resources_tab, module_inst_resources_mem => /=.

    simpl in Hinsttype; subst inst_types.
    
    iDestruct (big_sepL2_length with "Hwf") as "%Hiflen".
    simpl in Hiflen.
    unfold get_import_func_count in * => /=; simpl in Hiflen.

    iDestruct (big_sepL2_length with "Hwt") as "%Hitlen".
    simpl in Hitlen.
    unfold get_import_table_count in * => /=; simpl in Hitlen.
    
    iDestruct (big_sepL2_length with "Hwm") as "%Himlen".
    simpl in Himlen.
    unfold get_import_mem_count in * => /=; simpl in Himlen.

    rewrite -> drop_0 in *.

    do 8 (destruct inst_funcs => //).
    do 2 (destruct inst_tab => //).
    do 2 (destruct inst_memory => //).
    iExists f, f0, f1, f2, f3, f4, f5, t.

    iSimpl in "Hexphost".
    iDestruct "Hexphost" as "(Hexp0 & Hexp1 & Hexp2 & Hexp3 & Hexp4 & Hexp5 & Hexp6 & Hexp7 & _)".
    iDestruct "Hexp0" as (name0) "Hexp0".
    iDestruct "Hexp1" as (name1) "Hexp1".
    iDestruct "Hexp2" as (name2) "Hexp2".
    iDestruct "Hexp3" as (name3) "Hexp3".
    iDestruct "Hexp4" as (name4) "Hexp4".
    iDestruct "Hexp5" as (name5) "Hexp5".
    iDestruct "Hexp6" as (name6) "Hexp6".
    iDestruct "Hexp7" as (name7) "Hexp7".
    iExists name0, name1, name2, name3, name4, name5, name6, name7.
    
    iExists _, _, _, _, _, _, _.
    iExists _.
    iExists _, _, _, _, _, _, _.
    iExists _.

    iExists (λ a b, isStack a b m).
    iExists (λ n, (N.of_nat m↦[wmlength] N.of_nat n)%I).

    iSplitL "Hexp0 Hexp1 Hexp2 Hexp3 Hexp4 Hexp5 Hexp6 Hexp7"; first by iFrame => /=.
    
    iDestruct "Hwf" as "(Hf & Hf0 & Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & _)".
    iDestruct "Hwt" as "(Ht & _)".
    iDestruct "Hwm" as "(Hm & _)".

    iDestruct "Hm" as "(Hmem & Hmemlength & Hmlim)".
    
    iSplitL "Hf Hf0 Hf1 Hf2 Hf3 Hf4 Hf5 Ht".
    { unfold import_resources_wasm_typecheck_sepL2.
      iSplitR.
      { unfold import_resources_wasm_domcheck.
          by repeat rewrite dom_insert.
      }
      { simpl.
        apply (NoDup_fmap_2 N.of_nat) in Hnodupwf.
        iSplitL "Hf";
          last iSplitL "Hf0"; 
          last iSplitL "Hf1"; 
          last iSplitL "Hf2"; 
          last iSplitL "Hf3"; 
          last iSplitL "Hf4"; 
          last iSplitL "Hf5";
          last first.
        { iModIntro; iSplit => //.
          iExists _, _.
          iFrame.
          rewrite lookup_insert.
          iPureIntro.
            by split => //.
        }
        all: (iExists _; iFrame; rewrite - elem_of_list_to_map => //=; iPureIntro; split => //; apply elem_of_list_In; repeat ((try by left); right)).
      }
    }

    Transparent list_to_map.
    
    iSplitR.
    { iPureIntro.
      eapply (NoDup_fmap_2 (λ x, (MED_func (Mk_funcidx x)))) in Hnodupwf.
      { simpl in Hnodupwf.
        rewrite separate7.
        apply NoDup_app; split => //.
        split => //; last by apply NoDup_singleton.
          by set_solver+.
      }
      Unshelve.
      { move => x y Heq. by inversion Heq. }
    }

    iSplitR => //.
    
    iSplitR; first by iPureIntro => /=; lia.

    iSplitL "Hmemlength" ; first done.

    
    (* Proving the parametric spec of each function in the post condition *)
    repeat iSplitR.
    { iIntros "!>" (fr addr Φ) "!> (Hf & Hwf & Hlen & % & % & %) HΦ".
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
        iDestruct "H" as "(H & Hf)" => /=.
        iDestruct "Hf" as (f6) "[Hf %Hf4]".
        iApply (wp_wand_ctx with "[H Hf Hf0]").
        iAssert (⌜const_list (iris.of_val w)⌝%I) as "%Hconstw".
        { by iDestruct "H" as "[(-> & ?) | (-> & ?)]" => //. }
        iApply (wp_val_return with "Hf") => //.
        iIntros "Hf".
        rewrite app_nil_r app_nil_l.
        instantiate (1 := (λ v, ((⌜ v = immV [value_of_int (-1)%Z] ⌝ ∗ N.of_nat m↦[wmlength]N.of_nat addr)%I ∨ ((∃ k, ⌜ v = immV [value_of_uint k]⌝ ∗ ⌜ (0 <= k <= ffff0000)%N⌝ ∗ isStack k [] m ∗ N.of_nat m↦[wmlength](N.of_nat addr + page_size)%N))) ∗ N.of_nat f↦[wf] _ ∗ ↪[frame] f6 )%I).
        iApply wp_value => //=.
        iDestruct "H" as "[(-> & Hmlen) | (-> & Hstack & Hmlen)]" => //. 
        { iFrame.
          iLeft.
          iFrame.
          done.
        }
        { iDestruct (stack_pure with "Hstack") as "H".
          iDestruct "H" as "(%Hdiv & %Hvb & %Hlen & Hstack)".
          iFrame.
          iRight.
          iExists _.
          iFrame.
          done.
        }
        iIntros (v) "(H & Hfunc & Hf)".
        iExists _.
        iFrame.       
        iIntros "Hf".
        iSimpl.
        iAssert (⌜exists kv, v = immV [kv] ⌝%I) as "%Hv".
        { iDestruct "H" as "[(-> & ?) | H]" => //; try by iExists _.
          iDestruct "H" as (k) "(-> & ?)".
          by iExists _.
        }
        destruct Hv as [kv ->].
        iApply (wp_frame_value with "Hf") => //.
        iNext.
        instantiate (1 := (λ v, ((⌜ v = immV [value_of_int (-1)%Z] ⌝ ∗ N.of_nat m↦[wmlength]N.of_nat addr)%I ∨ ((∃ k, ⌜ v = immV [value_of_uint k]⌝ ∗ ⌜ (0 <= k <= ffff0000)%N⌝ ∗ isStack k [] m ∗
                                                                                             N.of_nat m↦[wmlength](N.of_nat addr + page_size)%N))) ∗
                                                                                             N.of_nat f↦[wf]_)%I).
        iSimpl.
        by iFrame.
      }
      iIntros (w) "[[H Hf0] Hf]".
      iApply "HΦ".
      iFrame.
      iDestruct "H" as "[(-> & ?) | H]" => //.
      { iLeft.
        iFrame.
        done.
      }
      { iDestruct "H" as (k) "(-> & ? & ?)".
        iRight.
        iExists _.
        iFrame.
        rewrite Nat.add_comm.
        rewrite of_nat_to_nat_plus.
        rewrite N.add_comm.
        iFrame.
        done.
      }
    }
      
    { iIntros "!>" (v0 s0 vs Φ) "!> (Hf & Hf0 & %H & %Hlen & %Hdiv & Hlen) HΦ".
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
        lia.
        iIntros (w) "H".
        iDestruct "H" as (k) "(-> & H & %Hk & Hf)" => /=.
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
                                            N.of_nat f0 ↦[wf] _ ∗ ↪[frame] _)%I).
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
                                                                                        N.of_nat f0↦[wf] _)%I).                            
        iSimpl.
        iFrame.
        iExists k.
        done. }
      iIntros (w) "[(H & Hs & Hf0) Hf]".
      iDestruct "H" as (k) "%Hk".
      iApply "HΦ".
      iFrame.
      by iExists _.
    }
        
    { iIntros "!>" (v0 s0 vs Φ) "!> (Hf & Hf0 & %H & %Hlen & %Hdiv & Hlen) HΦ".
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
        lia.
        iIntros (w) "H".
        iDestruct "H" as (k) "(-> & H & %Hk & Hf)" => /=.
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
                                           N.of_nat f1↦[wf] _
                            ∗ ↪[frame] _
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
        instantiate (1 := λ v, ((∃ (k: Z), ⌜ v = immV [value_of_int k] ⌝ ∗
                                                 ⌜ (k = 1 /\ (N.of_nat (length s0) = two14 - 1)%N) \/ (k = 0 /\ (N.of_nat (length s0) < (two14 - 1))%N) ⌝) ∗
                                                                                        isStack v0 s0 m ∗
                                                                                        N.of_nat f1↦[wf] _)%I). 
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
    }
    
    { iIntros "!>" (a v0 s0 vs Φ) "!> (Hf & Hf0 & %H & %Ha & Hs) HΦ". 
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
        lia.
        iIntros (w) "H".
        iDestruct "H" as "(-> & Hs & Hf)" => /=.
        iDestruct "Hf" as (f6) "[Hf %Hf4]".
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
                                            N.of_nat f2↦[wf] _ ∗ ↪[frame] _)%I).
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
                                            N.of_nat f2↦[wf] _)%I).
        iSimpl.
        iFrame.
        done.
      }
      iIntros (w) "[(-> & Hs & Hf0) Hf]".
      iApply "HΦ".
      by iFrame.
    }
        
    { iIntros "!>" (a v0 s0 vs Φ) "!> (Hf & Hf0 & %H & %Ha & %Hlen & Hs) HΦ".
      iApply wp_wand_r.
      iSplitR "HΦ".
      { rewrite (separate2 (AI_basic (u32const _)) _ _).
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
        lia.
        iIntros (w) "(-> & Hs & Hf)".
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
                                           isStack v0 (a :: s0) m ∗
                                          N.of_nat f3↦[wf] _ ∗ ↪[frame] _)%I).
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
                                          N.of_nat f3↦[wf] _)%I).
        iSimpl.
        iFrame.
        iFrame.
        done. }
      iIntros (w) "[(-> & Hs & Hf0) Hf]".
      iApply "HΦ".
      by iFrame.
    }
        
    { iIntros "!>" (f6 fi v0 s0 a cl Φ Ψ Ξ)
              "!> (Hf & Hf0 & Hs & HΦ & Htab & Hcl & %Hclt & #Hspec) HΞ".
      iApply wp_wand_r.
      iSplitR "HΞ".
      { rewrite (separate2 (AI_basic (u32const _)) _ _).
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
        iDestruct "Hf" as (f7) "[Hf %Hf4]".
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
                                           N.of_nat f4↦[wf] _ ∗ ↪[frame] _ )%I).
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
                                 N.of_nat f4↦[wf] _)%I).
        iSimpl.
        iFrame.
        iFrame.
        done. }
      iIntros (w) "[(-> & Hs & Ht & Ha & Hf0) Hf]".
      iApply "HΞ".
      by iFrame.
    }
    
    (* Trap spec *)  
    { iIntros "!>" (f6 fi v0 s0 a cl γ Φ Ψ Hsub Ξ)
              "!> (Hf & Hs & HΦ & #Htab & #Hcl & Hown & Hf0) HΞ".
      iApply wp_wand_r.
      iSplitR "HΞ".
      { rewrite (separate2 (AI_basic (u32const _)) _ _).
        rewrite - (app_nil_r [AI_basic _]).
        iApply (wp_invoke_native with "Hf0 Hf") => //.
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
        lia. iFrame "Hcl".
        iIntros (w) "[[-> | Hs] Hf]";
        iDestruct "Hf" as (f7) "[Hf [Hown %Hf4]]".
        { iApply (wp_wand_ctx with "[Hf]").
          iSimpl. take_drop_app_rewrite_twice 0 0.
          iApply wp_trap_ctx;auto.
          iIntros (v1) "[-> Hf]".
          iExists _. iFrame. iIntros "Hf".
          iApply (wp_frame_trap with "Hf").
          instantiate (1:=(λ v, (⌜v = trapV⌝ ∨ ⌜ v = immV [] ⌝ ∗ _) ∗ na_own logrel_nais ⊤)%I). iNext. iFrame.  eauto.
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
                                           N.of_nat f4↦[wf] _ ∗ ↪[frame] _)%I).
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
                                 N.of_nat f4↦[wf] _)%I).
        iSimpl. iSplitR;[done|].
        iFrame. }

      iSimpl.
      iIntros (w) "[[[-> | (-> & Hs & Hf0)] Hown] Hf]".
      all: try iApply "HΞ";iFrame. by iLeft.
      iRight. iSplit;auto. iFrame.
    }
      
    (* length spec *)
    { iIntros "!>" (v0 s0 f6 len Φ) "!> (Hf & Hf0 & %Hret & Hs) HΦ".
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
        iApply (spec_stack_length with "[Hs Hf]").
        iFrame.
        repeat iSplit ; iPureIntro => //=.
        iIntros (w) "(-> & Hs & Hf)".
        iApply (wp_wand_ctx with "[Hs Hf Hf0]").
        iApply (wp_val_return with "Hf") => //.
        iIntros "Hf".
        rewrite app_nil_r app_nil_l.
        iApply wp_value => //=.
        unfold IntoVal.
        apply of_to_val => //.
        iFrame.
        instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗
                                           isStack v0 s0 m ∗
                                            N.of_nat f5 ↦[wf] _ ∗ ↪[frame] _)%I).
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
        instantiate (1 := λ v, ( ⌜ v = immV [value_of_uint _] ⌝ ∗ isStack v0 s0 m ∗ N.of_nat f5↦[wf] _)%I).
        iSimpl.
        iFrame.
        done. }
      iIntros (w) "[(-> & Hs & Hf0) Hf]".
      iApply "HΦ".
      by iFrame.
    }
Qed.
  

End StackModule.
