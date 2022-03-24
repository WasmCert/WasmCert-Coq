From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_rules.
Require Export datatypes host operations properties opsem typing.
Require Export iris_logrel.
Require Import iris_fundamental_const
        iris_fundamental_cvtop
        iris_fundamental_drop
        iris_fundamental_nop
        iris_fundamental_relop
        iris_fundamental_testop
        iris_fundamental_select
        iris_fundamental_unreachable
        iris_fundamental_unop
        iris_fundamental_binop
        iris_fundamental_br
        iris_fundamental_loop
        iris_fundamental_br_if
        iris_fundamental_call
        iris_fundamental_composition
        iris_fundamental_call_indirect
        iris_fundamental_get_local
        iris_fundamental_set_local
        iris_fundamental_tee_local
        iris_fundamental_get_global
        iris_fundamental_set_global
        iris_fundamental_load
        iris_fundamental_store
        iris_fundamental_current_memory
        iris_fundamental_grow_memory
        iris_fundamental_nil
        iris_fundamental_weakening
        iris_fundamental_br_table
        iris_fundamental_block
        iris_fundamental_if.
Import uPred.

Section fundamental.
  Import DummyHosts. (* placeholder *)

  Context `{!wfuncG Σ, !wtabG Σ, !wtabsizeG Σ, !wmemG Σ, !wmemsizeG Σ, !wglobG Σ, !wframeG Σ, HWP: host_program_logic, !logrel_na_invs Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* ------------------------------- FTLR: simple typing ----------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)
  
  Theorem be_fundamental C es τ : be_typing C es τ -> ⊢ semantic_typing (HWP:=HWP) C (to_e_list es) τ.
  Proof.
    induction 1.
    { by apply typing_const. }
    { by apply typing_unop. }
    { by apply typing_binop. }
    { by apply typing_testop. }
    { by apply typing_relop. }
    { by apply typing_cvtop_convert. }
    { by apply typing_cvtop_reinterpret. }
    { by apply typing_unreachable. }
    { by apply typing_nop. }
    { by apply typing_drop. }
    { by apply typing_select. }
    { by apply typing_block. }
    { by apply typing_loop. }
    { by apply typing_if. }
    { by apply typing_br. }
    { by apply typing_br_if. }
    { by apply typing_br_table. }
    { admit. }
    { by apply typing_call. }
    { by apply typing_call_indirect. }
    { by apply typing_get_local. }
    { by apply typing_set_local. }
    { by apply typing_tee_local. }
    { by apply typing_get_global. }
    { by eapply typing_set_global. }
    { by apply typing_load. }
    { by apply typing_store. }
    { by apply typing_current_memory. }
    { by apply typing_grow_memory. }
    { by apply typing_nil. }
    { eapply typing_composition.
      { apply IHbe_typing1. }
      { apply IHbe_typing2. } }
    { by apply typing_weakening. }
  Admitted.

End fundamental.
