From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_rules iris_host.
Require Export datatypes operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

(* Shorthands for common constructors *)
Definition xx i := (VAL_int32 (Wasm_int.int_of_Z i32m i)).
Definition xb b := (VAL_int32 (wasm_bool b)).

(* Tactics *)
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

Section wp_helpers.
  Context `{!wasmG Σ}.

End wp_helpers.

(* Example Programs *)
Section Example_Add.

(* Simple examples demonstrating the contents of modules *)
Definition Add_module :=
  Build_module
    (* Function types *) [:: (Tf [::T_i32; T_i32] [::T_i32]) ]
    (* Functions *) [:: Build_module_func
                       (* Type signature, referencing from the function type components *) (Mk_typeidx 0)
                       (* List of local variable types to be used -- none for the addition here *) [::]
                       (* Function body *) [:: BI_get_local 0; BI_get_local 1; BI_binop T_i32 (Binop_i BOI_add)]
                       ]
    (* Tables *) [::]
    (* Memories *) [::]
    (* Globals *) [::]
    (* Table initializers *) [::]
    (* Memory initializers *) [::]
    (* Start function *) None
    (* Imports *) [::]
    (* Exports *) [:: Build_module_export
                     (* export name *) (list_byte_of_string "add")
                     (* export description *) (MED_func (Mk_funcidx 0))
                     ].


Definition M2 :=
  Build_module
    (* Function types *) [:: (Tf [::T_i32; T_i32] [::T_i32]); (Tf [::] [::T_i32]) ]
    (* Functions *) [:: Build_module_func
                       (* Type signature, referencing from the function type components *) (Mk_typeidx 1)
                       (* List of local variable types to be used -- none for the addition here *) [::]
                       (* Function body *) [:: BI_const (xx 13); BI_const (xx 2); BI_call 0]
                       (* Note that the imports take precedence, i.e. the imported function is the 0th function, and
                          this function is the 1st function instead. *)
                       ]
    (* Tables *) [::]
    (* Memories *) [::]
    (* Globals *) [::]
    (* Table initializers *) [::]
    (* Memory initializers *) [::]
    (* Start function *) (* This would actually not work -- the start function must have an empty function type *)
                  (* (Some (Build_module_start (Mk_funcidx 1))) *)
                  None
    (* Imports *) [:: Build_module_import
                     (* import module name (superfluous) *) (list_byte_of_string "Add_module")
                     (* import function name (superfluous) *) (list_byte_of_string "add")
                     (* import type description *) (ID_func 0)
                     ]
    (* Exports *) [:: Build_module_export
                     (* export name *) (list_byte_of_string "f")
                     (* export description *) (MED_func (Mk_funcidx 1))
                     ].

Definition module_decls := [:: Add_module; M2].

Definition add_program_instantiate :=
  [:: ID_instantiate [::0%N] 0 [::];
  (* The above exports the function 'add' to the 0th vi store of the host, which contains a list of exports consisting of
     only one function -- the add function. *)
  ID_instantiate [::1%N] 1 [:: 0%N]]. 


(* verify that both modules are well-typed *)
Lemma add_module_valid: module_typing Add_module [::] [:: ET_func (Tf [::T_i32; T_i32] [::T_i32])].
Proof.
  unfold module_typing.
  (* We have to provide the type of each function and each global in the instantiate module. *)
  exists [Tf [::T_i32; T_i32] [::T_i32]], [::].
  simpl.
  (* Most of the components of the module are empty and can be resolved trivially. *)
  repeat split; (try by apply Forall2_nil); (try by apply Forall_nil).
  - (* module_func_typing *)
    constructor; last by apply Forall2_nil.
    unfold module_func_typing.
    repeat split => //=.
    (* be_typing of the function body *)
    eapply bet_composition_front; first by apply bet_get_local => //.
    eapply bet_composition_front with (t2s := [T_i32; T_i32]).
    + replace [T_i32; T_i32] with ([T_i32] ++ [T_i32]) => //.
      apply bet_weakening_empty_1.
      by apply bet_get_local.
    + apply bet_binop.
      by constructor.
  - (* module_export_typing *)
    constructor; last by apply Forall2_nil.
    by unfold module_export_typing => /=.
Qed.


Lemma M2_valid: module_typing M2 [:: ET_func (Tf [::T_i32; T_i32] [::T_i32])] [:: ET_func (Tf [::] [::T_i32])].
Proof.
  unfold module_typing.
  exists [::Tf [::] [::T_i32]], [::].
  simpl.
  repeat split; (try by apply Forall2_nil); (try by apply Forall_nil).
  - (* module_func_typing *)
    constructor; last by apply Forall2_nil.
    unfold module_func_typing.
    repeat split => //=.
    (* be_typing of the function body *)
    eapply bet_composition_front; first by apply bet_const => //.
    eapply bet_composition_front with (t2s := [T_i32; T_i32]) => /=.
    + replace [T_i32; T_i32] with ([T_i32] ++ [T_i32]) => //.
      apply bet_weakening_empty_1.
      by apply bet_const.
    + by apply bet_call => //.
  - (* module_import_typing *)
    unfold module_import_typing => /=.
    by constructor => //. 
  - (* module_export_typing *)
    constructor; last by apply Forall2_nil.
    by unfold module_export_typing => /=.    
Qed.

End Example_Add.


