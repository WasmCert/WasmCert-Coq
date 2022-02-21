From mathcomp Require Import ssreflect eqtype seq ssrbool ssrfun.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
(* From iris.bi Require Export weakestpre. *)
Require Export iris iris_locations iris_properties iris_wp stdpp_aux.
Require Export datatypes host operations properties opsem instantiation.

Section Iris_host.

Import DummyHosts.

Definition reduce := @reduce host_function host_instance.

Definition host_val := val.

(* Domain of the variable instantiation store *)
Definition vi := nat.

(* variable instantiation store *)
Definition vi_store := gmap vi (list module_export).

Definition module_decl := module.

(* an import is specified by giving the index of the instance to the module_export and a name given by the string *)
Definition vimp : Type := vi * (seq.seq Byte.byte).

(* There is only one instance declaration instruction: instantiating a module.
   ID_instantiate vi vm vimps is supposed to instantiate the module vmth module
   in the program state, taking imports as specified by each of the vimps, 
   and store the list of exports in the vi_store for future use.
 *)
Inductive inst_decl: Type :=
  ID_instantiate: vi -> nat -> list vimp -> inst_decl.

Definition host_prog : Type := (list module) * (list inst_decl).

Definition host_config : Type := store_record * vi_store * host_prog * (list administrative_instruction).

Definition instantiate := instantiate host_function host_instance.

Print module_export.

Print name.

Definition map_start (start: option nat) : list administrative_instruction :=
  match start with
  | Some n => [AI_invoke n]
  | None => []
  end.

Fixpoint lookup_export vexts name : option module_export_desc :=
  match vexts with
  | [] => None
  | e :: vexts' => if e.(modexp_name) == name then Some e.(modexp_desc)
                                            else lookup_export vexts' name
  end.

Definition lookup_export_vi (vis: vi_store) (vimp: vimp) : option module_export_desc :=
  let (vi, vname) := vimp in
  match vis !! vi with
  | Some vexts => lookup_export vexts vname
  | None => None
  end.

Definition empty_instance := Build_instance [::] [::] [::] [::] [::].
Definition empty_frame := Build_frame [::] empty_instance.

Inductive host_reduce: host_config -> host_config -> Prop :=
| HR_host_step: forall s vis m vi vm vimps imps s' vis' ms idecs' inst exps start vs,
    ms !! vm = Some m ->
    those ((lookup_export_vi vis) <$> vimps) = Some imps ->
    instantiate s m imps ((s', inst, exps), start) ->
    const_list vs ->
    vis' = <[ vi := exps ]> vis ->
    host_reduce (s, vis, (ms, (ID_instantiate vi vm vimps) :: idecs'), vs) (s', vis', (ms, idecs'), map_start start)
| HR_wasm_step: forall s vis ms idecs s' es es' hs hs',
    reduce hs s empty_frame es hs' s' empty_frame es' ->
    host_reduce (s, vis, (ms, idecs), es) (s', vis, (ms, idecs), es').
    
End Iris_host.
