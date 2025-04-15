(* Interface for wast testing scripts *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Export opsem interpreter_ctx instantiation_func.
From Coq Require Import BinNat String.

Module Wast_interface.

  Definition is_canonical_nan (t: number_type) (v: value) : bool :=
    match t, v with
    | Tnum_f32, VAL_num (VAL_float32 c) => Wasm_float.float_is_canonical f32m c
    | Tnum_f64, VAL_num (VAL_float64 c) => Wasm_float.float_is_canonical f64m c
    | _, _ => false
    end.

  Definition is_arithmetic_nan (t: number_type) (v: value) : bool :=
    match t, v with
    | Tnum_f32, VAL_num (VAL_float32 c) => Wasm_float.float_is_arithmetic f32m c
    | Tnum_f64, VAL_num (VAL_float64 c) => Wasm_float.float_is_arithmetic f64m c
    | _, _ => false
    end.
  
End Wast_interface.

(*
From stdpp Require Import gmap.
From HB Require Import structures.

Definition wast_host_state := gmap string (gmap string extern_value).

Definition wast_var := name.

Definition wast_module := module.

Inductive wast_action : Type :=
| WAC_invoke: wast_var -> name -> list value -> wast_action
| WAC_get (* TODO *)
.

Inductive wast_nan: Set :=
| WNA_canonical
| WNA_arithmetic
.

Inductive wast_numpat: Type :=
| WNP_num: value -> wast_numpat
| WNP_nan: wast_nan -> wast_numpat
.

Inductive wast_vecpat: Type := (* TODO *).

Inductive wast_refpat: Type := (* TODO *).

Inductive wast_result : Type :=
| WR_numres: wast_numpat -> wast_result
| WR_vecres: wast_vecpat -> wast_result
| WR_refres: wast_refpat -> wast_result
.

Inductive wast_assertion : Type :=
| WAS_malformed: wast_module -> string -> wast_assertion 
| WAS_invalid: wast_module -> string -> wast_assertion 
| WAS_unlinkable: wast_module -> string -> wast_assertion 
| WAS_uninstantiable: wast_module -> string -> wast_assertion 
| WAS_return: wast_action -> list wast_result -> wast_assertion 
| WAS_trap: wast_action -> string -> wast_assertion 
| WAS_exhaustion: wast_action -> string -> wast_assertion 
.

Inductive wast_command : Type :=
| WC_module: option wast_var -> wast_module -> wast_command
| WC_register (* TODO *)
| WC_action (* TODO *)
| WC_assertion: wast_assertion -> wast_command
| WC_meta (* TODO *)
.

Definition wast_script : Type :=
  list wast_command.

Definition wast_command_eq_dec : forall ws1 ws2 : wast_command,
  {ws1 = ws2} + {ws1 <> ws2}.
Proof. decidable_equality. Defined.

Definition wast_command_eqb v1 v2 : bool := wast_command_eq_dec v1 v2.
Definition eqwast_commandP : Equality.axiom wast_command_eqb :=
  eq_dec_Equality_axiom wast_command_eq_dec.

HB.instance Definition wast_command_eqMixin := hasDecEq.Build wast_command eqwast_commandP.

Definition wast_host_state_eq_dec : forall wh1 wh2 : wast_host_state,
  {wh1 = wh2} + {wh1 <> wh2}.
Proof.
  do 2 (apply gmap_eq_dec).
  unfold EqDecision, Decision.
  by apply extern_value_eq_dec.
Defined.

Definition wast_host_state_eqb v1 v2 : bool := wast_host_state_eq_dec v1 v2.
Definition eqwast_host_stateP : Equality.axiom wast_host_state_eqb :=
  eq_dec_Equality_axiom wast_host_state_eq_dec.

HB.instance Definition wast_host_state_eqMixin := hasDecEq.Build wast_host_state eqwast_host_stateP.
Local Instance wast_host_function : host_function_class.
Proof.
  by refine (@Build_host_function_class wast_command wast_command_eq_dec).
Defined.

#[export]
Instance wast_host : host.
Proof.
  by refine {|
      host_state := wast_host_state;
      host_application _ _ _ _ _ _ _ := False
    |}.
Defined.

Inductive run_wast_result : Type :=
| RWR_ok: wast_host_state -> store_record -> run_wast_result
| RWR_error: wast_host_state -> store_record -> string -> run_wast_result
.

(*
Definition string_of_name (n: name) : string :=
  string_of_list_byte n.

Definition get_import_path (m: module) : list (string * string) :=
  map (fun imp => (string_of_name (imp_module imp), string_of_name (imp_name imp))) m.(mod_imports).

Definition get_exports (f: frame) : list (string * extern_value) :=
  map (fun exp_inst => (string_of_name (exportinst_name exp_inst), exportinst_val exp_inst)) f.(f_inst).(inst_exports).

(* Provide the instruction for invoking an external function under a given store *)
Definition invoke_extern (s: store_record) (ext: extern_value) (args: list value) : option (list administrative_instruction) :=
  match ext with
  | EV_func fi =>
      match lookup_N s.(s_funcs) fi with
      | Some (FC_func_native (Tf ts1 ts2) _ _) =>
          if (those (map (typeof_value s) args) == Some ts1) then
            Some (v_to_e_list args ++ [::AI_invoke fi])
          else None
      | _ => None
      end
  | _ => None
  end.
 *)

Definition get_import_extern (hs: wast_host_state) (imp_path: string * string) : option extern_value :=
  match imp_path with
  | (modname, impname) =>
      option_bind _ _ (fun m => m !! impname) (hs !! modname) 
  end.

Definition get_import_externs (hs: wast_host_state) (imp_paths: list (string * string)) :=
  those (map (fun p => get_import_extern hs p) imp_paths).

Definition run_command (hs: wast_host_state) (s: store_record) (cmd: wast_command): run_wast_result :=
  match cmd with
  | WC_module ovar wmod =>
      let imp_paths := Instantiation_func_extract.get_import_path wmod in
      match get_import_externs hs imp_paths with
      | Some imps =>
          match interp_instantiate hs s wmod imps with
          | Some (hs', s', f, bes) =>
              match 
              RWR_ok hs' s'
          | None => RWR_error hs s "instantiation error"
          end
      | None => RWR_error hs s "invalid imports"
      end
  | _ => RWR_error hs s "unsupported wast command"
  end.

      
      
      

Module Wast_interface.

  Import instantiation_func.

  
  
End Wast_interface.
*)
