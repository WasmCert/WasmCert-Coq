(* The setup for extraction *)
From Coq Require Import String.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From HB Require Import structures.
From Wasm Require Import memory host interpreter_ctx instantiation_func pp.
From ExtLib Require Import Structures.Monad.
From ExtLib Require Import IdentityMonad.

From Wasm Require Import memory_vec.

Module Memory_instance.

  Definition memory_instance := Memory_vec.
  
End Memory_instance.

Module Extraction_instance.

Section DummyHost.

Existing Instance Memory_instance.memory_instance.
  
Definition host_function := void.
Definition host_event := ident.
Definition host_ret := @ret _ Monad_ident.
Definition host_bind := @bind _ Monad_ident.

Definition host_function_eq_dec : forall f1 f2 : host_function, {f1 = f2} + {f1 <> f2}.
Proof. decidable_equality. Defined.

#[export]
Instance hfc: host_function_class.
Proof.
  exact (Build_host_function_class host_function_eq_dec).
Defined.

Definition host_apply (_ : store_record) (_ : function_type) :=
  of_void (seq value -> ident (option (store_record * result))).

#[export]
Instance host_instance : host.
Proof.
  by refine {|
      host_state := unit;
      host_application _ _ _ _ _ _ _ := False
    |}.
Defined.

Definition host_application_impl : host_state -> store_record -> function_type -> host_function -> seq value ->
                                   (host_state * option (store_record * result)).
Proof.
  move => ??? hf.
  by refine ((of_void _) hf).
Defined.

Definition host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).
Proof.
  move => ??? hf; by inversion hf.
Defined.

End DummyHost.


Section Interpreter_ctx_extract.

  Definition empty_frame := empty_frame.

  Definition store_record := store_record.
  
Definition cfg_tuple_ctx : Type := cfg_tuple_ctx.

Definition run_step_ctx_result : host_state -> cfg_tuple_ctx -> BinNums.N -> Type := run_step_ctx_result.

Definition run_one_step (cfg: cfg_tuple_ctx) (d: BinNums.N) : run_step_ctx_result tt cfg d := run_one_step host_application_impl_correct tt cfg d.

Definition run_v_init : store_record -> list administrative_instruction -> option cfg_tuple_ctx := run_v_init.

Definition interp_cfg_of_wasm := interp_cfg_of_wasm.

End Interpreter_ctx_extract.


Section PP.

Definition pp_values := pp_values.

Definition pp_store := pp_store.

Definition pp_cfg_tuple_ctx_except_store := pp_cfg_tuple_ctx_except_store.

Definition pp_res_cfg_except_store {cfg: cfg_tuple_ctx} {d: BinNums.N} (res: run_step_ctx_result tt cfg d) := pp_res_cfg_except_store res.

Definition pp_administrative_instructions := pp_administrative_instructions.

Definition pp_extern_value := pp_extern_value.

End PP.


Section Instantiation_func_extract.

Definition empty_store_record : store_record := {|
    s_funcs := nil;
    s_tables := nil;
    s_mems := nil;
    s_globals := nil;
    s_elems := nil;
    s_datas := nil;
  |}.

(* Provide a unit host state and convert the starting expression to administrative *)
Definition interp_instantiate_wrapper (s: store_record) (m : module) (v_imps: list extern_value) : option config_tuple * string :=
  match interp_instantiate tt s m v_imps with
  | (Some (hs', s', f, bes), str) => (Some (s', (f, to_e_list bes)), str)
  | (None, str) => (None, str)
  end.

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
            Some (v_to_e_list args ++ [::AI_invoke fi])%list
          else None
      | _ => None
      end
  | _ => None
  end.

Definition wasm_global_get (s: store_record) (ext: extern_value) : option value :=
  match ext with
  | EV_global gi =>
      match lookup_N s.(s_globals) gi with
      | Some gv => Some gv.(g_val)
      | None => None
      end
  | _ => None
  end.

End Instantiation_func_extract.

Section Wast.
  
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

  Definition is_funcref (v: value) : bool :=
    match v with
    | VAL_ref (VAL_ref_func _) => true
    | _ => false
    end.

  Definition is_externref (v: value) : bool :=
    match v with
    | VAL_ref (VAL_ref_extern _) => true
    | _ => false
    end.
  
End Wast.

End Extraction_instance.
