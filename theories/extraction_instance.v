(* The setup for extraction *)
From Coq Require Import String ZArith.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From HB Require Import structures.
From Wasm Require Import numerics memory host interpreter_ctx instantiation_func pp.
From ExtLib Require Import Structures.Monad IdentityMonad.

From Wasm Require Import memory_vec binary_format_parser text_format_parser.

Module Memory_instance.

  Definition memory_instance := Memory_vec.
  
End Memory_instance.

  
(* A more general extraction that allows non-trivial host functions, extracting the interpreter as a functor-like module. Not using the monadic design yet as that requires corresponding changes to the interpreter as well. *)
Module Type Parametric_host.

  Parameter host_function: Type.

  Parameter host_function_eq_dec: forall (a b: host_function),
      {a = b} + {a <> b}.

  #[export]
    Instance hfc: host_function_class := Build_host_function_class host_function_eq_dec.

  Parameter host_state_type : Type.

  (* Host function application are left as parameters and must be realised in a separate file in extraction. *)
  (* Migrate to monadic host operations when the interpreter updates to itree *)
  Parameter host_apply_pure: host_state_type -> store_record -> function_type -> host_function -> seq value -> (host_state_type * option (store_record * result)).

  (* However, such a parametric host cannot be proven to respect Wasm's store invariant, as they will be formulated in OCaml. *)
  Axiom host_application_extension : forall hs s ft h vs hs' s' r,
      host_apply_pure hs s ft h vs = (hs', Some (s', r)) ->
      store_extension s s'.

  Axiom host_application_typing : forall hs s ft h vs hs' s' r,
      host_apply_pure hs s ft h vs = (hs', Some (s', r)) ->
      store_typing s ->
      store_typing s'.

  Axiom host_application_respect : forall hs s ts1 ts2 h vs hs' s' r,
      host_apply_pure hs s (Tf ts1 ts2) h vs = (hs', Some (s', r)) ->
      result_types_agree s' ts2 r.

End Parametric_host.

Module Monadic_host (PH: Parametric_host).

  Include PH.
  
  Definition host_event := ident.
  Definition host_ret := @ret _ Monad_ident.
  Definition host_bind := @bind _ Monad_ident.

End Monadic_host.
  
Module Utility.
  
  Definition vali32_of_Z (z: Z) : value :=
    VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m z)).
  
  Definition vali64_of_Z (z: Z) : value :=
    VAL_num (VAL_int64 (Wasm_int.int_of_Z i64m z)).

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

  Definition v128_extract_lanes (sh: vshape) (v: v128) :=
    v128_extract_lanes sh SX_S v.
  
End Wast.

  
End Utility.


Module Extraction_instance (PH: Parametric_host).

Module MH := Monadic_host PH.

Include MH.

Export PH.

Definition run_parse_module_str := run_parse_module_str.
Definition run_parse_arg := run_parse_arg.
                                         

#[export]
Instance host_instance : host.
Proof.
  refine {|
      host_state := host_state_type;
      host_application hs s ft hf vs hs' res := host_apply_pure hs s ft hf vs = (hs', res)
    |}.
  - intros; by eapply host_application_extension; eauto.
  - intros; by eapply host_application_typing; eauto.
  - intros; by eapply host_application_respect; eauto.
Defined.

Definition host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_apply_pure hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).
Proof.
  done.
Defined.

Section Interpreter_ctx_extract.

Definition empty_frame := empty_frame.
  
Definition store_record := store_record.
  
Definition cfg_tuple_ctx : Type := cfg_tuple_ctx.

Definition run_step_ctx_result : host_state -> cfg_tuple_ctx -> N -> Type := run_step_ctx_result.

Definition run_one_step (hs: host_state) (cfg: cfg_tuple_ctx) (d: N) : run_step_ctx_result hs cfg d := run_one_step host_application_impl_correct hs cfg d.

Definition run_v_init : store_record -> list administrative_instruction -> option cfg_tuple_ctx := run_v_init.

Definition interp_cfg_of_wasm := interp_cfg_of_wasm.

End Interpreter_ctx_extract.


Section PP.

Definition pp_values := pp_values.

Definition pp_store := pp_store.

Definition pp_cfg_tuple_ctx_except_store := pp_cfg_tuple_ctx_except_store.

Definition pp_res_cfg_except_store {hs: host_state} {cfg: cfg_tuple_ctx} {d: N} (res: run_step_ctx_result hs cfg d) := pp_res_cfg_except_store res.

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
Definition interp_instantiate_wrapper (hs: host_state) (s: store_record) (m : module) (v_imps: list extern_value) : option config_tuple * string :=
  match interp_instantiate hs s m v_imps with
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

End Extraction_instance.
