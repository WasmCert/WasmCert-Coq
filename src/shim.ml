module type Host = sig

  (** The type of host functions. *)
  type host_function

  (** Equality of host functions. *)
  val host_function_eq_dec : host_function -> host_function -> bool

  (** The monad of host events. *)
  type 'a host_event
  val host_ret : 'a -> 'a host_event
  val host_bind : 'a host_event -> ('a -> 'b host_event) -> 'b host_event

  (** Application of a host function in the host monad. *)
  val host_apply :
    Extract.store_record -> Extract.function_type -> host_function -> Extract.value0 list ->
    (Extract.store_record * Extract.result) option host_event

  (** Printing a host function. *)
  val show_host_function : host_function -> string
end

module DummyHost = struct
  include Extract.DummyHost
  let show_host_function _ = assert false
end

module type InterpreterType = sig

  module Host : Host
  include module type of Host

  val ( >>= ) : 'a host_event -> ('a -> 'b host_event) -> 'b host_event
  val ( let* ) : 'a host_event -> ('a -> 'b host_event) -> 'b host_event
  val ( let+ ) : 'a host_event -> ('a -> 'b) -> 'b host_event
  val ( and+ ) : 'a host_event -> 'b host_event -> ('a * 'b) host_event
  val pure : 'a -> 'a host_event

  type store_record = Extract.DummyHost.store_record
  type frame = Extract.frame
  type config_tuple = Extract.Interpreter_ctx_extract.cfg_tuple_ctx
  type res_tuple = Extract.Interpreter_ctx_extract.run_step_ctx_result
  type basic_instruction = Extract.basic_instruction
  type administrative_instruction = Extract.administrative_instruction
  type moduleinst = Extract.moduleinst

  (** Run one step of the interpreter. *)
  val run_step_compat :
    Obj.t -> config_tuple -> res_tuple

  (* Reform the one step result back to a cfg tuple, if possible *)
  val run_step_cfg_ctx_reform:
    config_tuple -> config_tuple option

  val run_v_init : 
    store_record -> administrative_instruction list -> config_tuple option

  val run_v_init_with_frame : 
    store_record -> frame -> administrative_instruction list -> config_tuple

  (** Look-up a specific extracted function of the instantiation and invoke with the provided arguments. *)
  val invoke_exported_function_args :
    string -> store_record -> frame -> Extract.value0 list -> (administrative_instruction list) option

  (** Perform the instantiation of a module. *)
  val interp_instantiate_wrapper :
    Extract.module0 -> (((Obj.t * store_record) * frame) * administrative_instruction list) option

  val run_parse_module : string -> Extract.module0 option
  val run_parse_arg : string -> Extract.value0 option

  val pp_values : Extract.value0 list -> string
  val pp_store : int -> Dune__exe__Extract.DummyHost.store_record -> string
  val pp_cfg_tuple_ctx_except_store :
    config_tuple -> string
    
  val pp_res_cfg_except_store :
    Obj.t -> config_tuple -> res_tuple -> string
  val pp_es : Extract.administrative_instruction list -> string

end

module Interpreter =
functor (EH : Host) -> struct

  module Host = EH
  include Host

  let ( >>= ) = host_bind

  let ( let* ) = host_bind

  let pure = host_ret

  let ( let+ ) a f =
    let* a = a in
    pure (f a)

  let ( and+ ) a b =
    let* a = a in
    let* b = b in
    pure (a, b)

  module Interpreter = Extract.Interpreter_ctx_extract
  module Instantiation = Extract.Instantiation_func_extract
  module PP = Extract.PP

  type store_record = Extract.DummyHost.store_record
  type frame = Extract.frame
  type config_tuple = Extract.Interpreter_ctx_extract.cfg_tuple_ctx
  type res_tuple = Extract.Interpreter_ctx_extract.run_step_ctx_result
  type basic_instruction = Extract.basic_instruction
  type administrative_instruction = Extract.administrative_instruction
  type moduleinst = Extract.moduleinst


  (** Run one step of the interpreter. *)
  let run_step_compat = 
    Interpreter.run_one_step_ctx

  (* Reform the one step result back to a cfg tuple, if possible *)
  let run_step_cfg_ctx_reform = Interpreter.run_step_cfg_ctx_reform

  let run_v_init = Interpreter.run_v_init

  let run_v_init_with_frame = Interpreter.run_v_init_with_frame

  let invoke_exported_function_args name =
    Instantiation.invoke_exported_function_args (Utils.explode name)

  let interp_instantiate_wrapper m =
    Instantiation.interp_instantiate_wrapper m
(*
  let show_host_function_char_list h = Utils.explode (show_host_function h)
*)
  let run_parse_module m = Extract.run_parse_module (Utils.explode m)

  let run_parse_arg a = Extract.run_parse_arg (Utils.explode a)

  let pp_values l =
    Utils.implode (PP.pp_values l)

  let pp_store i st =
    Utils.implode (PP.pp_store (Convert.to_nat i) st)

  let pp_cfg_tuple_ctx_except_store r =
    Utils.implode (PP.pp_cfg_tuple_ctx_except_store r)  
    
  let pp_res_cfg_except_store hs cfg res =
    Utils.implode (PP.pp_res_cfg_except_store hs cfg res)

  let pp_es es =
    Utils.implode (PP.pp_administrative_instructions O es)

end
