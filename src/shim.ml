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
  type wasm_config_tuple = Extract.config_tuple
  type interp_config_tuple = Extract.Interpreter_ctx_extract.cfg_tuple_ctx
  type res_tuple = Extract.Interpreter_ctx_extract.run_step_ctx_result
  type basic_instruction = Extract.basic_instruction
  type administrative_instruction = Extract.administrative_instruction
  type moduleinst = Extract.moduleinst
  type value = Extract.value0
  type externval = Extract.extern_value

  val empty_store_record : store_record

  (** Run one step of the interpreter. *)
  val run_one_step :
    interp_config_tuple -> res_tuple

  val run_v_init : 
    store_record -> administrative_instruction list -> interp_config_tuple option

  val interp_cfg_of_wasm : 
    wasm_config_tuple -> interp_config_tuple

  val wasm_global_get :
    store_record -> externval -> value option

  (** Look-up a specific extracted function of the instantiation and invoke with the provided arguments. *)
  val invoke_extern :
    store_record -> externval -> value list -> (administrative_instruction list) option

  (** Perform the instantiation of a module. *)
  val interp_instantiate_wrapper :
    store_record -> Extract.module0 -> externval list  -> wasm_config_tuple option * string

  val get_import_path: Extract.module0 -> (string * string) list
  val get_exports : frame -> (string * externval) list

  val run_parse_module : string -> Extract.module0 option
  val run_parse_arg : string -> value option

  val pp_values : value list -> string
  val pp_store : int -> Dune__exe__Extract.DummyHost.store_record -> string
  val pp_cfg_tuple_ctx_except_store :
    interp_config_tuple -> string
    
  val pp_res_cfg_except_store :
    interp_config_tuple -> res_tuple -> string
  val pp_es : Extract.administrative_instruction list -> string

  val pp_externval: externval -> string

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
  type wasm_config_tuple = Extract.config_tuple
  type interp_config_tuple = Extract.Interpreter_ctx_extract.cfg_tuple_ctx
  type res_tuple = Extract.Interpreter_ctx_extract.run_step_ctx_result
  type basic_instruction = Extract.basic_instruction
  type administrative_instruction = Extract.administrative_instruction
  type moduleinst = Extract.moduleinst
  type value = Extract.value0
  type externval = Extract.extern_value

  let empty_store_record = Instantiation.empty_store_record

  (** Run one step of the interpreter. *)
  let run_one_step = 
    Interpreter.run_one_step

  let run_v_init = Interpreter.run_v_init

  let interp_cfg_of_wasm = Interpreter.interp_cfg_of_wasm

  let wasm_global_get =
    Instantiation.wasm_global_get

  let invoke_extern =
    Instantiation.invoke_extern

  let interp_instantiate_wrapper s m extvals =
    let (res, msg) = Instantiation.interp_instantiate_wrapper s m extvals in
    (res, Utils.implode msg)

  let get_import_path m = 
    let implode_pair p =
      let (m, imp) = p in
      (Utils.implode m, Utils.implode imp) in
    List.map implode_pair (Instantiation.get_import_path m)

  let get_exports f = 
    let exps = Instantiation.get_exports f in
    List.map (fun exp -> let (n, v) = exp in (Utils.implode n, v)) exps

  let run_parse_module m = Extract.run_parse_module (Utils.explode m)

  let run_parse_arg a = Extract.run_parse_arg (Utils.explode a)

  let pp_values l =
    Utils.implode (PP.pp_values l)

  let pp_store i st =
    Utils.implode (PP.pp_store (Convert.to_nat i) st)

  let pp_cfg_tuple_ctx_except_store r =
    Utils.implode (PP.pp_cfg_tuple_ctx_except_store r)  
    
  let pp_res_cfg_except_store cfg res =
    Utils.implode (PP.pp_res_cfg_except_store cfg res)

  let pp_es es =
    Utils.implode (PP.pp_administrative_instructions O es)

  let pp_externval extval = 
    Utils.implode (PP.pp_extern_value extval)
end
