module type Host = sig

  include Extract.Parametric_host

  (** The monad of host events. *)
  type 'a host_event
  val host_ret : 'a -> 'a host_event
  val host_bind : 'a host_event -> ('a -> 'b host_event) -> 'b host_event

  (** Application of a host function in the host monad. *)
  val host_apply :
    host_state_type -> Extract.store_record -> Extract.function_type -> host_function -> Extract.value0 list ->
    (Extract.store_record * Extract.result) option host_event

end

module type InterpreterType = sig

  module Host : Host
  include module type of Host

  val ( >>= ) : 'a host_event -> ('a -> 'b host_event) -> 'b host_event
  val ( let* ) : 'a host_event -> ('a -> 'b host_event) -> 'b host_event
  val ( let+ ) : 'a host_event -> ('a -> 'b) -> 'b host_event
  val ( and+ ) : 'a host_event -> 'b host_event -> ('a * 'b) host_event
  val pure : 'a -> 'a host_event

  type store_record = Extract.store_record
  type frame = Extract.frame
  type wasm_config_tuple = Extract.config_tuple
  type interp_config_tuple = Extract.cfg_tuple_ctx
  type res_tuple = Extract.run_step_ctx_result
  type basic_instruction = Extract.basic_instruction
  type administrative_instruction = Extract.administrative_instruction
  type moduleinst = Extract.moduleinst
  type value = Extract.value0
  type externval = Extract.extern_value

  val empty_store_record : store_record

  (** Run one step of the interpreter. *)
  val run_one_step :
    interp_config_tuple -> Z.t -> res_tuple

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

  val run_parse_module_str : string -> Extract.module0 option
  val run_parse_arg : string -> value option

  val pp_values : value list -> string
  val pp_store : int -> Extract.store_record -> string
  val pp_cfg_tuple_ctx_except_store :
    interp_config_tuple -> string
    
  val pp_res_cfg_except_store :
    interp_config_tuple -> res_tuple -> string
  val pp_es : Extract.administrative_instruction list -> string

  val pp_externval: externval -> string

  val is_canonical_nan: Extract.number_type -> value -> bool

  val is_arithmetic_nan: Extract.number_type -> value -> bool

  val is_funcref : value -> bool

  val is_externref : value -> bool

  val v128_extract_lanes: Extract.vshape -> Extract.SIMD.v128 -> Extract.value_num list

end

module Extraction_instance = Extract.Extraction_instance (Ocaml_host.Ocaml_host)

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

  type store_record = Extract.store_record
  type frame = Extract.frame
  type wasm_config_tuple = Extract.config_tuple
  type interp_config_tuple = Extraction_instance.cfg_tuple_ctx
  type res_tuple = Extraction_instance.run_step_ctx_result
  type basic_instruction = Extract.basic_instruction
  type administrative_instruction = Extract.administrative_instruction
  type moduleinst = Extract.moduleinst
  type value = Extract.value0
  type externval = Extract.extern_value

  let empty_store_record = Extraction_instance.empty_store_record

  (** Run one step of the interpreter. *)
  let run_one_step cfg d = 
    Extraction_instance.run_one_step (Obj.magic ()) cfg d

  let run_v_init = Extraction_instance.run_v_init

  let interp_cfg_of_wasm = Extraction_instance.interp_cfg_of_wasm

  let wasm_global_get =
    Extraction_instance.wasm_global_get

  let invoke_extern =
    Extraction_instance.invoke_extern

  let interp_instantiate_wrapper s m extvals =
    let (res, msg) = Extraction_instance.interp_instantiate_wrapper (Obj.magic ()) s m extvals in
    (res, msg)

  let get_import_path m = 
    Extraction_instance.get_import_path m

  let get_exports f = 
    let exps = Extraction_instance.get_exports f in
    List.map (fun exp -> let (n, v) = exp in (n, v)) exps

  let run_parse_module_str m = Extract.run_parse_module_str m

  let run_parse_arg a = Extract.run_parse_arg a

  let pp_values l =
    Extraction_instance.pp_values l

  let pp_store i st =
    Extraction_instance.pp_store (Convert.to_nat i) st

  let pp_cfg_tuple_ctx_except_store r =
    Extraction_instance.pp_cfg_tuple_ctx_except_store r
    
(* Depth doesn't matter for pretty printing cfg *)
  let pp_res_cfg_except_store cfg res =
    Extraction_instance.pp_res_cfg_except_store (Obj.magic ()) cfg (Utils.z_of_int 0) res

  let pp_es es =
    Extraction_instance.pp_administrative_instructions O es

  let pp_externval extval = 
    Extraction_instance.pp_extern_value extval

  let is_canonical_nan =
    Extraction_instance.is_canonical_nan

  let is_arithmetic_nan =
    Extraction_instance.is_arithmetic_nan

  let is_funcref = Extraction_instance.is_funcref

  let is_externref = Extraction_instance.is_externref

  let v128_extract_lanes sh v = 
    Extraction_instance.v128_extract_lanes sh v
end
