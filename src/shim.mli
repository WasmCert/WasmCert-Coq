(** Interface between [Extract] and the main files. *)

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

module Extraction_instance : Host

module type InterpreterType = sig

  module Host : Host
  include module type of Host

  (** The usual monadic notations. *)
  val ( >>= ) : 'a host_event -> ('a -> 'b host_event) -> 'b host_event
  val ( let* ) : 'a host_event -> ('a -> 'b host_event) -> 'b host_event
  val ( let+ ) : 'a host_event -> ('a -> 'b) -> 'b host_event
  val ( and+ ) : 'a host_event -> 'b host_event -> ('a * 'b) host_event
  val pure : 'a -> 'a host_event

  type store_record = Extract.Extraction_instance.store_record
  type frame = Extract.frame
  type wasm_config_tuple = Extract.config_tuple
  type interp_config_tuple = Extract.Extraction_instance.cfg_tuple_ctx
  type res_tuple = Extract.Extraction_instance.run_step_ctx_result
  type basic_instruction = Extract.basic_instruction
  type administrative_instruction = Extract.administrative_instruction
  type moduleinst = Extract.moduleinst
  type value = Extract.value0
  type externval = Extract.extern_value

  val empty_store_record : store_record

  (** Run one step of the interpreter. *)
  val run_one_step :
    interp_config_tuple -> int -> res_tuple

  (* Given a store and an admin instruction list to run, construct the corresponding interpreter configuration to run. *)
  val run_v_init : 
    store_record -> administrative_instruction list -> interp_config_tuple option

  (* Convert a Wasm configuration tuple (s; f; es) to an interpreter configuration (in theories/interpreter_ctx.v). *)
  val interp_cfg_of_wasm : 
    wasm_config_tuple -> interp_config_tuple

  (* Get a global variable from the Wasm store by its address (externval). *)
  val wasm_global_get :
    store_record -> externval -> value option

  (** Look-up a specific extracted function of the instantiation. *)
  val invoke_extern:
    store_record -> externval -> value list -> (administrative_instruction list) option

  (** Perform the instantiation of a module. *)
  val interp_instantiate_wrapper :
    store_record -> Extract.module0 -> externval list  -> wasm_config_tuple option * string

  (** Extracting the import path from the parsed module. *)
  val get_import_path: Extract.module0 -> (string * string) list

  (** Extracting the exports from the resulting frame. *)
  val get_exports : frame -> (string * externval) list

  (** Parsing. *)
  val run_parse_module : string -> Extract.module0 option

  val run_parse_arg : string -> Extract.value0 option

  (** Pretty-printing. *)

  val pp_values : Extract.value0 list -> string
  val pp_store : int (** The indentation level *) -> store_record -> string

  val pp_cfg_tuple_ctx_except_store :
    interp_config_tuple -> string
    
  val pp_res_cfg_except_store :
    interp_config_tuple -> res_tuple -> string

  val pp_es : Extract.administrative_instruction list -> string

  val pp_externval: externval -> string

  val is_canonical_nan: Extract.number_type -> value -> bool

  val is_arithmetic_nan: Extract.number_type -> value -> bool

  val v128_extract_lanes: Extract.vshape -> Extract.SIMD.v128 -> Extract.value_num list

end

module Interpreter : functor (EH : Host) ->
InterpreterType
  with module Host = EH
  and type 'a host_event = 'a EH.host_event
