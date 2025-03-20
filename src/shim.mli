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

module DummyHost : Host

module type InterpreterType = sig

  module Host : Host
  include module type of Host

  (** The usual monadic notations. *)
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
  type value = Extract.value0
  type externval = Extract.extern_value

  val empty_store_record : store_record

  (** Run one step of the interpreter. *)
  val run_step_compat :
    Obj.t -> config_tuple -> res_tuple

  (* Reform the one step result back to a cfg tuple, if possible *)
  val run_step_cfg_ctx_reform:
    config_tuple -> config_tuple option

  val run_v_init : 
    store_record -> administrative_instruction list -> config_tuple option

  val run_v_init_with_frame : 
    store_record -> frame -> administrative_instruction list-> config_tuple

  (** Look-up a specific extracted function of the instantiation. *)
  val invoke_exported_function_args :
    string -> store_record -> frame -> value list -> (administrative_instruction list) option

  (** Perform the instantiation of a module. *)
  val interp_instantiate_wrapper :
    store_record -> Extract.module0 -> externval list  -> (((Obj.t * store_record) * frame) * administrative_instruction list) option

  (** Parsing. *)

  val run_parse_module : string -> Extract.module0 option

  val run_parse_arg : string -> Extract.value0 option

  (** Pretty-printing. *)

  val pp_values : Extract.value0 list -> string
  val pp_store : int (** The indentation level *) -> store_record -> string

  val pp_cfg_tuple_ctx_except_store :
    config_tuple -> string
    
  val pp_res_cfg_except_store :
    Obj.t -> config_tuple -> res_tuple -> string

  val pp_es : Extract.administrative_instruction list -> string


end

module Interpreter : functor (EH : Host) ->
InterpreterType
  with module Host = EH
  and type 'a host_event = 'a EH.host_event
