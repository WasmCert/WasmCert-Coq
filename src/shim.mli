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
      host_function Extract.store_record -> Extract.function_type -> host_function -> Extract.value0 list ->
      (host_function Extract.store_record * Extract.result) option host_event

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

    type store_record = Dune__exe__Extract.EmptyHost.store_record
    type config_tuple = host_function Extract.config_tuple
    type res_tuple = host_function Extract.res_tuple
    type administrative_instruction = Extract.administrative_instruction

    (** Run the interpreter until reaching a result. *)
    (* val run_v : *)
    (*   int (** The depth *) -> Extract.instance -> config_tuple -> *)
    (*   (store_record * Extract.res) host_event *)

    val run_v :
      int -> Extract.typeidx ->
      Obj.t * Obj.t Extract.store_record * Extract.frame * administrative_instruction list ->
      (Obj.t * Obj.t Extract.store_record) * Extract.res

    (* val run_v : *)
    (*   int (** The depth *) -> Extract.instance -> config_tuple -> *)
    (*   (store_record * Extract.res) host_event *)

    (* val run_v : *)
    (*   int (** The depth *) -> Extract.typeidx -> *)
    (*   Obj.t * Obj.t Extract.store_record * Extract.frame * administrative_instruction list -> *)
    (*   (Obj.t * Obj.t Extract.store_record) * Extract.res *)

    (** Run one step of the interpreter. *)
    val run_step :
      (* int (** The depth *) -> Extract.instance -> config_tuple -> *)
      (* host_function Extract.res_tuple host_event *)
      int -> 'a ->
      Obj.t * Obj.t Extract.store_record * Extract.frame * administrative_instruction list -> Extract.res_step'

    (** State whether a list of administrative instructions is actually just a list of values. *)
    val is_const_list : administrative_instruction list -> Extract.value0 list option

    (** Look-up a specific extracted function of the instantiation. *)
    val lookup_exported_function :
      (* string -> (store_record * Extract.instance) * Extract.module_export list -> *)
      (* config_tuple option *)
      string -> (Dune__exe__Extract.EmptyHost.store_record * Extract.instance) *
      Extract.module_export list ->
      ((Dune__exe__Extract.EmptyHost.store_record * Extract.frame) * administrative_instruction list) option

    (** Perform the instantiation of a module. *)
    val interp_instantiate_wrapper :
      Extract.module0 ->
      (((Dune__exe__Extract.EmptyHost.store_record * Extract.instance) * Extract.module_export list) * Extract.typeidx option) option

    (** Parsing. *)

    val run_parse_module : string -> Extract.module0 option

    (** Pretty-printing. *)

    val pp_values : Extract.value0 list -> string
    val pp_store : int (** The indentation level *) -> Dune__exe__Extract.EmptyHost.store_record -> string
    val pp_res_tuple_except_store : res_tuple -> string
    val pp_config_tuple_except_store : config_tuple -> string

  end

module Interpreter : functor (EH : Host) ->
  InterpreterType
    with module Host = EH
    and type 'a host_event = 'a EH.host_event

