(** Functions to execute the definitions of the [Shim] module. *)

(** A host implementation. *)
module Host : sig
    include Shim.Host

    (** We add the ability to throw error in the monad. *)
    val error : string -> 'a host_event

    (** We also add a way to pattern-match the monad. *)
    val pmatch :
      ('a -> 'b) (** Normal case *) ->
      (string -> 'b) (** Error case *) ->
      'a host_event -> 'b host_event

    (** Helper functions to convert between similar monads. *)
    val from_out : 'a Output.out -> 'a host_event
    val to_out : 'a host_event -> 'a host_event Output.out

  end

module Interpreter : Shim.InterpreterType with type 'a host_event = 'a Host.host_event

(* Type of the interpreter evaluation result *)
type eval_cfg_result =
  | Cfg_res of Interpreter.store_record * Extract.frame * Extract.value0 list
  | Cfg_trap of Interpreter.store_record * Extract.frame
  | Cfg_err

(* Evaluating an interpreter configuration fully. *)
val eval_interp_cfg: Output.verbosity -> int -> Interpreter.interp_config_tuple -> eval_cfg_result

(* Evaluate a Wasm configuration using the interpreter configuration. *)
val eval_wasm_cfg: Output.verbosity -> Interpreter.wasm_config_tuple -> eval_cfg_result

(* Type of the host extern val store *)
module StringMap : Map.S with type key = string

type host_extern_store = (Interpreter.externval StringMap.t) StringMap.t

(* Given a starting state and a list of imports (store references), instantiating a module.
   Return the interpreter result after running the instantiation instructions. Does not update the host export store. *)
val instantiate: Output.verbosity -> host_extern_store -> Interpreter.store_record -> Extract.module0 -> eval_cfg_result Host.host_event

(* A host wrapper for the instantiation function that updates the host export store. *)
val instantiate_host: Output.verbosity -> host_extern_store -> Interpreter.store_record -> string -> Extract.module0 -> (host_extern_store * Interpreter.store_record) Host.host_event

(** Given a verbosity level, a host and Wasm state, a list of arguments, and a module and function name, invoke the Wasm function. *)
val invoke_func : Output.verbosity -> host_extern_store -> (Interpreter.store_record * Extract.frame) -> Extract.value0 list -> string -> string -> Interpreter.store_record Host.host_event
