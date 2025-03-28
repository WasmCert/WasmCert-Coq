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

type eval_cfg_result =
  | Cfg_res of Interpreter.store_record * Extract.frame * Extract.value0 list
  | Cfg_trap of Interpreter.store_record * Extract.frame
  | Cfg_err

(* Evaluating an interpreter configuration fully. *)
val eval_interp_cfg: Output.verbosity -> int -> Interpreter.interp_config_tuple -> eval_cfg_result

(* Evaluate a Wasm configuration using the interpreter configuration. *)
val eval_wasm_cfg: Output.verbosity -> Interpreter.wasm_config_tuple -> eval_cfg_result

(* Given a starting state and a list of imports (store references), instantiating a module.
   Return the interpreter result after running the instantiation instructions. *)
val instantiate: Output.verbosity -> Interpreter.store_record -> Extract.module0 -> (Interpreter.externval list) -> eval_cfg_result Host.host_event

(** Given a verbosity level, a boolean stating whether the program should crash if the interpreted
   code does, a configuration tuple, a function name, interpret the Wasm function. *)
val invocation_interpret : Output.verbosity -> bool -> (Interpreter.store_record * Extract.frame) -> Extract.value0 list -> string -> unit Host.host_event

(** Given a verbosity level, a boolean stating whether interactive mode is enable, another boolan
   stating whether the program should crash if the interpreted code does, a module, a function name,
   instantiate, then interpret a parsed Wasm module. *)
val instantiate_interpret : Output.verbosity -> bool -> Extract.module0 -> Extract.value0 list -> string -> unit Host.host_event

