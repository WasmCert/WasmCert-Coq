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

(** Read-eval-print-loop. *)
val repl : Output.verbosity -> ((Extract.Equality.sort * Interpreter.store_record) * Extract.instance) * Extract.module_export list -> string -> unit Host.host_event

(** Given a verbosity level, a boolean stating whether the program should crash if the interpreted
   code does, a configuration tuple, a function name, interpret the Wasm function. *)
val interpret : Output.verbosity -> bool -> ((Extract.Equality.sort * Interpreter.store_record) * Extract.instance) * Extract.module_export list -> string -> unit Host.host_event

(** Given a verbosity level, a boolean stating whether interactive mode is enable, another boolan
   stating whether the program should crash if the interpreted code does, a module, a function name,
   instantiate, then interpret a parsed Wasm module. *)
val instantiate_interpret : Output.verbosity -> bool -> bool -> Extract.module0 -> string -> unit Host.host_event

