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
  end

module Interpreter : Shim.InterpreterType with type 'a Host.host_event = 'a Host.host_event

(** Read-eval-print-loop. *)
val repl : (Interpreter.store_record * Extract.instance) * Extract.module_export list -> string -> int -> unit Host.host_event

(* TODO
(** Given a verbosity level, a boolean stating whether the program should crash if the interpreted
   code does, a configuration tuple, a function name, and a depth, interpret the Wasm function. *)
val interpret : Output.verbosity -> bool -> (store_record * Extract.instance) * Extract.module_export list -> string -> int -> unit Host.host_event
*)

