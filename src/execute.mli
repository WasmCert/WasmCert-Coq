(** Functions to execute the definitions of the [Shim] module. *)

(** A host implementation. *)
module Host : Shim.Host

module Interpreter : Shim.InterpreterType with module Host = Host

(** The output associated with the functions of this module. *)
type 'a out =
  | OK of 'a
  | Error of string

(** Read-eval-print-loop. *)
val repl : ((Interpreter.store_record * Extract.instance) * Extract.module_export list) -> string -> int -> unit out Interpreter.host_event

