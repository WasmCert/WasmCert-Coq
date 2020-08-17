(** Functions to execute the definitions of the [Shim] module. *)

(** A host implementation. *)
module Host : Shim.Host

module Interpreter : Shim.InterpreterType with module Host = Host

(* TODO: This file really should deal with the execution of the interpreter in a monad that can
   perform side effects, and thus incorporate most of [Wasm_interpreter.interpret]. *)

(** Read-eval-print-loop. *)
val repl : ((Interpreter.store_record * Extract.instance) * Extract.module_export list) -> string -> int -> [> `Ok of unit] Interpreter.host_event

