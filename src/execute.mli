
(** A host implementation. *)
module Host : Extract.Executable_Host

module Interpreter : Shim.InterpreterType with module Host = Host

(* TODO: This file really should deal with the execution of the interpreter in a monad that can
   perform side effects, and thus incorporate most of [Wasm_interpreter.interpret]. *)

(** Read-eval-print-loop. *)
val repl : ((Extract.Equality.sort Extract.store_record * Extract.instance) * Extract.module_export list) -> string -> int -> [> `Ok of unit]


