(** Parsing **)

(** Trying to guess the module name by the file name provided for the module. *)
val extract_module_name: string -> string

(* Convert a Wasm text module into the binary format. *)
val binary_of_text: string -> string option

(** Parse a module given the module string. The text flag specifies whether the argument is in binary format or text format. *)
val parse_module: Output.verbosity -> bool -> string -> Extract.module0 Execute.Host.host_event

(* Parse a list of modules. *)
val parse_modules: Output.verbosity -> bool -> string list -> (Extract.module0 list) Execute.Host.host_event

(* Parsing the arguments of a function call in text format. *)
val parse_arg: string -> (Execute.Interpreter.value) option

val parse_args: string list -> (Execute.Interpreter.value list) Execute.Host.host_event

(* Parsing a wast script. *)
val parse_wast: string -> Wasm.Script.script