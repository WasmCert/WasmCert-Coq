(** Parsing **)
open Execute.Interpreter
open Output

(** Trying to guess the module name by the file name provided for the module. *)
let extract_module_name src =
  let name = Filename.basename src in
  if (String.length name >= 5 && String.sub name (String.length name - 5) 5 = ".wasm") then
      String.sub name 0 (String.length name - 5)
  else 
    if (String.length name >= 4 && String.sub name (String.length name - 4) 4 = ".wat") then
      String.sub name 0 (String.length name - 4)
    else
      name

let binary_of_text textstr =
  let open Wasm.Source in
  let (_ovar, wast_def) = Wasm.Parse.Module.parse_string textstr in
  match wast_def.it with
  | Wasm.Script.Textual wast_module -> 
      let bin_module = Wasm.Encode.encode wast_module in
      Some bin_module
  | _ -> None

let parse_binary_module bin_module = 
  match Execute.Interpreter.run_parse_module bin_module with
  | None -> Error "error in parsing module"
  | Some m -> OK m

(** Parse a module given the module string. The text flag specifies whether the argument is in binary format or text format. *)
let parse_module verbosity text mstr =
  (** Parsing. *)
  Execute.Host.from_out (
    let open Output in
    ovpending verbosity stage "parsing" (fun _ ->
      if text then
        match binary_of_text mstr with
        | Some bin_module -> parse_binary_module bin_module
        | None -> Error "error in parsing the text module"
        else
          parse_binary_module mstr
    ))

(* Parse a list of modules. *)
let rec parse_modules_acc verbosity text files acc =
  match files with
  | [] -> pure acc
  | f :: files' ->
    let* m = parse_module verbosity text f in
    parse_modules_acc verbosity text files' (acc @ [m])

let parse_modules verbosity text files =
  parse_modules_acc verbosity text files []

let parse_arg arg = 
  Execute.Interpreter.run_parse_arg arg

(* Parsing the arguments of a function call in text format. *)
let rec parse_args_acc args acc = 
  (match args with
  | [] -> pure acc
  | a :: args' -> 
    (match parse_arg a with
    | Some a' -> parse_args_acc args' (acc @ [a'])
    | None -> Execute.Host.from_out (Error ("Invalid argument: " ^ a))
    )
  )
 
let parse_args args = 
  parse_args_acc args []

let parse_wast scriptstr = 
  Wasm.Parse.Script.parse_string scriptstr