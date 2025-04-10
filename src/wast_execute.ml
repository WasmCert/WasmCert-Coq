(** Execution of Wast testing script **)

open Execute.Host
open Execute.Interpreter

let run_wast_command verbosity cmd hs s =
  let open Wasm.Script in
  let open Wasm.Source in
  match cmd.it with
  | Module (_ovar, moddef) -> 
    begin match moddef.it with 
    | Textual ast_module ->
      let bin_module = Wasm.Encode.encode ast_module in
      let* m = Parse.parse_module verbosity false bin_module in
      let* (hs', s') = Execute.instantiate_modules verbosity hs s [""] [m] in
      pure (hs', s')
    | _ -> error "Unsupported module encoding"
    end
  | _ -> error "Unsupported wast command"
    

let rec run_wast_commands verbosity cmds hs s =
  match cmds with
  | [] -> Printf.printf "Execution finished.\n"; pure ()
  | cmd :: cmds' ->
    let* (hs', s') = run_wast_command verbosity cmd hs s in
    run_wast_commands verbosity cmds' hs' s'

let run_wast_script verbosity script =
  let starting_host_store = Execute.StringMap.empty in
  let starting_store = empty_store_record in
  run_wast_commands verbosity script starting_host_store starting_store

let run_wast_string verbosity scriptstr = 
  let script = Parse.parse_wast scriptstr in
  run_wast_script verbosity script

