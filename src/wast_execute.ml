(** Execution of Wast testing script **)

open Execute.Host
open Execute.Interpreter
open Output

let ovar_to_name default ovar = 
  let open Wasm.Source in 
  match ovar with
  | Some v -> v.it
  | None -> default

(* Some stupid hacks here *)
let wasm_val_to_coq wval = 
  let open Wasm.Source in
  match wval.it with
  | Wasm.Values.Num num ->
    let val_sexpr = Wasm.Arrange.instr (Wasm.Ast.Const (num @@ no_region) @@ no_region) in
    let val_string = Wasm.Sexpr.to_string 1000 val_sexpr in
    let val_string_fixed = String.sub val_string 1 (String.length val_string - 3) in
      (*Printf.printf "%s" val_string_fixed;*)
      Parse.parse_arg val_string_fixed
  | _ -> None

let rec wasm_vals_to_coq_aux args acc = 
  (match args with
  | [] -> pure acc
  | a :: args' -> 
    (match wasm_val_to_coq a with
    | Some a' -> wasm_vals_to_coq_aux args' (acc @ [a'])
    | None -> Execute.Host.from_out (Error ("Invalid argument in Wast script"))
    )
  )

let wasm_vals_to_coq args = 
  wasm_vals_to_coq_aux args []

let run_wast_command verbosity cmd hs s mod_counter default_module_name =
  let open Wasm.Script in
  let open Wasm.Source in
  match cmd.it with
  | Module (ovar, moddef) -> 
    begin match moddef.it with 
    | Textual ast_module ->
      let bin_module = Wasm.Encode.encode ast_module in
      let* m = Parse.parse_module verbosity false bin_module in
      let modname = ovar_to_name ("default_module_" ^ (string_of_int mod_counter)) ovar in
      let* (hs', s') = Execute.instantiate_modules verbosity hs s [modname] [m] in
        debug_info verbosity result (fun _ -> "Successfully instantiated module " ^ modname ^ ".\n");
        pure (hs', s', mod_counter+1, modname)
    | _ -> error "Unsupported module encoding"
    end
  | Assertion asrt -> 
    begin match asrt.it with 
    | AssertReturn (act, expect_rets) ->
      begin match act.it with
      | Invoke (ovar, funcname_utf8, val_args) ->
        let modname = ovar_to_name default_module_name ovar in
        let funcname = Wasm.Ast.string_of_name funcname_utf8 in 
        let* args = wasm_vals_to_coq val_args in
        let* (s', _vs) = Execute.invoke_func verbosity hs (s, Extract.empty_frame) args modname funcname in 
          debug_info verbosity result (fun _ -> "Successfully executed function " ^ funcname ^ " of module: " ^ modname ^ ".\n");
          pure (hs, s', mod_counter, default_module_name)
      | Get (_ovar, _funcname) ->
        error "Unsupported wast action: Get"
      end
    | _ -> error "Unsupported wast assertion"
    end
  | _ -> error "Unsupported wast command"
    

let rec run_wast_commands verbosity cmds hs s mod_counter default_module_name =
  match cmds with
  | [] -> 
    debug_info verbosity result (fun _ -> "Execution finished.\n"); 
    pure ()
  | cmd :: cmds' ->
    let* (hs', s', mod_counter', default_module_name') = run_wast_command verbosity cmd hs s mod_counter default_module_name in
    run_wast_commands verbosity cmds' hs' s' mod_counter' default_module_name'

let run_wast_script verbosity script =
  let starting_host_store = Execute.StringMap.empty in
  let starting_store = empty_store_record in
  run_wast_commands verbosity script starting_host_store starting_store 0 ""

let run_wast_string verbosity scriptstr = 
  let script = Parse.parse_wast scriptstr in
  run_wast_script verbosity script

