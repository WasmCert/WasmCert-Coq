(** Execution of Wast testing script **)

open Execute.Host
open Execute.Interpreter
open Output

open Wasm.Source
open Wasm.Values
open Wasm.Script

let ovar_to_name default ovar = 
  let open Wasm.Source in 
  match ovar with
  | Some v -> v.it
  | None -> default

let wasm_num_to_hexstring num = 
  let open Wasm.Source in
  (* This somehow doesn't include the type signature. *)
  let val_string = Wasm.Values.hex_string_of_num num in
  (*Printf.printf "%s\n" val_string;*)
    Wasm.Types.string_of_num_type (Wasm.Values.type_of_num num) ^ ".const " ^ val_string


let wasm_val_to_string wval = 
  let open Wasm.Source in
  match wval.it with
  | Wasm.Values.Num num -> Some (wasm_num_to_hexstring num)
  | _ -> None
(*
let wasm_vals_to_string wvals = 
  String.concat "" (List.filter_map (function | Some x -> Some x | _ -> None) (List.map wasm_val_to_string wvals))
*)

let wasm_numpat_to_string numpat =
  let open Wasm.Script in
  match numpat with
  | NumPat num -> wasm_num_to_hexstring num.it
  | NanPat _nanop -> "Nan"

let wasm_result_to_string ret = 
  let open Wasm.Script in
  let open Wasm.Source in
  match ret.it with
  | NumResult numpat -> wasm_numpat_to_string numpat
  | _ -> "Unsupported result type: vec/ref"

let wasm_results_to_string rets = 
  String.concat "; " (List.map wasm_result_to_string rets)


(* Some stupid hacks here -- does this lose precision for floats? *)
let wasm_val_to_coq wval = 
  match wasm_val_to_string wval with
  | Some valstr -> Parse.parse_arg valstr
  | None -> None

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

let wasm_num_to_coq wnum = 
    wasm_val_to_coq ((Num wnum) @@ no_region)

let wasm_assert_nanpat ret nanop =
  match nanop.it with
  | F32 CanonicalNan -> Extract.Wast_interface.is_canonical_nan Extract.T_f32 ret
  | F64 CanonicalNan -> Extract.Wast_interface.is_canonical_nan Extract.T_f64 ret
  | F32 ArithmeticNan -> Extract.Wast_interface.is_arithmetic_nan Extract.T_f32 ret
  | F64 ArithmeticNan -> Extract.Wast_interface.is_arithmetic_nan Extract.T_f64 ret
  | _ -> false

let wasm_assert_numpat ret numpat = 
  match numpat with
  | NumPat num -> (wasm_num_to_coq num.it = Some ret)
  | NanPat nanop -> wasm_assert_nanpat ret nanop

let wasm_assert_ret ret ret_exp = 
  match ret_exp.it with
  | NumResult numpat -> wasm_assert_numpat ret numpat
  | _ -> false

let wasm_assert_rets rets ret_exps = 
  let assert_results = List.map2 wasm_assert_ret rets ret_exps in
  List.fold_left (fun a b -> a && b) true assert_results

let load_wast_module verbosity hs s ovar moddef mod_counter =
  match moddef.it with 
  | Textual ast_module ->
    let bin_module = Wasm.Encode.encode ast_module in
    let* m = Parse.parse_module verbosity false bin_module in
    let modname = ovar_to_name ("default_module_" ^ (string_of_int mod_counter)) ovar in
    let* (hs', s') = Execute.instantiate_modules verbosity hs s [modname] [m] in
      debug_info verbosity stage (fun _ -> "Successfully instantiated module " ^ modname ^ ".\n");
      pure (hs', s', mod_counter+1, modname)
  | _ -> error "Unsupported module encoding"

let run_wast_command verbosity cmd hs s mod_counter default_module_name =
  let open Wasm.Script in
  let open Wasm.Source in
  match cmd.it with
  | Module (ovar, moddef) -> 
    let* (hs', s', modc, defname) = load_wast_module verbosity hs s ovar moddef mod_counter in
    pure (hs', s', modc, defname, true)
  | Assertion asrt -> 
    begin match asrt.it with 
    | AssertReturn (act, expect_rets) ->
      begin match act.it with
      | Invoke (ovar, funcname_utf8, val_args) ->
        let open Execute in
        let modname = ovar_to_name default_module_name ovar in
        let funcname = Wasm.Ast.string_of_name funcname_utf8 in 
        let* args = wasm_vals_to_coq val_args in
        (*Printf.printf "%s" (Utils.implode (Extract.PP.pp_values args));*)
        let* res = invoke_func verbosity hs (s, Extract.empty_frame) args modname funcname in 
        begin match res with
        | Cfg_err -> error "Invocation error"
        | Cfg_res (s', _, vs) ->
          debug_info verbosity stage (fun _ -> "Successfully executed function " ^ funcname ^ " of module: " ^ modname ^ ".\n");
          debug_info verbosity stage (fun _ -> "Returned: ");
          debug_info verbosity stage (fun _ -> print_invoke_result verbosity res; "");
          debug_info verbosity stage (fun _ -> "Expected: " ^ wasm_results_to_string expect_rets ^ "\n");
          let assert_result = wasm_assert_rets vs expect_rets in
            if assert_result then
              (debug_info verbosity stage (fun _ -> "Test passed: result matches asserted value\n");
              pure (hs, s', mod_counter, default_module_name, true))
            else 
              (debug_info verbosity stage (fun _ -> "Test failed: result mismatches\n");
              pure (hs, s', mod_counter, default_module_name, false))
        | Cfg_trap (s', _) -> 
          debug_info verbosity stage (fun _ -> "Test failed: unexpected trap\n");
          pure (hs, s', mod_counter, default_module_name, false)
        end
      | Get (_ovar, _funcname) ->
        debug_info verbosity result (fun _ -> "Unsupported wast action: Get");
        error "Unsupported wast action: Get"
      end
    | AssertInvalid (moddef, _str) ->
      (* very ugly... *)
      let exception Exn in
      let res = (load_wast_module verbosity hs s None moddef mod_counter) in
        begin try (pmatch (fun r -> 
          match r with
          | (hs, s, mod_counter, default_module_name) -> 
            debug_info verbosity stage (fun _ -> "Test failed: an invalid module was successfully instantiated\n");
            (hs, s, mod_counter, default_module_name, false)
          ) 
        (fun _ -> raise Exn) res)
        with Exn -> 
          debug_info verbosity stage (fun _ -> "Test passed: correctly rejected an invalid module\n");
          pure (hs, s, mod_counter, default_module_name, true)
        end
    | AssertMalformed (moddef, _str) ->
      let exception Exn in
      let res = (load_wast_module verbosity hs s None moddef mod_counter) in
        begin try (pmatch (fun r -> 
          match r with
          | (hs, s, mod_counter, default_module_name) -> 
            debug_info verbosity stage (fun _ -> "Test failed: an invalid module was successfully instantiated\n");
            (hs, s, mod_counter, default_module_name, false)
          ) 
        (fun _ -> raise Exn) res)
        with Exn -> 
          debug_info verbosity stage (fun _ -> "Test passed: correctly rejected an invalid module\n");
          pure (hs, s, mod_counter, default_module_name, true)
        end
    | _ -> error "Unsupported wast assertion"
    end
  | _ -> error "Unsupported wast command"
    

let rec run_wast_commands verbosity cmds hs s mod_counter default_module_name assert_ok assert_total =
  match cmds with
  | [] -> 
    pure (assert_ok, assert_total)
  | cmd :: cmds' ->
    let* (hs', s', mod_counter', default_module_name', verdict) = run_wast_command verbosity cmd hs s mod_counter default_module_name in
    let new_ok = assert_ok + if verdict then 1 else 0 in 
    let new_total = assert_total + 1 in
    Printf.printf "\rTests passed: %d/%d (%.2f%%)" new_ok new_total (float_of_int new_ok *. 100.0 /. float_of_int new_total);
    flush stdout;
    run_wast_commands verbosity cmds' hs' s' mod_counter' default_module_name' new_ok new_total

let run_wast_script verbosity script =
  let starting_host_store = Execute.StringMap.empty in
  let starting_store = empty_store_record in
  let* ret = run_wast_commands verbosity script starting_host_store starting_store 0 "" 0 0 in
  match ret with
    | (assert_ok, assert_total) -> 
      debug_info verbosity result (fun _ -> "\n");
      (*debug_info verbosity result (fun _ -> Printf.sprintf "Result: %d/%d (%.2f%%)\n" assert_ok assert_total (float_of_int assert_ok *. 100.0 /. float_of_int assert_total));*)
      pure ()
    

let run_wast_string verbosity scriptstr = 
  let script = Parse.parse_wast scriptstr in
  run_wast_script verbosity script


  