(** Execution of Wast testing script **)

open Execute
open Execute.Host
open Execute.Interpreter
open Output

open Wasm.Source
open Wasm.Values
open Wasm.Script

exception Timeout

let with_timeout timeout f =
  let _ =
    Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Timeout))
  in
  ignore (Unix.alarm timeout);
  try
    let r = f () in
    ignore (Unix.alarm 0); r
  with
  | e -> ignore (Unix.alarm 0); raise e

let ovar_to_name default hs ovar = 
  match ovar with
  | Some v -> 
    let (_, varmap) = hs in
    begin match StringMap.find_opt v.it varmap with
    | Some s -> pure s
    | None -> error ("Invalid module variable name: " ^ v.it)
    end
  | None -> pure default

let wasm_num_to_hexstring num = 
  (* This somehow doesn't include the type signature. *)
  let val_string = hex_string_of_num num in
  (*Printf.printf "%s\n" val_string;*)
    Wasm.Types.string_of_num_type (type_of_num num) ^ ".const " ^ val_string

let wasm_ref_to_string = function
  | NullRef t -> "ref.null " ^ Wasm.Types.string_of_refed_type t
  | ExternRef n -> "ref.extern " ^ Wasm.I32.to_string_u n
  | _ -> assert false

let wasm_val_to_string wval = 
  match wval.it with
  | Num num -> Some (wasm_num_to_hexstring num)
  | Ref ref -> Some (wasm_ref_to_string ref)
  | _-> Some (string_of_value wval.it)
(*
let wasm_vals_to_string wvals = 
  String.concat "" (List.filter_map (function | Some x -> Some x | _ -> None) (List.map wasm_val_to_string wvals))
*)

let wasm_numpat_to_string numpat =
  match numpat with
  | NumPat num -> wasm_num_to_hexstring num.it
  | NanPat _nanop -> "Nan"

let wasm_refpat_to_string refpat = 
  match refpat with
  | RefPat ref -> string_of_ref ref.it
  | _ -> "Unsupported refpat printout"

let wasm_result_to_string ret = 
  match ret.it with
  | NumResult numpat -> wasm_numpat_to_string numpat
  | RefResult refpat -> wasm_refpat_to_string refpat
  | _ -> "Unsupported result type: vec"

let wasm_results_to_string rets = 
  String.concat "; " (List.map wasm_result_to_string rets)

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

let wasm_assert_refpat ret refpat =
  match refpat with
  | RefPat r -> (wasm_val_to_coq ((Ref r.it) @@ no_region) = Some ret)
  | RefTypePat Wasm.Types.FuncRefType -> Extract.Wast_interface.is_funcref ret
  | RefTypePat Wasm.Types.ExternRefType -> Extract.Wast_interface.is_externref ret

let wasm_assert_ret ret ret_exp = 
  match ret_exp.it with
  | NumResult numpat -> wasm_assert_numpat ret numpat
  | RefResult refpat -> wasm_assert_refpat ret refpat
  | _ -> false

let wasm_assert_rets rets ret_exps = 
  let assert_results = List.map2 wasm_assert_ret rets ret_exps in
  List.fold_left (fun a b -> a && b) true assert_results

let load_wast_module verbosity hs s ovar moddef mod_counter =
  begin try
  match moddef.it with 
  | Textual ast_module ->
    let bin_module = Wasm.Encode.encode ast_module in
    let* m = Parse.parse_module verbosity false bin_module in
    let modname = "default_module_" ^ (string_of_int mod_counter) in
    let* varname = begin match ovar with
    | Some v -> 
      let (_, varmap) = hs in
      begin match StringMap.find_opt v.it varmap with
      | Some _ -> error ("Module variable name " ^ v.it ^ " already exists")
      | None -> pure v.it
      end
    | None -> pure ""
    end in
    let* (hs', s') = Execute.instantiate_modules verbosity hs s [modname] [m] in
    debug_info verbosity stage (fun _ -> "Successfully instantiated module " ^ modname ^ ".\n");
    if varname != "" then
      let (exts, varmap) = hs' in
      let varmap' = StringMap.add varname modname varmap in
        debug_info verbosity stage (fun _ -> "Module registered to module variable " ^ varname ^ ".\n");
        pure ((exts, varmap'), s', mod_counter+1, modname)
    else 
      pure (hs', s', mod_counter+1, modname)
  | Encoded (modnamestr, bin_module) -> 
    let* m = Parse.parse_module verbosity false bin_module in
    let modname = if modnamestr = "" then ("default_module_" ^ (string_of_int mod_counter)) else modnamestr in
    let* (hs', s') = Execute.instantiate_modules verbosity hs s [modname] [m] in
      debug_info verbosity stage (fun _ -> "Successfully instantiated module " ^ modname ^ ".\n");
      pure (hs', s', mod_counter+1, modname)
  | Quoted (modnamestr, text_module) -> 
    let* m = Parse.parse_module verbosity true text_module in
    let modname = if modnamestr = "" then ("default_module_" ^ (string_of_int mod_counter)) else modnamestr in
    let* (hs', s') = Execute.instantiate_modules verbosity hs s [modname] [m] in
      debug_info verbosity stage (fun _ -> "Successfully instantiated module " ^ modname ^ ".\n");
      pure (hs', s', mod_counter+1, modname)
  with
  | _ -> error "Exception raised in loading module"
  end

let print_wast_command cmd = 
  let cmd_sexpr = Wasm.Arrange.script `Textual [cmd] in
  let cmd_string = String.concat "" (List.map (Wasm.Sexpr.to_string 200) cmd_sexpr) in
  cmd_string

let wasm_name_to_raw_string n = 
  Wasm.Utf8.encode n

let run_invoke verbosity act_invoke hs s default_module_name fuel = 
  match act_invoke with
  | (ovar, funcname_utf8, val_args) ->
    let* modname = ovar_to_name default_module_name hs ovar in
    let funcname = wasm_name_to_raw_string funcname_utf8 in 
    let* args = wasm_vals_to_coq val_args in
    let* res = invoke_func verbosity hs (s, Extract.empty_frame) args modname funcname fuel in 
      debug_info verbosity stage (fun _ -> "Successfully executed function " ^ funcname ^ " of module: " ^ modname ^ ".\n");
      pure res

let run_get verbosity act_get hs s default_module_name = 
  match act_get with
  | (ovar, extname_utf8) ->
    let* modname = ovar_to_name default_module_name hs ovar in
    let extname = wasm_name_to_raw_string extname_utf8 in
      global_get verbosity hs s modname extname

let run_wast_command verbosity timeout fuel cmd hs s mod_counter default_module_name test_counter =
  debug_info verbosity stage 
  (fun _ -> 
    "\n\n----------\nTest " ^ string_of_int test_counter ^ "\n----------\n" ^ print_wast_command cmd ^ "\n"
    );
 begin try
  begin match cmd.it with
  | Module (ovar, moddef) -> 
    let* (hs', s', modc, defname) = load_wast_module verbosity hs s ovar moddef mod_counter in
    pure (hs', s', modc, defname)
  | Action act ->
    begin match act.it with
    | Invoke (ovar, funcname_utf8, val_args) ->
      let* res = run_invoke verbosity (ovar, funcname_utf8, val_args) hs s default_module_name fuel in 
      begin match res with
      | Cfg_err -> error "Invocation error"
      | Cfg_trap _ -> error "Unexpecte trap"
      | Cfg_res (s', _, _) ->
        pure (hs, s', mod_counter, default_module_name)
      | Cfg_exhaustion -> error "Unexpected exhaustion"
      end
    | Get (ovar, extname_utf8) ->
        let* _ = run_get verbosity (ovar, extname_utf8) hs s default_module_name in
        debug_info verbosity stage (fun _ -> "Test passed: successfully retrieved the value " ^ wasm_name_to_raw_string extname_utf8);
        pure (hs, s, mod_counter, default_module_name)
    end
  | Assertion asrt -> 
    begin match asrt.it with 
    | AssertReturn (act, expect_rets) ->
      begin match act.it with
      | Invoke (ovar, funcname_utf8, val_args) ->
        let* res = run_invoke verbosity (ovar, funcname_utf8, val_args) hs s default_module_name fuel in 
        begin match res with
        | Cfg_err -> error "Invocation error"
        | Cfg_exhaustion -> error "Unexpected exhaustion"
        | Cfg_res (s', _, vs) ->
          debug_info verbosity stage (fun _ -> "Returned: ");
          debug_info verbosity stage (fun _ -> Execute.print_invoke_result verbosity res; "");
          debug_info verbosity stage (fun _ -> "Expected: " ^ wasm_results_to_string expect_rets ^ "\n");
          let assert_result = wasm_assert_rets vs expect_rets in
            if assert_result then
              (debug_info verbosity stage (fun _ -> "Test passed: result matches asserted value\n");
              pure (hs, s', mod_counter, default_module_name))
            else 
              error "Result mismatches"
        | Cfg_trap _ -> 
              error "Unexpected trap"
        end
      | Get (ovar, extname_utf8) ->
        let* res_v = run_get verbosity (ovar, extname_utf8) hs s default_module_name in
        let assert_result = wasm_assert_rets [res_v] expect_rets in
          if assert_result then
            (debug_info verbosity stage (fun _ -> "Test passed: result matches asserted value\n");
              pure (hs, s, mod_counter, default_module_name))
          else
            error "Result mismatches"
      end
    | AssertTrap (act, _) ->
      begin match act.it with
      | Invoke (ovar, funcname_utf8, val_args) ->
        let* res = run_invoke verbosity (ovar, funcname_utf8, val_args) hs s default_module_name fuel in
        begin match res with
        | Cfg_err -> error "Invocation error"
        | Cfg_exhaustion -> error "Unexpected exhaustion when trap is expected"
        | Cfg_res _ ->
          error "Unexpected successful execution when trap is expected"
        | Cfg_trap (s', _) -> 
          debug_info verbosity stage (fun _ -> "Test passed: execution trapped as expected\n");
          pure (hs, s', mod_counter, default_module_name)
        end
      | Get (_ovar, _funcname) ->
        error "Unsupported wast action: Get"
      end
    | AssertExhaustion (act, _) ->
      begin match act.it with
      | Invoke (ovar, funcname_utf8, val_args) ->
        let* res = try 
        (with_timeout (timeout - 1) (fun _ -> run_invoke verbosity (ovar, funcname_utf8, val_args) hs s default_module_name fuel)) 
      with | Timeout ->
        debug_info verbosity stage (fun _ -> "An assert_exhaustion assertion was halted due to timing out\n");
          pure Cfg_exhaustion
      in
        begin match res with
        | Cfg_err -> error "Invocation error"
        | Cfg_res _ ->
          error "Unexpected successful execution when exhaustion is expected"
        | Cfg_trap _ -> 
          error "Unexpected trap when exhaustion is expected"
        | Cfg_exhaustion ->
          debug_info verbosity stage (fun _ -> "Test passed: correctly exhausted\n");
          pure (hs, s, mod_counter, default_module_name)
        end
      | Get (_ovar, _funcname) ->
        error "Unsupported wast action: Get"
      end
    | AssertInvalid (moddef, _str) ->
      (* very ugly... *)
      let res = (load_wast_module verbosity hs s None moddef mod_counter) in
      begin match to_out res with
      | OK _ -> 
        error "Unexpected successful instantiation of an invalid module"
      | Error _ -> 
        debug_info verbosity stage (fun _ -> "Test passed: correctly rejected an invalid module\n");
        pure (hs, s, mod_counter, default_module_name)
      end
    (* The following three assertiosn are grouped into one *)
    | AssertMalformed (moddef, _str)
    | AssertUnlinkable (moddef, _str)
    | AssertUninstantiable (moddef, _str) ->
      let res = (load_wast_module verbosity hs s None moddef mod_counter) in
      begin match to_out res with
      | OK _ -> 
        error "Unexpected successful instantiation of a malformed module"
      | Error _ -> 
        debug_info verbosity stage (fun _ -> "Test passed: correctly rejected a malformed module\n");
        pure (hs, s, mod_counter, default_module_name)
      end
    end
  | Register (newname_utf8, ovar) ->
    let newname = wasm_name_to_raw_string newname_utf8 in
    let (exts, varmap) = hs in
    (* Updating the varmap, if a varname is specified. Also retrieving the module name in the export store to be updated later *)
    let* (oldname, varmap') = begin match ovar with
    | Some v -> 
      let varname = v.it in
      begin match StringMap.find_opt varname varmap with
      | Some oldname ->
        (* Updating the module varmap *)
        pure (oldname, StringMap.add varname newname varmap)
      | None -> error ("Nonexistent module variable " ^ varname ^ " to be registered")
      end
    | None -> 
      (* No varname is specified; registering the default module. The varmap does not need to be updated *)
      pure (default_module_name, varmap)
    end in
    (* Updating the module exports map *)
    let exts' = begin match StringMap.find_opt oldname exts with 
    | Some modmap -> exts |> StringMap.remove oldname |> StringMap.add newname modmap
    | None -> 
      (* This must mean that whatever module being registered has no export, so the registration is technically redundant. *)
      debug_info verbosity intermediate (fun _ -> "Warning: potential redundant registration since no export is found\n");
      exts
    end in
      debug_info verbosity stage (fun _ -> "Test passed: successfully registered module previously named " ^ oldname ^ " with new name: " ^ newname ^ "\n");
      pure ((exts', varmap'), s, mod_counter, newname)
  | _ -> error "Unsupported wast command"
  end
  with 
  | _ -> error "Unknown exception"
end
    

let rec run_wast_commands verbosity timeout fuel cmds hs s mod_counter default_module_name assert_ok assert_total =
  match cmds with
  | [] -> 
    pure (assert_ok, assert_total)
  | cmd :: cmds' ->
      let verdict = 
        try
          (with_timeout timeout (fun _ -> run_wast_command verbosity timeout fuel cmd hs s mod_counter default_module_name (assert_total+1))) with
          | Timeout -> error "Execution was timed out"
         in
        begin match to_out verdict with
        | OK eve -> 
          let* (hs', s', mod_counter', default_module_name') = eve in
          let new_ok = assert_ok + 1 in
          let new_total = assert_total + 1 in
            Printf.printf "\rTests passed: %d/%d (%.2f%%) " new_ok new_total (float_of_int new_ok *. 100.0 /. float_of_int new_total);
            flush stdout;
            run_wast_commands verbosity timeout fuel cmds' hs' s' mod_counter' default_module_name' new_ok new_total
        | Error msg ->
            debug_info verbosity stage ~style:red (fun _ -> "Test failed: " ^ msg ^ "\n");
            let new_ok = assert_ok in
            let new_total = assert_total + 1 in
            Printf.printf "\rTests passed: %d/%d (%.2f%%) " new_ok new_total (float_of_int new_ok *. 100.0 /. float_of_int new_total);
            flush stdout;
            run_wast_commands verbosity timeout fuel cmds' hs s mod_counter default_module_name new_ok new_total
          end
      


let spectest_host_str = 
  "(module
  (global (export \"global_i32\") i32 (i32.const 666))      ;; value 666
  (global (export \"global_i64\") i64 (i64.const 666))      ;; value 666
  (global (export \"global_f32\") f32 (f32.const 666.6))      ;; value 666.6
  (global (export \"global_f64\") f64 (f64.const 666.6))      ;; value 666.6

  (table (export \"table\") 10 20 funcref)  ;; null-initialized

  (memory (export \"memory\") 1 2)          ;; zero-initialized

  (func (export \"print\"))
  (func (export \"print_i32\") (param i32))
  (func (export \"print_i64\") (param i64))
  (func (export \"print_f32\") (param f32))
  (func (export \"print_f64\") (param f64))
  (func (export \"print_i32_f32\") (param i32 f32))
  (func (export \"print_f64_f64\") (param f64 f64))
)"

let register_spectest_host verbosity hs s = 
  let* m = Parse.parse_module verbosity true spectest_host_str in
  let modname = "spectest" in
  let* (hs', s') = Execute.instantiate_modules verbosity hs s [modname] [m] in
    debug_info verbosity stage (fun _ -> "Successfully instantiated module " ^ modname ^ ".\n");
    pure (hs', s')

let run_wast_script verbosity timeout fuel script =
  let starting_host_store = (Execute.StringMap.empty, Execute.StringMap.empty) in
  let starting_store = empty_store_record in
  let* (hs, s) = register_spectest_host verbosity starting_host_store starting_store in
  let* ret = run_wast_commands verbosity timeout fuel script hs s 0 "" 0 0 in
  match ret with
    | (assert_ok, assert_total) -> 
      debug_info verbosity result (fun _ -> "\n");
      let color = if (assert_ok = assert_total) then Output.green else Output.red in
        debug_info verbosity result ~style:color (fun _ -> Printf.sprintf "Result: %d/%d (%.2f%%)\n" assert_ok assert_total (float_of_int assert_ok *. 100.0 /. float_of_int assert_total));
      pure ()
    

let run_wast_string verbosity timeout fuel scriptstr = 
  let script = Parse.parse_wast scriptstr in
  run_wast_script verbosity timeout fuel script


  