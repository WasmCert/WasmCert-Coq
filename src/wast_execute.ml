(** Execution of Wast testing script **)

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

let ovar_to_name default ovar = 
  let open Wasm.Source in 
  match ovar with
  | Some v -> v.it
  | None -> default

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
  match moddef.it with 
  | Textual ast_module ->
    let bin_module = Wasm.Encode.encode ast_module in
    let* m = Parse.parse_module verbosity false bin_module in
    let modname = ovar_to_name ("default_module_" ^ (string_of_int mod_counter)) ovar in
    let* (hs', s') = Execute.instantiate_modules verbosity hs s [modname] [m] in
      debug_info verbosity stage (fun _ -> "Successfully instantiated module " ^ modname ^ ".\n");
      pure (hs', s', mod_counter+1, modname)
  | Encoded (modnamestr, bin_module) -> 
    let* m = Parse.parse_module verbosity false bin_module in
    let modname = if modnamestr = "" then ("default_module_" ^ (string_of_int mod_counter)) else modnamestr in
    let* (hs', s') = Execute.instantiate_modules verbosity hs s [modname] [m] in
      debug_info verbosity stage (fun _ -> "Successfully instantiated module " ^ modname ^ ".\n");
      pure (hs', s', mod_counter+1, modname)
  | Quoted _ -> error "Unsupported module encoding: Quoted"

let print_wast_command cmd = 
  let cmd_sexpr = Wasm.Arrange.script `Textual [cmd] in
  let cmd_string = String.concat "" (List.map (Wasm.Sexpr.to_string 200) cmd_sexpr) in
  cmd_string

let run_wast_command verbosity cmd hs s mod_counter default_module_name test_counter =
  debug_info verbosity stage 
  (fun _ -> 
    "\n\n----------\nTest " ^ string_of_int test_counter ^ "\n----------\n" ^ print_wast_command cmd ^ "\n"
    );
  begin try
  begin match cmd.it with
  | Module (ovar, moddef) -> 
    let* (hs', s', modc, defname) = load_wast_module verbosity hs s ovar moddef mod_counter in
    pure (hs', s', modc, defname)
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
              pure (hs, s', mod_counter, default_module_name))
            else 
              error "result mismatches"
        | Cfg_trap _ -> 
              error "unexpected trap"
        end
      | Get (_ovar, _funcname) ->
        error "Unsupported wast action: Get"
      end
    | AssertTrap (act, _) ->
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
        | Cfg_res _ ->
          error "Unexpected successful execution when trap is expected"
        | Cfg_trap (s', _) -> 
          debug_info verbosity stage (fun _ -> "Test passed: execution trapped as expected\n");
          pure (hs, s', mod_counter, default_module_name)
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
    | AssertMalformed (moddef, _str) ->
      let res = (load_wast_module verbosity hs s None moddef mod_counter) in
      begin match to_out res with
      | OK _ -> 
        error "Unexpected successful instantiation of a malformed module"
      | Error _ -> 
        debug_info verbosity stage (fun _ -> "Test passed: correctly rejected a malformed module\n");
        pure (hs, s, mod_counter, default_module_name)
      end
    | _ -> error "Unsupported wast assertion"
    end
  | _ -> error "Unsupported wast command"
  end
  with 
  | _ -> error "Unknown exception"
end
    

let rec run_wast_commands verbosity timeout cmds hs s mod_counter default_module_name assert_ok assert_total =
  match cmds with
  | [] -> 
    pure (assert_ok, assert_total)
  | cmd :: cmds' ->
      let verdict = 
        try
          (with_timeout timeout (fun _ -> run_wast_command verbosity cmd hs s mod_counter default_module_name (assert_total+1))) with
          | Timeout -> error "Execution was timed out"
         in
        begin match to_out verdict with
        | OK eve -> 
          let* (hs', s', mod_counter', default_module_name') = eve in
          let new_ok = assert_ok + 1 in
          let new_total = assert_total + 1 in
            Printf.printf "\rTests passed: %d/%d (%.2f%%) " new_ok new_total (float_of_int new_ok *. 100.0 /. float_of_int new_total);
            flush stdout;
            run_wast_commands verbosity timeout cmds' hs' s' mod_counter' default_module_name' new_ok new_total
        | Error msg ->
            debug_info verbosity stage ~style:red (fun _ -> "Test failed: " ^ msg ^ "\n");
            let new_ok = assert_ok in
            let new_total = assert_total + 1 in
            Printf.printf "\rTests passed: %d/%d (%.2f%%) " new_ok new_total (float_of_int new_ok *. 100.0 /. float_of_int new_total);
            flush stdout;
            run_wast_commands verbosity timeout cmds' hs s mod_counter default_module_name new_ok new_total
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

let run_wast_script verbosity timeout script =
  let starting_host_store = Execute.StringMap.empty in
  let starting_store = empty_store_record in
  let* (hs, s) = register_spectest_host verbosity starting_host_store starting_store in
  let* ret = run_wast_commands verbosity timeout script hs s 0 "" 0 0 in
  match ret with
    | (assert_ok, assert_total) -> 
      debug_info verbosity result (fun _ -> "\n");
      let color = if (assert_ok = assert_total) then Output.green else Output.red in
        debug_info verbosity result ~style:color (fun _ -> Printf.sprintf "Result: %d/%d (%.2f%%)\n" assert_ok assert_total (float_of_int assert_ok *. 100.0 /. float_of_int assert_total));
      pure ()
    

let run_wast_string verbosity timeout scriptstr = 
  let script = Parse.parse_wast scriptstr in
  run_wast_script verbosity timeout script


  