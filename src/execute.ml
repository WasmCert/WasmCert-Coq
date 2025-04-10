
open Output

module Host = struct

    (* We build on top of this host, wrapping it inside the type [out]. *)
    module Host = Shim.DummyHost

    type host_function = Host.host_function
    let host_function_eq_dec = Host.host_function_eq_dec

    type 'a host_event = 'a out Host.host_event
    let host_ret v = Host.host_ret (OK v)
    let host_bind v cont =
      Host.host_bind v (function
        | OK v -> cont v
        | Error msg -> Host.host_ret (Error msg))

    let host_apply st t h vs =
      Host.host_bind (Host.host_apply st t h vs) (fun r -> host_ret r)

    let show_host_function = Host.show_host_function

    let error msg = Host.host_ret (Error msg)

    let pmatch ok error v =
      Host.host_bind v (function
        | OK v -> host_ret (ok v)
        | Error msg -> host_ret (error msg))

    let from_out = function
      | OK v -> host_ret v
      | Error msg -> error msg

    exception ToOut of string

    let to_out v =
      (* FIXME: This is not the nicest code ever. *)
      try OK (pmatch (fun x -> x) (fun msg -> raise (ToOut msg)) v)
      with ToOut msg -> Error msg

  end

module Interpreter = Shim.Interpreter (Host)

(** An alias of [Host] to be able to retrieve it later. *)
module TopHost = Host

open Interpreter

type eval_cfg_result =
  | Cfg_res of store_record * frame * value list
  | Cfg_trap of store_record * frame
  | Cfg_err

let rec eval_interp_cfg verbosity gen cfg =
  let print_step_header gen =
    debug_info verbosity intermediate ~style:bold
      (fun () -> Printf.sprintf "step %d:\n" gen) in
  let cfg_res = run_one_step cfg in
  print_step_header gen;
  debug_info verbosity intermediate
    (fun _ -> pp_res_cfg_except_store cfg cfg_res);
  match cfg_res with
  | RSC_normal (_hs', cfg') ->
    eval_interp_cfg verbosity (gen+1) cfg'
  | RSC_value (s, f, vs) ->
    debug_info verbosity stage ~style:green (fun _ -> "success after " ^ string_of_int gen ^ " steps\n");
    (Cfg_res (s, f, vs))
  | RSC_trap (s, f) ->
    debug_info verbosity stage ~style:red (fun _ -> "trap after " ^ string_of_int gen ^ " steps\n");
    Cfg_trap (s, f)
  | RSC_invalid ->
    debug_info verbosity stage ~style:red (fun _ -> "Invalid cfg\n");
    Cfg_err
  | RSC_error ->
    debug_info verbosity stage ~style:red (fun _ -> "Ill-typed input\n");
    Cfg_err
  
let eval_wasm_cfg verbosity cfg =
  let interp_cfg_inst = interp_cfg_of_wasm cfg in
  debug_info verbosity intermediate (fun _ ->
    Printf.sprintf "\nExecuting configuration:\n%s\n" (pp_cfg_tuple_ctx_except_store interp_cfg_inst));
  eval_interp_cfg verbosity 1 interp_cfg_inst


module StringMap = Map.Make(String);;

type host_extern_store = (Interpreter.externval StringMap.t) StringMap.t

let invoke_func verbosity exts sf args modname name =
  let (s, f) = sf in
  let* es_init =
    TopHost.from_out (
      ovpending verbosity stage "interpreting" (fun _ ->
        if (String.equal name "") then
          Error ("no function name specified")
        else
          begin match StringMap.find_opt modname exts with
          | Some mmap ->
            begin match StringMap.find_opt name mmap with
            | Some extval ->
              begin match invoke_extern s extval args with
              | None -> Error ("Unknown function `" ^ name ^ "`, or invalid argument types")
              | Some es_init -> OK es_init
              end
            | None -> Error "The specified function does not exist"
            end
          | None -> Error "The specified module does not exist"
          end
      )) in
    let cfg_init = (s, (f, es_init)) in
    let res = eval_wasm_cfg verbosity cfg_init in
    debug_info_span verbosity result stage (fun _ ->
      match res with
      | Cfg_res (_, _, vs) -> pp_values vs
      | Cfg_trap (_, _) -> "Execution returned a trap; run the interpreter in detailed mode (--vi) for more information\n"
      | Cfg_err -> "Execution returned an error; run the interpreter in detailed mode (--vi) for more information\n"
    );
    match res with
    | Cfg_res (s, _, _) -> pure s
    | Cfg_trap (s, _) -> pure s
    | Cfg_err -> TopHost.error ""

let instantiate_imps verbosity s m imps =
  let* wasm_cfg =
    TopHost.from_out (
      ovpending verbosity stage "instantiation" (fun _ ->
        match interp_instantiate_wrapper s m imps with
        | None -> Error "instantiation error"
        | Some cfg -> OK cfg)) in
  pure (eval_wasm_cfg verbosity wasm_cfg)

let get_ext_import exts path = 
  let (m, imp_name) = path in
  match StringMap.find_opt m exts with
  | Some imps_map ->
    StringMap.find_opt imp_name imps_map
  | None -> None

let instantiate verbosity exts s m = 
  let import_paths = get_import_path m in
  let oext_vals = List.map (get_ext_import exts) import_paths in
  let ext_vals = List.filter_map (fun x -> x) oext_vals in
  if List.length oext_vals = List.length ext_vals then
    let* inst_res = instantiate_imps verbosity s m ext_vals in
    pure inst_res
  else
    TopHost.error "invalid module imports"

let instantiate_host verbosity exts s module_name m = 
  let* inst_res = instantiate verbosity exts s m in
  (* Add the exported instances to the host store. *)
  match inst_res with
  | Cfg_res (s', f, _vs) -> 
    let exps = get_exports f in
    let exps_str = List.map 
      (fun exp -> 
        match exp with
        | (exp_name, exp_val) -> exp_name ^ " at " ^ pp_externval exp_val ^ ";") exps in
    let exps_map = StringMap.of_seq (List.to_seq exps) in
    let exts'' = StringMap.add module_name exps_map exts in
    debug_info verbosity stage (fun _ -> "Adding the following exports to module " ^ module_name ^ " : " ^ (String.concat "" exps_str) ^ "\n");
    pure (exts'', s')
  (* Trap won't be counted as an irrecoverable error in the host *)
  | Cfg_trap (s', f) -> 
    let exps = get_exports f in
    let exps_map = StringMap.of_seq (List.to_seq exps) in
    let exts'' = StringMap.add module_name exps_map exts in
    pure (exts'', s')
  | Cfg_err -> TopHost.error "invalid module instantiation"

(*
let instantiate_interpret verbosity error_code_on_crash exts s m args name =
  let* sf =
    let* inst_result = instantiate verbosity empty_store_record m [] in
    TopHost.from_out (
      ovpending verbosity stage "instantiation" (fun _ ->
        match inst_result with
        | Cfg_err -> Error "instantiation error"
        | Cfg_trap _ -> Error "instantiation error: initialisers resulted in a trap"
        | Cfg_res (s, f, _vs) -> OK (s, f))
  ) in
    debug_info verbosity intermediate (fun _ -> Printf.sprintf "\nInstantiation success\n");
    invocation_interpret verbosity error_code_on_crash sf args name
*)