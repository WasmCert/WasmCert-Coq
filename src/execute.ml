
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
  | Cfg_exhaustion

let rec eval_interp_cfg verbosity gen fuel cfg =
  let print_step_header gen =
    debug_info verbosity intermediate ~style:bold
      (fun () -> Printf.sprintf "step %d:\n" gen) in
  if (fuel >= 0) && (gen >= fuel) then begin
    debug_info verbosity stage ~style:red (fun _ -> "Fuel exhaustion\n");
    Cfg_exhaustion
  end
  else
    let cfg_res = run_one_step cfg in
      print_step_header gen;
      debug_info verbosity intermediate
        (fun _ -> pp_res_cfg_except_store cfg cfg_res);
      match cfg_res with
      | RSC_normal (_hs', cfg') ->
        eval_interp_cfg verbosity (gen+1) fuel cfg'
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
  
let eval_wasm_cfg verbosity fuel cfg =
  let interp_cfg_inst = interp_cfg_of_wasm cfg in
  debug_info verbosity intermediate (fun _ ->
    Printf.sprintf "\nExecuting configuration:\n%s\n" (pp_cfg_tuple_ctx_except_store interp_cfg_inst));
  eval_interp_cfg verbosity 1 fuel interp_cfg_inst


module StringMap = Map.Make(String);;

type host_extern_store = ((Interpreter.externval StringMap.t) StringMap.t) * (string StringMap.t)

let invoke_func verbosity hs sf args modname name fuel =
  let (exts, _) = hs in
  let (s, f) = sf in
  let* es_init =
    TopHost.from_out (
      ovpending verbosity stage "interpreting" (fun _ ->
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
    pure (eval_wasm_cfg verbosity fuel cfg_init)

let print_invoke_result verbosity res = 
  debug_info verbosity result (fun _ ->
    match res with
    | Cfg_res (_, _, vs) -> pp_values vs
    | Cfg_trap (_, _) -> "Execution returned a trap; run the interpreter in detailed mode (--vi) for more information\n"
    | Cfg_err -> "Execution returned an error; run the interpreter in detailed mode (--vi) for more information\n"
    | Cfg_exhaustion -> "Fuel exhaustion\n"
  )

let instantiate_imps verbosity s m imps =
  let* wasm_cfg =
    TopHost.from_out (
      ovpending verbosity stage "instantiation" (fun _ ->
        match interp_instantiate_wrapper s m imps with
        | (None, errmsg) -> Error ("instantiation error: " ^ errmsg)
        | (Some cfg, _) -> OK cfg)) in
  pure (eval_wasm_cfg verbosity (-1) wasm_cfg)

let get_ext_import hs path = 
  let (m, imp_name) = path in
  let (exts, _) = hs in
  match StringMap.find_opt m exts with
  | Some imps_map ->
    StringMap.find_opt imp_name imps_map
  | None -> None

let instantiate verbosity hs s m = 
  let import_paths = get_import_path m in
  let oext_vals = List.map (get_ext_import hs) import_paths in
  let ext_vals = List.filter_map (fun x -> x) oext_vals in
  if List.length oext_vals = List.length ext_vals then
    let* inst_res = instantiate_imps verbosity s m ext_vals in
    pure inst_res
  else
    TopHost.error "invalid module imports"

let instantiate_host verbosity hs s module_name m = 
  let* inst_res = instantiate verbosity hs s m in
  (* Add the exported instances to the host store. *)
    match inst_res with
    | Cfg_res (s', f, _vs) -> 
      let exps = get_exports f in
      let exps_str = List.map 
        (fun exp -> 
          match exp with
          | (exp_name, exp_val) -> exp_name ^ " at " ^ pp_externval exp_val ^ ";") exps in
      let exps_map = StringMap.of_seq (List.to_seq exps) in
      let (exts, modvarmaps) = hs in
      let exts' = StringMap.add module_name exps_map exts in
      let hs' = (exts', modvarmaps) in
      debug_info verbosity stage (fun _ -> "Adding the following exports to module " ^ module_name ^ " : " ^ (String.concat "" exps_str) ^ "\n");
      pure (hs', s')
    (* Trap should be counted as an instantiation error *)
    | Cfg_trap (s', f) -> 
      TopHost.error "Instantiation resulted in a trap"
    | Cfg_err -> TopHost.error "invalid module instantiation"
    | Cfg_exhaustion -> TopHost.error "instantiation resulted in exhaustion"

let rec instantiate_modules verbosity hs s names modules =
  match (names, modules) with
  | ([], _) -> pure (hs, s)
  | (name :: names', m :: modules') -> 
    debug_info verbosity stage (fun () -> "Processing module: " ^ name ^ "\n");
    let* (hs', s') = instantiate_host verbosity hs s name m in
      instantiate_modules verbosity hs' s' names' modules'
  | _ -> TopHost.error "Invalid module name parsing results"

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