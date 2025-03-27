
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

(*open Host*)
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

let invocation_interpret verbosity error_code_on_crash sf args (name: string) =
  let (s, f) = sf in
  let* es_init =
    TopHost.from_out (
      ovpending verbosity stage "interpreting" (fun _ ->
        if (String.equal name "") then
          Error ("no function name specified")
        else
        match invoke_exported_function_args name s f args with
        | None -> Error ("unknown function `" ^ name ^ "`, or unexpected argument types")
        | Some es_init -> OK es_init)
      ) in
    let cfg_init = (s, (f, es_init)) in
    let res = eval_wasm_cfg verbosity cfg_init in
    debug_info_span verbosity result stage (fun _ ->
      match res with
      | Cfg_res (_, _, vs) -> pp_values vs
      | Cfg_trap _ -> "Execution returned a trap; run the interpreter in detailed mode (--vi) for more information\n"
      | Cfg_err -> "Execution returned an error; run the interpreter in detailed mode (--vi) for more information\n");
    if error_code_on_crash && (match res with Cfg_res _ -> false | _ -> true) then exit 1
    else pure ()

let instantiate verbosity s m imps =
  let* wasm_cfg =
    TopHost.from_out (
      ovpending verbosity stage "instantiation" (fun _ ->
        match interp_instantiate_wrapper s m imps with
        | None -> Error "instantiation error"
        | Some cfg -> OK cfg)) in
  pure (eval_wasm_cfg verbosity wasm_cfg)

let instantiate_interpret verbosity error_code_on_crash m args name =
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
