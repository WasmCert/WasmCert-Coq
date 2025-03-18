
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

(* artifact for interactive interpreter *)
(*let rec user_input prompt cb st =
  match LNoise.linenoise prompt with
  | None -> pure ()
  | Some v ->
    let* st' = cb v st in
    user_input prompt cb st'

let string_of_crash_reason = function
  | () -> "error"
*)
(*
let take_step verbosity _i cfg =
  let res = run_step_compat cfg in
  (*
  let store_status = if s = s' then "unchanged" else "changed" in
  debug_info result verbosity (fun _ ->
    Printf.sprintf "%sand store %s\n%!" (pp_res_tuple_except_store (tuple_drop_hs res)) store_status) ;
  *)
  match res with
  | ((_, _), Extract.RS_crash _) ->
    debug_info result verbosity ~style:red (fun _ -> "crash:") ;
    debug_info result verbosity (fun _ -> " " ^ string_of_crash_reason ()) ;
    pure cfg
  | ((_, _), Extract.RS_break _) ->
    debug_info result verbosity ~style:red (fun _ -> "break") ;
    pure cfg
  | ((_, _), Extract.RS_return vs) ->
    debug_info result verbosity ~style:green (fun _ -> "return:") ;
    debug_info result verbosity (fun _ -> " " ^ pp_values vs) ;
    pure cfg
  | ((s', vs'), Extract.RS_normal es) ->
    pure ((s', vs'), es)

let repl verbosity sies (name : string) =
  error ("unimplemented")
  LNoise.set_hints_callback (fun line ->
      (* FIXME: Documentation is needed here. I don’t know what these lines do. *)
      if line <> "git remote add " then None
      else Some (" <this is the remote name> <this is the remote URL>",
                 LNoise.Yellow,
                 true)
    );
  LNoise.history_load ~filename:"history.txt" |> ignore;
  LNoise.history_set ~max_length:100 |> ignore;
  LNoise.set_completion_callback begin fun line_so_far ln_completions ->
    (if line_so_far = "" then
      ["store"]
    else if line_so_far <> "" && line_so_far.[0] = 's' then
      ["store"]
    else [])
      |> List.iter (LNoise.add_completion ln_completions);
  end;
  ["interactive Wasm interpreter";
   "get tab completion with <TAB>";
   "type quit to exit gracefully"]
  |> List.iter print_endline;
  let (((_, s), i), _) = sies in
  match lookup_exported_function name sies with
  | None -> error ("unknown function `" ^ name ^ "`")
  | Some cfg0 ->
    debug_info result verbosity (fun _ ->
      Printf.sprintf "\n%sand store\n%s\n%!"
        (pp_config_tuple_except_store (tuple_drop_hs cfg0))
        (pp_store 1 s)) ;
    (fun from_user cfg ->
      if from_user = "quit" then exit 0;
      LNoise.history_add from_user |> ignore;
      LNoise.history_save ~filename:"history.txt" |> ignore;
      if from_user = "" || from_user = "step" then take_step verbosity i cfg
      else if from_user = "s" || from_user = "store" then
        (let (((_, s), _), _) = cfg in
         Printf.sprintf "%s%!" (pp_store 0 s) |> print_endline;
         pure cfg)
      else if from_user = "help" then
        (Printf.sprintf "commands:\nstep: take a step\nstore: display the store\nquit: quit\nhelp: this help message" |> print_endline;
         pure cfg)
      else (Printf.sprintf "unknown command" |> print_endline; pure cfg))
    |> (fun cb -> user_input "> " cb cfg0)
*)

let invocation_interpret verbosity error_code_on_crash hsfesargs (name: string) =
  let print_step_header gen =
    debug_info verbosity intermediate ~style:bold
      (fun () -> Printf.sprintf "step %d:\n" gen) in
  let ((((hs, s), f_instantiation), es_instantiation), args) = hsfesargs in
  
  let rec eval_cfg gen hs cfg =
      (let cfg_res = run_step_compat hs cfg in
      print_step_header gen ;
      debug_info verbosity intermediate
        (fun _ -> pp_res_cfg_except_store hs cfg cfg_res);
      match cfg_res with
      | RSC_normal (hs', cfg') ->
        (* reforming the resulting interpreter cfg to the normal form *)
        begin match run_step_cfg_ctx_reform cfg' with
        | Some cfg_next -> 
            eval_cfg (gen+1) hs' cfg_next
        | None ->
          debug_info verbosity stage ~style:red (fun _ -> "Configuration reformation failure; this should not happen for valid Wasm modules. Please file a bug report at GitHub/WasmCert-Coq.\n");
          pure None
        end
      | RSC_value (s, _f, vs) ->
        debug_info verbosity stage ~style:green (fun _ -> "success after " ^ string_of_int gen ^ " steps\n");
        pure (Some (hs, s, vs))
      | RSC_trap (_s, _f) ->
        debug_info verbosity stage ~style:red (fun _ -> "trap after " ^ string_of_int gen ^ " steps\n");
        pure None
      | RSC_invalid ->
        debug_info verbosity stage ~style:red (fun _ -> "Invalid cfg\n");
        pure None
      | RSC_error ->
        debug_info verbosity stage ~style:red (fun _ -> "Ill-typed input\n");
        pure None
      )
    in

  debug_info verbosity intermediate (fun _ ->
    Printf.sprintf "\nPost-instantiation stage for table and memory initialisers...\n");
  
  (* In Wasm 2.0, module instantiation results in a series of table and memory initialiser instructions followed by an invocation of the start function *)  
  match run_v_init_with_frame s f_instantiation es_instantiation with
  | cfg_instantiation -> 
    let* res = eval_cfg 1 hs cfg_instantiation in
    begin match res with
    | Some (hs', s', _) ->
      debug_info verbosity intermediate (fun _ ->
      Printf.sprintf "\nInstantiation success\n");
      let* es_init =
        TopHost.from_out (
          ovpending verbosity stage "interpreting" (fun _ ->
            if (String.equal name "") then
              Error ("no function name specified")
            else
            match invoke_exported_function_args name s f_instantiation args with
            | None -> Error ("unknown function `" ^ name ^ "`, or unexpected argument types")
            | Some es_init -> OK es_init)
          ) in
      begin match run_v_init_with_frame s' Extract.empty_frame es_init with
      | cfg_init -> 
        print_step_header 0 ;
        debug_info verbosity intermediate (fun _ ->
          Printf.sprintf "\nExecuting configuration:\n%s\n" (pp_cfg_tuple_ctx_except_store cfg_init));
        let* res = eval_cfg 1 hs' cfg_init in
        debug_info_span verbosity result stage (fun _ ->
          match res with
          | Some (_, _, vs) -> pp_values vs
          | None -> "Execution returned a trap or an error; run the interpreter in detailed mode (--vi) for more information\n");
        if error_code_on_crash && (match res with None -> true | Some _ -> false) then exit 1
        else pure ()
      end
    | None -> Printf.printf "Invocation failed"; pure ()
    end





  

(* TODO: update the interactive interpreter. The interactive flag is currently disabled. *)
let instantiate_interpret verbosity error_code_on_crash m args name =
  let* hs_s_f_es_args =
    TopHost.from_out (
      ovpending verbosity stage "instantiation" (fun _ ->
        match interp_instantiate_wrapper m with
        | None -> Error "instantiation error"
        | Some hs_s_f_es -> OK (hs_s_f_es, args))) in
  (*if interactive then repl verbosity store_inst_exps name
  else if no_ctx_optimise then interpret verbosity error_code_on_crash store_inst_exps name
  else*) invocation_interpret verbosity error_code_on_crash hs_s_f_es_args name
