
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

open Host
open Interpreter
(*
let config_tuple_patch cfg =
  let ((s, f), es) = cfg in
  (((Obj.magic s, s), f), es)

let config_tuple_patch_flat cfg =
  let ((s, f), es) = cfg in
  (Obj.magic s, s, f, es)
*)
(* read-eval-print loop; work in progress *)
let rec user_input prompt cb st =
  match LNoise.linenoise prompt with
  | None -> pure ()
  | Some v ->
    let* st' = cb v st in
    user_input prompt cb st'

let string_of_crash_reason = function
  | () -> "error"

(* XXX fix this in Coq? *)
let tuple_drop_hs res =
  match res with
  | (((_, s), f), r) -> ((s, f), r)

let take_step verbosity _i cfg =
  let ((s, _), _)  = (*Convert.from_triple*) cfg in
  let res = run_step_compat cfg in
  let ((s', _), _)  = (*Convert.from_triple*) res in
  let store_status = if s = s' then "unchanged" else "changed" in
  debug_info result verbosity (fun _ ->
    Printf.sprintf "%sand store %s\n%!" (pp_res_tuple_except_store (tuple_drop_hs res)) store_status) ;
  match (*Convert.from_triple*) res with
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

let interpret verbosity error_code_on_crash sies (name: string) =
  let print_step_header gen =
    debug_info verbosity intermediate ~style:bold
      (fun () -> Printf.sprintf "step %d:\n" gen) in
 (* let print_exhaustion gen = 
    debug_info verbosity intermediate ~style:bold
      (fun () -> Printf.sprintf "step %d: \n Execution halted due to fuel exhaustion\n" gen) in*)
  let* cfg0 =
    TopHost.from_out (
      ovpending verbosity stage "interpreting" (fun _ ->
        match lookup_exported_function name sies with
        | None -> Error ("unknown function `" ^ name ^ "`")
        | Some cfg0 -> OK cfg0)) in
  let rec eval_cfg gen cfg =
   (* if (gen >= max_steps) then 
      (print_exhaustion gen;
      debug_info verbosity result ~style:bold (fun _ -> "fuel exhaustion\n");
      pure None)
    else *)
      (let cfg_res = run_step_compat cfg in
      print_step_header gen ;
      debug_info verbosity intermediate
        (fun _ -> pp_res_tuple_except_store (tuple_drop_hs cfg_res));
      debug_info_span verbosity intermediate intermediate
        (fun () ->
          let (((_, s), _), _) = cfg in
          let (((_, s'), _), _) = cfg_res in
          let store_status = if s = s' then "unchanged" else "changed" in
          Printf.sprintf "and store %s\n" store_status);
      debug_info verbosity store
        (fun () ->
          let (((_, s'), _), _) = cfg_res in
          Printf.sprintf "and store\n%s" (pp_store 1 s'));
      match cfg_res with
      | (_, RS_crash _) ->
        wait_message verbosity;
        debug_info verbosity result ~style:red (fun _ -> "crash\n");
        pure None
      | (_, RS_break _) ->
        wait_message verbosity;
        debug_info verbosity result ~style:bold (fun _ -> "break\n");
        pure None
      | (_, RS_return vs) ->
        wait_message verbosity;
        debug_info verbosity result ~style:green (fun _ -> "return");
        debug_info verbosity result (fun _ -> Printf.sprintf " %s\n" (pp_values vs));
        pure (Some vs)
      | (((hs', s'), vs'), RS_normal es) ->
        begin match is_const_list es with
        | Some vs -> 
          debug_info verbosity stage ~style:green (fun _ -> "success after " ^ string_of_int gen ^ " steps\n");
          pure (Some vs)
        | None -> eval_cfg (gen + 1) ((((hs', s'), vs'), es))
        end) in

  debug_info verbosity result ~style:yellow (fun _ -> "Context optimisation disabled\n");
  print_step_header 0 ;
  debug_info verbosity intermediate (fun _ ->
    Printf.sprintf "\n%s\n" (pp_config_tuple_except_store (tuple_drop_hs cfg0)));
  let* res = eval_cfg 1 cfg0 in
  debug_info_span verbosity result stage (fun _ ->
    match res with
    | Some vs -> pp_values vs
    | None -> "");
  if error_code_on_crash && (match res with None -> true | Some _ -> false) then exit 1
  else pure ()

  (*
module Interpreter_ctx_extract :
 sig
  val host_application_impl :
    Equality.sort -> EmptyHost.store_record -> function_type -> Equality.sort
    -> value list -> Equality.sort * (EmptyHost.store_record * result) option

  val run_one_step_ctx : Equality.sort -> cfg_tuple_ctx -> run_step_ctx_result

  val run_step_cfg_ctx_reform : cfg_tuple_ctx -> cfg_tuple_ctx option

  val run_v_init :
    Equality.sort store_record -> administrative_instruction list ->
    cfg_tuple_ctx option

  val es_of_cfg : cfg_tuple_ctx -> administrative_instruction list
 end
 *)

include Extract.Interpreter_ctx_extract

  let interpret_ctx verbosity error_code_on_crash sies (name: string) =
    let print_step_header gen =
      debug_info verbosity intermediate ~style:bold
        (fun () -> Printf.sprintf "step %d:\n" gen) in
   (* let print_exhaustion gen = 
      debug_info verbosity intermediate ~style:bold
        (fun () -> Printf.sprintf "step %d: \n Execution halted due to fuel exhaustion\n" gen) in*)
    let* cfg0 =
      TopHost.from_out (
        ovpending verbosity stage "interpreting" (fun _ ->
          match lookup_exported_function name sies with
          | None -> Error ("unknown function `" ^ name ^ "`")
          | Some cfg0 -> OK cfg0)) in
    let rec eval_cfg gen (hs: Extract.Equality.sort) (cfg: Extract.cfg_tuple_ctx) =
      (let run_step_res = run_one_step_ctx hs cfg in
        print_step_header gen ;
        match run_step_res with
        | Extract.RSC_error ->
          wait_message verbosity;
          debug_info verbosity result ~style:red (fun _ -> "crash_error\n");
          pure None
        | Extract.RSC_invalid ->
          wait_message verbosity;
          debug_info verbosity result ~style:red (fun _ -> "crash_invalid\n");
          pure None
        | Extract.RSC_value vs ->
          debug_info verbosity stage ~style:green (fun _ -> "success after " ^ string_of_int gen ^ " steps\n");
          pure (Some vs)
        | Extract.RSC_normal (hs_res, cfg_res) ->
          debug_info verbosity intermediate
          (fun () -> pp_es (es_of_cfg cfg_res)); 
          debug_info verbosity intermediate
          (fun () -> 
            let (((s, _), _), _) = cfg in
            let (((s', _), _), _) = cfg_res in 
            let store_status = if s = s' then "unchanged" else "changed" in
              Printf.sprintf "and store %s\n" store_status
            ); 
          debug_info verbosity store
          (fun () ->
            let (((s', _), _), _) = cfg_res in
              Printf.sprintf "and store\n%s" (pp_store 1 s'));
          (match run_step_cfg_ctx_reform cfg_res with
          | Some cfg_res' -> eval_cfg (gen + 1) hs_res cfg_res'
          | None -> pure None
          )
        ) in
    print_step_header 0 ;

    let (((hs, s), _), es) = cfg0 in
    debug_info verbosity intermediate
    (fun () -> pp_es es); 

    let cfg_init = run_v_init s es in
    (match cfg_init with
    | Some cfg_init' ->
      let* res = eval_cfg 0 hs cfg_init' in
      (debug_info_span verbosity result stage (fun _ ->
        match res with
        | Some vs -> pp_values vs
        | None -> ""
        );
        if error_code_on_crash && (match res with None -> true | Some _ -> false) then exit 1
        else pure ()
      )
    | None -> debug_info verbosity result ~style:red (fun _ -> "invalid starting es\n"); exit 1
    )

(* TODO: update the interactive to use the context-optimised version as well *)
let instantiate_interpret verbosity interactive no_ctx_optimise error_code_on_crash m name =
  let* store_inst_exps =
    TopHost.from_out (
      ovpending verbosity stage "instantiation" (fun _ ->
        match interp_instantiate_wrapper m with
        | None -> Error "instantiation error"
        | Some (store_inst_exps, _) -> OK store_inst_exps)) in
  if interactive then repl verbosity store_inst_exps name
  else if no_ctx_optimise then interpret verbosity error_code_on_crash store_inst_exps name
  else interpret_ctx verbosity error_code_on_crash store_inst_exps name
