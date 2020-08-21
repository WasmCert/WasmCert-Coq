
(** The output associated with the functions of this module. *)
type 'a out =
  | OK of 'a
  | Error of string

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

    let host_apply st f vs =
      Host.host_bind (Host.host_apply st f vs) (fun r -> host_ret r)

    let show_host_function = Host.show_host_function

  end

module Interpreter = Shim.Interpreter (Host)

open Interpreter

(* read-eval-print loop; work in progress *)
let rec user_input prompt cb st =
  match LNoise.linenoise prompt with
  | None -> pure (OK ())
  | Some v ->
    let* st' = cb v st in
    user_input prompt cb st'

let string_of_crash_reason = function
  | () -> "error"

let take_step depth i cfg =
  let ((s, _), _)  = (*Convert.from_triple*) cfg in
  let* res = run_step depth i cfg in
  let ((s', _), _)  = (*Convert.from_triple*) res in
  let store_status = if s = s' then "unchanged" else "changed" in
  Printf.printf "%sand store %s\n%!" (pp_res_tuple_except_store res) store_status;
  match (*Convert.from_triple*) res with
  | ((_, _), Extract.RS_crash) ->
    Printf.printf "\x1b[31mcrash\x1b[0m: %s\n%!" (string_of_crash_reason ());
    pure cfg
  | ((_, _), Extract.RS_break _) ->
    Printf.printf "\x1b[33mbreak\x1b[0m\n%!";
    pure cfg
  | ((_, _), Extract.RS_return vs) ->
    Printf.printf "\x1b[32mreturn\x1b[0m %s\n%!" (pp_values vs);
    pure cfg
  | ((s', vs'), Extract.RS_normal es) ->
    pure ((s', vs'), es)

let repl sies (name : string) (depth : int) =
  LNoise.set_hints_callback (fun line ->
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
  let ((s, i), _) = sies in
  match lookup_exported_function name sies with
  | None -> pure (Error ("unknown function `" ^ name ^ "`"))
  | Some cfg0 ->
    Printf.printf "\n%sand store\n%s\n%!"
      (pp_config_tuple_except_store cfg0)
      (pp_store 1 s);
    (fun from_user cfg ->
      if from_user = "quit" then exit 0;
      LNoise.history_add from_user |> ignore;
      LNoise.history_save ~filename:"history.txt" |> ignore;
      if from_user = "" || from_user = "step" then take_step depth i cfg
      else if from_user = "s" || from_user = "store" then
        (let ((s, _), _) = cfg in
         Printf.sprintf "%s%!" (pp_store 0 s) |> print_endline;
         pure cfg)
      else if from_user = "help" then
        (Printf.sprintf "commands:\nstep: take a step\nstore: display the store\nquit: quit\nhelp: this help message" |> print_endline;
         pure cfg)
      else (Printf.sprintf "unknown command" |> print_endline; pure cfg))
    |> (fun cb -> user_input "> " cb cfg0)

