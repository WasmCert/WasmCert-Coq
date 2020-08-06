(* read-eval-print loop; work in progress *)
let rec user_input prompt cb st =
  match LNoise.linenoise prompt with
  | None -> `Ok ()
  | Some v ->
    let st' = cb v st in
    user_input prompt cb st'

let string_of_crash_reason = function
  | () -> "error"

let string_of_char c = String.make 1 c
let rec implode = function
| [] -> ""
| c :: cs -> string_of_char c ^ (implode cs)

let explode s =
  List.init (String.length s) (String.get s)

let take_step depth_coq i cfg =
  let ((s, _), _)  = (*Convert.from_triple*) cfg in
  let res = Extract.run_step depth_coq i cfg in (* TODO: Use [Shim.run_step] instead. Use monadic style. *)
  let ((s', _), _)  = (*Convert.from_triple*) res in
  let store_status = if s = s' then "unchanged" else "changed" in
  Printf.printf "%sand store %s\n%!" (Convert.from_string (Extract.pp_res_tuple_except_store res)) store_status;
  match (*Convert.from_triple*) res with
  | ((_, _), RS_crash crash) ->
    Printf.printf "\x1b[31mcrash\x1b[0m: %s\n%!" (string_of_crash_reason crash);
    cfg
  | ((_, _), RS_break _) ->
    Printf.printf "\x1b[33mbreak\x1b[0m\n%!";
    cfg
  | ((_, _), RS_return vs) ->
    Printf.printf "\x1b[32mreturn\x1b[0m %s\n%!" (implode (Extract.pp_values vs));
    cfg
  | ((s', vs'), RS_normal es) ->
    ((s', vs'), es)

let repl sies (name : string) (depth : int) : [> `Ok of unit] =
  let name_coq = explode name in
  let depth_coq = Convert.to_nat depth in
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
  match Extract.lookup_exported_function name_coq sies with
  | None -> `Error (false, "unknown function `" ^ name ^ "`")
  | Some cfg0 ->
    Printf.printf "\n%sand store\n%s\n%!"
      (implode (Extract.pp_config_tuple_except_store cfg0))
      (implode (Extract.pp_store (Convert.to_nat 1) s));
    (fun from_user cfg ->
      if from_user = "quit" then exit 0;
      LNoise.history_add from_user |> ignore;
      LNoise.history_save ~filename:"history.txt" |> ignore;
      if from_user = "" || from_user = "step" then take_step depth_coq i cfg
      else if from_user = "s" || from_user = "store" then
        (let ((s, _), _) = cfg in
         Printf.sprintf "%s%!" (implode (Extract.pp_store (Convert.to_nat 0) s)) |> print_endline;
         cfg)
      else if from_user = "help" then
        (Printf.sprintf "commands:\nstep: take a step\nstore: display the store\nquit: quit\nhelp: this help message" |> print_endline;
         cfg)
      else (Printf.sprintf "unknown command" |> print_endline; cfg))
    |> (fun cb -> user_input "> " cb cfg0)

