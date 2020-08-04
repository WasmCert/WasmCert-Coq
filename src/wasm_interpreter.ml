(** Main file for the Wasm interpreter **)

(* TODO: refactor *)

(* TODO: use notty rather than this ad-hoc mess *)
let ansi_bold = "\x1b[1m"
let ansi_reset = "\x1b[0m"
let ansi_green = "\x1b[32m"
let ansi_red = "\x1b[31m"

let debug_info verbosity min_level (f : unit -> unit) =
  if verbosity >= min_level then (f (); flush stdout; flush stderr) else ()

let debug_info_span verbosity min_level max_level (f : unit -> unit) =
  if verbosity >= min_level && verbosity <= max_level then
    (f (); flush stdout; flush stderr)
  else ()

let string_of_crash_reason = function
| () -> "error"

(** ANSI escape sequence to delete [n] characters. *)
let ansi_delete_chars n =
  "\x1b[" ^ string_of_int n ^ "D"

let terminal_magic verbosity =
  (* yuck *)
  debug_info verbosity 2 (fun () -> Printf.printf "...");
  debug_info verbosity 1 (fun () -> Printf.printf "%s " (ansi_delete_chars 3));
  debug_info verbosity 2 (fun () -> Printf.printf "%s" (ansi_delete_chars 1))

(** Given a verbosity level, a configuration tuple, a function name, and a depth, interpret the Wasm function. *)
let interpret verbosity error_code_on_crash sies (name : string) (depth : int) =
  debug_info verbosity 2 (fun () -> Printf.printf "interpreting...");
  let name_coq = Repl.explode name in
  let depth_coq = Convert.to_nat depth in
  match Extract.lookup_exported_function name_coq sies with
  | None -> `Error (false, "unknown function `" ^ name ^ "`")
  | Some cfg0 ->
    let ((_, inst), _) = sies in
    let rec eval gen cfg =
      (let cfg_res = Extract.run_step depth_coq inst cfg in
       debug_info verbosity 3
        (fun () ->
          Printf.printf "%sstep %d%s:\n%s"
            ansi_bold gen
            ansi_reset
            (Repl.implode (Extract.pp_res_tuple_except_store cfg_res)));
      debug_info_span verbosity 3 3
        (fun () ->
          let ((s, _), _)  = cfg in
          let ((s', _), _)  = cfg_res in
          let store_status = if s = s' then "unchanged" else "changed" in
          Printf.printf "and store %s\n" store_status);
      debug_info verbosity 4
        (fun () ->
          let ((s', _), _)  = cfg_res in
          Printf.printf "and store\n%s"
            (Repl.implode (Extract.pp_store (Convert.to_nat 1) s')));
       match cfg_res with
       | (_, RS_crash crash) ->
         terminal_magic verbosity;
         Printf.printf "%scrash%s: %s\n" ansi_red ansi_reset (string_of_crash_reason crash);
         None
       | (_, RS_break _) ->
         terminal_magic verbosity;
         Printf.printf "\x1b[33mbreak\x1b[0m\n";
         None
       | (_, RS_return vs) ->
         terminal_magic verbosity;
         Printf.printf "\x1b[32mreturn\x1b[0m %s\n" (Repl.implode (Extract.pp_values vs));
         Some vs
       | ((s', vs'), RS_normal es) ->
         begin match Extract.those_const_list es with
         | Some vs -> Some vs
         | None -> eval (gen + 1) (((s', vs'), es))
         end) in
    debug_info verbosity 2 (fun () -> Printf.printf "%s" (ansi_delete_chars 3));
    debug_info_span verbosity 2 2 (fun () -> Printf.printf " %sOK%s\n" ansi_green ansi_reset);
    debug_info verbosity 3 (fun () -> Printf.printf "\n%sstep 0:\n%s\n%s\n" ansi_bold ansi_reset (Repl.implode (Extract.pp_config_tuple_except_store cfg0)));
    let res = eval 1 cfg0 in
    debug_info_span verbosity 1 2
      (fun () ->
        match res with
        | Some vs ->
          Printf.printf "%s%!" (Repl.implode (Extract.pp_values vs))
        | None -> ()
      );
    if error_code_on_crash && (match res with None -> true | Some _ -> false) then exit 1
    else `Ok ()

let instantiate_interpret verbosity interactive error_code_on_crash m name depth =
  debug_info verbosity 2 (fun () -> Printf.printf "instantiation...");
  match Extract.interp_instantiate_wrapper m with
  | None -> `Error (false, "instantiation error")
  | Some (store_inst_exps, _) ->
    debug_info verbosity 2 (fun () -> Printf.printf "%s \x1b[32mOK\x1b[0m\n" (ansi_delete_chars 3));
    if interactive then Repl.repl store_inst_exps name depth
    else interpret verbosity error_code_on_crash store_inst_exps name depth

(** Main function *)
let process_args_and_run verbosity text no_exec interactive error_code_on_crash func_name depth srcs =
  try
    (** Preparing the files. *)
    let files =
      List.map (fun dest ->
        if not (Sys.file_exists dest) || Sys.is_directory dest then
          invalid_arg (Printf.sprintf "No file %s found." dest)
        else
          let in_channel = open_in_bin dest in
          let rec aux acc =
            match try Some (input_char in_channel)
                  with End_of_file -> None with
            | Some c -> aux (c :: acc)
            | None ->
              close_in in_channel;
              List.rev acc in
          aux []) srcs in
    (** Parsing. *)
    debug_info verbosity 2 (fun () -> Printf.printf "parsing...");
    let m =
      if text then
        invalid_arg "Text mode not yet implemented."
      else
        match Extract.run_parse_module (List.concat files) with
        | None -> invalid_arg "syntax error"
        | Some m -> m in
    debug_info verbosity 2 (fun () -> Printf.printf "%s \x1b[32mOK\x1b[0m\n%!" (ansi_delete_chars 3));
    (** Running. *)
    if no_exec then
      (debug_info verbosity 2 (fun () -> Printf.printf "skipping interpretation because of --no-exec.\n%!");
       `Ok ())
    else instantiate_interpret verbosity interactive error_code_on_crash m func_name depth
  with Invalid_argument msg -> `Error (false, msg)

(** Command line interface *)

open Cmdliner

let verbosity =
  let doc = "Verbosity level; default = 1.\n" ^
  "\t0: print nothing.\n" ^
  "\t1: print result.\n" ^
  "\t2: also print stage.\n" ^
  "\t3: also print intermediate states, without stores.\n" ^
  "\t4 also print stores." in
  Arg.(value & opt int 3 & info ["v"; "verbosity"] ~doc)

let text =
  let doc = "Read text format." in
  Arg.(value & flag & info ["text"] ~doc)

let no_exec =
  let doc = "Stop before executing (only go up to typechecking)." in
  Arg.(value & flag & info ["no-exec"] ~doc)

let interactive =
  let doc = "Interactive execution." in
  Arg.(value & flag & info ["i"; "interactive"] ~doc)

let error_code_on_crash =
  let doc = "Return an error code on crash." in
  Arg.(value & flag & info ["E"; "error-if-crash"] ~doc)

let func_name =
  let doc = "Name of the Wasm function to run." in
  Arg.(required & pos ~rev:true 1 (some string) None & info [] ~docv:"NAME" ~doc)

let depth =
  let doc = "Depth to which to run the Wasm evaluator." in
  Arg.(required & pos ~rev:true 0 (some int) None & info [] ~docv:"DEPTH" ~doc)

let srcs =
  let doc = "Source file(s) to interpret." in
  Arg.(non_empty & pos_left ~rev:true 1 file [] & info [] ~docv:"FILE" ~doc)

let cmd =
  let doc = "Interpret WebAssembly files" in
  let man_xrefs = [] in
  let exits = Term.default_exits in
  let man =
    [ `S Manpage.s_bugs;
      `P "Report them at https://github.com/Imperial-Wasm/wasm_coq/issues"; ]
  in
  (Term.(ret (const process_args_and_run $ verbosity $ text $ no_exec $ interactive $ error_code_on_crash $ func_name $ depth $ srcs)),
   Term.info "wasm_interpreter" ~version:"%%VERSION%%" ~doc ~exits ~man ~man_xrefs)

let () = Term.(exit @@ eval cmd)

