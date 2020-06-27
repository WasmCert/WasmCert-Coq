(** Main file for the Wasm interpreter **)

(* TODO: refactor *)

let ansi_bold = "\x1b[1m"
let ansi_reset = "\x1b[0m"

let debug_info verbosity min_level (f : unit -> unit) =
  if verbosity >= min_level then (f (); flush stdout; flush stderr) else ()

let debug_info_span verbosity min_level max_level (f : unit -> unit) =
  if verbosity >= min_level && verbosity <= max_level then
    (f (); flush stdout; flush stderr)
  else ()

let string_of_crash_reason = function
| Extract.C_error -> "error"
| Extract.C_exhaustion -> "exhaustion"

(** ANSI escape sequence to delete [n] characters. *)
let ansi_delete_chars n =
  "\x1b[" ^ string_of_int n ^ "D"

let terminal_magic verbosity =
  (* yuck *)
  debug_info verbosity 2 (fun () -> Printf.printf "...");
  debug_info verbosity 1 (fun () -> Printf.printf "%s " (ansi_delete_chars 3));
  debug_info verbosity 2 (fun () -> Printf.printf "%s" (ansi_delete_chars 1))

(** Given a verbosity level, a configuration tuple, a function name, and a depth, interpret the Wasm function. *)
let interpret verbosity sies (name : string) (depth : int) =
  debug_info verbosity 1 (fun () -> Printf.printf "interpreting...");
  debug_info verbosity 2 (fun () -> Printf.printf "%s" (ansi_delete_chars 3)); (* yuck *)
  let name_coq = Convert.to_byte_list name in
  let depth_coq = Convert.to_nat depth in
  match Extract.lookup_exported_function name_coq sies with
  | None -> `Error (false, "unknown function `" ^ name ^ "`")
  | Some cfg0 ->
    let (_, inst, _) = Convert.from_triple sies in
    let rec f gen cfg =
      (let res = Extract.run_step depth_coq inst cfg in
       debug_info verbosity 2
        (fun () ->
          Printf.printf "%sstep %d%s:\n%s"
            ansi_bold gen
            ansi_reset
            (Convert.from_string (Extract.pp_res_tuple_except_store res)));
      debug_info_span verbosity 2 2
        (fun () ->
          let (s, _, _)  = Convert.from_triple cfg in
          let (s', _, _)  = Convert.from_triple res in
          let store_status = if s = s' then "unchanged" else "changed" in
          Printf.printf "and store %s\n" store_status);
      debug_info verbosity 3
        (fun () ->
          let (s', _, _)  = Convert.from_triple res in
          Printf.printf "and store\n%s"
            (Convert.from_string (Extract.pp_store (Convert.to_nat 1) s')));
       match Convert.from_triple res with
       | (_, _, RS_crash crash) ->
         terminal_magic verbosity;
         Printf.printf "\x1b[31mcrash\x1b[0m: %s\n" (string_of_crash_reason crash);
         ()
       | (_, _, RS_break _) ->
         terminal_magic verbosity;
         Printf.printf "\x1b[33mbreak\x1b[0m\n";
         ()
       | (_, _, RS_return vs) ->
         terminal_magic verbosity;
         Printf.printf "\x1b[32mreturn\x1b[0m %s\n" (Convert.from_string (Extract.pp_values vs));
         ()
       | (s', vs', RS_normal es) ->
         if Convert.from_bool (Extract.const_list es) then ()
         else f (gen + 1) (Convert.to_triple (s', vs', es))) in
    debug_info verbosity 2 (fun () -> Printf.printf "\n%sstep %d:\n%s\n%s\n" ansi_bold 0 ansi_reset (Convert.from_string (Extract.pp_config_tuple_except_store cfg0)));
    f 1 cfg0;
    `Ok ()

let instantiate_interpret verbosity interactive m name depth =
  debug_info verbosity 1 (fun () -> Printf.printf "instantiation...");
  match Extract.interp_instantiate_wrapper m with
  | None -> `Error (false, "instantiation error")
  | Some (Extract.Pair (store_inst_exps, _)) ->
    debug_info verbosity 1 (fun () -> Printf.printf "%s \x1b[32mOK\x1b[0m\n" (ansi_delete_chars 3));
    if interactive then Repl.repl store_inst_exps name depth
    else interpret verbosity store_inst_exps name depth

(** Main function *)
let process_args_and_run verbosity text no_exec interactive func_name depth srcs =
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
            | Some c -> aux (Convert.to_ascii c :: acc)
            | None ->
              close_in in_channel;
              List.rev acc in
          aux []) srcs in
    (** Parsing. *)
    debug_info verbosity 1 (fun () -> Printf.printf "parsing...");
    let m =
      if text then
        invalid_arg "Text mode not yet implemented."
      else
        match Extract.run_parse_module_from_asciis (Convert.to_list (List.concat files)) with
        | Extract.None -> invalid_arg "syntax error"
        | Extract.Some m -> m in
    debug_info verbosity 1 (fun () -> Printf.printf "%s \x1b[32mOK\x1b[0m\n%!" (ansi_delete_chars 3));
    (** Running. *)
    if no_exec then
      (debug_info verbosity 1 (fun () -> Printf.printf "skipping interpretation because of --no-exec.\n%!");
       `Ok ())
    else instantiate_interpret verbosity interactive m func_name depth
  with Invalid_argument msg -> `Error (false, msg)

(** Command line interface *)

open Cmdliner

let verbosity =
  let doc = "Verbosity level; default = 1.\n" ^
  "\t0: print nothing.\n" ^
  "\t1: print stage.\n" ^
  "\t2: also print intermediate states, without stores.\n" ^
  "\t3 also print stores." in
  Arg.(value & opt int 1 & info ["v"; "verbosity"] ~doc)

let text =
  let doc = "Read text format." in
  Arg.(value & flag & info ["text"] ~doc)

let no_exec =
  let doc = "Stop before executing (only go up to typechecking)." in
  Arg.(value & flag & info ["no-exec"] ~doc)

let interactive =
  let doc = "Interactive execution." in
  Arg.(value & flag & info ["i"; "interactive"] ~doc)

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
  (Term.(ret (const process_args_and_run $ verbosity $ text $ no_exec $ interactive $ func_name $ depth $ srcs)),
   Term.info "wasm_interpreter" ~version:"%%VERSION%%" ~doc ~exits ~man ~man_xrefs)

let () = Term.(exit @@ eval cmd)

