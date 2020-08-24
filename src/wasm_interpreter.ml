(** Main file for the Wasm interpreter **)

(* TODO: refactor *)

let interpret verbosity error_code_on_crash sies (name : string) (depth : int) = (* TODO: This function really should be in [Execute]. *)
  let open Output in
  let open Execute.Host in
  let open Execute.Interpreter in
  let print_step_header gen =
    debug_info verbosity intermediate ~style:bold
      (fun () -> Printf.sprintf "step %d:\n" gen) in
  match ovpending verbosity stage "interpreting" (fun _ ->
    match lookup_exported_function name sies with
    | None -> `Error (false, "unknown function `" ^ name ^ "`")
    | Some cfg0 -> `Ok cfg0) with
  | `Error e -> `Error e
  | `Ok cfg0 ->
    let ((_, inst), _) = sies in
    let rec eval gen cfg =
      let* cfg_res = run_step depth inst cfg in
      print_step_header gen ;
      debug_info verbosity intermediate
        (fun _ -> pp_res_tuple_except_store cfg_res);
      debug_info_span verbosity intermediate intermediate
        (fun () ->
          let ((s, _), _) = cfg in
          let ((s', _), _) = cfg_res in
          let store_status = if s = s' then "unchanged" else "changed" in
          Printf.sprintf "and store %s\n" store_status);
      debug_info verbosity store
        (fun () ->
          let ((s', _), _) = cfg_res in
          Printf.sprintf "and store\n%s" (pp_store 1 s'));
      match cfg_res with
      | (_, RS_crash) ->
        wait_message verbosity;
        debug_info verbosity result ~style:red (fun _ -> "crash");
        pure None
      | (_, RS_break _) ->
        wait_message verbosity;
        debug_info verbosity result ~style:bold (fun _ -> "break");
        pure None
      | (_, RS_return vs) ->
        wait_message verbosity;
        debug_info verbosity result ~style:green (fun _ -> "return");
        debug_info verbosity result (fun _ -> Printf.sprintf " %s\n" (pp_values vs));
        pure (Some vs)
      | ((s', vs'), RS_normal es) ->
        begin match is_const_list es with
        | Some vs -> pure (Some vs)
        | None -> eval (gen + 1) (((s', vs'), es))
        end in
    print_step_header 0 ;
    debug_info verbosity intermediate (fun _ ->
      Printf.sprintf "\n%s\n" (pp_config_tuple_except_store cfg0));
    let* res = eval 1 cfg0 in
    debug_info_span verbosity result stage (fun _ ->
      match res with
      | Some vs -> pp_values vs
      | None -> "");
    if error_code_on_crash && (match res with None -> true | Some _ -> false) then exit 1
    else pure ()

let instantiate_interpret verbosity interactive error_code_on_crash m name depth =
  debug_info verbosity stage (fun () -> Printf.printf "instantiation...");
  match interp_instantiate_wrapper m with
  | None -> `Error (false, "instantiation error")
  | Some (store_inst_exps, _) ->
    debug_info verbosity stage (fun () -> Printf.printf "%s \x1b[32mOK\x1b[0m\n" (ansi_delete_chars 3));
    if interactive then Execute.repl store_inst_exps name depth
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
    debug_info verbosity stage (fun () -> Printf.printf "parsing...");
    let m =
      if text then
        invalid_arg "Text mode not yet implemented."
      else
        match (* TODO: Use [Shim]. *) Extract.run_parse_module (List.concat files) with
        | None -> invalid_arg "syntax error"
        | Some m -> m in
    debug_info verbosity stage (fun () -> Printf.printf "%s \x1b[32mOK\x1b[0m\n%!" (ansi_delete_chars 3));
    (** Running. *)
    if no_exec then
      (debug_info verbosity stage (fun () -> Printf.printf "skipping interpretation because of --no-exec.\n%!");
       `Ok ())
    else instantiate_interpret verbosity interactive error_code_on_crash m func_name depth
  with Invalid_argument msg -> `Error (false, msg)

(** Command line interface *)

open Cmdliner

let verbosity =
  let mk v str doc =
    (v, Arg.info str ~doc) in
  let doc = "Verbosity level" in
  Arg.(value & Output.(vflag result [
      mk none ["n"; "nothing"] "Print nothing" ;
      mk result ["r"; "result"] "Only print the result" ;
      mk stage ["s"; "stage"] "Also print stage" ;
      mk intermediate ["i"; "intermediate"] "Also print intermediate states, without stores" ;
      mk store ["a"; "all"; "store"] "Also print stores" ;
    ]) & info ["v"; "verbosity"] ~doc)

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
      `P "Report them at https://github.com/WasmCert/WasmCert-Coq/issues"; ]
  in
  (Term.(ret (const process_args_and_run $ verbosity $ text $ no_exec $ interactive $ error_code_on_crash $ func_name $ depth $ srcs)),
   Term.info "wasm_interpreter" ~version:"%%VERSION%%" ~doc ~exits ~man ~man_xrefs)

let () = Term.(exit @@ eval cmd)

