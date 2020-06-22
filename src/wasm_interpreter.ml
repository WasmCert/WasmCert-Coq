(** Main file for the Wasm interpreter **)

let run files =
  match Extract.run_parse_module_from_asciis (Convert.to_list (List.concat files)) with
  | None -> `Error (false, "Syntax error")
  | Some m ->
    Printf.printf "Parsing successful\n";
    (match Extract.interp_instantiate_wrapper m with
     | None -> `Error (false, "instantiation error")
     | Some inst ->
       Printf.printf "instantiation successful\n";
       `Ok ())
    (* TODO: Link to [Extract.run_v]. *)

let interpret verbose text no_exec srcs fname =
  try
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
    run files
  with Invalid_argument msg -> `Error (false, msg)

(* Command line interface *)

open Cmdliner

let verbose =
  let doc = "Print intermediate states." in
  Arg.(value & flag & info ["v"; "verbose"] ~doc)

let text =
  let doc = "Read text format." in
  Arg.(value & flag & info ["text"] ~doc)

let no_exec =
  let doc = "Stop before executing (only go up to typechecking)." in
  Arg.(value & flag & info ["no-exec"] ~doc)

let srcs =
  let doc = "Source file(s) to interpret." in
  Arg.(non_empty & pos_left ~rev:true 0 file [] & info [] ~docv:"FILE" ~doc)

let fname =
  let doc = "Name of the Wasm function to run." in
  Arg.(required & pos ~rev:true 0 (some string) None & info [] ~docv:"NAME" ~doc)

let cmd =
  let doc = "Interpret WebAssembly files" in
  let man_xrefs = [] in
  let exits = Term.default_exits in
  let man =
    [ `S Manpage.s_bugs;
      `P "Report them at https://github.com/Imperial-Wasm/wasm_coq/issues"; ]
  in
  (Term.(ret (const interpret $ verbose $ text $ no_exec $ srcs $ fname)),
   Term.info "wasm_interpreter" ~version:"%%VERSION%%" ~doc ~exits ~man ~man_xrefs)

let () = Term.(exit @@ eval cmd)

