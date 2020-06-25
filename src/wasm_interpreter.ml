(** Main file for the Wasm interpreter **)

let explode s = List.init (String.length s) (String.get s)

let ansi_bold = Convert.from_string (Extract.ansi_bold)
let ansi_reset = Convert.from_string (Extract.ansi_reset)

let debug_info verbose f =
  if verbose then (f (); flush stdout; flush stderr) else ()

let string_of_crash_reason = function
| Extract.C_error -> "error"
| Extract.C_exhaustion -> "exhaustion"

let run2 (verbose : bool) sies (name : string) (depth : int) =
  let name_coq = Convert.to_list (List.map (fun c -> Extract.byte_of_ascii (Convert.to_ascii c)) (explode name)) in
  let depth_coq = Convert.to_nat depth in
  match Extract.lookup_exported_function name_coq sies with
  | None -> `Error (false, "unknown function `" ^ name ^ "`")
  | Some cfg0 ->
    let (_, i, _) = Convert.from_triple sies in
    let rec f gen cfg =
      (let res = Extract.run_step depth_coq i cfg in
       debug_info verbose (fun () -> Printf.printf "%sstep %d:%s\n%s\n" ansi_bold gen ansi_reset (Convert.from_string (Extract.pp_res_tuple res)));
       match Convert.from_triple res with
       | (_, _, RS_crash crash) ->
         Printf.printf "crash: %s\n" (string_of_crash_reason crash);
         `Ok ()
       | (_, _, RS_break _) ->
         Printf.printf "break!?\n";
         `Ok ()
       | (_, _, RS_return vs) ->
        Printf.printf "returned %s\n" (Convert.from_string (Extract.pp_values vs));
        `Ok ()
       | (s', vs', RS_normal es) ->
         f (gen + 1) (Convert.to_triple (s', vs', es))) in
    debug_info verbose (fun () -> Printf.printf "%sstep %d:%s\n%s\n" ansi_bold 0 ansi_reset (Convert.from_string (Extract.pp_config_tuple cfg0)));
    f 1 cfg0

let run verbose files name depth =
  match Extract.run_parse_module_from_asciis (Convert.to_list (List.concat files)) with
  | None -> `Error (false, "syntax error")
  | Some m ->
    debug_info verbose (fun () -> Printf.printf "parsing successful\n");
    (match Extract.interp_instantiate_wrapper m with
     | None -> `Error (false, "instantiation error")
     | Some (Extract.Pair (store_inst_exps, _)) ->
       debug_info verbose (fun () -> Printf.printf "instantiation successful\n");
       run2 verbose store_inst_exps name depth)

let interpret verbose text no_exec func_name depth srcs =
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
    run verbose files func_name depth
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
  (Term.(ret (const interpret $ verbose $ text $ no_exec $ func_name $ depth $ srcs)),
   Term.info "wasm_interpreter" ~version:"%%VERSION%%" ~doc ~exits ~man ~man_xrefs)

let () = Term.(exit @@ eval cmd)

