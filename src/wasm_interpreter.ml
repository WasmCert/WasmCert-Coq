(** Main file for the Wasm interpreter **)

(** Convert a string to a list of characters. *)
let explode s = List.init (String.length s) (String.get s)

(** Given the first part of a configuration tuple [Extract.((store_record, value0 list) prod)],
   run it. *)
let run verbose sies (name : string) (depth : int) =
  let print_step gen tuple =
    Printf.printf "%sstep %d:%s\n%s\n%!"
      (Convert.from_string (Extract.ansi_bold))
      gen
      (Convert.from_string (Extract.ansi_reset))
      (Convert.from_string tuple) in
  let name' =
    Convert.to_list (List.map (fun c ->
      Extract.byte_of_ascii (Convert.to_ascii c)) (explode name)) in
  let depth' = Convert.to_nat depth in
  match Extract.lookup_exported_function name' sies with
  | Extract.None -> `Error (false, "unknown function `" ^ name ^ "`")
  | Extract.Some cfg0 ->
    let Extract.Pair (Extract.Pair (_, i), _) = sies in
    let rec f gen cfg =
      (let res = Extract.run_step depth' i cfg in
       if verbose then print_step gen (Extract.pp_res_tuple res);
       match res with
       | Extract.(Pair (Pair (_, _), RS_crash _)) -> `Error (false, "crash")
       | Extract.(Pair (Pair (_, _), RS_break _)) -> `Error (false, "break")
       | Extract.(Pair (Pair (_, _), RS_return vs)) ->
         let vs = Convert.from_list vs in
         `Ok (Printf.printf "%s" (String.concat ", " (List.map Convert.string_of_value vs)))
       | Extract.(Pair (Pair (s', vs'), RS_normal es)) ->
         (** The execution must keep on. *)
         f (gen + 1) (Extract.Pair (Extract.Pair (s', vs'), es))) in
    if verbose then print_step 0 (Extract.pp_config_tuple cfg0);
    f 1 cfg0

(** Given the Wasm parsed program (currently [Extract.module0] in the extraction,
   instantiate and run it. *)
let instantiate_and_run m verbose quiet name depth =
  if not quiet then Printf.printf "Instantiating… ";
  match Extract.interp_instantiate_wrapper m with
  | Extract.None -> `Error (false, "instantiation error")
  | Extract.Some (Extract.Pair (store_inst_exps, _)) ->
    if not quiet then Printf.printf "Done.\n%!";
    run verbose store_inst_exps name depth

(** The function called from [Cmdliner]. *)
let interpret verbose quiet text no_exec func_name depth srcs =
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
    if not quiet then Printf.printf "Parsing… ";
    let m =
      if text then
        invalid_arg "Text mode not yet implemented."
      else
        match Extract.run_parse_module_from_asciis (Convert.to_list (List.concat files)) with
        | Extract.None -> invalid_arg "syntax error"
        | Extract.Some m -> m in
    if not quiet then Printf.printf "Done.\n%!";
    (** Running. *)
    if no_exec then
      (if not quiet then Printf.printf "Skipping the execution because of the --no-exec argument.\n%!";
       `Ok ())
    else instantiate_and_run m verbose quiet func_name depth
  with Invalid_argument msg -> `Error (false, msg)

(** Command line interface *)

open Cmdliner

let verbose =
  let doc = "Print intermediate states." in
  Arg.(value & flag & info ["v"; "verbose"] ~doc)

let quiet =
  let doc = "Do not print what the interpreter is doing as it does it." in
  Arg.(value & flag & info ["q"; "quiet"] ~doc)

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
  (Term.(ret (const interpret $ verbose $ quiet $ text $ no_exec $ func_name $ depth $ srcs)),
   Term.info "wasm_interpreter" ~version:"%%VERSION%%" ~doc ~exits ~man ~man_xrefs)

let () = Term.(exit @@ eval cmd)

