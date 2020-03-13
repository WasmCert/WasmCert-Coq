(** Main file for the Wasm interpreter **)

(** Converts a [bool] to [Parse_wasm.bool]. **)
let to_bool = function
  | true -> Parse_wasm.True
  | false -> Parse_wasm.False

(** Converts a [list] to [Parse_wasm.list]. **)
let rec to_list = function
  | [] -> Parse_wasm.Nil
  | e :: l -> Parse_wasm.Cons (e, to_list l)

(** Converts a [char] to [Parse_wasm.ascii]. **)
let to_ascii c =
  let c = Char.code c in
  let h i = to_bool ((c land (1 lsl i)) <> 0) in
  Parse_wasm.Ascii (h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7)

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
            | Some c -> aux (to_ascii c :: acc)
            | None ->
              close_in in_channel ;
              List.rev acc in
          aux []) srcs in
    match Parse_wasm.parse_wasm (to_list (List.concat files)) with
    | None -> `Error (false, "Syntax error")
    | Some e -> `Ok (Printf.printf "Parsing successful") (* TODO: Actually run something. *)
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
      `P "Report them at https://github.com/rems-project/wasm_coq/issues"; ]
  in
  (Term.(ret (const interpret $ verbose $ text $ no_exec $ srcs $ fname)),
   Term.info "wasm_interpreter" ~version:"%%VERSION%%" ~doc ~exits ~man ~man_xrefs)

let () = Term.(exit @@ eval cmd)

