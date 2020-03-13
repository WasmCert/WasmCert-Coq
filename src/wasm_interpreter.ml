(** Main file for the Wasm interpreter **)

let cp verbose recurse force srcs dest =
  if List.length srcs > 1 &&
  (not (Sys.file_exists dest) || not (Sys.is_directory dest))
  then
    `Error (false, dest ^ " is not a directory")
  else
    `Ok (Printf.printf
     "verbose = %B\nrecurse = %B\nforce = %B\nsrcs = %s\ndest = %s\n"
      verbose recurse force (String.concat ", " srcs) dest)

let interpret_wasm verbose text no_exec srcs fname =
  (* TODO: do something *)
  `Ok (Printf.printf
    "verbose = %B\ntext = %B\nno_exec = %B\nsrcs = %s\nfname = %s\n"
    verbose text no_exec (String.concat ", " srcs) fname)

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
  (Term.(ret (const cp $ verbose $ text $ no_exec $ srcs $ fname)),
   Term.info "wasm_interpreter" ~version:"%%VERSION%%" ~doc ~exits ~man ~man_xrefs)

let () = Term.(exit @@ eval cmd)

