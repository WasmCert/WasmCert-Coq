(** Main file for the Wasm interpreter **)

(*open Convert*)

(** Main function *)
let process_args_and_run verbosity text no_exec error_code_on_crash (srcs: string list) func_name =
  let open Execute.Host in
  let open Execute.Interpreter in
  try
    (** Preparing the files. *)
    let files =
      List.map (fun dest ->
        if not (Sys.file_exists dest) || Sys.is_directory dest then
          invalid_arg (Printf.sprintf "No file %s found." dest)
        else
          let in_channel = open_in_bin dest in
          let s = really_input_string in_channel (in_channel_length in_channel) in
          close_in in_channel;
          s) srcs in
    (** Parsing. *)
    let* m =
      from_out (
        let open Output in
        ovpending verbosity stage "parsing" (fun _ ->
          if text then
            Error "Text mode not yet implemented."
          else
            match Execute.Interpreter.run_parse_module (String.concat "" files) with
            | None -> Error "syntax error"
            | Some m -> (OK m)
            )
            ) in
    (** Running. *)
    if no_exec then
      Output.(
        debug_info verbosity stage (fun _ ->
          "skipping interpretation because of --no-exec.\n") ;
        Execute.Interpreter.pure ()
      )
    else Execute.instantiate_interpret verbosity error_code_on_crash m func_name
  with Invalid_argument msg -> error msg

(** Similar to [process_args_and_run], but differs in the output type. *)
let process_args_and_run_out verbosity text no_exec error_code_on_crash srcs func_name =
  process_args_and_run verbosity text no_exec error_code_on_crash srcs func_name
  |> Execute.Host.to_out |> Output.Out.convert

(** Command line interface *)

open Cmdliner

let verbosity =
  let mk v l doc =
    let doc = "Verbosity level: " ^ doc in
    (v, Arg.info l ~doc) in
  Arg.(value & vflag Output.result Output.[
      mk none ["vn"; "nothing"] "Print nothing" ;
      mk result ["vr"; "result"] "Only print the result" ;
      mk stage ["vs"; "stage"] "Print the stage and the result" ;
      mk intermediate ["vi"; "intermediate"] "Print all intermediate states, without stores" ;
      mk store ["va"; "all"; "store"] "Print everything, including stores" ;
    ])

let text =
  let doc = "Read text format." in
  Arg.(value & flag & info ["text"] ~doc)

let no_exec =
  let doc = "Stop before executing (only go up to typechecking)." in
  Arg.(value & flag & info ["no-exec"] ~doc)

  (*
let interactive =
  let doc = "Interactive execution." in
  Arg.(value & flag & info ["i"; "interactive"] ~doc)
*)
  (*
let fuel =
  let doc = "Specify maximum amount of steps to run." in
  Arg.(value & opt (some int) None & info ["f"; "fuel"] ~doc)
*)
let error_code_on_crash =
  let doc = "Return an error code on crash." in
  Arg.(value & flag & info ["E"; "error-if-crash"] ~doc)

let func_name =
  let doc = "Name of the Wasm function to run." in
  Arg.(value & opt string "start" & info ["r"; "run"] ~docv:"NAME" ~doc)
  

let srcs =
  let doc = "Source file(s) to interpret." in
  let docinfo = 
    Arg.info [] ~docv:"FILE" ~doc:doc in
  Arg.(non_empty & pos_all file [] & docinfo)


let cmd = 
  let doc = "Interpret WebAssembly files" in
  let man_xrefs = [] in
  let exits = Cmd.Exit.defaults in
  let man =
    [ `S Manpage.s_bugs;
      `P "Report them at https://github.com/WasmCert/WasmCert-Coq/issues"; ]
  in
  Cmd.v 
     (Cmd.info "wasm_interpreter" ~version:"c9b010d-dirty" ~doc ~exits ~man ~man_xrefs)
     Term.(ret (const process_args_and_run_out $ verbosity $ text $ no_exec (* $ interactive *) $ error_code_on_crash $ srcs $ func_name ))

  
let () = Stdlib.exit @@ 
   match Cmd.eval_value cmd with
   | Ok _ -> Cmd.Exit.ok
   | Error _ -> Cmd.Exit.some_error
   

