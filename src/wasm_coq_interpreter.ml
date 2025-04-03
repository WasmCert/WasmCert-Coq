(** Main file for the Wasm interpreter **)
open Execute.Interpreter
open Output

(** Trying to guess the module name by the file name provided for the module. *)
let extract_module_name src =
  let name = Filename.basename src in
  if (String.length name >= 5 && String.sub name (String.length name - 5) 5 = ".wasm") then
      String.sub name 0 (String.length name - 5)
  else name

(** Parse a module given the module string. The text flag specifies whether the argument is in binary format or text format. *)
let parse_module verbosity text mstr =
  (** Parsing. *)
  Execute.Host.from_out (
    let open Output in
    ovpending verbosity stage "parsing" (fun _ ->
      if text then
        Error "Text mode not yet implemented."
      else
        match Execute.Interpreter.run_parse_module mstr with
        | None -> Error "error in parsing module"
        | Some m -> OK m
    ))

(* Parse a list of modules. *)
let rec parse_modules_acc verbosity text files acc =
  match files with
  | [] -> pure acc
  | f :: files' ->
    let* m = parse_module verbosity text f in
    parse_modules_acc verbosity text files' (acc @ [m])

let parse_modules verbosity text files =
  parse_modules_acc verbosity text files []


(* Parsing the arguments of a function call in text format. *)
let rec parse_args_acc args acc = 
  (match args with
  | [] -> pure acc
  | a :: args' -> 
    (match Execute.Interpreter.run_parse_arg a with
    | Some a' -> parse_args_acc args' (acc @ [a'])
    | None -> Execute.Host.from_out (Error ("Invalid argument: " ^ a))
    )
  )
 
let parse_args args = 
  parse_args_acc args []

(* Instantiate a sequence of modules with names. *)
let rec instantiate_modules verbosity exts s names modules =
  match (names, modules) with
  | ([], _) -> pure (exts, s)
  | (name :: names', m :: modules') -> 
    debug_info verbosity stage (fun () -> "Processing module: " ^ name ^ "\n");
    let* (exts', s') = Execute.instantiate_host verbosity exts s name m in
      instantiate_modules verbosity exts' s' names' modules'
  | _ -> Execute.Host.from_out (Error ("Invalid module name parsing results"))

(** Main function *)
let process_args_and_run verbosity text no_exec (srcs: string list) func_name src_module_name arg_strings =
  let open Execute.Host in
  let open Execute.Interpreter in
  try
    (** Preparing the files. *)
    (** Each file should contain a single Wasm module binary. The modules will be instantiated by their order. *)
    let files =
      List.map (fun dest ->
        if not (Sys.file_exists dest) || Sys.is_directory dest then
          invalid_arg (Printf.sprintf "No file %s found." dest)
        else
          let in_channel = open_in_bin dest in
          let s = really_input_string in_channel (in_channel_length in_channel) in
          close_in in_channel;
          s) srcs in
    let mnames = List.map extract_module_name srcs in
    let* modules = parse_modules verbosity text files in
    let starting_host_store = Execute.StringMap.empty in
    let starting_store = Execute.Interpreter.empty_store_record in
    let* (exts, s) = instantiate_modules verbosity starting_host_store starting_store mnames modules in
    let* args = parse_args arg_strings in
    (** Running. *)
    if no_exec then
      Output.(
        debug_info verbosity stage (fun _ ->
          "skipping interpretation because of --no-exec.\n") ;
        Execute.Interpreter.pure ()
      )
    else 
      let running_module_name = 
        (if src_module_name = "" then 
          List.hd (List.rev mnames) 
        else src_module_name) in
      let* _ = Execute.invoke_func verbosity exts (s, Extract.empty_frame) args running_module_name func_name in 
    pure ()
  with Invalid_argument msg -> error msg

(** Similar to [process_args_and_run], but differs in the output type. *)
let process_args_and_run_out verbosity text no_exec wast_mode srcs func_name src_module_name args =
  (if wast_mode then 
    (*Output.(
        debug_info verbosity stage (fun _ ->
          "Wast mode not yet implemented .\n") ;
        Execute.Interpreter.pure ()
      )*)
      Execute.Host.error "Wast mode not yet implemented"
else
  process_args_and_run verbosity text no_exec srcs func_name src_module_name args)
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

let func_name =
  let doc = "Name of the Wasm function to run." in
  Arg.(value & opt string "" & info ["r"; "run"] ~docv:"NAME" ~doc)

let module_name = 
  let doc = "Name of the source Wasm module to locate the function. Defaults to the last module. " in
  Arg.(value & opt string "" & info ["m"; "module"] ~docv:"MODULE" ~doc)

let args = 
  let doc = "Arguments to passed in to the function" in
  Arg.(value & opt_all string [] & info ["a"; "arg"] ~docv:"ARG" ~doc)

let wast = 
  let doc = "Running a .wast test suite" in
  Arg.(value & flag & info ["wast"] ~docv:"ARG" ~doc)

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
     Term.(ret (const process_args_and_run_out $ verbosity $ text $ no_exec $ wast $ srcs $ func_name $ module_name $ args ))

  
let () = Stdlib.exit @@ 
   match Cmd.eval_value cmd with
   | Ok _ -> Cmd.Exit.ok
   | Error _ -> Cmd.Exit.some_error
