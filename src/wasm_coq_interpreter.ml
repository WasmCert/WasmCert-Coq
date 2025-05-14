(** Main file for the Wasm interpreter **)

(** Main function *)
let process_args_and_run verbosity text no_exec max_call_depth srcs func_name src_module_name arg_strings =
  let open Execute.Host in
  let open Execute.Interpreter in
  let open Parse in
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
    let starting_host_store = (Execute.StringMap.empty, Execute.StringMap.empty) in
    let starting_store = empty_store_record in
    let* (exts, s) = Execute.instantiate_modules verbosity starting_host_store starting_store mnames modules in
    let* args = parse_args arg_strings in
    (** Running. *)
    if no_exec then
      Output.(
        debug_info verbosity stage (fun _ ->
          "skipping interpretation because of --no-exec.\n") ;
        pure ()
      )
    else 
      let running_module_name = 
        (if src_module_name = "" then 
          List.hd (List.rev mnames) 
        else src_module_name) in
      let* ret = Execute.invoke_func verbosity exts (s, Extract.empty_frame) args running_module_name func_name max_call_depth in 
        Execute.print_invoke_result verbosity ret;
      pure ()
  with Invalid_argument msg -> error msg

(* Reference interpreter allows only 256 nested calls:
https://github.com/WebAssembly/spec/blob/main/interpreter/main/flags.ml
 *)
let wast_budget = 256

(** Similar to [process_args_and_run], but differs in the output type. *)
let process_args_and_run_out verbosity text no_exec wast_mode wast_timeout max_call_depth srcs func_name src_module_name args =
  (if wast_mode then 
    let files =
      List.map (fun dest ->
        if not (Sys.file_exists dest) || Sys.is_directory dest then
          invalid_arg (Printf.sprintf "No file %s found." dest)
        else
          let in_channel = open_in_bin dest in
          let s = really_input_string in_channel (in_channel_length in_channel) in
          close_in in_channel;
          s) srcs in
    match files with
    | [] -> Execute.Host.error "No wast file provided"
    | [scriptstr] -> 
      let wast_max_call_depth = if max_call_depth = -1 then wast_budget else max_call_depth in
        Wast_execute.run_wast_string verbosity wast_timeout wast_max_call_depth scriptstr
    | _ -> Execute.Host.error "Wast mode does not support multiple files"
else
  process_args_and_run verbosity text no_exec max_call_depth srcs func_name src_module_name args)
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
let max_call_depth =
  let doc = "Specify maximum amount of steps to run." in
  Arg.(value & opt (some int) None & info ["f"; "max_call_depth"] ~doc)
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

let wast_timeout = 
  let doc = "Set the timeout for running .wast test suites" in
  Arg.(value & opt int 10 & info ["t"] ~docv:"ARG" ~doc)

let max_call_depth = 
  let doc = "Set the maximum depths of call stack allowed in the interpreter (-1 for unlimited)" in
  Arg.(value & opt int (-1) & info ["f"] ~docv:"FUEL" ~doc)

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
     Term.(ret (const process_args_and_run_out $ verbosity $ text $ no_exec $ wast $ wast_timeout $ max_call_depth $ srcs $ func_name $ module_name $ args ))

  
let () = Stdlib.exit @@ 
   match Cmd.eval_value cmd with
   | Ok _ -> Cmd.Exit.ok
   | Error _ -> Cmd.Exit.some_error
