
type verbosity = int

let none = 0
let result = 1
let stage = 2
let intermediate = 3
let store = 4

type style = string

(* TODO: use notty rather than this ad-hoc mess *)
let ansi_bold = "\x1b[1m"
let ansi_reset = "\x1b[0m"
let ansi_green = "\x1b[32m"
let ansi_red = "\x1b[31m"

let normal = ansi_reset
let bold = ansi_bold
let green = ansi_green
let red = ansi_red

(** ANSI escape sequence to delete [n] characters. *)
let ansi_delete_chars n =
  "\x1b[" ^ string_of_int n ^ "D"

let debug_info verbosity min_level ?(style=normal) f =
  if verbosity >= min_level then (
    Printf.printf "%s%s%s" style (f ()) ansi_reset;
    flush stdout;
    flush stderr
  )

let debug_info_span verbosity min_level max_level ?(style=normal) f =
  if verbosity <= max_level then debug_info verbosity min_level ~style f

let wait_message verbosity =
  (* yuck *)
  debug_info verbosity 2 (fun () -> Printf.sprintf "...");
  debug_info verbosity 1 (fun () -> Printf.sprintf "%s " (ansi_delete_chars 3));
  debug_info verbosity 2 (fun () -> Printf.sprintf "%s" (ansi_delete_chars 1))

let pending verbosity min_level _ =
  debug_info verbosity min_level (fun _ -> "...") ;
  fun _ -> debug_info verbosity min_level (fun _ -> Printf.sprintf "%s" (ansi_delete_chars 3))

let vpending verbosity min_level f =
  let p = pending verbosity min_level () in
  let v = f () in
  p () ;
  v

let ovpending (verbosity : verbosity) min_level ?(style=normal) msg f =
  debug_info verbosity min_level ~style (fun _ -> msg) ;
  let r = vpending verbosity min_level f in
  let _ =
    match r with
    | `Ok _ -> Printf.printf " %sOK%s\n" ansi_green ansi_reset
    | `Error _ -> Printf.printf " %sfailure%s\n" ansi_red ansi_reset in
  r

