(** Functions to control the program output. *)

type verbosity

val none : verbosity (** Print nothing. *)
val result : verbosity (** Print the result. *)
val stage : verbosity (** Also print state. *)
val intermediate : verbosity (** Also print intermediate states. *)
val store : verbosity (** Also print stores. *)

(** Some styles that can be applied to the text. *)
type style

val normal : style
val bold : style
val green : style
val red : style

(** Given the current verbosity level, the minimum verbosity level required, and a function,
   only call and print the function if the verbosity level enables it. *)
val debug_info : verbosity -> verbosity -> ?style:style -> (unit -> string) -> unit

(** Same as [debug_info], but with an additional maximum verbosity. *)
val debug_info_span : verbosity -> verbosity -> verbosity -> ?style:style -> (unit -> string) -> unit

(* FIXME: @opqrs: this corresponds to your function [terminal_magic], which I’m not sure how to
   document. *)
val wait_message : verbosity -> unit

(** [pending v min ()] prints ["..."] if [v >= min].
   Calling the returned function erase these three dots. *)
val pending : verbosity -> verbosity -> unit -> unit -> unit

(** Same as [pending], but does it during the computation of the prodived function. *)
val vpending : verbosity -> verbosity -> (unit -> 'a) -> 'a

(** Similarly to [ovpending], but the success is provided by the boolean. *)
val bvpending : verbosity -> verbosity -> ?style:style -> string -> (unit -> bool * 'a) -> 'a

(** An output type, returning either a success with a value or an error message. *)
type 'a out =
  | OK of 'a
  | Error of string

(** Same as [vpending], but print the action given with the string, and append an ["OK"]
   or ["failure"] message depending on the function. *)
val ovpending : verbosity -> verbosity -> ?style:style -> string -> (unit -> 'a out) -> 'a out

(** A monad for [out]. *)
module Out : sig

    val ( >>= ) : 'a out -> ('a -> 'b out) -> 'b out
    val ( let* ) : 'a out -> ('a -> 'b out) -> 'b out
    val ( let+ ) : 'a out -> ('a -> 'b) -> 'b out
    val ( and+ ) : 'a out -> 'b out -> ('a * 'b) out
    val pure : 'a -> 'a out

    (** Conversion function to the usual output of Cmdliner. *)
    val convert : 'a out -> [> `Ok of 'a | `Error of bool * string ]

  end

