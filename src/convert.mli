(** Conversion between OCaml types and the Coq ones.
   This module is mainly used by [Shim]. *)

(* These functions are not to be used when importing [ExtrOcamlBasic] and [ExtrOcamlString] in [extraction.v].
(** Convert [bool] to [Extract.bool]. *)
val to_bool : bool -> Extract.bool

(** Convert [Extract.bool] to [bool]. *)
val from_bool : Extract.bool -> bool

(** Convert [list] to [Extract.list]. *)
val to_list : 'a list -> 'a Extract.list

(** Convert [Extract.list] to [list]. *)
val from_list : 'a Extract.list -> 'a list

(** Convert [char] to [Extract.ascii]. *)
val to_ascii : char -> Extract.ascii

(** Convert [Extract.ascii] to [char]. *)
val from_ascii : Extract.ascii -> char

(** Convert [Extract.string] to [string]. *)
val from_string : Extract.string -> string

(** Convert [string] to [Extract.byte Extract.list]. *)
val to_byte_list : string -> Extract.byte Extract.list

(** Convert extracted pairs to OCaml pairs. *)
val from_pair : ('a, 'b) Extract.prod -> ('a * 'b)

(** Convert OCaml pairs to extracted pairs. *)
val to_pair : ('a * 'b) -> ('a, 'b) Extract.prod

(** Same as [from_pair] but for triples. *)
val from_triple : (('a, 'b) Extract.prod, 'c) Extract.prod -> ('a * 'b * 'c)

(** Same as [to_pair] but for triples. *)
val to_triple : ('a * 'b * 'c) -> (('a, 'b) Extract.prod, 'c) Extract.prod
*)

(** Convert [int] to [Extract.nat]. **)
val to_nat : int -> Extract.nat

(** Convert [Extract.nat] to [int]. **)
val from_nat : Extract.nat -> int

(** Convert [Extract.positive] to [int]. *)
val from_positive : Extract.positive -> int

(** Convert [Extract.z] to [int]. *)
val from_z : Extract.z -> int

(** Print a Wasm value. *) (* TODO: Removed, now subsumed by [Execute.Interpreter.pp_values]. *)
val string_of_value : Extract.value0 -> string

