(** Conversion between OCaml types and the Coq ones. **)

(** Convert [bool] to [Extract.bool]. **)
val to_bool : bool -> Extract.bool

(** Convert [Extract.bool] to [bool]. **)
val from_bool : Extract.bool -> bool

(** Convert [list] to [Extract.list]. **)
val to_list : 'a list -> 'a Extract.list

(** Convert [Extract.list] to [list]. **)
val from_list : 'a Extract.list -> 'a list

(** Convert [char] to [Extract.ascii]. **)
val to_ascii : char -> Extract.ascii

(** Convert [Extract.ascii] to [char]. **)
val from_ascii : Extract.ascii -> char

(** Convert [Extract.string] to [string]. **)
val from_string : Extract.string -> string

(** Convert [int] to [Extract.nat]. **)
val to_nat : int -> Extract.nat

(** Convert [Extract.nat] to [int]. **)
val from_nat : Extract.nat -> int

val from_pair : ('a, 'b) Extract.prod -> ('a * 'b)

val to_pair : ('a * 'b) -> ('a, 'b) Extract.prod

val from_triple : (('a, 'b) Extract.prod, 'c) Extract.prod -> ('a * 'b * 'c)

val to_triple : ('a * 'b * 'c) -> (('a, 'b) Extract.prod, 'c) Extract.prod

(** Convert [Extract.positive] to [int]. **)
val from_positive : Extract.positive -> int

(** Convert [Extract.z] to [int]. **)
val from_z : Extract.z -> int

(** Pretty-print a value. *)
val string_of_value : Extract.value0 -> string

