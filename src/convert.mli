(** Conversion between OCaml types and the Coq ones. **)

(** Converts [bool] to [Extract.bool]. **)
val to_bool : bool -> Extract.bool

(** Converts [Extract.bool] to [bool]. **)
val from_bool : Extract.bool -> bool

(** Converts [list] to [Extract.list]. **)
val to_list : 'a list -> 'a Extract.list

(** Converts [Extract.list] to [list]. **)
val from_list : 'a Extract.list -> 'a list

(** Converts [char] to [Extract.ascii]. **)
val to_ascii : char -> Extract.ascii

(** Converts [Extract.ascii] to [char]. **)
val from_ascii : Extract.ascii -> char

(** Converts [Extract.string] to [string]. **)
val from_string : Extract.string -> string

(** Converts [int] to [Extract.nat]. **)
val to_nat : int -> Extract.nat

(** Converts [Extract.nat] to [int]. **)
val from_nat : Extract.nat -> int

