(** Conversion between OCaml types and the Coq ones. **)

(** Convert [int] to [Extract.nat]. **)
val to_nat : int -> Extract.nat

(** Convert [Extract.nat] to [int]. **)
val from_nat : Extract.nat -> int

(** Convert [Extract.positive] to [int]. **)
val from_positive : Extract.positive -> int

(** Convert [Extract.z] to [int]. **)
val from_z : Extract.z -> int

