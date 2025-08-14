(** Convert [int] to [Extract.nat]. **)
val to_nat : int -> Extract.nat

(** Convert [Extract.nat] to [int]. **)
val from_nat : Extract.nat -> int

val z_of_int: int -> Big_int_Z.big_int

val int_of_z: Big_int_Z.big_int -> int