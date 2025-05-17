(** Convert [int] to [Extract.nat]. **)
val to_nat : int -> Extract.nat

(** Convert [int] to [Extract.positive]. **)
val to_positive : int -> Extract.positive

(** Convert [int] to [Extract.n]. **)
val to_n : int -> Extract.n

(** Convert [Extract.nat] to [int]. **)
val from_nat : Extract.nat -> int

(** Convert [Extract.positive] to [int]. *)
val from_positive : Extract.positive -> int

(** Convert [Extract.z] to [int]. *)
val from_z : Extract.z -> int

(** Convert [Extract.n] to [int]. *)
val from_n : Extract.n -> int


