type 'a t
val length  : 'a t -> Big_int_Z.big_int
val get     : 'a t -> Big_int_Z.big_int -> 'a
val set     : 'a t -> Big_int_Z.big_int -> 'a -> 'a t

val set_gen : 'a t -> Big_int_Z.big_int -> Big_int_Z.big_int -> (Big_int_Z.big_int -> 'a) -> 'a t
(** [set_gen p start_pos block_len generator] returns a new persistent array
    based on [p] where the range of length [block_len] starting at [start_pos]
    is updated by calling [generator] for each index 0 to [block_len - 1].
    [block_len] must be greater than 0. *)

val default : 'a t -> 'a
val make    : Big_int_Z.big_int -> 'a -> 'a t
val make_copy    : Big_int_Z.big_int -> 'a -> 'a t -> Big_int_Z.big_int -> 'a t
val copy    : 'a t -> 'a t