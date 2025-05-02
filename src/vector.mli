open Containers
open CCVector

module type Byte = sig
  type t
  val default: t
  val eq_dec: t -> t -> bool
end

module type Memory = sig
  type elem_t = Byte.t

  type mem_t = byte vector

  val mem_make: int -> elem_t -> mem_t
  val mem_length: mem_t -> int
  val mem_lookup: int -> mem_t -> elem_t option
  val mem_grow: int -> mem_t -> mem_t
  val mem_update: int -> elem_t -> mem_t -> mem_t option
  val mem_eq_dec: mem_t -> mem_t -> bool
end

module Memory_vec (b: Byte) : Memory with type byte = b.t
