(* A wrapper file for the custom Parray module to take arguments of type `Z.t` instead of OCaml's `int`.
   Note that this does not magically allow the 31st bit to be used on 32-bit OCaml distributions.
   It is rather for connecting the unbounded integer types in the extracted code to the `int`
   length parameter requried by OCaml's `Array.make`.
*)

type 'a t = 'a Parray.t

let z_of_int x =
  Big_int_Z.big_int_of_int x

let int_of_z z =
  if Big_int_Z.is_int_big_int z then 
    Big_int_Z.int_of_big_int z
else invalid_arg "int_of_z overflow"

let length a = z_of_int (Parray.length a)
let make z a = Parray.make (int_of_z z) a

let copy = Parray.copy

let make_copy n init arr initlen =
  Parray.make_copy (int_of_z n) init arr (int_of_z initlen)

let get a z = Parray.get a (int_of_z z)

let set a z v = Parray.set a (int_of_z z) v

let set_gen a z len gen =
  Parray.set_gen a (int_of_z z) (int_of_z len) (fun id -> gen (z_of_int id))

let default = Parray.default