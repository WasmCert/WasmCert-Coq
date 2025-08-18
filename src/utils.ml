let string_of_char c = String.make 1 c

let z_of_int x =
  Big_int_Z.big_int_of_int x

let int_of_z z =
  if Big_int_Z.is_int_big_int z then 
    Big_int_Z.int_of_big_int z
else invalid_arg "int_of_z overflow"