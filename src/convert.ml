let rec to_nat = function
  | 0 -> Extract.O
  | n when n > 0 -> Extract.S (to_nat (n - 1))
  | _ -> failwith "not a nat"

let rec from_nat = function
  | Extract.O -> 0
  | Extract.S n -> 1 + from_nat n

let z_of_int x =
  Big_int_Z.big_int_of_int x

let int_of_z z =
  if Big_int_Z.is_int_big_int z then 
    Big_int_Z.int_of_big_int z
else invalid_arg "int_of_z overflow"