


let rec to_nat = function
  | 0 -> Extract.O
  | n when n > 0 -> Extract.S (to_nat (n - 1))
  | _ -> failwith "not a nat"

let rec from_nat = function
  | Extract.O -> 0
  | Extract.S n -> 1 + from_nat n

let rec from_positive = function
  | Extract.XH -> 1
  | Extract.XO p -> 2 * from_positive p
  | Extract.XI p -> 1 + 2 * from_positive p

let from_z = function
  | Extract.Z0 -> 0
  | Extract.Zpos p -> from_positive p
  | Extract.Zneg p -> - from_positive p

