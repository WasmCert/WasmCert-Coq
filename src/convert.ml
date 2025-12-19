let rec to_nat = function
  | 0 -> Extract.O
  | n when n > 0 -> Extract.S (to_nat (n - 1))
  | _ -> failwith "not a nat"

let rec from_nat = function
  | Extract.O -> 0
  | Extract.S n -> 1 + from_nat n