let rec to_nat = function
  | 0 -> Extract.O
  | n when n > 0 -> Extract.S (to_nat (n - 1))
  | _ -> failwith "not a nat"

let rec to_positive z =
  if z < 1 then failwith "not a positive"
  else if z = 1 then Extract.XH
  else 
    let pos' = to_positive (z / 2) in
    let d = z mod 2 in
    if d = 0 then
      Extract.XO pos'
    else 
      Extract.XI pos'

let to_n z =
  if z = 0 then Extract.N0
  else Npos (to_positive z)

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

let from_n = function
  | Extract.N0 -> 0
  | Extract.Npos p -> from_positive p