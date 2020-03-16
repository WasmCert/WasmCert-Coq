
let to_bool = function
  | true -> Extract.True
  | false -> Extract.False

let from_bool = function
  | Extract.True -> true
  | Extract.False -> false

let rec to_list = function
  | [] -> Extract.Nil
  | e :: l -> Extract.Cons (e, to_list l)

let rec from_list = function
  | Extract.Nil -> []
  | Extract.Cons (e, l) -> e :: from_list l

let to_ascii c =
  let c = Char.code c in
  let h i = to_bool ((c land (1 lsl i)) <> 0) in
  Extract.Ascii (h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7)

let rec to_nat = function
  | 0 -> Extract.O
  | n -> Extract.S (to_nat (n - 1))

let rec from_nat = function
  | Extract.O -> 0
  | Extract.S n -> 1 + from_nat n

