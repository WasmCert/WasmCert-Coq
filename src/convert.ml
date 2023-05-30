(* These functions are not to be used when importing [ExtrOcamlBasic] and [ExtrOcamlString] in [extraction.v].
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

let from_ascii (Extract.Ascii (b0, b1, b2, b3, b4, b5, b6, b7)) : char =
  let h b = match b with Extract.True -> 1 | Extract.False -> 0 in
  Char.chr (h b0 + 2 * (h b1 + 2 * (h b2 + 2 * (h b3 + 2 * (h b4 + 2 * (h b5 + 2 * (h b6 + 2 * h b7)))))))

let rec from_string = function
| Extract.EmptyString -> ""
| Extract.String (c, cs) ->
  String.make 1 (from_ascii c) ^ from_string cs

let to_byte_list s =
  let explode s = List.init (String.length s) (String.get s) in
  to_list (List.map (fun c -> Extract.byte_of_ascii (to_ascii c)) (explode s))

let from_pair = function
| Extract.Pair (a, b) -> (a, b)

let to_pair (a, b) = Extract.Pair (a, b)

let from_triple = function
| Extract.Pair (Extract.Pair (a, b), c) -> (a, b, c)

let to_triple (a, b, c) = Extract.Pair (Extract.Pair (a, b), c)
*)

let from_string str = Utils.implode str

let string_of_value =
  Extract.value_rec_safe
    (fun v -> Printf.sprintf "Int32: %s" (from_string (Extract.pp_i32 v)))
    (fun v -> Printf.sprintf "Int64: %s" (from_string (Extract.pp_i64 v)))
    (fun v -> Printf.sprintf "Float32: %s" (from_string (Extract.pp_f32 v)))
    (fun v -> Printf.sprintf "Float64: %s" (from_string (Extract.pp_f64 v)))

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

