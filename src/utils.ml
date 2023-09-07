let string_of_char c = String.make 1 c

let explode s =
  List.init (String.length s) (String.get s)

let implode l = String.concat "" (List.map string_of_char l)
