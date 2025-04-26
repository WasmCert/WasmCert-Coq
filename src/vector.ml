open Containers
open CCVector

let vec_make b n = CCVector.make b n

let vec_length v = CCVector.length v

let vec_grow len_delta v = 
  let tail = vec_make 0 len_delta in
  CCVector.append v tail;
  v

let vec_lookup i v =
  CCVector.get v i

let vec_update i x v =
  CCVector.set v i x;
  v

let vec_eq v1 v2 = 
  v1 = v2
