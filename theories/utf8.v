(* utf8 validity for strings *)

From Coq Require Import Strings.Byte BinNums List NArith.

Section utf8.

Local Open Scope N_scope.
Local Open Scope bool_scope.

(* Check if a byte is a continuation byte (10xxxxxx) *)
Definition is_cont (b : byte) : bool :=
  let n := to_N b in (128 <=? n) && (n <=? 191).

(* Convert N to lower 6 bits (used for continuation bytes) *)
Definition lower_6 (n : N) := N.land n 63.

Notation " x << e " := (N.shiftl x e) (at level 5).

Fixpoint utf8_valid (bs : list byte) : bool :=
  match bs with
  | nil => true
  | b :: bs' =>
      let n := to_N b in
      if n <=? 127 then
        utf8_valid bs'
      else if (192 <=? n) && (n <=? 223) then
             match bs' with
             | b1 :: bs'' =>
                 if is_cont b1 then
                   let n1 := lower_6 (to_N b1) in
                   let cp := ((n - 192) << 6) + n1 in
                   if cp <? 128 then false else utf8_valid bs''
                 else false
             | _ => false
             end
           else if (224 <=? n) && (n <=? 239) then
                  match bs' with
                  | b1 :: b2 :: bs'' =>
                      if is_cont b1 && is_cont b2 then
                        let n1 := lower_6 (to_N b1) in
                        let n2 := lower_6 (to_N b2) in
                        let cp := ((n - 224) << 12) + (n1 << 6) + n2 in
                        if cp <? 2048 then false
                        else if (55296 <=? cp) && (cp <=? 57343) then false
                             else utf8_valid bs''
                      else false
                  | _ => false
                  end
                else if (240 <=? n) && (n <=? 247) then
                       match bs' with
                       | b1 :: b2 :: b3 :: bs'' =>
                           if is_cont b1 && is_cont b2 && is_cont b3 then
                             let n1 := lower_6 (to_N b1) in
                             let n2 := lower_6 (to_N b2) in
                             let n3 := lower_6 (to_N b3) in
                             let cp := ((n - 240) << 18) + (n1 << 12) + (n2 << 6) + n3 in
                             if cp <? 65536 then false
                             else if (1114111 <? cp) then false
                                  else utf8_valid bs''
                           else false
                       | _ => false
                       end
                     else false
  end.

End utf8.
