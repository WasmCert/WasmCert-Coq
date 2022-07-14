(** a naive functional representation of an array *)
(* (C) J. Pichon - see LICENSE.txt *)

(* this works well when there are few updates *)
Module Type Index_Sig.
Parameter Index : Type.
Parameter index_eqb : Index -> Index -> bool.
Parameter Value : Type.
End Index_Sig.

Module Make (X : Index_Sig).
  Import X.

Inductive array : Type :=
| A_init : Value -> array
| A_update : Index -> Value -> array -> array.

Definition make (v : Value) : array :=
  A_init v.

Fixpoint get (arr : array) (idx : Index) : Value :=
  match arr with
  | A_init a => a
  | A_update idx' a arr' =>
    if index_eqb idx idx' then a
    else get arr' idx
  end.

Definition set (arr : array) (idx : Index) (a : Value) : array :=
  A_update idx a arr.

End Make.

