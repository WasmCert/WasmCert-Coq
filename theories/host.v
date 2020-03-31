(** Axiomatisation of the host. **)
(* (C) M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import common datatypes.

Set Implicit Arguments.

(* TODO
Record host := {
    host_state : eqType
  }.
*)

Parameter host_state : eqType.
Parameter host_function : eqType.

Parameter host_apply : store_record -> function_type -> list value -> (* FIXME: datatypes.host_state -> *) option (store_record * list value).

