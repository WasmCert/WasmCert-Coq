(** Axiomatisation of the host. **)
(* (C) M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import common datatypes.

Set Implicit Arguments.

Section Parameterised.

(** We assume a set of host functions. **)
Variable host_function : Type.

Let store_record := store_record host_function.

(** The application of a host function either:
  - returns a result [Some (st', result)], containing a new store and a result (which can be [Trap]),
  - diverges, represented as [None].
  This can be non-deterministic. **)

(** We provide two versions of the host.
  One computable based on the [host_apply] monadic binder, to be used in the interpreter,
  and one based on a relation, to be used in the operational semantics. **)

Record monadic_host := {
    host_monad : Type -> Type ;
    host_apply : forall A : Type,
      store_record -> host_function -> seq value ->
      (option (store_record * result) -> host_monad A) ->
      host_monad A ;
    (* FIXME: Should it be defined after the typing, to get some notions of correctness? *)
  }.

Record host := {
    host_state : eqType ;
    host_application : host_state -> store_record -> host_function -> seq value ->
                       host_state -> option (store_record * result) -> Prop
  }.

(* TODO: Relation between [monadic_host] and [host]. *)

End Parameterised.

