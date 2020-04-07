(** Axiomatisation of the host. **)
(* (C) M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import common datatypes.

Set Implicit Arguments.

Section Parameterised.

(** To avoid circular dependencies, we assume the type declared in the [datatypes] module. **)
Variables store_record : Type.

(** We assume a set of host functions. **)
Variable host_function : eqType.

(** We assume some ways to have a way of knowing what is the type of a host function. **)
Hypothesis s_is_hfuncs : store_record -> host_function -> function_type -> Prop. (* FIXME: Way to many circular dependencies here. I suggest to split [datatypes] in two: [datatypes] and [store] (with the function closures and everything). *)

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
      store_record -> host_function -> list value ->
      (option (store_record * list result) -> host_monad A) ->
      host_monad A ;
    (* TODO: induction property stating that if the host keeps its promise about types,
       and that the property is somehow compatible with the state, then we can infer the
       property. *)
  }.

Record host := {
    host_state : eqType ;
    host_application : store_record -> host_function -> list value -> option (store_record * list result) -> Prop
  }.

(* TODO: Relation between [monadic_host] and [host] *)

End Parameterised.

