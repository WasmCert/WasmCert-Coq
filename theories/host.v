(** Axiomatisation of the host. **)
(* (C) M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import common datatypes.
From Mon.sprop Require Import SPropMonadicStructures.

Set Implicit Arguments.

Section Parameterised.

(** We assume a set of host functions. **)
Variable host_function : Type.

Let store_record := store_record host_function.

(** The application of a host function either:
  - returns [Some (st', result)], returning a new Wasm store and a result (which can be [Trap]),
  - diverges, represented as [None].
  This can be non-deterministic. **)

(** We provide two versions of the host.
  One based on a relation, to be used in the operational semantics,
  and one computable based on the [host_monad] monad, to be used in the interpreter.
  There is no host state in the host monad: it is entirely caught by the (state) monad. **)

Record host := {
    host_state : eqType ;
    host_application : host_state -> store_record -> host_function -> seq value ->
                       host_state -> option (store_record * result) -> Prop
    (* FIXME: Should the resulting [host_state] be part of the [option]?
      (See https://github.com/rems-project/wasm_coq/issues/16#issuecomment-616402508
       for a discussion about this.) *)
  }.

Record monadic_host := {
    host_monad :> Monad ;
    host_apply : store_record -> host_function -> seq value ->
                 host_monad (option (store_record * result))
  }.

(** Relation between [monadic_host] and [host]. **)
Record monadic_host_spec := {
    (** The specification monad used to specify the program. **)
    monadic_host_spec_monad :> OrderedMonad
  }.

End Parameterised.

Arguments host_application [_ _].
Arguments host_apply [_ _].

