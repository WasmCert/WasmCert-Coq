(** Axiomatisation of the host. **)
(* (C) M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import common datatypes.
From ITree Require Import ITree ITreeFacts.

Import Monads.

Set Implicit Arguments.
Set Universe Polymorphism.

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
    host_state : eqType (** For the relation-based version, we assume some kind of host state. **) ;
    host_application : host_state -> store_record -> host_function -> seq value ->
                       host_state -> option (store_record * result) -> Prop
                       (** An application of the host function. **)
    (* FIXME: Should the resulting [host_state] be part of the [option]?
      (See https://github.com/rems-project/wasm_coq/issues/16#issuecomment-616402508
       for a discussion about this.) *)
  }.

Record executable_host := {
    host_event : Type -> Type (** The events that the host actions can yield. **) ;
    host_monad : Monad host_event (** They form a monad. **) ;
    host_apply : store_record -> host_function -> seq value ->
                 host_event (option (store_record * result))
                 (** The application of a host function, returning a value in the monad. **)
  }.

(** Relation between [host] and [executable_host]. **)
(* TODO
Record host_spec := {
  }.
 *)

End Parameterised.

Arguments host_application [_ _].
Arguments host_apply [_ _].

