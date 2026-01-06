(** Axiomatisation of the host. **)
(* (C) M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From HB Require Import structures.
From Wasm Require Import common datatypes operations typing memory.
From ExtLib Require Import Structures.Monad.

(* XXX unused? *)
(* Import Monads. *)

Set Implicit Arguments.

(** * General host definitions **)

(** We provide two versions of the host.
  One based on a relation, to be used in the operational semantics,
  and one computable based on the [host_monad] monad, to be used in the interpreter.
  There is no host state in the host monad: it is entirely caught by the (state) monad. **)

(** ** Predicate Host **)

(** We start with a host expressed as a predicate, useful for proofs. **)

Section Predicate.

Context `{hfc: host_function_class} `{memory: BlockUpdateMemory}.
(** We assume a set of host functions. **)

(** The application of a host function either:
  - returns [Some (st', result)], returning a new Wasm store and a result (which can be [Trap]),
  - diverges, represented as [None]
  This can be non-deterministic. **)

Class host := {
    host_state : Type (** For the relation-based version, we assume some kind of host state. **) ;
    host_application : host_state -> store_record -> function_type -> host_function -> seq value ->
                       host_state -> option (store_record * result) -> Prop
                       (** An application of the host function. **) ;

    host_application_extension : forall s t st h vs s' st' r,
      host_application s st t h vs s' (Some (st', r)) ->
      store_extension st st' (** The returned store must be an extension of the original one. **) ;
    host_application_typing : forall s t st h vs s' st' r,
      host_application s st t h vs s' (Some (st', r)) ->
      store_typing st ->
      store_typing st' (** [host_application] preserves store typing. **) ;
    host_application_respect : forall s t1s t2s st h vs s' st' r,
      values_typing st vs t1s ->
      host_application s st (Tf t1s t2s) h vs s' (Some (st', r)) ->
      result_types_agree st' t2s r (** [host_application] respects types. **)
  }.

End Predicate.


(*
(** ** Executable Host **)

(** We start with a host expressed as a predicate, useful for proofs. **)

Section Executable.

Context `{hfc: host_function_class} `{memory: Memory}.

Class executable_host := make_executable_host {
    host_event : Type -> Type (** The events that the host actions can yield. **) ;
    host_monad : Monad host_event (** They form a monad. **) ;
    host_apply : store_record -> function_type -> host_function -> seq value ->
                 host_event (option (store_record * result))
                 (** The application of a host function, returning a value in the monad. **)
  }.

End Executable.

Arguments host_apply [_ _].
*)
