(** Axiomatisation of the host. **)
(* (C) M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import common datatypes.
From ExtLib Require Import Monad.

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
    (* FIXME: Should the resulting [host_state] be part of the [option]? *)
  }.

Record monadic_host := {
    host_monad : Type -> Type ;
    host_Monad : Monad host_monad ;
    host_apply : store_record -> host_function -> seq value ->
                 host_monad (option (store_record * result))
  }.

(** We introduce this structure to be able to reason about monads,
  and in particular to be able to relate a monadic interpreter with
  a usual small-step semantics.
  It is based on a special high-order predicate that transpose a
  predicate about inside the monad. **)
Record ReasonMonad m (M : Monad m) := {
    reason_predicate : forall A : Type, (A -> Prop) -> m A -> Prop ;
    reason_predicate_ret : forall A (p : A -> Prop) (a : A), p a -> reason_predicate p (ret a) ;
    reason_predicate_bind : forall A B (p : A -> Prop) (q : B -> Prop) (f : A -> m B) (m : m A),
      (forall a : A, p a -> reason_predicate q (f a)) ->
      reason_predicate p m ->
      reason_predicate q (bind m f)
  }.
Arguments ReasonMonad m {M}.

(** In particular, any injective monad can be reasonned as-is. **)
Program Definition injective_ReasonMonad : forall m (M : Monad m),
  (forall A, injective (ret : A -> m A)) ->
  ReasonMonad m :=
  fun m M I => {|
      reason_predicate := fun A p m => forall r, m = ret r -> p r
    |}.
Next Obligation.
  apply I in H0. by subst.
Qed.
Next Obligation.
  admit (* FIXME: Where are the axioms on [bind]? *)
Qed.

(** Relation between [monadic_host] and [host]. **)

(* TODO *)

End Parameterised.

Arguments host_application [_ _].

Arguments host_return [_ _ _].
Arguments host_bind [_ _ _ _].
Arguments host_apply [_ _].
