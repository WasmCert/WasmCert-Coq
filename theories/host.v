(** Axiomatisation of the host. **)
(* (C) M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import common datatypes.
From Prelude Require Import Classes.

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
    host_monad : Type -> Type ;
    host_Monad :> Monad host_monad ;
    host_apply : store_record -> host_function -> seq value ->
                 host_monad (option (store_record * result))
  }.

Global Instance monadic_host_Monad : forall mh, Monad (host_monad mh).
Proof. move=> mh. exact mh. Defined.

(** We introduce this structure to be able to reason about monads,
  and in particular to be able to relate a monadic interpreter with
  a usual small-step semantics.
  It is based on a special high-order predicate that transpose a
  predicate about inside the monad. **)
Class ReasonMonad m (M : Monad m) := {
    reason_predicate : forall A : Type, (A -> Prop) -> m A -> Prop ;
    reason_predicate_pure : forall A (p : A -> Prop) (a : A), p a -> reason_predicate p (pure a) ;
    reason_predicate_bind : forall A B (p : A -> Prop) (q : B -> Prop) (f : A -> m B) (m : m A),
      (forall a : A, p a -> reason_predicate q (f a)) ->
      reason_predicate p m ->
      reason_predicate q (m >>= f)%monad
  }.
Arguments ReasonMonad m {M}.

(** In particular, some monads can be reversed. **)
Class ReversibleMonad m (M : Monad m) := {
    reversible_pure : forall A, injective (pure (a := _) : A -> m A) ;
    reversible_bind : forall A B (f : A -> m B) (m : m A) (b : B),
      (m >>= f)%monad = pure b ->
      exists a, m = pure a /\ f a = pure b
  }.
Arguments ReversibleMonad m {M}.

(** Any reversible monad comes with a natural way to reason on it. **)
Instance ReversibleMonad_ReasonMonad : forall m (M : Monad m),
  ReversibleMonad m ->
  ReasonMonad m.
Proof.
  move=> m M RM.
  refine {|
      reason_predicate := fun A p m => forall r, m = pure r -> p r
    |}.
  - move=> > ? > H. apply reversible_pure in H => //. by subst.
  - move=> > Rf Rp > E. apply reversible_bind in E => //. move: E => [a [E1 E2]].
    apply: Rf E2. by apply: Rp E1.
Defined.

(** Relation between [monadic_host] and [host]. **)
Record monad_host_match (h : host) (mh : monadic_host) := {
    host_reason : ReasonMonad (host_monad mh)
    (* TODO: Can we make it a reader monad just there? *)
  }.

End Parameterised.

Arguments host_application [_ _].
Arguments host_apply [_ _].

