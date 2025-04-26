(** Axiomatisation of the host. **)
(* (C) M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From HB Require Import structures.
From Wasm Require Import common datatypes operations typing memory_list.
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

Context `{hfc: host_function_class} `{memory: Memory}.
(** We assume a set of host functions. **)

(** The application of a host function either:
  - returns [Some (st', result)], returning a new Wasm store and a result (which can be [Trap]),
  - diverges, represented as [None].
  This can be non-deterministic. **)

Class host := {
    host_state : eqType (** For the relation-based version, we assume some kind of host state. **) ;
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

(** ** Relation between both versions **)

Section Parameterised.

Context `{ho: host}.

Variable ehost : executable_host.

(* TODO. What we really need is the property with the interactive tree interpretation.
(** Relation between [host] and [executable_host]. **)
Definition host_spec :=
  forall st t h vs st' r,
    host_apply ehost st t h vs = Some (st', r) -> (* FIXME: under the [host_event] monad! *)
    host_application host st t h vs st' r.
*)

End Parameterised.

(** * Extractible module **)

(** The definitions of the previous section are based on dependent types, which are very
  practical to manipulate them in Coq, but do not extract very well.
  The following is an extract-friendly adaptation using modules.
  We also require other useful hypotheses **)

Module Type Executable_Host.

Parameter host_function : Type.
Parameter host_function_eq_dec : forall f1 f2 : host_function, {f1 = f2} + {f1 <> f2}.
Parameter host_event : Type -> Type.
Parameter host_ret : forall t : Type, t -> host_event t.
Parameter host_bind : forall t u : Type, host_event t -> (t -> host_event u) -> host_event u.

#[export]
Instance hfc: host_function_class.
Proof.
  exact (Build_host_function_class host_function_eq_dec).
Defined.

#[export]
Instance memory: Memory := memory_list.Memory_list.

Parameter host_apply : store_record -> function_type -> host_function -> seq value ->
                       host_event (option (store_record * result)).

End Executable_Host.

(** Such a module can easily be converted into an [executable_host] definition. **)

Module convert_to_executable_host (H : Executable_Host).
  
Export H.

Definition host_function_eqb f1 f2 : bool := host_function_eq_dec f1 f2.

Definition host_functionP : Equality.axiom host_function_eqb :=
  eq_dec_Equality_axiom host_function_eq_dec.

HB.instance Definition host_function_eqMixin := hasDecEq.Build host_function host_functionP.

Definition host_monad : Monad host_event := {|
    ret := host_ret ;
    bind := host_bind
  |}.

Definition executable_host_instance : executable_host :=
  make_executable_host host_monad host_apply.

Definition host_functor := Functor_Monad (M := host_monad).

End convert_to_executable_host.


(** * Host instantiations **)

(** ** Dummy host **)

From ExtLib Require Import IdentityMonad.

(** This host provides no function. **)

Module DummyHost <: Executable_Host.

Definition host_function := void.
Definition host_event := ident.
Definition host_ret := @ret _ Monad_ident.
Definition host_bind := @bind _ Monad_ident.

Definition host_function_eq_dec : forall f1 f2 : host_function, {f1 = f2} + {f1 <> f2}.
Proof. decidable_equality. Defined.

#[export]
Instance hfc: host_function_class.
Proof.
  exact (Build_host_function_class host_function_eq_dec).
Defined.

#[export]
Instance memory: Memory := memory_list.Memory_list.

Definition store_record :Type := store_record.

Definition host_apply (_ : store_record) (_ : function_type) :=
  of_void (seq value -> ident (option (store_record * result))).

#[export]
Instance host_instance : host.
Proof.
  by refine {|
      host_state := unit;
      host_application _ _ _ _ _ _ _ := False
    |}.
Defined.

Definition host_application_impl : host_state -> store_record -> function_type -> host_function -> seq value ->
                                   (host_state * option (store_record * result)).
Proof.
  move => ??? hf.
  by refine ((of_void _) hf).
Defined.

Definition host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).
Proof.
  move => ??? hf; by inversion hf.
Defined.

End DummyHost.

Module DummyHosts.

Module Exec := convert_to_executable_host DummyHost.
Export Exec.

End DummyHosts.

