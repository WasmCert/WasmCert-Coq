(* Some extra operations on lists. *)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

Set Implicit Arguments.

Require Import List.

(** Given list of option types, check that all options are [Some]
   and return the corresponding list of values. **)
Fixpoint those0 {A} (l : list (option A)) : option (list A) :=
  match l with
  | nil => Some nil
  | None :: xs => None
  | (Some y) :: xs =>
    option_map (fun ys => y :: ys) (those0 xs)
  end.

Local Fixpoint those_aux {A} (acc : option (list A)) (l : list (option A)) : option (list A) :=
  match acc with
  | None => None
  | Some ys_rev =>
    match l with
    | nil => Some ys_rev
    | None :: xs => None
    | Some y :: xs =>
      those_aux (Some (y :: ys_rev)) xs
    end
  end.

(** A tail-recursive variant of [those0]. **)
Definition those {A} (l : list (option A)) : option (list A) :=
  match those_aux (Some nil) l with
  | None => None
  | Some l => Some (List.rev l)
  end.

Local Lemma those0_None : forall A (l : list (option A)),
  In None l <-> those0 l = None.
Proof.
  induction l as [|o l]; simpl.
  - split; inversion 1.
  - destruct o as [a|]; split; auto.
    + rewrite IHl. intros [?|E]; [discriminate|]. rewrite E. auto.
    + destruct those0; simpl; try discriminate. rewrite IHl. auto.
Qed.

Local Lemma those_aux_None : forall A (la : list A) l,
  In None l <-> those_aux (Some la) l = None.
Proof.
  intros A la l. generalize la. clear la. induction l as [|o l]; intros la; simpl.
  - split; inversion 1.
  - destruct o as [a|].
    + rewrite <- IHl. split; auto. intros [?|?]; [discriminate|auto].
    + split; auto.
Qed.

Local Lemma cons_app : forall A (a : A) l, a :: l = (a :: nil) ++ l.
Proof. reflexivity. Qed.

Local Lemma those_those0_gen : forall A l (la : list A),
  Forall (fun o : option A => o <> None) l ->
  exists rl rl',
    those0 l = Some rl /\ those_aux (Some la) l = Some rl' /\
    List.rev la ++ rl = List.rev rl'.
Proof.
  induction l; intros la F.
  - repeat eexists. rewrite app_nil_r. reflexivity.
  - inversion F. subst.
    destruct a as [a|]; try solve [ exfalso; auto ].
    edestruct IHl as (rl&rl'&E1&E2&E3); auto.
    repeat eexists.
    + simpl. rewrite E1. reflexivity.
    + simpl. rewrite E2. reflexivity.
    + rewrite <- E3. rewrite cons_app with (l := rl). rewrite cons_app with (l := la).
      rewrite rev_app_distr. rewrite <- app_assoc. reflexivity.
Qed.

(** [those0] and [those] are indeed equivalent. **)
Lemma those_those0 : forall A (l : list (option A)),
  those0 l = those l.
Proof.
  intros A l. unfold those.
  destruct (Forall_Exists_dec (fun o => o <> None)
              (fun x => ltac:(destruct x; auto; left; discriminate)) l) as [d|d].
  - eapply those_those0_gen in d. destruct d as (rl&rl'&E1&E2&E3).
    rewrite E1. rewrite E2. rewrite <- E3. reflexivity.
  - rewrite Exists_exists in d. destruct d as (x&I&E). destruct x.
    + exfalso. apply E. discriminate.
    + set (I' := I). clearbody I'.
      rewrite those0_None in I. rewrite I.
      rewrite those_aux_None in I'. rewrite I'.
      reflexivity.
Qed.


From ITree Require ITree ITreeFacts.

Section Monad.

Import ITree ITreeFacts.
Import Monads.
Import MonadNotation.

(** Let us assume a monad. **)
Variable m : Type -> Type.
Context {M : Monad m}.

(** Calls a function to each of the elements of a list, bindings the results into a new list. **)
Fixpoint bind_list0 {A B} (f : A -> m B) (l : list A) : m (list B) :=
  match l with
  | nil => ret nil
  | a :: l =>
    r <- f a ;;
    l' <- bind_list0 f l ;;
    ret (r :: l')
  end.

Fixpoint bind_list_aux {A B} (f : A -> m B) acc (l : list A) : m (list B) :=
  match l with
  | nil => ret (List.rev acc)
  | a :: l =>
    r <- f a ;;
    bind_list_aux f (r :: acc) l
  end.

(** A tail-recursive version of [bind_list0]. **)
Definition bind_list {A B} (f : A -> m B) :=
  bind_list_aux f nil.

End Monad.
