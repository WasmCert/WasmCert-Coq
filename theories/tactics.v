Require Import common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import properties.

(** Simplify an hypothesis, possibly rewriting it everywhere. **)
Ltac simplify_hypothesis Hb :=
  repeat rewrite length_is_size in Hb;
  repeat match type of Hb with
  | is_true (es_is_trap _) => move/es_is_trapP: Hb => Hb
  | is_true (const_list (_ :: _)) => rewrite const_list_cons in Hb
  | ?b = true => fold (is_true b) in Hb
  | (_ == _) = false => move/eqP in Hb
  | context C [size (rev _)] => rewrite size_rev in Hb
  | context C [take _ (rev _)] => rewrite take_rev in Hb
  | context C [rev (rev _)] => rewrite revK in Hb
  | context C [true && _] => rewrite Bool.andb_true_l in Hb
  | context C [_ && true] => rewrite Bool.andb_true_r in Hb
  | context C [false || _] => rewrite Bool.orb_false_l in Hb
  | context C [_ || false] => rewrite Bool.orb_false_r in Hb
  | is_true true => clear Hb
  | is_true false => exfalso; apply: notF; apply: Hb
  | is_true (_ == _) => move/eqP in Hb
  | ?x = ?x => clear Hb
  | _ = _ => rewrite Hb in *
  end.

(** Apply [simplify_hypothesis] to all hypotheses. **)
Ltac simplify_goal :=
  repeat match goal with H: _ |- _ => progress simplify_hypothesis H end.

(** A common pattern in the proof: using an hypothesis on the form [rev l = l'] to rewrite [l]. **)
Ltac subst_rev_const_list :=
 repeat lazymatch goal with
 | HRevConst: rev ?lconst = ?h :: ?t |- _ =>
   apply rev_move in HRevConst; rewrite HRevConst; rewrite -cat1s; rewrite rev_cat;
   rewrite -v_to_e_cat; rewrite -catA
 end.

(** Simplify the lists in the goal. **)
Ltac simplify_lists :=
  (** Common rewriting rules. **)
  repeat first [
      rewrite drop_rev
    | rewrite take_rev
    | rewrite revK
    | rewrite length_is_size
    | rewrite size_take
    | rewrite size_drop
    | rewrite size_rev
    | rewrite v_to_e_size
    | rewrite rev_cat
    | rewrite rev_cons -cats1
    | rewrite -v_to_e_cat
    | rewrite -v_to_e_rev
    | rewrite -v_to_e_take
    | rewrite -v_to_e_drop];
  (** Putting all the lists into a normal form, as concatenations of as many things.
    Because [cat1s] conflicts with [cats0], replacing any occurence of [[X]] to
    [[X] ++ [::]], it has to be done separately.
    Rewrite with the associated [math goal with] is avoid to deal with existential
    vairables. **)
  repeat match goal with
  |- context C [?x :: ?l] =>
     lazymatch l with [::] => fail | _ => rewrite -(cat1s x l) end
  end;
  repeat lazymatch goal with
  | |- context C [[::] ++ _] => rewrite cat0s
  | |- context C [_ ++ [::]] => rewrite cats0
  | |- context C [rcons _ _] => rewrite -cats1
  | |- context C [(_ ++ _) ++ _] => rewrite -catA
  | |- context C [rev [::]] => rewrite rev0
  | |- context C [v_to_e_list [::]] => rewrite v_to_e_list0
  | |- context C [v_to_e_list [:: _]] => rewrite v_to_e_list1
  end;
  try subst_rev_const_list.

(** Explode a tuple into all its components. **)
Ltac explode_value v :=
  lazymatch type of v with
  | (_ * _)%type =>
    let v1 := fresh "v1" in
    let v2 := fresh "v2" in
    destruct v as [v1 v2];
    explode_value v1;
    explode_value v2
  | _ => idtac
  end.


(** Try to solve a goal of the form [const_list _]. **)
Ltac solve_const_list :=
  repeat rewrite const_list_concat;
  repeat rewrite const_list_cons;
  by [| apply: v_to_e_is_const_list ].

(** Try to solve a goal of the form [l1 = l2] where [l1] and [l2] are two lists. **)
Ltac show_list_equality :=
  simplify_lists; simplify_goal;
  by [| repeat f_equal
      | repeat rewrite catA; repeat f_equal
      | repeat rewrite -catA; repeat f_equal
      | eauto
      | erewrite cats0; eauto
      | erewrite cat0s; eauto
      | repeat (repeat rewrite catA; f_equal; repeat rewrite -catA; f_equal)
      | repeat (repeat rewrite -catA; f_equal; repeat rewrite catA; f_equal) ].
