From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import operations opsem properties typing_inversion.

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

(* TODO: find better fixes than the current duplication. *)
Ltac split_et_composition:=
  lazymatch goal with
  | H: e_typing _ _ (_ ++ _) _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let t2s := fresh "t2s" in
    let t3s := fresh "t3s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply e_composition_typing in H;
    destruct H as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]]; subst
  | H: typing.e_typing _ _ (_ ++ _) _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let t2s := fresh "t2s" in
    let t3s := fresh "t3s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply e_composition_typing in H;
    destruct H as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]]; subst
  end.

Ltac invert_e_typing:=
  repeat lazymatch goal with
  | H: e_typing _ _ (_ ++ _) _ |- _ =>
    split_et_composition
  | H: typing.e_typing _ _ (_ ++ _) _ |- _ =>
    split_et_composition
  | H: e_typing _ _ [::AI_label _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Label_typing in H;
    destruct H as [ts [t1s [H1 [H2 [H3 H4]]]]]; subst
  | H: typing.e_typing _ _ [::AI_label _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    eapply Label_typing in H; eauto;
    destruct H as [ts [t1s [H1 [H2 [H3 H4]]]]]; subst
         end.

Ltac auto_basic :=
  repeat lazymatch goal with
  | |- es_is_basic [::AI_basic _; AI_basic _; AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- es_is_basic [::AI_basic _; AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- es_is_basic [::AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- es_is_basic [::AI_basic _] =>
    simpl; repeat split
  | |- e_is_basic (AI_basic ?e) =>
    by unfold e_is_basic; exists e
  end.

(** A common scheme in the progress proof, with a continuation. **)
Ltac solve_progress_cont cont :=
  repeat eexists;
  solve [
      apply r_simple; solve [ eauto | constructor; eauto | cont; eauto ]
    | cont ].

(** The same, but without continuation. **)
Ltac solve_progress :=
  solve_progress_cont ltac:(fail).
