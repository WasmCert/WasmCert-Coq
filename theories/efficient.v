(* Several functions require safe/efficient extraction targets for OCaml execution *)
From Coq Require Import ZArith List ssreflect ssrbool.
From Wasm Require Import common.

Open Scope list_scope.

Module EfficientExtraction.
  
  (* List lookup without converting the index to nat  *)
  Fixpoint skip_pos {T: Type} (l: list T) (p: positive) : option (list T) :=
    match p with
    | xH =>
        match l with
        | nil => None
        | _ :: l' => Some l'
        end
    | xO p' =>
        match skip_pos l p' with
        | Some l' => skip_pos l' p'
        | None => None
        end
    | xI p' =>
        match l with
        | nil => None
        | _ :: l' =>
            match skip_pos l' p' with
            | Some l'' => skip_pos l'' p'
            | None => None
            end
        end
    end.

  (* This design allows list lookup to be done in O(min(n, length l)). *)
  Definition lookup_N_safe {T: Type} (l: list T) (n: N) :=
    match n with
    | N0 => List.nth_error l 0
    | Npos p =>
        match skip_pos l p with
        | Some (x :: _) => Some x
        | _ => None
        end
    end.

End EfficientExtraction.

Section Soundness.
  Import EfficientExtraction.

  Lemma skip_pos_eq : forall {T: Type} (l: list T) (p: positive),
      (Pos.to_nat p <= length l) ->
      skip_pos l p = Some (List.skipn (Pos.to_nat p) l).
  Proof.
    move => T l p; move: l; induction p; move => l Hlen => //=.
    - destruct l => //; simpl in *; try by lias.
      do 2 try rewrite IHp => //; try by lias.
      + rewrite Pmult_nat_mult.
        rewrite skipn_skipn.
        do 2 f_equal.
        by lias.
      + rewrite length_skipn; by lias.
    - do 2 try rewrite IHp => //; try by lias.
      + rewrite skipn_skipn.
        do 2 f_equal.
        by lias.
      + rewrite length_skipn; by lias.
    - destruct l => //; simpl in *; by lias.
  Qed.

  Lemma skip_pos_oob : forall {T: Type} (l: list T) (p: positive),
      (Pos.to_nat p > length l) ->
      skip_pos l p = None.
  Proof.
    move => T l p; move: l; induction p; move => l Hlen => //=.
    - destruct l => //; simpl in *; try by lias.
      destruct (Pos.to_nat p <=? length l) eqn:Hlen2; move/Nat.leb_spec0 in Hlen2.
      + rewrite skip_pos_eq => //.
        apply IHp.
        rewrite length_skipn.
        by lias.
      + by rewrite IHp => //; lias.
    - destruct (Pos.to_nat p <=? length l) eqn:Hlen2; move/Nat.leb_spec0 in Hlen2.
      + rewrite skip_pos_eq => //.
        apply IHp.
        rewrite length_skipn.
        by lias.
      + by rewrite IHp; lias.
    - do 2 (destruct l; simpl in *; lias).
  Qed.
  
  Lemma lookup_N_safe_sound: forall {T: Type} (l: list T) (n:N),
      lookup_N_safe l n = nth_error l (N.to_nat n).
  Proof.
    move => T l; destruct n as [ | p] => //=.
    destruct (Pos.to_nat p <=? length l) eqn:Hlen; move/Nat.leb_spec0 in Hlen.
    - rewrite skip_pos_eq => //.
      by rewrite - hd_error_skipn.
    - rewrite skip_pos_oob => //; last by lias.
      symmetry.
      apply nth_error_None.
      by lias.
  Qed.
    
End Soundness.
