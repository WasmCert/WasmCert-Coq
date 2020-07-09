
Require List.

Fixpoint those0 {A} (l : list (option A)) : option (list A) :=
match l with
| nil => Some nil
| cons x xs =>
  match x with
  | None => None
  | Some y =>
    match those0 xs with
    | None => None
    | Some ys => Some (cons y ys)
    end
  end
end.

Fixpoint those_aux {A} (acc : option (list A)) (l : list (option A)) : option (list A) :=
match acc with
| None => None
| Some ys_rev =>
  match l with
  | nil => Some ys_rev
  | cons x xs =>
    match x with
    | None => None
    | Some y => those_aux (Some (cons y ys_rev)) xs
    end
  end
end.

Definition those {A} (l : list (option A)) : option (list A) :=
match those_aux (Some nil) l with
| None => None
| Some l => Some (List.rev l)
end.

Lemma those_those0 : forall A (l : list (option A)),
those0 l = those l.
Proof.
(* TODO *)
Admitted.

Fixpoint mapi_aux {A B} (acc : nat * list B) (f : nat -> A -> B) (xs : list A) : list B :=
  let '(i, ys_rev) := acc in
  match xs with
  | nil =>
    List.rev ys_rev
  | cons x xs' =>
    let y := f i x in
    mapi_aux (i + 1, cons y ys_rev) f xs'
  end.

Definition mapi {A B} (f : nat -> A -> B) (xs : list A) : list B :=
  mapi_aux (0, nil) f xs.

Definition fold_lefti {A B} (f : nat -> A -> B -> A) (xs : list B) (acc0 : A) : A :=
  let '(_, acc_end) :=
    List.fold_left
      (fun '(k, acc) x =>
        (k + 1, f k acc x))
      xs
      (0, acc0) in
  acc_end.
