
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