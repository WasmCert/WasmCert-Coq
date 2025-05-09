(* Several functions require safe/efficient extraction targets for OCaml execution *)
From Coq Require Import ZArith List.

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
