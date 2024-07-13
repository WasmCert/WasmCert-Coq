(** Definition of bytes **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
Require Import common.
From compcert Require Import Integers.
From parseque Require Import Char.

Definition byte := Integers.byte.

#[export]
Instance EqDec_byte : EqDec.EqDec byte := {
  EqDec.eq_dec := Integers.Byte.eq_dec;
}.

Fixpoint encode (n : nat) : byte :=
  match n with
  | 0 => Integers.Byte.zero
  | S n' => Integers.Byte.add Integers.Byte.one (encode n')
  end.

Definition byte_eq_dec : forall (a b : byte), _ := EqDec.eq_dec.
Definition byte_eqb a b := is_left (byte_eq_dec a b).
Definition eqbyteP : Equality.axiom byte_eqb :=
  eq_dec_Equality_axiom byte_eq_dec.

Canonical Structure byte_eqMixin := EqMixin eqbyteP.
Canonical Structure byte_eqType := Eval hnf in EqType byte byte_eqMixin.


Definition bytes := seq byte.

Definition bytes_eq_dec : forall (a b : bytes), {a = b} + {a <> b}.
Proof. apply: List.list_eq_dec. apply: byte_eq_dec. Defined.
Definition bytes_eqb (a b : bytes) := is_left (bytes_eq_dec a b).
Definition eqbytesP : Equality.axiom bytes_eqb :=
  eq_dec_Equality_axiom bytes_eq_dec.

Fixpoint bytes_takefill (a : byte) (n : nat) (aas : bytes) : bytes :=
  match n with
  | O => nil
  | S n' =>
    match aas with
    | nil => cons a (bytes_takefill a n' aas)
    | cons a' aas' => cons a' (bytes_takefill a n' aas')
    end
  end.

Fixpoint bytes_replicate (n : nat) (b : byte) : bytes :=
  match n with
  | 0 => [::]
  | n'.+1 => b :: bytes_replicate n' b
  end.

Definition msbyte (bs : bytes) : option byte :=
  last_error bs.

Definition compcert_byte_of_byte (b : Byte.byte) : byte :=
  (* TODO: this is not great *)
  encode (Byte.to_nat b).

Definition byte_of_compcert_byte (b : byte) : Byte.byte :=
  (* TODO: is that correct? *)
  match Byte.of_nat (BinInt.Z.to_nat b.(Byte.intval)) with
  | None => Byte.x00
  | Some b' => b'
  end.

Declare Scope byte_scope.
Delimit Scope byte_scope with byte.
Open Scope byte_scope.

(* TODO: is there a better way to do this? With LTac? *)
Notation "#A" := 10 : byte_scope.
Notation "#B" := 11 : byte_scope.
Notation "#C" := 12 : byte_scope.
Notation "#D" := 13 : byte_scope.
Notation "#E" := 14 : byte_scope.
Notation "#F" := 15 : byte_scope.
Notation "#00" := Integers.Byte.zero : byte_scope.
Notation "#01" := Integers.Byte.one : byte_scope.
Notation "#02" := (encode 2) : byte_scope.
Notation "#03" := (encode 3) : byte_scope.
Notation "#04" := (encode 4) : byte_scope.
Notation "#05" := (encode 5) : byte_scope.
Notation "#06" := (encode 6) : byte_scope.
Notation "#07" := (encode 7) : byte_scope.
Notation "#08" := (encode 8) : byte_scope.
Notation "#09" := (encode 9) : byte_scope.
Notation "#0A" := (encode #A) : byte_scope.
Notation "#0B" := (encode #B) : byte_scope.
Notation "#0C" := (encode #C) : byte_scope.
Notation "#0D" := (encode #D) : byte_scope.
Notation "#0E" := (encode #E) : byte_scope.
Notation "#0F" := (encode #F) : byte_scope.
Notation "#10" := (encode (1 * 16)) : byte_scope.
Notation "#11" := (encode (1 * 16 + 1)) : byte_scope.
Notation "#1A" := (encode (1 * 16 + #A)) : byte_scope.
Notation "#1B" := (encode (1 * 16 + #B)) : byte_scope.
Notation "#20" := (encode (2 * 16)) : byte_scope.
Notation "#21" := (encode (2 * 16 + 1)) : byte_scope.
Notation "#22" := (encode (2 * 16 + 2)) : byte_scope.
Notation "#23" := (encode (2 * 16 + 3)) : byte_scope.
Notation "#24" := (encode (2 * 16 + 4)) : byte_scope.
Notation "#25" := (encode (2 * 16 + 5)) : byte_scope.
Notation "#26" := (encode (2 * 16 + 6)) : byte_scope.
Notation "#27" := (encode (2 * 16 + 7)) : byte_scope.
Notation "#28" := (encode (2 * 16 + 8)) : byte_scope.
Notation "#29" := (encode (2 * 16 + 9)) : byte_scope.
Notation "#2A" := (encode (2 * 16 + #A)) : byte_scope.
Notation "#2B" := (encode (2 * 16 + #B)) : byte_scope.
Notation "#2C" := (encode (2 * 16 + #C)) : byte_scope.
Notation "#2D" := (encode (2 * 16 + #D)) : byte_scope.
Notation "#2E" := (encode (2 * 16 + #E)) : byte_scope.
Notation "#2F" := (encode (2 * 16 + #F)) : byte_scope.
Notation "#30" := (encode (3 * 16)) : byte_scope.
Notation "#31" := (encode (3 * 16 + 1)) : byte_scope.
Notation "#32" := (encode (3 * 16 + 2)) : byte_scope.
Notation "#33" := (encode (3 * 16 + 3)) : byte_scope.
Notation "#34" := (encode (3 * 16 + 4)) : byte_scope.
Notation "#35" := (encode (3 * 16 + 5)) : byte_scope.
Notation "#36" := (encode (3 * 16 + 6)) : byte_scope.
Notation "#37" := (encode (3 * 16 + 7)) : byte_scope.
Notation "#38" := (encode (3 * 16 + 8)) : byte_scope.
Notation "#39" := (encode (3 * 16 + 9)) : byte_scope.
Notation "#3A" := (encode (3 * 16 + #A)) : byte_scope.
Notation "#3B" := (encode (3 * 16 + #B)) : byte_scope.
Notation "#3C" := (encode (3 * 16 + #C)) : byte_scope.
Notation "#3D" := (encode (3 * 16 + #D)) : byte_scope.
Notation "#3E" := (encode (3 * 16 + #E)) : byte_scope.
Notation "#3F" := (encode (3 * 16 + #F)) : byte_scope.

Notation "#40" := (encode (4 * 16 + 0)) : byte_scope.
Notation "#41" := (encode (4 * 16 + 1)) : byte_scope.
Notation "#42" := (encode (4 * 16 + 2)) : byte_scope.
Notation "#43" := (encode (4 * 16 + 3)) : byte_scope.
Notation "#44" := (encode (4 * 16 + 4)) : byte_scope.
Notation "#45" := (encode (4 * 16 + 5)) : byte_scope.
Notation "#46" := (encode (4 * 16 + 6)) : byte_scope.
Notation "#47" := (encode (4 * 16 + 7)) : byte_scope.
Notation "#48" := (encode (4 * 16 + 8)) : byte_scope.
Notation "#49" := (encode (4 * 16 + 9)) : byte_scope.
Notation "#4A" := (encode (4 * 16 + #A)) : byte_scope.
Notation "#4B" := (encode (4 * 16 + #B)) : byte_scope.
Notation "#4C" := (encode (4 * 16 + #C)) : byte_scope.
Notation "#4D" := (encode (4 * 16 + #D)) : byte_scope.
Notation "#4E" := (encode (4 * 16 + #E)) : byte_scope.
Notation "#4F" := (encode (4 * 16 + #F)) : byte_scope.

Notation "#50" := (encode (5 * 16 + 0)) : byte_scope.
Notation "#51" := (encode (5 * 16 + 1)) : byte_scope.
Notation "#52" := (encode (5 * 16 + 2)) : byte_scope.
Notation "#53" := (encode (5 * 16 + 3)) : byte_scope.
Notation "#54" := (encode (5 * 16 + 4)) : byte_scope.
Notation "#55" := (encode (5 * 16 + 5)) : byte_scope.
Notation "#56" := (encode (5 * 16 + 6)) : byte_scope.
Notation "#57" := (encode (5 * 16 + 7)) : byte_scope.
Notation "#58" := (encode (5 * 16 + 8)) : byte_scope.
Notation "#59" := (encode (5 * 16 + 9)) : byte_scope.
Notation "#5A" := (encode (5 * 16 + #A)) : byte_scope.
Notation "#5B" := (encode (5 * 16 + #B)) : byte_scope.
Notation "#5C" := (encode (5 * 16 + #C)) : byte_scope.
Notation "#5D" := (encode (5 * 16 + #D)) : byte_scope.
Notation "#5E" := (encode (5 * 16 + #E)) : byte_scope.
Notation "#5F" := (encode (5 * 16 + #F)) : byte_scope.

Notation "#60" := (encode (6 * 16 + 0)) : byte_scope.
Notation "#61" := (encode (6 * 16 + 1)) : byte_scope.
Notation "#62" := (encode (6 * 16 + 2)) : byte_scope.
Notation "#63" := (encode (6 * 16 + 3)) : byte_scope.
Notation "#64" := (encode (6 * 16 + 4)) : byte_scope.
Notation "#65" := (encode (6 * 16 + 5)) : byte_scope.
Notation "#66" := (encode (6 * 16 + 6)) : byte_scope.
Notation "#67" := (encode (6 * 16 + 7)) : byte_scope.
Notation "#68" := (encode (6 * 16 + 8)) : byte_scope.
Notation "#69" := (encode (6 * 16 + 9)) : byte_scope.
Notation "#6A" := (encode (6 * 16 + #A)) : byte_scope.
Notation "#6B" := (encode (6 * 16 + #B)) : byte_scope.
Notation "#6C" := (encode (6 * 16 + #C)) : byte_scope.
Notation "#6D" := (encode (6 * 16 + #D)) : byte_scope.
Notation "#6E" := (encode (6 * 16 + #E)) : byte_scope.
Notation "#6F" := (encode (6 * 16 + #F)) : byte_scope.

Notation "#70" := (encode (7 * 16 + 0)) : byte_scope.
Notation "#71" := (encode (7 * 16 + 1)) : byte_scope.
Notation "#72" := (encode (7 * 16 + 2)) : byte_scope.
Notation "#73" := (encode (7 * 16 + 3)) : byte_scope.
Notation "#74" := (encode (7 * 16 + 4)) : byte_scope.
Notation "#75" := (encode (7 * 16 + 5)) : byte_scope.
Notation "#76" := (encode (7 * 16 + 6)) : byte_scope.
Notation "#77" := (encode (7 * 16 + 7)) : byte_scope.
Notation "#78" := (encode (7 * 16 + 8)) : byte_scope.
Notation "#79" := (encode (7 * 16 + 9)) : byte_scope.
Notation "#7A" := (encode (7 * 16 + #A)) : byte_scope.
Notation "#7B" := (encode (7 * 16 + #B)) : byte_scope.
Notation "#7C" := (encode (7 * 16 + #C)) : byte_scope.
Notation "#7D" := (encode (7 * 16 + #D)) : byte_scope.
Notation "#7E" := (encode (7 * 16 + #E)) : byte_scope.
Notation "#7F" := (encode (7 * 16 + #F)) : byte_scope.

Notation "#80" := (encode (8 * 16 + 0)) : byte_scope.
Notation "#81" := (encode (8 * 16 + 1)) : byte_scope.
Notation "#82" := (encode (8 * 16 + 2)) : byte_scope.
Notation "#83" := (encode (8 * 16 + 3)) : byte_scope.
Notation "#84" := (encode (8 * 16 + 4)) : byte_scope.
Notation "#85" := (encode (8 * 16 + 5)) : byte_scope.
Notation "#86" := (encode (8 * 16 + 6)) : byte_scope.
Notation "#87" := (encode (8 * 16 + 7)) : byte_scope.
Notation "#88" := (encode (8 * 16 + 8)) : byte_scope.
Notation "#89" := (encode (8 * 16 + 9)) : byte_scope.
Notation "#8A" := (encode (8 * 16 + #A)) : byte_scope.
Notation "#8B" := (encode (8 * 16 + #B)) : byte_scope.
Notation "#8C" := (encode (8 * 16 + #C)) : byte_scope.
Notation "#8D" := (encode (8 * 16 + #D)) : byte_scope.
Notation "#8E" := (encode (8 * 16 + #E)) : byte_scope.
Notation "#8F" := (encode (8 * 16 + #F)) : byte_scope.

Notation "#90" := (encode (9 * 16 + 0)) : byte_scope.
Notation "#91" := (encode (9 * 16 + 1)) : byte_scope.
Notation "#92" := (encode (9 * 16 + 2)) : byte_scope.
Notation "#93" := (encode (9 * 16 + 3)) : byte_scope.
Notation "#94" := (encode (9 * 16 + 4)) : byte_scope.
Notation "#95" := (encode (9 * 16 + 5)) : byte_scope.
Notation "#96" := (encode (9 * 16 + 6)) : byte_scope.
Notation "#97" := (encode (9 * 16 + 7)) : byte_scope.
Notation "#98" := (encode (9 * 16 + 8)) : byte_scope.
Notation "#99" := (encode (9 * 16 + 9)) : byte_scope.
Notation "#9A" := (encode (9 * 16 + #A)) : byte_scope.
Notation "#9B" := (encode (9 * 16 + #B)) : byte_scope.
Notation "#9C" := (encode (9 * 16 + #C)) : byte_scope.
Notation "#9D" := (encode (9 * 16 + #D)) : byte_scope.
Notation "#9E" := (encode (9 * 16 + #E)) : byte_scope.
Notation "#9F" := (encode (9 * 16 + #F)) : byte_scope.

Notation "#A0" := (encode (#A * 16 + 0)) : byte_scope.
Notation "#A1" := (encode (#A * 16 + 1)) : byte_scope.
Notation "#A2" := (encode (#A * 16 + 2)) : byte_scope.
Notation "#A3" := (encode (#A * 16 + 3)) : byte_scope.
Notation "#A4" := (encode (#A * 16 + 4)) : byte_scope.
Notation "#A5" := (encode (#A * 16 + 5)) : byte_scope.
Notation "#A6" := (encode (#A * 16 + 6)) : byte_scope.
Notation "#A7" := (encode (#A * 16 + 7)) : byte_scope.
Notation "#A8" := (encode (#A * 16 + 8)) : byte_scope.
Notation "#A9" := (encode (#A * 16 + 9)) : byte_scope.
Notation "#AA" := (encode (#A * 16 + #A)) : byte_scope.
Notation "#AB" := (encode (#A * 16 + #B)) : byte_scope.
Notation "#AC" := (encode (#A * 16 + #C)) : byte_scope.
Notation "#AD" := (encode (#A * 16 + #D)) : byte_scope.
Notation "#AE" := (encode (#A * 16 + #E)) : byte_scope.
Notation "#AF" := (encode (#A * 16 + #F)) : byte_scope.

Notation "#B0" := (encode (#B * 16 + 0)) : byte_scope.
Notation "#B1" := (encode (#B * 16 + 1)) : byte_scope.
Notation "#B2" := (encode (#B * 16 + 2)) : byte_scope.
Notation "#B3" := (encode (#B * 16 + 3)) : byte_scope.
Notation "#B4" := (encode (#B * 16 + 4)) : byte_scope.
Notation "#B5" := (encode (#B * 16 + 5)) : byte_scope.
Notation "#B6" := (encode (#B * 16 + 6)) : byte_scope.
Notation "#B7" := (encode (#B * 16 + 7)) : byte_scope.
Notation "#B8" := (encode (#B * 16 + 8)) : byte_scope.
Notation "#B9" := (encode (#B * 16 + 9)) : byte_scope.
Notation "#BA" := (encode (#B * 16 + #A)) : byte_scope.
Notation "#BB" := (encode (#B * 16 + #B)) : byte_scope.
Notation "#BC" := (encode (#B * 16 + #C)) : byte_scope.
Notation "#BD" := (encode (#B * 16 + #D)) : byte_scope.
Notation "#BE" := (encode (#B * 16 + #E)) : byte_scope.
Notation "#BF" := (encode (#B * 16 + #F)) : byte_scope.

Notation "#C0" := (encode (#C * 16 + 0)) : byte_scope.
Notation "#C1" := (encode (#C * 16 + 1)) : byte_scope.
Notation "#C2" := (encode (#C * 16 + 2)) : byte_scope.
Notation "#C3" := (encode (#C * 16 + 3)) : byte_scope.
Notation "#C4" := (encode (#C * 16 + 4)) : byte_scope.
Notation "#C5" := (encode (#C * 16 + 5)) : byte_scope.
Notation "#C6" := (encode (#C * 16 + 6)) : byte_scope.
Notation "#C7" := (encode (#C * 16 + 7)) : byte_scope.
Notation "#C8" := (encode (#C * 16 + 8)) : byte_scope.
Notation "#C9" := (encode (#C * 16 + 9)) : byte_scope.
Notation "#CA" := (encode (#C * 16 + #A)) : byte_scope.
Notation "#CB" := (encode (#C * 16 + #B)) : byte_scope.
Notation "#CC" := (encode (#C * 16 + #C)) : byte_scope.
Notation "#CD" := (encode (#C * 16 + #D)) : byte_scope.
Notation "#CE" := (encode (#C * 16 + #E)) : byte_scope.
Notation "#CF" := (encode (#C * 16 + #F)) : byte_scope.

Notation "#D0" := (encode (#D * 16 + 0)) : byte_scope.
Notation "#D1" := (encode (#D * 16 + 1)) : byte_scope.
Notation "#D2" := (encode (#D * 16 + 2)) : byte_scope.
Notation "#D3" := (encode (#D * 16 + 3)) : byte_scope.
Notation "#D4" := (encode (#D * 16 + 4)) : byte_scope.
Notation "#D5" := (encode (#D * 16 + 5)) : byte_scope.
Notation "#D6" := (encode (#D * 16 + 6)) : byte_scope.
Notation "#D7" := (encode (#D * 16 + 7)) : byte_scope.
Notation "#D8" := (encode (#D * 16 + 8)) : byte_scope.
Notation "#D9" := (encode (#D * 16 + 9)) : byte_scope.
Notation "#DA" := (encode (#D * 16 + #A)) : byte_scope.
Notation "#DB" := (encode (#D * 16 + #B)) : byte_scope.
Notation "#DC" := (encode (#D * 16 + #C)) : byte_scope.
Notation "#DD" := (encode (#D * 16 + #D)) : byte_scope.
Notation "#DE" := (encode (#D * 16 + #E)) : byte_scope.
Notation "#DF" := (encode (#D * 16 + #F)) : byte_scope.

Notation "#E0" := (encode (#E * 16 + 0)) : byte_scope.
Notation "#E1" := (encode (#E * 16 + 1)) : byte_scope.
Notation "#E2" := (encode (#E * 16 + 2)) : byte_scope.
Notation "#E3" := (encode (#E * 16 + 3)) : byte_scope.
Notation "#E4" := (encode (#E * 16 + 4)) : byte_scope.
Notation "#E5" := (encode (#E * 16 + 5)) : byte_scope.
Notation "#E6" := (encode (#E * 16 + 6)) : byte_scope.
Notation "#E7" := (encode (#E * 16 + 7)) : byte_scope.
Notation "#E8" := (encode (#E * 16 + 8)) : byte_scope.
Notation "#E9" := (encode (#E * 16 + 9)) : byte_scope.
Notation "#EA" := (encode (#E * 16 + #A)) : byte_scope.
Notation "#EB" := (encode (#E * 16 + #B)) : byte_scope.
Notation "#EC" := (encode (#E * 16 + #C)) : byte_scope.
Notation "#ED" := (encode (#E * 16 + #D)) : byte_scope.
Notation "#EE" := (encode (#E * 16 + #E)) : byte_scope.
Notation "#EF" := (encode (#E * 16 + #F)) : byte_scope.

Notation "#F0" := (encode (#F * 16 + 0)) : byte_scope.
Notation "#F1" := (encode (#F * 16 + 1)) : byte_scope.
Notation "#F2" := (encode (#F * 16 + 2)) : byte_scope.
Notation "#F3" := (encode (#F * 16 + 3)) : byte_scope.
Notation "#F4" := (encode (#F * 16 + 4)) : byte_scope.
Notation "#F5" := (encode (#F * 16 + 5)) : byte_scope.
Notation "#F6" := (encode (#F * 16 + 6)) : byte_scope.
Notation "#F7" := (encode (#F * 16 + 7)) : byte_scope.
Notation "#F8" := (encode (#F * 16 + 8)) : byte_scope.
Notation "#F9" := (encode (#F * 16 + 9)) : byte_scope.
Notation "#FA" := (encode (#F * 16 + #A)) : byte_scope.
Notation "#FB" := (encode (#F * 16 + #B)) : byte_scope.
Notation "#FC" := (encode (#F * 16 + #C)) : byte_scope.
Notation "#FD" := (encode (#F * 16 + #D)) : byte_scope.
Notation "#FE" := (encode (#F * 16 + #E)) : byte_scope.
Notation "#FF" := (encode (#F * 16 + #F)) : byte_scope.

