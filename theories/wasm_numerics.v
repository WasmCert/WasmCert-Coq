(** Common useful definitions **)
(* (C) M. Bodin, J. Pichon - see LICENSE.txt *)

Require Import wasm_common.
Require Import ZArith.Int.
Require Coq.ZArith.BinInt.
From compcert Require Integers Floats.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Most of the content of this file follows comes from
  https://webassembly.github.io/spec/core/exec/numerics.html **)

(** * Integers **)

Module Wasm_int.

(** ** Declaration of Operations **)

Record mixin_of (int_t : Type) := Mixin {
  int_zero : int_t;
  int_clz : int_t -> int_t;
  int_ctz : int_t -> int_t;
  int_popcnt : int_t -> int_t;
  (**)
  int_add : int_t -> int_t -> int_t;
  int_sub : int_t -> int_t -> int_t;
  int_mul : int_t -> int_t -> int_t;
  int_div_u : int_t -> int_t -> option int_t;
  int_div_s : int_t -> int_t -> option int_t;
  int_rem_u : int_t -> int_t -> option int_t;
  int_rem_s : int_t -> int_t -> option int_t;
  int_and : int_t -> int_t -> int_t;
  int_or : int_t -> int_t -> int_t;
  int_xor : int_t -> int_t -> int_t;
  int_shl : int_t -> int_t -> int_t;
  int_shr_u : int_t -> int_t -> int_t;
  int_shr_s : int_t -> int_t -> int_t;
  int_rotl : int_t -> int_t -> int_t;
  int_rotr : int_t -> int_t -> int_t;
  (**)
  int_eqz : int_t -> bool;
  (**)
  int_eq : int_t -> int_t -> bool;
  int_lt_u : int_t -> int_t -> bool;
  int_lt_s : int_t -> int_t -> bool;
  int_gt_u : int_t -> int_t -> bool;
  int_gt_s : int_t -> int_t -> bool;
  int_le_u : int_t -> int_t -> bool;
  int_le_s : int_t -> int_t -> bool;
  int_ge_u : int_t -> int_t -> bool;
  int_ge_s : int_t -> int_t -> bool;
  (**)
  int_of_nat : nat -> int_t;
  nat_of_int : int_t -> nat;
}.

Record class_of T := Class {base : Equality.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >-> Equality.class_of.

Structure type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Definition int_ne (e : type) : sort e -> sort e -> bool :=
  let 'Pack _ (Class _ (Mixin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_eq _ _ _ _ _ _ _ _ _ _)) := e in
    fun x => fun y => negb (int_eq x y).

(** ** Instantiations **)

Module Make (WS: Integers.WORDSIZE).

Import Coq.ZArith.BinInt.

Import Integers.

Include Make (WS).

Definition T := int.

Definition fail_on_zero (op : T -> T -> T) i1 i2 :=
  if eq i2 zero then None
  else Some (op i1 i2).

Lemma Z_eqP : Equality.axiom Coqlib.zeq.
Proof.
  move=> x y. case: Coqlib.zeq.
  - by left.
  - by right.
Qed.

Definition Z_eqMixin := EqMixin Z_eqP.

Canonical Structure Z_eqType := EqType Z Z_eqMixin.

Coercion Z.of_nat : nat >-> Z.

Fixpoint power_index_to_bits (c : nat) (l : seq Z) : seq bool :=
  match c with
  | 0 => [::]
  | c.+1 => ((c : Z) \in l) :: power_index_to_bits c l
  end.

Lemma power_index_to_bits_size : forall c x,
  seq.size (power_index_to_bits c x) = c.
Proof.
  move=> c. elim: c; first by [].
  move=> n + x /=. by move=> ->.
Qed.

Lemma power_index_to_bits_none : forall c (l : seq Z),
  (forall i, i < c -> (i : Z) \notin l) ->
  power_index_to_bits c l = nseq c false.
Proof.
  move=> c. elim: c; first by [].
  move=> c IH l A /=.
  rewrite (Bool.negb_involutive_reverse (_ \in l)) A //=.
  rewrite IH //. move=> i I. apply: A. by apply: leq_trans I.
Qed.

Lemma power_index_to_bits_in : forall c l n,
  n < c ->
  seq.nth false (power_index_to_bits c l) (c - n - 1) = ((n : Z) \in l).
Proof.
  move=> c l n => /leP I. move: l. elim: I.
  - move=> l /=. by rewrite_by (n.+1 - n - 1 = 0).
  - clear. move=> c I IH l. rewrite_by (c.+1 - n - 1 = 1 + (c - n - 1)). by apply IH.
Qed.

(** Given a [T], return a sequence of bits representing the integer.
  The first bit is the most significant bit. **)
Definition convert_to_bits (x : T) : seq bool :=
  let l := Zbits.Z_one_bits wordsize (intval x) 0 in
  (** [l] is the list of positions (unitary position being the position [0]) where
      the value [x] has a bit as true. **)
  power_index_to_bits wordsize l.

Lemma convert_to_bits_size : forall x,
  seq.size (convert_to_bits x) = wordsize.
Proof.
  move=> x. by apply: power_index_to_bits_size.
Qed.

Lemma convert_to_bits_zero : convert_to_bits zero = seq.nseq wordsize false.
Proof.
  rewrite /convert_to_bits. rewrite Zbits.Z_one_bits_zero /=.
  elim: wordsize; first by [].
  by move=> n /= ->.
Qed.

Lemma convert_to_bits_one :
  convert_to_bits one
  = rcons (seq.nseq (wordsize - 1) false) true.
Proof.
  have E: intval one = Zpower.two_p Z0.
  { compute. move: WS.wordsize_not_zero. by elim: WS.wordsize. }
  rewrite /convert_to_bits E Zbits.Z_one_bits_two_p /=.
  - rewrite /convert_to_bits /wordsize.
    move: WS.wordsize_not_zero. case: WS.wordsize => //.
    move=> ws _ /=.
    rewrite_by (ws.+1 - 1 = ws).
    elim Ews: ws => [|ws]; first by [].
    move=> IH /=.
    have Rf: Zpos (BinPos.Pos.of_succ_nat ws) \in [:: Z0] = false; first by [].
    rewrite {} Rf. rewrite IH //.
  - split=> //. rewrite /wordsize.
    move: WS.wordsize_not_zero. by case: WS.wordsize => //.
Qed.

Lemma nat_Z_lt_neq : forall a b,
  a < b ->
  (a == b :> Z) = false.
Proof.
  move=> a b. move/leP => I. apply/Z_eqP. lias.
Qed.

Lemma nat_Z_gt_neq : forall a b,
  a < b ->
  (b == a :> Z) = false.
Proof.
  move=> ? ? ?. by rewrite eqtype.eq_sym nat_Z_lt_neq.
Qed.

Lemma convert_to_bits_two_p : forall p : nat,
  p < wordsize ->
  convert_to_bits (repr (Zpower.two_p p))
  = seq.nseq (wordsize - 1 - p) false ++ [:: true] ++ seq.nseq p false.
Proof.
  rewrite /convert_to_bits /repr /intval. move=> p I.
  have Rm: Z_mod_modulus (Zpower.two_p p) = Zpower.two_p p.
  { rewrite /Z_mod_modulus. case Epp: Zpower.two_p => //=.
    - rewrite Zbits.P_mod_two_p_eq. rewrite Z.mod_small //.
      split=> //. rewrite <- Epp. clear Epp.
      rewrite Coqlib.two_power_nat_two_p. apply: Coqlib.two_p_monotone_strict.
      split=> //.
      + by apply: Zorder.Zle_0_nat.
      + apply: Znat.inj_lt. by apply/leP.
    - exfalso. move: Epp. by case: (p). }
  rewrite {} Rm. rewrite Zbits.Z_one_bits_two_p /=.
  - have I': (p < wordsize)%coq_nat; first by apply/ltP. elim: I'.
    + move=> /=. rewrite_by (p.+1 - 1 - p = 0).
      rewrite in_cons in_nil eqxx /=. f_equal.
      rewrite power_index_to_bits_none //.
      move=> i I'. by rewrite in_cons in_nil nat_Z_lt_neq.
    + move=> ws Ip E /=. rewrite E /=.
      rewrite in_cons in_nil nat_Z_gt_neq.
      * by rewrite_by (ws.+1 - 1 - p = (ws - 1 - p).+1).
      * lias.
  - split.
    + by apply: Znat.Nat2Z.is_nonneg.
    + apply: Znat.inj_lt. by apply/leP.
Qed.

(* FIXME: Stuffs that we might want to prove.
Fixpoint convert_from_bits l : T :=
  match l with
  | [::] => repr 0
  | b :: l =>
    let i :=
      if b then
        Zpower.two_p (seq.size l)
      else 0 in
    add (repr i) (convert_from_bits l)
  end.

Lemma convert_to_from_bits : forall a,
  lt a (repr (Zpower.two_p wordsize)) ->
  a = convert_from_bits (convert_to_bits a).
Proof.
  (* TODO *)
Admitted.

Lemma convert_to_bits_disjunct_sum : forall a b,
  seq.all2 (fun a b => ~~ (a && b)) (convert_to_bits (repr a)) (convert_to_bits (repr b)) ->
  convert_to_bits (repr (a + b))
  = allpairs orb (convert_to_bits (repr a)) (convert_to_bits (repr b)).
Proof.
  rewrite /convert_to_bits /repr /intval.

  elim: wordsize; first by [].
  move=> ws IH a b E.
Admitted. (* TODO *)

Lemma convert_to_bits_testbit : forall n x,
  n < wordsize ->
  seq.nth false (convert_to_bits x) n
  = Z.testbit (intval x) (wordsize - n - 1).
Proof.
  rewrite /convert_to_bits.

  move=> n. elim: n.
  - move=> x _. admit.
  - clear n. move=> n IH x I. simpl.
  
  elim: wordsize => ws; first by [].
  move=> IH n x I. elim: n => /=.
  /=.
  simpl. rewrite <- IHws.
  destruct n.
  - simpl. case O: Z.odd.
Qed.

Lemma convert_to_bits_eq : forall a b,
  convert_to_bits a = convert_to_bits b ->
  eq a b.
*)

(** Return the count of leading zero bits. **)
Definition clz i :=
  let l := convert_to_bits i in
  repr (seq.find (fun b => b == false) l).

(** Return the count of trailing zero bits. **)
Definition ctz i :=
  let l := convert_to_bits i in
  repr (seq.find (fun b => b == false) (seq.rev l)).

(** Return the count of non-zero bits. **)
Definition popcnt i :=
  let l := convert_to_bits i in
  repr (seq.count (fun b => b == true) l).

(* FIXME: stuff that we probably want to prove.
Lemma clz_wordsize : forall i,
  clz i = repr wordsize ->
  i = repr 0.

Lemma ctz_wordsize : forall i,
  ctz i = repr wordsize ->
  i = repr 0.

Lemma popcnt_wordsize : forall i,
  popcnt i = repr wordsize ->
  i = repr 0.

Lemma ctz_shl : forall i k,
  ctz (shl i k) = min wordsize (ctz i + k).

Lemma clz_shr : forall i k,
  clz (shr i k) = min wordsize (clz i + k).
*)

Definition Tmixin : mixin_of T := {|
     int_zero := zero ;
     int_clz := clz ;
     int_ctz := ctz ;
     int_popcnt := popcnt ;
     (**)
     int_add := add ;
     int_sub := sub ;
     int_mul := mul ;
     int_div_u := fail_on_zero divu ;
     int_div_s := fail_on_zero divs ;
     int_rem_u := fail_on_zero modu ;
     int_rem_s := fail_on_zero mods ;
     int_and := and ;
     int_or := or ;
     int_xor := xor ;
     int_shl := shl ;
     int_shr_u := shru ;
     int_shr_s := shr ; (* FIXME: Possibly not the right value. *)
     int_rotl := rol ;
     int_rotr := ror ;
     (**)
     int_eqz := eq zero ;
     (**)
     int_eq := eq ;
     int_lt_u := ltu ;
     int_lt_s := lt ;
     int_gt_u x y := ltu y x ;
     int_gt_s x y := lt y x ;
     int_le_u x y := negb (ltu y x) ;
     int_le_s x y := negb (lt y x) ;
     int_ge_u x y := negb (ltu x y) ;
     int_ge_s x y := negb (lt x y) ;
     (**)
     int_of_nat n := repr n
       (* Note that [repr] takes the modulus of the number modulo the range. *) ;
     nat_of_int i := Z.to_nat (intval i)
   |}.

Lemma Z_lt_irrelevant : forall x y (p1 p2 : Z.lt x y), p1 = p2.
Proof.
  rewrite /Z.lt. move=> x y p1 p2.
  apply: Eqdep_dec.eq_proofs_unicity. move=> [] []; (by left) || (right; discriminate).
Qed.

Lemma eq_eqP : Equality.axiom eq.
Proof.
  move=> x y. rewrite /eq. case: Coqlib.zeq => [E|E].
  - apply/ReflectT. move: E. case: x => x [Vx Rx]. case: y => y [Vy Ry].
    simpl. move=> E //=. subst. f_equal.
    rewrite (Z_lt_irrelevant Vx Vy).
    by rewrite (Z_lt_irrelevant Rx Ry).
  - apply/ReflectF. move=> ?. subst. exact: E.
Qed.

Definition cT : type := Pack {| base := EqMixin eq_eqP; mixin := Tmixin |}.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Equality.class bT) b => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.

End Make.

Module Int32.
Include Make(Integers.Wordsize_32).
End Int32.

Module Int64.
Include Make(Integers.Wordsize_64).
End Int64.

End Wasm_int.


(** * FLoats **)

(** ** Declaration of Operations **)

Module Wasm_float.

Record mixin_of (float_t : Type) := Mixin {
  float_zero : float_t;
  float_neg : float_t -> float_t;
  float_abs : float_t -> float_t;
  float_ceil : float_t -> float_t;
  float_floor : float_t -> float_t;
  float_trunc : float_t -> float_t;
  float_nearest : float_t -> float_t;
  float_sqrt : float_t -> float_t;
  float_add : float_t -> float_t -> float_t;
  float_sub : float_t -> float_t -> float_t;
  float_mul : float_t -> float_t -> float_t;
  float_div : float_t -> float_t -> float_t;
  float_min : float_t -> float_t -> float_t;
  float_max : float_t -> float_t -> float_t;
  float_copysign : float_t -> float_t -> float_t;
  float_eq : float_t -> float_t -> bool;
  float_lt : float_t -> float_t -> bool;
  float_gt : float_t -> float_t -> bool;
  float_le : float_t -> float_t -> bool;
  float_ge : float_t -> float_t -> bool;
}.

Record class_of T := Class {base : Equality.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >->  Equality.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Definition float_ne (e : type) : sort e -> sort e -> bool :=
  let 'Pack _ (Class _ (Mixin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ float_eq _ _ _ _)) := e in
    fun x => fun y => negb (float_eq x y).

Parameters (T : Type) (cT : type). (* TODO: Same as Wasm_int, this is not the way to go. *)

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Equality.class bT) b => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.

End Wasm_float.

(** ** Instantiations **)

(* TODO: Wasm_float32 *)

Module Wasm_float64.

Import Integers.

Import Raux.

Import Wasm_float.

Import Floats.

Include Float.

Definition T := float.

(** State whether the given float is a NaN. **)
Definition is_nan : T -> bool := Binary.is_nan _ _.

(** State whether the given float is negative. **)
Definition sign : T -> bool := Binary.Bsign _ _.

(** State whether the given float is a zero. **)
Definition is_zero (f : T) :=
  if f is Binary.B754_zero _ then true else false.

(** State whether the given float is an infinity. **)
Definition is_infinity (f : T) :=
  if f is Binary.B754_infinity _ then true else false.

(** +∞ **)
Definition pos_infinity : T := Binary.B754_infinity _ _ false.

(** -∞ **)
Definition neg_infinity : T := Binary.B754_infinity _ _ true.

(** +0 **)
Definition pos_zero : T := Binary.B754_zero _ _ false.

(** -0 **)
Definition neg_zero : T := Binary.B754_zero _ _ true.

(** An unspecified positive unsed in [unspec_nan], whose value is made opaque to
  avoid overspecification. **)
Definition unspec_nan_pl : { pl | Binary.nan_pl 53 pl = true }.
  have pl: { pl | Binary.nan_pl 53 pl = true
                  /\ exists b E,
                       proj1_sig Archi.default_nan_64 = Binary.B754_nan _ _ b pl E }.
  { case: Archi.default_nan_64 => f. case: f => // b pl Epl Inan. by repeat eexists. }
  case: pl. move=> pl [E _]. by exists pl.
Qed.

(** An unspecified nan. **)
Definition unspec_nan : T :=
  Binary.B754_nan _ _ ltac:(abstract exact true) _ (proj2_sig unspec_nan_pl).

(** Taking the opposite of a floating point number. **)
Definition opp : T -> T.
  refine (Binary.Bopp _ _ (fun _ => exist _ unspec_nan _)); reflexivity.
Defined.

(** Given a mantissa and an exponent (in radix two), produce a representation for a float.
  The sign is not specified if given 0 as a mantissa. **)
Definition normalise (m e : Z) : T.
  refine (Binary.binary_normalize _ _ _ _ Binary.mode_NE m e ltac:(abstract exact false));
    reflexivity.
Defined.

(** As Flocq is completely undocumented, let us introduce a unit test here, to check
  that indeed we have the correct understanding of definitions.
  We define [half] to be [0.5], adds it to itself, then check that the result is one.
  (Note that because of rounding errors, it may actually not be equal for some parameters,
  but it seems to be fine here.) **)
Definition normalise_unit_test : Prop.
  refine (let half := normalise 1 (-1) in _).
  refine (let twice_half : T :=
            Binary.Bplus _ _ _ _ (fun _ _ => exist _ unspec_nan _) Binary.mode_NE half half in _).
  refine (let one := Binary.Bone _ _ _ _ in _).
  refine (cmp Ceq twice_half one = true).
Grab Existential Variables.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
Defined.
Lemma normalise_unit_test_ok : normalise_unit_test.
Proof.
  reflexivity.
Qed.

(** In contrary to the Wasm specification, we consider that [nans] only takes one parameter
  instead of a set. **)
Definition nans : T -> T :=
  let set_bit_sign default f :=
    if f is Binary.B754_nan b pl E then Binary.B754_nan _ _ true pl E
    else default in
  set_bit_sign (set_bit_sign unspec_nan unspec_nan).

Lemma nans_is_nan : forall f,
  is_nan (nans f) = true.
Proof.
  move=> f. rewrite /nans. case: f => //.
Qed.

(** Importing the square root of floats from the Flocq library with the
  round-to-nearest ties-to-even mode. **)
Definition sqrt (f : T) : T.
  refine (Binary.Bsqrt _ _ _ _ (fun f => exist _ _ (nans_is_nan f)) Binary.mode_NE f);
    abstract lias.
Defined.

Definition fsqrt (f : float) :=
  if is_nan f then nans f
  else if sign f then nans zero
  else if f is Binary.B754_infinity false then pos_infinity
  else if is_zero f then f
  else sqrt f.

(** It seems that Flocq does not define any ceil and floor functions on floating point numbers
  (it does define it on the [R] type, but it is not really useful for us.
  Inspired by CompCert’s [IEEE754_extra.ZofB], we build this operation, parameterised by two
  divisions functions (one for negative numbers and one for positive numbers).
  These divisions functions only differ in the way they round numbers (up, down, or nearest).
  Note that these parameters are used to compute the absolute value of the resulting integer. **)
Definition ZofB_param (divP divN : Z -> Z -> Z) (f : T) :=
  match f with
  | Binary.B754_zero _ => Some 0%Z
  | @Binary.B754_finite _ _ s m 0 _ => Some (cond_Zopp s (Z.pos m))
  | Binary.B754_finite s m (Z.pos e) _ => Some (cond_Zopp s (Z.pos m) * Z.pow_pos radix2 e)%Z
  | Binary.B754_finite s m (Z.neg e) _ =>
    let div := if s then divN else divP in
    Some (cond_Zopp s (div (Z.pos m) (Z.pow_pos radix2 e)))
  | _ => None
  end.

(** We now instantiate this function with the following three division operations, only
  differenciated in how they round numbers. **)
Definition div_down : Z -> Z -> Z := Z.div.
Definition div_up (a b : Z) : Z :=
  ((if Zeq_bool (a mod b) 0 then 0 else 1) + a / b)%Z.
Definition div_near (a b : Z) : Z :=
  (if Z.ltb (a mod b) (b / 2) then div_down a b
   else if Z.gtb (a mod b) (b / 2) then div_up a b
   else (** Ties to even **)
     let d := div_down a b in
     let u := div_up a b in
     if Z.even d then d else u)%Z.

(** From these functions, we can define the usual ceil, floor, trunc, and nearest functions.
  A -o suffix has been added as these function return an option type (returning [None] for
  non-finite and NaN values). **)
Definition ceilo := ZofB_param div_up div_down.
Definition flooro := ZofB_param div_down div_up.
Definition trunco := ZofB_param div_down div_down.
Definition nearesto := ZofB_param div_near div_near.

(** CompCert’s function [IEEE754_extra.ZofB] is exactly [trunco]. **)
Lemma trunco_is_ZofB : forall f,
  trunco f = IEEE754_extra.ZofB _ _ f.
Proof.
  move=> f. case: f => // s m e. by case: s.
Qed.

(** This function does the countrary: it translates an integer to floating point number. **)
Definition BofZ : Z -> T.
  refine (IEEE754_extra.BofZ _ _ _ _); abstract lias.
Defined.

(** [BofZ] is actually just the same thing than calling [normalise] with an empty exponent. **)
Lemma BofZ_normalise : forall i, BofZ i = normalise i 0.
Proof.
  rewrite /BofZ /IEEE754_extra.BofZ /normalise => i.
  f_equal; apply Logic.Eqdep_dec.eq_proofs_unicity_on;
    move=> c; case: c; by [ left | right ]. (* LATER: Remove this bruteforce. *)
Qed.

(** We can then define versions of these operators directly from float to float,
  leaving the float as-is if not a finite value. **)
Definition floatify F (f : T) :=
  if F f is Some i then BofZ i else f.
Definition ceil := floatify ceilo.
Definition floor := floatify flooro.
Definition trunc := floatify trunco.
Definition nearest := floatify nearesto.

(** As above, here are some unit tests to be sure that we are indeed expecting the right thing. **)
Definition ceil_unit_test_1 : Prop :=
  let half := normalise 1 (-1) in
  ceil half = BofZ 1.
Lemma ceil_unit_test_1_ok : ceil_unit_test_1.
Proof.
  reflexivity.
Qed.

Definition ceil_unit_test_2 : Prop :=
  let mhalf := normalise (-1) (-1) in
  ceil mhalf = BofZ 0.
Lemma ceil_unit_test_2_ok : ceil_unit_test_2.
Proof.
  reflexivity.
Qed.

Definition floor_unit_test_1 : Prop :=
  let half := normalise 1 (-1) in
  floor half = BofZ 0.
Lemma floor_unit_test_1_ok : floor_unit_test_1.
Proof.
  reflexivity.
Qed.

Definition floor_unit_test_2 : Prop :=
  let mhalf := normalise (-1) (-1) in
  floor mhalf = BofZ (-1).
Lemma floor_unit_test_2_ok : floor_unit_test_2.
Proof.
  reflexivity.
Qed.

Definition trunc_unit_test_1 : Prop :=
  let half := normalise 1 (-1) in
  trunc half = BofZ 0.
Lemma trunc_unit_test_1_ok : trunc_unit_test_1.
Proof.
  reflexivity.
Qed.

Definition trunc_unit_test_2 : Prop :=
  let mhalf := normalise (-1) (-1) in
  trunc mhalf = BofZ 0.
Lemma trunc_unit_test_2_ok : trunc_unit_test_2.
Proof.
  reflexivity.
Qed.

Definition nearest_unit_test_1 : Prop :=
  let half := normalise 1 (-1) in
  nearest half = BofZ 0.
Lemma nearest_unit_test_1_ok : nearest_unit_test_1.
Proof.
  reflexivity.
Qed.

Definition nearest_unit_test_2 : Prop :=
  let mhalf := normalise (-1) (-1) in
  nearest mhalf = BofZ 0.
Lemma nearest_unit_test_2_ok : nearest_unit_test_2.
Proof.
  reflexivity.
Qed.

Definition nearest_unit_test_3 : Prop :=
  let one_pfive := normalise 3 (-1) in
  nearest one_pfive = BofZ 2.
Lemma nearest_unit_test_3_ok : nearest_unit_test_3.
Proof.
  reflexivity.
Qed.

Definition nearest_unit_test_4 : Prop :=
  let mone_pfive := normalise (-3) (-1) in
  nearest mone_pfive = BofZ (-2).
Lemma nearest_unit_test_4_ok : nearest_unit_test_4.
Proof.
  reflexivity.
Qed.

(** We now define the operators [fceil], [ffloor], [ftrunc], and [fnearest] as defined
  in the Wasm standartd. **)

Definition fceil (f : float) :=
  if is_nan f then nans f
  else if is_infinity f then f
  else if is_zero f then f
  else if cmp Clt f neg_zero && cmp Cgt f (BofZ (-1)) then neg_zero
  else ceil f.

Definition ffloor (f : float) :=
  if is_nan f then nans f
  else if is_infinity f then f
  else if is_zero f then f
  else if cmp Cgt f pos_zero && cmp Clt f (BofZ 1) then pos_zero
  else floor f.

Definition ftrunc (f : float) :=
  if is_nan f then nans f
  else if is_infinity f then f
  else if is_zero f then f
  else if cmp Cgt f pos_zero && cmp Clt f (BofZ 1) then pos_zero
  else if cmp Clt f neg_zero && cmp Cgt f (BofZ (-1)) then neg_zero
  else trunc f.

Definition fnearest (f : float) :=
  if is_nan f then nans f
  else if is_infinity f then f
  else if is_zero f then f
  else if cmp Cgt f pos_zero && cmp Clt f (normalise 1 (-1)) then pos_zero
  else if cmp Clt f neg_zero && cmp Cgt f (normalise (-1) (-1)) then neg_zero
  else nearest f.

(** Negate the sign bit of a float. **)
Definition negate_sign (f : T) : T :=
  match f with
  | Binary.B754_zero s => Binary.B754_zero _ _ (~~ s)
  | Binary.B754_infinity s => Binary.B754_infinity _ _ (~~ s)
  | Binary.B754_nan s pl E => Binary.B754_nan _ _ (~~ s) pl E
  | Binary.B754_finite s m e E => Binary.B754_finite _ _ (~~ s) m e E
  end.

Definition fcopysign (f1 f2 : T) :=
  if sign f1 == sign f2 then f1
  else negate_sign f1.

Definition Tmixin : mixin_of T := {|
    float_zero := pos_zero ;
    float_neg := neg ;
    float_abs := abs ;
    float_ceil := fceil ;
    float_floor := ffloor ;
    float_trunc := ftrunc ;
    float_nearest := fnearest ;
    float_sqrt := fsqrt ;
    float_add := add ;
    float_sub := sub ;
    float_mul := mul ;
    float_div := mul ;
    float_min x y := if cmp Clt x y then x else y ;
    float_max x y := if cmp Cgt x y then x else y ;
    float_copysign := fcopysign ;
    float_eq := cmp Ceq ;
    float_lt := cmp Clt ;
    float_gt := cmp Cgt ;
    float_le := cmp Cle ;
    float_ge := cmp Cge
  |}.

Definition eqTP := Equality_axiom_eq_dec eq_dec.

Canonical T_eqMixin := EqMixin eqTP. (* LATER: Frustration: Coq ignores this one because [fun v1 v2 : float => is_left (eq_dec v1 v2)] is not named. *)
Canonical T_eqType := Eval hnf in EqType T T_eqMixin.

Definition cT : type.
  refine (@Pack T {| mixin := Tmixin |}).
  apply T_eqMixin.
Defined.

End Wasm_float64.

