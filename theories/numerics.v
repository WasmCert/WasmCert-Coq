(** Common useful definitions **)
(* (C) M. Bodin, J. Pichon - see LICENSE.txt *)

Require Import common.
From Coq Require ZArith ZArith.Int ZArith.BinInt ZArith.Zpower.
From compcert Require Integers Floats.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

From Flocq Require Import Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Most of the content of this file follows the specification from
  https://webassembly.github.io/spec/core/exec/numerics.html **)

(** * Integers **)

Module Wasm_int.

Import ZArith.BinInt.

Coercion Z.of_nat : nat >-> Z.

(** ** Declaration of Operations **)

(** These operations follow the standard straightforwardly.
  Some of these operations are sometimes said to be undefined
  in the standard: such operations have been translated by
  returning an option type, as is usual in Coq. **)
(** Operations have been added converting to and from [nat] and [Z].
  These are typically used in the specification to convert to and
  from list lengths and other computed values:
  - [int_of_Z] converts a [Z] into [int_t].  The number is considered
    modulo the maximum representable integer.  It doesn’t matter
    whether the number is meant to be considered as signed or unsigned,
    as both would return the same representation: signedness is only
    important when interpreting the stored integer, not when converting
    to it.  This is due to the fact that converting any representation to
    a signed or unsigned one, then back to its original signed or unsigned
    interpretation leaves it unchanged: see Lemma [signed_repr_unsigned] and
    [unsigned_repr_signed] below.
  - [nat_of_uint] considers an [int_t] as an unsigned interpretation
    and converts it into a natural number.
  - [Z_of_uint] returns the same result than [nat_of_uint], but
    encoded in [Z].
  - [Z_of_sint] considers an [int_t] as a signed interpretation and
    converts it into a [Z]. **)

Record mixin_of (int_t : Type) := Mixin {
  int_zero : int_t ;
  (** Bit operations **)
  int_clz : int_t -> int_t ;
  int_ctz : int_t -> int_t ;
  int_popcnt : int_t -> int_t ;
  (** Binary operators **)
  int_add : int_t -> int_t -> int_t ;
  int_sub : int_t -> int_t -> int_t ;
  int_mul : int_t -> int_t -> int_t ;
  int_div_u : int_t -> int_t -> option int_t ;
  int_div_s : int_t -> int_t -> option int_t ;
  int_rem_u : int_t -> int_t -> option int_t ;
  int_rem_s : int_t -> int_t -> option int_t ;
  (** Binary operators about bits **)
  int_and : int_t -> int_t -> int_t ;
  int_or : int_t -> int_t -> int_t ;
  int_xor : int_t -> int_t -> int_t ;
  int_shl : int_t -> int_t -> int_t ;
  int_shr_u : int_t -> int_t -> int_t ;
  int_shr_s : int_t -> int_t -> int_t ;
  int_rotl : int_t -> int_t -> int_t ;
  int_rotr : int_t -> int_t -> int_t ;
  (** Equalities **)
  int_eq : int_t -> int_t -> bool ;
  int_eqz : int_t -> bool ;
  (** Comparisons **)
  int_lt_u : int_t -> int_t -> bool ;
  int_lt_s : int_t -> int_t -> bool ;
  int_gt_u : int_t -> int_t -> bool ;
  int_gt_s : int_t -> int_t -> bool ;
  int_le_u : int_t -> int_t -> bool ;
  int_le_s : int_t -> int_t -> bool ;
  int_ge_u : int_t -> int_t -> bool ;
  int_ge_s : int_t -> int_t -> bool ;
  (** Conversion to and from [nat] and [Z] **)
  int_of_Z : Z -> int_t ;
  nat_of_uint : int_t -> nat ;
  N_of_uint : int_t -> N ;
  Z_of_uint : int_t -> Z ;
  Z_of_sint : int_t -> Z ;
}.

Record class_of T := Class { base : Equality.class_of T; mixin : mixin_of T }.
Local Coercion base : class_of >-> Equality.class_of.

Structure type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Definition int_ne (e : type) : sort e -> sort e -> bool :=
  let 'Pack _ (Class _ m) := e in
    fun x => fun y => negb (int_eq m x y).

(** ** Definitions **)

Module Make (WS: Integers.WORDSIZE).

Import Integers.

Include Make (WS).

(** We use CompCert’s [int] as a representation, as CompCert is associated
  with very similar operations than Wasm, and has already been overly tested. **)
Definition T := int.

Lemma Z_lt_irrelevant : forall x y (p1 p2 : Z.lt x y), p1 = p2.
Proof.
  rewrite /Z.lt. move=> x y p1 p2.
  apply: Eqdep_dec.eq_proofs_unicity. move=> [] []; by [ left | right; discriminate ].
Qed.

Lemma eq_T_intval : forall x y : T, intval x = intval y -> x = y.
Proof.
  move=> [x [Vx Rx]] [y [Vy Ry]] /= E. subst. f_equal.
  rewrite (Z_lt_irrelevant Vx Vy).
  by rewrite (Z_lt_irrelevant Rx Ry).
Qed.

Lemma eq_eqP : Equality.axiom (eq : T -> T -> bool).
Proof.
  move=> x y. rewrite /eq. case: Coqlib.zeq => [E|E].
  - apply/ReflectT. by apply: eq_T_intval.
  - apply/ReflectF. move=> ?. subst. exact: E.
Qed.

Lemma Z_mod_modulus_id : forall i,
  (-1 < i < modulus)%Z ->
  Z_mod_modulus i = i.
Proof.
  move=> i C. rewrite/Z_mod_modulus /=. destruct i; try by lias.
  rewrite Zbits.P_mod_two_p_eq. apply: Z.mod_small.
  unfold modulus in C. by lias.
Qed.

Lemma Z_mod_modulus_intval : forall i : T,
  Z_mod_modulus (intval i) = intval i.
Proof. move=> [i C]. by apply: Z_mod_modulus_id. Qed.

Lemma Z_mod_modulus_add_modulus : forall i,
  Z_mod_modulus i = Z_mod_modulus (i + modulus).
Proof.
  move=> i. destruct i as [|i|i].
  - rewrite /= Zbits.P_mod_two_p_eq. rewrite/Zpower.two_power_nat.
    rewrite -(Zdiv.Z_mod_plus _ (-1)) => //.
    by rewrite Z.mod_small; lias.
  - repeat rewrite /= Zbits.P_mod_two_p_eq /Zpower.two_power_nat.
    by rewrite -(Zdiv.Z_mod_plus _ 1).
  - rewrite {1}/Z_mod_modulus. rewrite Zbits.P_mod_two_p_eq. case: Coqlib.zeq => [E|E].
    + rewrite/Z_mod_modulus. destruct (_ + _)%Z as [|p|p] eqn:Ep.
      * by lias.
      * rewrite Zbits.P_mod_two_p_eq. rewrite -Ep /modulus.
        rewrite -(Zdiv.Z_mod_plus _ (-1)) => //.
        rewrite_by (Z.neg i + Zpower.two_power_nat wordsize
                    + -1 * Zpower.two_power_nat wordsize = Z.neg i)%Z.
        apply Zdiv.Z_mod_zero_opp_full in E. by lias.
      * rewrite Zbits.P_mod_two_p_eq. destruct Coqlib.zeq as [E'|E'] => //.
        apply Zdiv.Z_mod_zero_opp_full in E. simpl in E.
        unfold modulus, Zpower.two_power_nat in *.
        rewrite -(Zdiv.Z_mod_plus _ 1) in E; last by lias.
        rewrite Z.mul_1_l in E. rewrite Ep in E.
        by rewrite -Z.mod_opp_l_nz; lias.
    + rewrite/Z_mod_modulus. rewrite /modulus /Zpower.two_power_nat.
      destruct (_ + _)%Z as [|p|p] eqn:Ep.
      * exfalso. apply: E.
        rewrite_by (Z.pos i = Z.pos (Zpower.shift_nat wordsize 1)).
        by apply: Zdiv.Z_mod_same_full.
      * rewrite Zbits.P_mod_two_p_eq. rewrite -Ep.
        rewrite -(Zdiv.Z_mod_plus (_ + _)%Z (-1)) => //.
        rewrite_by (Z.neg i + Zpower.two_power_nat wordsize
                    + -1 * Zpower.two_power_nat wordsize = Z.neg i)%Z.
        rewrite_by (Z.neg i mod Zpower.two_power_nat wordsize
                    = - Z.pos i mod Zpower.two_power_nat wordsize)%Z.
        by rewrite Zdiv.Z_mod_nz_opp_full; last by lias.
      * rewrite Zbits.P_mod_two_p_eq.
        rewrite_by (Z.pos p = Z.pos i - Z.pos (Zpower.shift_nat wordsize 1))%Z.
        destruct Coqlib.zeq as [E'|E'].
        -- unfold Zpower.two_power_nat in *.
           rewrite Zdiv.Zplus_mod in E'.
           rewrite Zdiv.Z_mod_zero_opp_full in E'; last by rewrite Zdiv.Z_mod_same_full.
           rewrite Z.add_0_r in E'. by rewrite Zdiv.Zmod_mod in E'.
        -- rewrite Zdiv.Zplus_mod. rewrite/Zpower.two_power_nat.
           rewrite Zdiv.Z_mod_zero_opp_full; last by rewrite Zdiv.Z_mod_same_full.
           rewrite Z.add_0_r. by rewrite Zdiv.Zmod_mod.
Qed.

Lemma modulus_mod_2 : (modulus mod 2 = 0)%Z.
Proof.
  rewrite /modulus /Zpower.two_power_nat Zpower.shift_nat_correct Zpower.Zpower_nat_Z.
  move: WS.wordsize_not_zero => N. rewrite/wordsize.
  destruct WS.wordsize as [|ws] => //=. destruct ws as [|ws] => //=.
  rewrite /Z.pow_pos Pos.iter_succ. apply: Znumtheory.Zdivide_mod.
  rewrite_by (2 * Pos.iter (Z.mul 2) 1 (Pos.of_succ_nat ws) * 1
              = 2 * Pos.iter (Z.mul 2) 1 (Pos.of_succ_nat ws))%Z.
  by apply: Z.divide_factor_l.
Qed.

Lemma modulus_ge_2 : (modulus >= 2)%Z.
Proof.
  rewrite /modulus /Zpower.two_power_nat Zpower.shift_nat_correct Zpower.Zpower_nat_Z.
  move: WS.wordsize_not_zero. rewrite/wordsize. destruct WS.wordsize as [|ws] => //= _.
  rewrite /Z.pow_pos. destruct ws as [|ws] => //.
  rewrite Pos.iter_succ. replace 2%Z with (2 * 1)%Z at 3; last by lias.
  rewrite -> Z.mul_1_r. apply: Zorder.Zmult_ge_compat_l; last by lias.
  fold (Pos.of_succ_nat ws). move: (Zaux.Zpower_pos_gt_0 2 (Pos.of_succ_nat ws)).
  rewrite /Z.pow_pos. by lias.
Qed.

Lemma wordsize_modulus : (wordsize < modulus)%Z.
Proof.
  move: WS.wordsize_not_zero. rewrite /modulus /wordsize.
  case: WS.wordsize => [|ws] //= _.
  rewrite Zpower.two_power_nat_equiv -Pos2Z.inj_pow .
  apply: Pos2Z.pos_lt_pos. elim ws; first by [].
  move=> n. rewrite SuccNat2Pos.inj_succ.
  rewrite /Pos.pow Pos.iter_succ => IH. by lias.
Qed.

Lemma modulus_minus_half_modulus : (modulus - half_modulus = half_modulus)%Z.
Proof.
  rewrite /half_modulus. move: modulus_mod_2 (Zdiv.Zmod_eq_full modulus 2). by lias.
Qed.

Lemma modulus_twice_half_modulus : (modulus = 2 * half_modulus)%Z.
Proof. move: modulus_minus_half_modulus. by lias. Qed.

Lemma repr_add_modulus : forall i,
  repr i = repr (i + modulus).
Proof.
  move=> i. apply: eq_T_intval => /=. by rewrite Z_mod_modulus_add_modulus.
Qed.

Lemma repr_add_modulus_rev : forall i,
  repr (i - modulus) = repr i.
Proof.
  move=> i. rewrite repr_add_modulus. f_equal. by lias.
Qed.

Lemma repr_inv : forall i j : Z,
  (-1 < i < modulus)%Z ->
  (-1 < j < modulus)%Z ->
  repr i = repr j ->
  i = j.
Proof.
  move=> i j I J. rewrite /repr. case.
  by rewrite (Z_mod_modulus_id I) (Z_mod_modulus_id J).
Qed.

(** The following four lemmas justifies to not care about the sigedness of numbers
  when converting to [T]. **)

Lemma unsigned_repr_unsigned : forall i : T,
  unsigned (repr (unsigned i)) = unsigned i.
Proof.
  move=> i /=. by apply: Z_mod_modulus_intval.
Qed.

Lemma signed_repr_signed : forall i : T,
  signed (repr (signed i)) = signed i.
Proof.
  move=> i /=. rewrite/signed. destruct (Coqlib.zlt (unsigned i) half_modulus) eqn:E.
  - by rewrite unsigned_repr_unsigned E.
  - by rewrite repr_add_modulus_rev unsigned_repr_unsigned E.
Qed.

Lemma signed_repr_unsigned : forall i : T,
  signed (repr (unsigned i)) = signed i.
Proof.
  move=> i. by rewrite/signed unsigned_repr_unsigned.
Qed.

Lemma unsigned_repr_signed : forall i : T,
  unsigned (repr (signed i)) = unsigned i.
Proof.
  move=> i. rewrite/signed. destruct Coqlib.zlt as [E|E].
  - by rewrite unsigned_repr_unsigned.
  - by rewrite repr_add_modulus_rev unsigned_repr_unsigned.
Qed.


(** An operation that we did not find in CompCert was a way to convert
  an integer to its representation as a list of booleans.
  We thus define all the operations needed to get this list of booleans
  and the corresponding properties. **)

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

Lemma power_index_to_bits_in : forall c (l: seq Z) n,
  n < c ->
  seq.nth false (power_index_to_bits c l) (c - n - 1) = ((n : Z) \in l).
Proof.
  move=> c l n /leP I. move: l. elim: I.
  - move=> l /=. by rewrite_by (n.+1 - n - 1 = 0).
  - move=> {} c I IH l. rewrite_by (c.+1 - n - 1 = 1 + (c - n - 1)). by apply: IH.
Qed.

Lemma power_index_to_bits_nth : forall c l n,
  n < c ->
  seq.nth false (power_index_to_bits c l) n = ((Z.of_nat (c - n - 1)) \in l).
Proof.
  move=> c l n I. have E: (n = c - (c - n - 1) - 1); first by lias.
  rewrite {1} E. apply: power_index_to_bits_in. by lias.
Qed.

(** Given a [T], return a sequence of bits representing the integer.
  The first bit is the most significant bit. **)
Definition convert_to_bits (x : T) : seq bool :=
  let: l := Zbits.Z_one_bits wordsize (intval x) 0 in
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

Lemma convert_to_bits_nth : forall (p : nat) x,
  p < wordsize ->
  seq.nth false (convert_to_bits x) p
  = (Z.of_nat (wordsize - p - 1) \in Zbits.Z_one_bits wordsize (intval x) 0).
Proof.
  move=> p x I. rewrite /convert_to_bits. by rewrite power_index_to_bits_nth.
Qed.

Lemma convert_to_bits_one :
  convert_to_bits one
  = rcons (seq.nseq (wordsize - 1) false) true.
Proof.
  apply: (@eq_from_nth _ false).
  - rewrite convert_to_bits_size size_rcons size_nseq /wordsize.
    move: WS.wordsize_not_zero. by lias.
  - move=> i. rewrite convert_to_bits_size => I. rewrite convert_to_bits_nth //.
    have E: intval one = Zpower.two_p Z0.
    { compute. move: WS.wordsize_not_zero. by elim: WS.wordsize. }
    rewrite {} E Zbits.Z_one_bits_two_p /=.
    + rewrite nth_rcons nth_nseq size_nseq.
      case E: (i == wordsize - 1); move/ssrnat.eqnP: E => E.
      * rewrite {} E. rewrite_by (wordsize - (wordsize - 1) - 1 = 0).
        by rewrite_by (wordsize - 1 < wordsize - 1 = false).
      * rewrite_by (i < wordsize - 1 = true).
        rewrite in_cons in_nil Bool.orb_false_r.
        rewrite_by ((Z.of_nat (wordsize - i - 1) == 0) = (wordsize - i - 1 == 0)).
        apply gtn_eqF. move/leP: I E. move: WS.wordsize_not_zero. rewrite/wordsize. by lias.
    + by lias.
Qed.

(** As the definitions [zero], [one], and [mone] are used later on,
  let us ensure that some basic properties exist about them. **)

Lemma repr_0 : repr 0 = zero.
Proof. reflexivity. Qed.

Lemma repr_1 : repr 1 = one.
Proof. reflexivity. Qed.

Lemma repr_m1 : repr (-1) = mone.
Proof. reflexivity. Qed.

Lemma nat_Z_lt_neq : forall a b,
  a < b ->
  (a == b :> Z) = false.
Proof. by lias. Qed.

Lemma nat_Z_gt_neq : forall a b,
  a < b ->
  (b == a :> Z) = false.
Proof. by lias. Qed.

Lemma convert_to_bits_two_p : forall p : nat,
  p < wordsize ->
  convert_to_bits (repr (Zpower.two_p p))
  = seq.nseq (wordsize - 1 - p) false ++ [:: true] ++ seq.nseq p false.
Proof.
  rewrite /convert_to_bits /repr /intval. move=> p I.
  have Rm: Z_mod_modulus (Zpower.two_p p) = Zpower.two_p p.
  { rewrite /Z_mod_modulus. case Epp: Zpower.two_p => //=.
    - rewrite Zbits.P_mod_two_p_eq. rewrite Z.mod_small //.
      split=> //. rewrite - {} Epp.
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
      * by lias.
  - split.
    + by apply: Znat.Nat2Z.is_nonneg.
    + apply: Znat.inj_lt. by apply/leP.
Qed.

(** Auxiliary function for [convert_from_bits]. **)
Fixpoint convert_from_bits_to_Z_one_bits l : seq Z :=
  match l with
  | [::] => [::]
  | b :: l =>
    let: c := convert_from_bits_to_Z_one_bits l in
    if b then
      (seq.size l : Z) :: c
    else c
  end.

Lemma convert_from_bits_to_Z_one_bits_power_index_to_bits : forall l : seq Z,
  uniq l ->
  Zbits.powerserie (convert_from_bits_to_Z_one_bits (power_index_to_bits wordsize l))
  = Zbits.powerserie (filter (fun x => Coqlib.zlt x wordsize) l).
Proof.
  elim wordsize.
  - move=> /=. elim.
    + by [].
    + move=> a l IH /=. move/andP => [N U].
      by destruct a => //=; rewrite -IH.
  - move=> ws IH l U /=. rewrite power_index_to_bits_size. destruct in_mem eqn:E => /=.
    + rewrite IH => //.
      {
        move: l U E. clear. elim.
        - by [].
        - move=> a l IH /= /andP [N U]. rewrite in_cons => /orP. destruct Coqlib.zlt as [L|L] => /=.
          + move=> [+|I].
            * move/eqP => ?. subst. by lias.
            * rewrite_by (Zpower.two_p ws + (Zpower.two_p a
                          + Zbits.powerserie [seq x <- l | Coqlib.zlt x ws])
                          = Zpower.two_p a + (Zpower.two_p ws
                          + Zbits.powerserie [seq x <- l | Coqlib.zlt x ws]))%Z.
              rewrite IH => //. destruct Coqlib.zlt as [L'|L'] => //.
              exfalso. by lias.
          + move=> [+|I].
            * move/eqP => ?. subst. destruct Coqlib.zlt as [L'|L'] => //=.
              -- by rewrite filter_out_zlt.
              -- by lias.
            * rewrite IH => //. destruct Coqlib.zlt as [L'|L'] => //=.
              exfalso. have ?: (a = ws); first by lias. subst. by rewrite I in N.
      }
    + rewrite -filter_out_zlt; last by rewrite E. by rewrite IH.
Qed.

(** Converting a sequence of bits back to [T]. **)
Definition convert_from_bits l :=
  repr (Zbits.powerserie (convert_from_bits_to_Z_one_bits l)).

Lemma Zbits_Z_one_bits_range : forall wordsize x i b,
  b \in Zbits.Z_one_bits wordsize x i ->
  (i <= b < i + wordsize)%Z.
Proof.
  elim.
  - by [].
  - move=> ws IH x i b /=.
    have L: (b \in Zbits.Z_one_bits ws (Z.div2 x) (i + 1) ->
             (i <= b < i + Z.pos (Pos.of_succ_nat ws))%Z).
    { move=> I. apply IH in I. by lias. }
    destruct Z.odd.
    + rewrite in_cons. move/orP. move=> [E|I'].
      * by lias.
      * by apply: L.
    + by apply: L.
Qed.

Lemma Zbits_Z_one_bits_uniq : forall x i,
  uniq (Zbits.Z_one_bits wordsize x i).
Proof.
  elim wordsize.
  - by [].
  - move=> ws IH x i /=. destruct Z.odd => //=.
    apply/andP. split => //.
    apply/negP => I. apply Zbits_Z_one_bits_range in I. by lias.
Qed.

Lemma convert_to_from_bits : forall a,
  a = convert_from_bits (convert_to_bits a).
Proof.
  move=> a. rewrite /convert_from_bits convert_from_bits_to_Z_one_bits_power_index_to_bits.
  - have E: [seq x <- Zbits.Z_one_bits wordsize (intval a) 0 | Coqlib.zlt x wordsize]
            = Zbits.Z_one_bits wordsize (intval a) 0.
    {
      rewrite filter_for_all => //.
      rewrite list_all_forall => e. rewrite -List_In_in_mem => I.
      apply Zbits_Z_one_bits_range in I. destruct Coqlib.zlt => //.
      lias.
    }
    rewrite E -Zbits.Z_one_bits_powerserie.
    + apply: eq_T_intval => /=. by rewrite Z_mod_modulus_intval.
    + destruct a as [a C] => /=. move: {E} C. rewrite/modulus. by lias.
  - by apply: Zbits_Z_one_bits_uniq.
Qed.


(** Once the conversion to and from lists of bits have been defined,
  the bit-related functions are easy to define. **)

(** Return the count of leading zero bits. **)
Definition clz i :=
  let: l := convert_to_bits i in
  repr (seq.find (fun b => b == true) l).

(** Return the count of trailing zero bits. **)
Definition ctz i :=
  let: l := convert_to_bits i in
  repr (seq.find (fun b => b == true) (seq.rev l)).

(** Return the count of non-zero bits. **)
Definition popcnt i :=
  let: l := convert_to_bits i in
  repr (seq.count (fun b => b == true) l).

Local Lemma Zbits_powerserie_uniq_in : forall z l,
  uniq l ->
  z \in l ->
  Zbits.powerserie l = (Zpower.two_p z + Zbits.powerserie (filter (fun x => x != z) l))%Z.
Proof.
  move=> z. elim.
  - by [].
  - move=> z' l IH /= /andP [N U]. rewrite in_cons => /orP [+|I].
    + move/eqP => ?. subst.
      f_equal. rewrite eq_refl => /=. rewrite filter_for_all => //.
      rewrite list_all_forall => z''. rewrite -List_In_in_mem => I.
      apply/eqP => ?. subst. by rewrite I in N.
    + case_eq (z' == z) => /eqP D /=.
      * subst. by rewrite I in N.
      * rewrite IH => //. lias.
Qed.

Local Lemma power_index_to_bits_Zbits_powerserie : forall (wordsize : nat) l1 l2,
  uniq l1 ->
  uniq l2 ->
  power_index_to_bits wordsize l1 = power_index_to_bits wordsize l2 ->
  Zbits.powerserie (filter (fun b => Coqlib.zlt (-1) b && Coqlib.zlt b wordsize)%Z l1)
  = Zbits.powerserie (filter (fun b => Coqlib.zlt (-1) b && Coqlib.zlt b wordsize)%Z l2).
Proof.
  elim => /=.
  - move=> l1 l2 U1 U2 _. rewrite filter_none.
    + rewrite filter_none.
      * by [].
      * rewrite list_all_forall => a I.
        repeat destruct Coqlib.zlt => //. exfalso. by lias.
    + rewrite list_all_forall => a I.
      repeat destruct Coqlib.zlt => //. exfalso. by lias.
  - move=> ws IH l1 l2 U1 U2. case => E1 E2.
    repeat rewrite filter_and. destruct in_mem eqn: E1'.
    + rewrite (Zbits_powerserie_uniq_in (z := ws)).
      * rewrite (Zbits_powerserie_uniq_in (z := ws) (l := filter _ (filter _ l2))).
        -- f_equal. repeat rewrite -filter_and. erewrite eq_in_filter.
           ++ erewrite IH; try eassumption.
              f_equal. apply: eq_in_filter.
              move=> x I2. apply is_true_bool.
              by repeat destruct Coqlib.zlt => /=;
                (try by lias_simpl; have ?: (x = ws); [ lias | subst; eauto ]);
                lias.
           ++ move=> x I1. apply is_true_bool.
              by repeat destruct Coqlib.zlt => /=;
                (try by lias_simpl; have ?: (x = ws); [ lias | subst; eauto ]);
                lias.
        -- by repeat apply: filter_uniq.
        -- repeat rewrite mem_filter. by repeat destruct Coqlib.zlt => //=; lias.
      * by repeat apply filter_uniq.
      * repeat rewrite mem_filter. by repeat destruct Coqlib.zlt => //=; lias.
    + rewrite -filter_out_zlt; last by rewrite E1'.
      rewrite -filter_out_zlt; last by rewrite -E1.
      repeat rewrite -filter_and. by apply: IH.
Qed.

Lemma convert_to_bits_inj : forall a b,
  convert_to_bits a = convert_to_bits b ->
  a = b.
Proof.
  move=> [a Ra] [b Rb] E. apply: eq_T_intval => /=.
  unfold modulus in Ra, Rb.
  rewrite (Zbits.Z_one_bits_powerserie wordsize a); last by lias.
  rewrite (Zbits.Z_one_bits_powerserie wordsize b); last by lias.
  unfold convert_to_bits in E. move: E => /= E.
  apply power_index_to_bits_Zbits_powerserie in E.
  {
    move: E. repeat rewrite filter_for_all => //.
    - rewrite list_all_forall => e I. apply Zbits.Z_one_bits_range in I.
      apply/andP. repeat destruct Coqlib.zlt => //; by lias.
    - rewrite list_all_forall => e I. apply Zbits.Z_one_bits_range in I.
      apply/andP. repeat destruct Coqlib.zlt => //; by lias.
  }
  - by apply: Zbits_Z_one_bits_uniq.
  - by apply: Zbits_Z_one_bits_uniq.
Qed.

Lemma clz_wordsize : forall i,
  clz i = repr wordsize ->
  i = repr 0.
Proof.
  rewrite/clz. move=> i E.
  apply repr_inv in E.
  - have: ~~ seq.has (fun b => b == true) (convert_to_bits i).
    { rewrite has_find. rewrite convert_to_bits_size. by lias. }
    rewrite -all_predC => N.
    have Ec: (convert_to_bits i = convert_to_bits zero).
    {
      move/all_nthP: N => /= F. rewrite convert_to_bits_size in F.
      apply (@seq_nth_eq _ false).
      - by repeat rewrite convert_to_bits_size.
      - rewrite convert_to_bits_size => n I. rewrite convert_to_bits_zero nth_nseq.
        move: (F false n I). move/eqP. destruct nth => //.
          by destruct leq.
    }
    apply: convert_to_bits_inj Ec.
  - split; first by lias. apply: (Z.le_lt_trans _ _ _ _ wordsize_modulus).
    match goal with |- context C [find ?p ?l] => move: (find_size p l) end.
    rewrite convert_to_bits_size. by lias.
  - move: wordsize_modulus. by lias.
Qed.

Lemma ctz_wordsize : forall i,
  ctz i = repr wordsize ->
  i = repr 0.
Proof.
  rewrite/clz. move=> i E.
  apply repr_inv in E.
  - have: ~~ seq.has (fun b => b == true) (rev (convert_to_bits i)).
    { rewrite has_find. rewrite size_rev convert_to_bits_size. by lias. }
    rewrite -all_predC => N.
    have Ec: (rev (convert_to_bits i) = convert_to_bits zero).
    {
      move/all_nthP: N => /= F. rewrite size_rev convert_to_bits_size in F.
      apply (@seq_nth_eq _ false).
      - rewrite size_rev. by repeat rewrite convert_to_bits_size.
      - rewrite size_rev convert_to_bits_size => n I. rewrite convert_to_bits_zero nth_nseq.
        move: (F false n I). move/eqP. destruct nth => //.
          by destruct leq.
    }
    apply rev_move in Ec.
    have Ep: (rev (convert_to_bits zero) = convert_to_bits zero).
    { by rewrite convert_to_bits_zero rev_nseq => //. }
    rewrite Ep in Ec.
    apply: convert_to_bits_inj Ec.
  - split; first by lias. apply: (Z.le_lt_trans _ _ _ _ wordsize_modulus).
    match goal with |- context C [find ?p ?l] => move: (find_size p l) end.
    rewrite size_rev convert_to_bits_size. by lias.
  - move: wordsize_modulus. by lias.
Qed.

(* FIXME: stuff that we may want to prove. 
Lemma popcnt_wordsize : forall i,
  popcnt i = repr wordsize ->
  i = repr 0.

Lemma ctz_shl : forall i k,
  ctz (shl i k) = min wordsize (ctz i + k).

Lemma clz_shr : forall i k,
  clz (shr i k) = min wordsize (clz i + k).
*)

(** The following definitions mirrors as close as possible the specification
  of the corresponding operation in
  https://webassembly.github.io/spec/core/exec/numerics.html
  In the case of functions like [iadd] whose specification is just
  “Return the result of adding i1 and i2 modulo 2^N.”, this may not
  be obvious, but for more complex operations like [idiv_s], a great
  care has been taken to explicitely write all steps, even if these
  were redundant.
  This explicitness is a direct application of the line-by-line
  closeness of our specification. **)

(** Return the result of adding two numbers modulo [max_unsigned]. **)
Definition iadd : T -> T -> T := add.

(** Return the result of substracting two numbers modulo [max_unsigned]. **)
Definition isub : T -> T -> T := sub.

(** Return the result of multiplicating two numbers modulo [max_unsigned]. **)
Definition imul : T -> T -> T := mul.

(** Return the result of dividing two numbers towards zero,
  undefined if the second number is zero. **)
Definition idiv_u (i1 i2 : T) : option T :=
  if eq i2 zero then None
  else Some (divu i1 i2).

(** Signed division, following the Wasm standard. **)
Definition idiv_s (i1 i2 : T) : option T :=
  let: j1 := signed i1 in
  let: j2 := signed i2 in
  if j2 == 0 then None
  else
    let: d := (j1 ÷ j2)%Z in
    if d == half_modulus then None
    else Some (repr d).

(** The standard states as a property that [-2^(N-1)/-1] is not representable,
  and thus that [idiv_s] should not be defined on it. **)
Lemma idiv_s_2_wordsize_m1_m1 : idiv_s (repr (- Zpower.two_p (wordsize - 1))) (repr (-1)) = None.
Proof.
  rewrite /idiv_s /signed.
  have Em1: (unsigned (repr (-1)) = modulus - 1)%Z.
  {
    move: WS.wordsize_not_zero => N.
    by rewrite /= /wordsize Zbits.P_mod_two_p_eq Zdiv.Zmod_small; destruct WS.wordsize.
  }
  rewrite Em1.
  have Emhm: (modulus - 1 >= half_modulus)%Z.
  {
    apply: (Zorder.Zmult_ge_reg_r _ _ 2); first by lias.
    move: modulus_ge_2 (Zdiv.Zmod_eq modulus 2).
    rewrite modulus_mod_2 /half_modulus /modulus.
    lias.
  }
  destruct Coqlib.zlt as [?|?] => //.
  rewrite_by (modulus - 1 - modulus = -1)%Z.
  rewrite_by ((-1 == 0)%Z = false).
  rewrite -Pos2Z.opp_pos Z.quot_opp_r // Z.quot_1_r.
  have E: (unsigned (repr (- Zpower.two_p (wordsize - 1))) = half_modulus)%Z.
  {
    rewrite -half_modulus_power /= Z_mod_modulus_add_modulus.
    rewrite_by (-half_modulus + modulus = modulus - half_modulus)%Z.
    rewrite modulus_minus_half_modulus. apply: Z_mod_modulus_id.
    rewrite modulus_twice_half_modulus.
    move: half_modulus_pos. by lias.
  }
  rewrite E. destruct Coqlib.zlt as [E'|E'].
  - by lias.
  - rewrite_by ((-(half_modulus - modulus)) = modulus - half_modulus)%Z.
    rewrite modulus_minus_half_modulus. by rewrite_by (half_modulus == half_modulus).
Qed.

(** Return the quotient of two numbers, undefined if the second number is zero. **)
Definition irem_u (i1 i2 : T) : option T :=
  if eq i2 zero then None
  else Some (modu i1 i2).

(** This property of [idiv_u] and [irem_u] is stated in the Wasm standard. **)
Lemma idiv_u_irem_u : forall i1 i2 d r,
  idiv_u i1 i2 = Some d ->
  irem_u i1 i2 = Some r ->
  i1 = iadd (imul i2 d) r.
Proof.
  rewrite /idiv_u /irem_u. move=> i1 i2 d r. case E: (eq i2 zero) => //.
  case=> ED. rewrite - {} ED. case=> ER. rewrite - {} ER.
  move: E. rewrite /add /mul /divu /modu /eq.
  case i1 => {i1} v1 R1. case i2 => {i2} v2 R2 /=. case: Coqlib.zeq => // D _.
  apply: eq_T_intval => /=.
  have := Zdiv.Z_div_mod_full v1 _ D. rewrite Zaux.Zdiv_eucl_unique. move=> [E R].
  repeat rewrite Z_mod_modulus_eq. rewrite Z.mul_mod_idemp_r => //.
  rewrite Z.add_mod_idemp_l => //. rewrite Z.add_mod_idemp_r => //.
  rewrite -E. rewrite Zdiv.Zmod_small => //. by lias.
Qed.

(** Return the quotient of two numbers, with the sign of the dividend.
  Note that the sign convention differs from the [%] operator in C. **)
Definition irem_s (i1 i2 : T) : option T :=
  let: j1 := signed i1 in
  let: j2 := signed i2 in
  if j2 == 0 then None
  else
    (** We then return the remainder of dividing [j1] by [j2], with the sign of [j1]. **)
    let: r := (j1 mod j2)%Z in
    let: r :=
      if r == 0 then r
      else
        match r >=? 0, j1 >=? 0 with
        | true, true | false, false => r
        | true, false | false, true => r - j2
        end%Z in
    Some (repr r).

(** This property of [idiv_s] and [irem_s] is stated in the Wasm standard. **)
Lemma idiv_s_irem_s : forall i1 i2 d r,
  idiv_s i1 i2 = Some d ->
  irem_s i1 i2 = Some r ->
  i1 = iadd (imul i2 d) r.
Proof.
  rewrite /idiv_s /irem_s. move=> i1 i2 d r. case E1: (signed i2 == 0) => //.
  case E2: ((signed i1 ÷ signed i2)%Z == half_modulus) => //.
  case=> ED. rewrite - {} ED. case=> ER. rewrite - {} ER.
  apply: eq_T_intval. move: E1 E2. rewrite /add /mul /=.
  case i1 => {i1} v1 R1. case i2 => {i2} v2 R2 /=.
  move/eqP => D. have := Zdiv.Z_div_mod_full (signed {| intval := v1; intrange := R1 |}) _ D.
  rewrite Zaux.Zdiv_eucl_unique. move=> [E R] /eqP.
  repeat rewrite Z_mod_modulus_eq. rewrite Z.mul_mod_idemp_r => //.
  rewrite Z.add_mod_idemp_l => //. rewrite Z.add_mod_idemp_r => //.
  move: D E R. rewrite /signed. do 2 case: Coqlib.zlt; move=> /= I1 I2 D E R DH.
  - rewrite Zquot.Zquot_Zdiv_pos; [| by lias | by lias ].
    case r0: (v1 mod v2 == 0)%Z.
    + move/eqP: r0 => r0. rewrite r0. by rewrite Zdiv.Zmod_small; lias.
    + case Ir: (v1 mod v2 >=? 0)%Z.
      * have Ij1: (v1 >=? 0)%Z; first by apply/geb_spec0; lias.
        by rewrite Ij1 Zdiv.Zmod_small; lias.
      * move/geb_spec0: Ir => Ir. by inversion R; try lias.
  - rewrite_by (v1 - modulus = - (modulus - v1))%Z. rewrite Z.quot_opp_l => //.
    rewrite Zquot.Zquot_Zdiv_pos; [| by lias | by lias ].
    rewrite_by (- (modulus - v1) = v1 - modulus)%Z.
    case r0: ((v1 - modulus) mod v2 == 0)%Z.
    + move/eqP: r0 => r0. move: E. rewrite r0 => E.
      rewrite_by (modulus - v1 = - (v1 - modulus))%Z. rewrite Z.div_opp_l_z => //.
      rewrite_by (v2 * - - ((v1 - modulus) / v2) + 0 = (v2 * ((v1 - modulus) / v2) + 0))%Z.
      rewrite -E. rewrite Zdiv.Zminus_mod. rewrite Zdiv.Z_mod_same_full.
      rewrite_by (v1 mod modulus - 0 = v1 mod modulus)%Z. rewrite Zdiv.Zmod_mod.
      by rewrite Zdiv.Zmod_small; lias.
    + move/eqP: r0 => r0. case R => {} R; last by lias.
      have E1: ((v1 - modulus) mod v2 >=? 0)%Z; first by apply/geb_spec0; lias. rewrite E1.
      have E2: ((v1 - modulus) >=? 0 = false)%Z; first by apply/geb_spec0; lias. rewrite E2.
      rewrite_by (modulus - v1 = - (v1 - modulus))%Z. rewrite Z.div_opp_l_nz => //.
      rewrite_by ((v2 * - (- ((v1 - modulus) / v2) - 1) + ((v1 - modulus) mod v2 - v2))
                  = (v2 * ((v1 - modulus) / v2) + (v1 - modulus) mod v2))%Z.
      rewrite -E. rewrite Zdiv.Zminus_mod. rewrite Zdiv.Z_mod_same_full.
      rewrite_by (v1 mod modulus - 0 = v1 mod modulus)%Z. rewrite Zdiv.Zmod_mod.
      by rewrite Zdiv.Zmod_small; lias.
  - rewrite_by (v2 - modulus = - (modulus - v2))%Z. rewrite Z.quot_opp_r => //; last by lias.
    rewrite Zquot.Zquot_Zdiv_pos; [| by lias | by lias ].
    rewrite_by (- (modulus - v2) = v2 - modulus)%Z.
    case r0: (v1 mod (v2 - modulus) == 0)%Z.
    + move/eqP: r0 => r0. move: E. rewrite r0 => E.
      rewrite_by (modulus - v2 = - (v2 - modulus))%Z. rewrite Z.div_opp_r_z => //.
      rewrite_by (v2 * - - (v1 / (v2 - modulus)) + 0
                  = (((v2 - modulus) * (v1 / (v2 - modulus)) + 0))
                    + (v1 / (v2 - modulus) * modulus))%Z.
      rewrite -E. rewrite Zdiv.Zplus_mod. rewrite Zdiv.Z_mod_mult.
      rewrite_by (v1 mod modulus + 0 = v1 mod modulus)%Z. rewrite Zdiv.Zmod_mod.
      by rewrite Zdiv.Zmod_small; lias.
    + move/eqP: r0 => r0. case R => {} R; first by lias.
      have E1: (v1 mod (v2 - modulus) >=? 0 = false)%Z; first by apply/geb_spec0; lias. rewrite E1.
      have E2: (v1 >=? 0)%Z; first by apply/geb_spec0; lias. rewrite E2.
      rewrite_by (modulus - v2 = - (v2 - modulus))%Z. rewrite Z.div_opp_r_nz => //.
      rewrite_by (v2 * - (- (v1 / (v2 - modulus)) - 1) + (v1 mod (v2 - modulus) - (v2 - modulus))
                  = ((v2 - modulus) * (v1 / (v2 - modulus)) + v1 mod (v2 - modulus))
                    + (1 + (v1 / (v2 - modulus))) * modulus)%Z.
      rewrite -E. rewrite Zdiv.Zplus_mod. rewrite Zdiv.Z_mod_mult.
      rewrite_by (v1 mod modulus + 0 = v1 mod modulus)%Z. rewrite Zdiv.Zmod_mod.
      by rewrite Zdiv.Zmod_small; lias.
  - rewrite_by (v1 - modulus = - (modulus - v1))%Z. rewrite Z.quot_opp_l => //.
    rewrite_by (v2 - modulus = - (modulus - v2))%Z. rewrite Z.quot_opp_r => //; last by lias.
    rewrite Zquot.Zquot_Zdiv_pos; [| by lias | by lias ].
    rewrite_by (- (modulus - v1) = v1 - modulus)%Z. rewrite_by (- (modulus - v2) = v2 - modulus)%Z.
    case r0: ((v1 - modulus) mod (v2 - modulus) == 0)%Z.
    + move/eqP: r0 => r0. move: E. rewrite r0 => E.
      have r0': ((modulus - v1) mod (v2 - modulus) = 0)%Z.
      { rewrite_by (modulus - v1 = - (v1 - modulus))%Z. by rewrite Z.mod_opp_l_z. }
      rewrite_by (modulus - v2 = - (v2 - modulus))%Z. rewrite Z.div_opp_r_z => //.
      rewrite_by (modulus - v1 = - (v1 - modulus))%Z. rewrite Z.div_opp_l_z => //.
      rewrite_by (v2 * - - - - ((v1 - modulus) / (v2 - modulus)) + 0
                  = ((v2 - modulus) * ((v1 - modulus) / (v2 - modulus)) + 0)
                    + ((v1 - modulus) / (v2 - modulus)) * modulus)%Z.
      rewrite -E. rewrite Zdiv.Zplus_mod. rewrite Zdiv.Z_mod_mult.
      rewrite Zdiv.Zminus_mod. rewrite Zdiv.Z_mod_same_full.
      rewrite_by (v1 mod modulus - 0 = v1 mod modulus)%Z. rewrite Zdiv.Zmod_mod.
      rewrite_by (v1 mod modulus + 0 = v1 mod modulus)%Z. rewrite Zdiv.Zmod_mod.
      by rewrite Zdiv.Zmod_small; lias.
    + move/eqP: r0 => r0. case R => {} R; first by lias.
      have r0': ((modulus - v1) mod (v2 - modulus) <> 0)%Z.
      { rewrite_by (modulus - v1 = - (v1 - modulus))%Z. rewrite Z.mod_opp_l_nz => //. by lias. }
      have E1: ((v1 - modulus) mod (v2 - modulus) >=? 0 = false)%Z; first by apply/geb_spec0; lias.
      rewrite E1.
      have E2: ((v1 - modulus) >=? 0 = false)%Z; first by apply/geb_spec0; lias. rewrite E2.
      rewrite_by (modulus - v2 = - (v2 - modulus))%Z. rewrite Z.div_opp_r_nz => //.
      rewrite_by (modulus - v1 = - (v1 - modulus))%Z. rewrite Z.div_opp_l_nz => //.
      rewrite_by (v2 * - - (- (- ((v1 - modulus) / (v2 - modulus)) - 1) - 1)
                  = v2 * ((v1 - modulus) / (v2 - modulus)))%Z.
      rewrite_by (v2 * ((v1 - modulus) / (v2 - modulus)) + (v1 - modulus) mod (v2 - modulus)
                  = ((v2 - modulus) * ((v1 - modulus) / (v2 - modulus))
                     + (v1 - modulus) mod (v2 - modulus))
                    + ((v1 - modulus) / (v2 - modulus)) * modulus)%Z.
      rewrite -E. rewrite Zdiv.Zplus_mod. rewrite Zdiv.Z_mod_mult.
      rewrite Zdiv.Zminus_mod. rewrite Zdiv.Z_mod_same_full.
      rewrite_by (v1 mod modulus - 0 = v1 mod modulus)%Z. rewrite Zdiv.Zmod_mod.
      rewrite_by (v1 mod modulus + 0 = v1 mod modulus)%Z. rewrite Zdiv.Zmod_mod.
      by rewrite Zdiv.Zmod_small; lias.
Qed.

(** Return the bitwise conjunction of two numbers. **)
Definition iand : T -> T -> T := and.

(** Return the bitwise disjunction of two numbers. **)
Definition ior : T -> T -> T := or.

(** Return the bitwise exclusive disjunction of two numbers. **)
Definition ixor : T -> T -> T := xor.

(** Return the result of shifting left the first number by the second. **)
Definition ishl (i1 i2 : T) : T :=
(* TODO: We could slightly improve the specification here to make it closer to the Wasm specification.
Something like:
[[
  let: k := (unsigned i1 mod wordsize)%Z in
  shl k i2.
]]
*)
  shl i1 i2.

(** Return the result of shifting right the first number by the second. **)
(* TODO: Make it match better the specification. *)
Definition ishr_u : T -> T -> T := shru.

(* TODO
(** Shift [i] by [k] bits, extended with the most significant bit of the original value. **)
Definition shift_signed l k :=
  if k is k.+1 then
    if l is d :: l then
      let: l := d :: d :: l (* TODO: Drop the last one. *) in
      shift_signed l k
    else l
  else l.

Definition ishr_s (i1 i2 : T) :=
  let: k := unsigned i2 mod wordsize in
  let: r := shift_signed (convert_to_bits i1) k in
  (* TODO: convert back to a number. *)

(* LATER
Lemma ishr_s_shr : forall i1 i2,
  ishr_s i1 i2 = shr i1 i2.
*)
*)

Definition Tmixin : mixin_of T := {|
     int_zero := zero ;
     (** Bit operations **)
     int_clz := clz ;
     int_ctz := ctz ;
     int_popcnt := popcnt ;
     (** Binary operators **)
     int_add := iadd ;
     int_sub := isub ;
     int_mul := imul ;
     int_div_u := idiv_u ;
     int_div_s := idiv_s ;
     int_rem_u := irem_u ;
     int_rem_s := irem_s ;
     (** Binary operators about bits **)
     int_and := iand ;
     int_or := ior ;
     int_xor := ixor ;
     int_shl := ishl ;
     int_shr_u := ishr_u ;
     int_shr_s := shr (*TODO: ishr_s*) ;
     int_rotl := rol ;
     int_rotr := ror ;
     (** Equalities **)
     int_eq := eq ;
     int_eqz := eq zero ;
     (** Comparisons **)
     int_lt_u := ltu ;
     int_lt_s := lt ;
     int_gt_u x y := ltu y x ;
     int_gt_s x y := lt y x ;
     int_le_u x y := negb (ltu y x) ;
     int_le_s x y := negb (lt y x) ;
     int_ge_u x y := negb (ltu x y) ;
     int_ge_s x y := negb (lt x y) ;
     (** Conversion to and from [nat] **)
     int_of_Z n := repr n ;
     nat_of_uint i := Z.to_nat (unsigned i) ;
     N_of_uint i := Z.to_N (unsigned i) ;
     Z_of_uint i := unsigned i ;
     Z_of_sint i := signed i ;
   |}.

(** The operations [int_of_Z], [nat_of_uint], [Z_of_uint], and [Z_of_sint] are implicit
  in the Wasm specification.
  We prove here some properties showing that our implementation of these functions
  makes sense. **)

Lemma int_of_Z_nat_of_uint : forall i,
  int_of_Z Tmixin (nat_of_uint Tmixin i : Z) = i.
Proof.
  move=> [i ?]. apply: eq_T_intval => /=.
  rewrite Coqlib.Z_to_nat_max. rewrite Z.max_l; last by lias.
  by rewrite Z_mod_modulus_id.
Qed.

Lemma int_of_Z_Z_of_uint : forall i,
  int_of_Z Tmixin (Z_of_uint Tmixin i : Z) = i.
Proof.
  move=> [i ?]. apply: eq_T_intval => /=.
  by rewrite Z_mod_modulus_id.
Qed.

Lemma int_of_Z_Z_of_sint : forall i,
  int_of_Z Tmixin (Z_of_sint Tmixin i : Z) = i.
Proof.
  move=> [i ?]. apply: eq_T_intval => /=.
  rewrite /signed /=. destruct Coqlib.zlt as [E|E].
  - by rewrite Z_mod_modulus_id.
  - rewrite Z_mod_modulus_add_modulus. by rewrite Z_mod_modulus_id; lias.
Qed.

Lemma nat_of_uint_Z_of_uint : forall i,
  (nat_of_uint Tmixin i : Z) = Z_of_uint Tmixin i.
Proof.
  move=> [i ?] /=. rewrite Coqlib.Z_to_nat_max. by rewrite Z.max_l; lias.
Qed.

Definition cT : type := Pack {| base := EqMixin eq_eqP; mixin := Tmixin |}.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Local Definition xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Equality.class bT) b => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.

End Make.

(** ** Instantiations **)

(** Instantiations to 32 and 64 bits. **)

Module Int32.
Include Make(Integers.Wordsize_32).
End Int32.

Module Int64.
Include Make(Integers.Wordsize_64).
End Int64.

End Wasm_int.

Definition i32 : eqType := Wasm_int.Int32.eqType.
Definition i32r : Wasm_int.class_of i32 := Wasm_int.Int32.class.
Definition i32t : Wasm_int.type := Wasm_int.Pack i32r.
Definition i32m := Wasm_int.mixin i32r.
Definition i64 : eqType :=  Wasm_int.Int64.eqType.
Definition i64r : Wasm_int.class_of i64 := Wasm_int.Int64.class.
Definition i64t : Wasm_int.type := Wasm_int.Pack i64r.
Definition i64m := Wasm_int.mixin i64r.

Definition wasm_wrap (i : i64) : i32 :=
  Wasm_int.int_of_Z i32m (Wasm_int.Z_of_uint i64m i).

Definition wasm_extend_u (i : i32) : i64 :=
  Wasm_int.int_of_Z i64m (Wasm_int.Z_of_uint i32m i).

Definition wasm_extend_s (i : i32) : i64 :=
  Wasm_int.int_of_Z i64m (Wasm_int.Z_of_sint i32m i).


(** * Floats **)

(** ** Declaration of Operations **)

Module Wasm_float.

(** The operations on floats follow the standard.  In particular,
  [float_eq] is the floating-point equality [feq] defined in the
  standard and not the Leibniz equality: we have
  [float_eq NaN NaN = false] and [float_eq (+0) (-0) = true]. **)
(** Conversions functions to and from the two integers types are
  also listed in this type. **)

Record mixin_of (float_t : Type) := Mixin {
  float_zero : float_t;
  (** Unuary operators **)
  float_neg : float_t -> float_t ;
  float_abs : float_t -> float_t ;
  float_sqrt : float_t -> float_t ;
  (** Rounding **)
  float_ceil : float_t -> float_t ;
  float_floor : float_t -> float_t ;
  float_trunc : float_t -> float_t ;
  float_nearest : float_t -> float_t ;
  (** Binary operators **)
  float_add : float_t -> float_t -> float_t ;
  float_sub : float_t -> float_t -> float_t ;
  float_mul : float_t -> float_t -> float_t ;
  float_div : float_t -> float_t -> float_t ;
  float_min : float_t -> float_t -> float_t ;
  float_max : float_t -> float_t -> float_t ;
  float_copysign : float_t -> float_t -> float_t ;
  (** Comparisons **)
  float_eq : float_t -> float_t -> bool ;
  float_lt : float_t -> float_t -> bool ;
  float_gt : float_t -> float_t -> bool ;
  float_le : float_t -> float_t -> bool ;
  float_ge : float_t -> float_t -> bool ;
  (** Conversions **)
  float_ui32_trunc : float_t -> option i32 ;
  float_si32_trunc : float_t -> option i32 ;
  float_ui64_trunc : float_t -> option i64 ;
  float_si64_trunc : float_t -> option i64 ;
  float_convert_ui32 : i32 -> float_t ;
  float_convert_si32 : i32 -> float_t ;
  float_convert_ui64 : i64 -> float_t ;
  float_convert_si64 : i64 -> float_t ;
}.

Record class_of T := Class { base : Equality.class_of T; mixin : mixin_of T }.
Local Coercion base : class_of >-> Equality.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Definition float_ne (e : type) : sort e -> sort e -> bool :=
  let 'Pack _ (Class _ m) := e in
    fun x => fun y => negb (float_eq m x y).

(** ** Architectures **)

(** To avoid repeating definitions, we define this module type [FloatSize]
  specifying the [prec] (precision) and [emax] (maximum exponent) parameters
  of floating-point numbers.
  We also add in the module type all useful definitions not parameterised by
  [prec] and [emax] for defining the Wasm float operations. **)

Module Type FloatSize.

Import Integers.

Import Raux.

Import Floats.

Import ZArith.BinInt.

Parameters prec emax : Z.

Parameter prec_gt_0 : FLX.Prec_gt_0 prec.
Parameter Hmax : (prec < emax)%Z.

(** The following hypothesis is true in the case of Wasm, and it greatly simplifies proofs. **)
Parameter prec_gt_2 : (prec > 2)%Z.

Definition T := Binary.binary_float prec emax.

Parameter default_nan : { x : T | Binary.is_nan _ _ x }.

Definition compare := Binary.Bcompare prec emax.

Definition cmp (c : comparison) (f1 f2 : T) :=
  cmp_of_comparison c (compare f1 f2).

Definition eq_dec := IEEE754_extra.Beq_dec prec emax.

Parameter neg : T -> T.
Parameter abs : T -> T.
Parameter add : T -> T -> T.
Parameter sub : T -> T -> T.
Parameter mul : T -> T -> T.
Parameter div : T -> T -> T.

End FloatSize.

(** We then instanciate it with CompCert’s types. **)

Module FloatSize32.

Import Raux.

Import Floats.

Include Float32.

Import ZArith.BinInt.

Definition prec : BinNums.Z := 24.
Definition emax : BinNums.Z := 128.

Definition T := float32.

Definition default_nan := Bits.default_nan_pl32.

Lemma prec_gt_0 : FLX.Prec_gt_0 prec.
Proof. reflexivity. Qed.

Lemma Hmax : (prec < emax)%Z.
Proof. reflexivity. Qed.

Lemma prec_gt_2 : (prec > 2)%Z.
Proof. reflexivity. Qed.

End FloatSize32.

Module FloatSize64.

Import Raux.

Import Floats.

Include Float.


Import ZArith.BinInt.

Definition prec : BinNums.Z := 53.
Definition emax : BinNums.Z := 1024.

Definition T := float.

Definition default_nan := Bits.default_nan_pl64.

Lemma prec_gt_0 : FLX.Prec_gt_0 prec.
Proof. reflexivity. Qed.

Lemma Hmax : (prec < emax)%Z.
Proof. reflexivity. Qed.

Lemma prec_gt_2 : (prec > 2)%Z.
Proof. reflexivity. Qed.

End FloatSize64.

(** ** Definitions **)

Module Make (FS : FloatSize).

(* Import Zpower BinIntDef. *)
Import Integers.
Import Raux.
Import ZArith.
Import Floats.
Export FS.

Definition eqb v1 v2 := is_left (eq_dec v1 v2).
Definition eqbP : Equality.axiom eqb := eq_dec_Equality_axiom eq_dec.

Canonical Structure T_eqMixin := EqMixin eqbP.
Canonical Structure T_eqType := Eval hnf in EqType T T_eqMixin.

(** State whether the given float is a [NaN]. **)
Definition is_nan : T -> bool := Binary.is_nan _ _.

(** State whether the given float is negative. **)
Definition sign : T -> bool := Binary.Bsign _ _.

(** State whether the given float is a zero. **)
Definition is_zero (z : T) :=
  if z is Binary.B754_zero _ then true else false.

(** State whether the given float is an infinity. **)
Definition is_infinity (z : T) :=
  if z is Binary.B754_infinity _ then true else false.

(** [+∞] **)
Definition pos_infinity : T := Binary.B754_infinity _ _ false.

(** [-∞] **)
Definition neg_infinity : T := Binary.B754_infinity _ _ true.

(** [+0] **)
Definition pos_zero : T := Binary.B754_zero _ _ false.

(** [-0] **)
Definition neg_zero : T := Binary.B754_zero _ _ true.


(** The canonical [NaN] payload. **)
Definition canonical_pl := shift_pos (Z.to_pos prec - 2) 1.

(** States whether a [NaN] is canonical. **)
Definition is_canonical (z : T) :=
  if z is Binary.B754_nan _ pl _ then pl == canonical_pl else false.

(** State whether a [NaN] payload [pl] is an arithmetic [NaN].
  that is whether its most significant bit is [1]. **)
Definition pl_arithmetic (pl : positive) := Z.pos (Digits.digits2_pos pl) == (prec - 1)%Z.

Lemma pl_arithmetic_is_nan : forall pl,
  pl_arithmetic pl ->
  Binary.nan_pl prec pl.
Proof.
  rewrite /pl_arithmetic /Binary.nan_pl. move=> pl C. apply/Z.ltb_spec0. by lias.
Qed.

(** State whether a [NaN] is an arithmetical [NaN]. **)
Definition is_arithmetic (z : T) :=
  if z is Binary.B754_nan _ pl _ then pl_arithmetic pl else false.

Lemma is_arithmetic_is_nan : forall z,
  is_arithmetic z ->
  is_nan z.
Proof. by case. Qed.

Lemma canonical_pl_arithmetic : forall pl,
  Binary.nan_pl prec pl ->
  pl_arithmetic pl <-> (pl >= canonical_pl)%positive.
Proof.
  move=> pl.
  rewrite_by ((pl >= canonical_pl)%positive <-> (Z.pos pl >= Z.pos canonical_pl)%Z).
  rewrite /Binary.nan_pl /pl_arithmetic /canonical_pl.
  move: prec_gt_0 prec_gt_2. case: prec => [|precn|] // _ G2.
  rewrite shift_pos_correct Z.pow_pos_fold.
  rewrite_by (2 ^ Z.pos (precn - 2) * 1 = 2 ^ Z.pos (precn - 2))%Z.
  move/Z.ltb_spec0 => I.
  have R: (Z.pos pl >= 2 ^ Z.pos (precn - 2)
           <-> Z.succ (Z.log2 (Z.pos pl)) >= Z.pos precn - 1)%Z.
  {
    move {I}. have R: (Z.pos pl < 2 ^ Z.pos (precn - 2)
                       <-> Z.succ (Z.log2 (Z.pos pl)) < Z.pos precn - 1)%Z.
    { rewrite Z.log2_lt_pow2 => //. by lias. }
    by apply: not_iff_compat.
  }
  rewrite {} R.
  move: I. rewrite Digits.Zpos_digits2_pos.
  rewrite (Digits.Zdigits_unique _ _ (Z.succ (Z.log2 (Z.pos pl)))); first by lias.
  rewrite_by (Z.succ (Z.log2 (Z.pos pl)) - 1 = Z.log2 (Z.pos pl)).
  apply Z.log2_spec. by lias.
Qed.

Lemma canonical_pl_is_arithmetic : pl_arithmetic canonical_pl.
Proof.
  apply/canonical_pl_arithmetic; last by lias.
  rewrite /Binary.nan_pl /canonical_pl.
  rewrite Digits.Zpos_digits2_pos.
  rewrite shift_pos_correct Z.pow_pos_fold.
  rewrite_by (2 ^ Z.pos (Z.to_pos prec - 2) * 1 = 1 * 2 ^ Z.pos (Z.to_pos prec - 2))%Z.
  apply/Z.ltb_spec0.
  move: prec_gt_0. case Eprec: prec => [|precn|] // _.
  move: prec_gt_2. rewrite {} Eprec => precn2.
  rewrite (Digits.Zdigits_unique _ _ (Z.pos precn - 1)); first by lias.
  rewrite Pos2Z.id. rewrite_by (1 * 2 ^ Z.pos (precn - 2) = 2 ^ Z.pos (precn - 2)).
  rewrite Z.abs_eq; last by apply Z.pow_nonneg; lias.
  rewrite_by (radix_val radix2 = 2).
  rewrite_by (Z.pos precn - 1 - 1 = Z.pos (precn - 2)).
  split; first by lias.
  rewrite_by (Z.pos precn - 1 = 1 + Z.pos (precn - 2)).
  rewrite Zpower_plus => //.
  rewrite_by (2 ^ 1 = 2).
  assert (0 < 2 ^ Z.pos (precn - 2)); last by lias.
  by apply Z.pow_pos_nonneg.
Qed.

(** There are exactly two canonical [NaN]s: a positive one, and a negative one. **)
Definition canonical_nan s : T :=
  Binary.B754_nan _ _ s canonical_pl  (pl_arithmetic_is_nan canonical_pl_is_arithmetic).

Lemma is_canonical_nan_disj : forall z,
  is_canonical z ->
  exists s, z = canonical_nan s.
Proof.
  case=> //= s pl N /eqP C. exists s.
  rewrite /canonical_nan. subst. f_equal.
  apply: Eqdep_dec.eq_proofs_unicity. move=> [] []; by [ left | right; discriminate ].
Qed.

Definition unspec_canonical_nan := canonical_nan ltac:(abstract exact false).

(** Given a payload, update its most significant bit to [1]. **)
Definition make_arithmetic :
  { pl | Binary.nan_pl prec pl } ->
  { pl | Binary.nan_pl prec pl /\ pl_arithmetic pl }.
Proof.
  move=> [pl E]. case C: (pl_arithmetic pl).
  - exists pl. by repeat eexists.
  - move: C => /= C. move: prec_gt_0. case Eprec: prec => [|precn|] // _.
    set pl' := (Pos.lor pl canonical_pl)%positive. exists pl'.
    have Cpl: pl_arithmetic pl'; last by split; first (rewrite -Eprec; apply: pl_arithmetic_is_nan).
    rewrite /pl' /Binary.nan_pl /pl_arithmetic => {pl'} /=.
    rewrite Digits.Zpos_digits2_pos.
    rewrite (Digits.Zdigits_unique _ _ (Z.succ (Z.log2 (Z.pos (Pos.lor pl canonical_pl))))).
    + rewrite_by (Z.pos (Pos.lor pl canonical_pl) = Z.lor (Z.pos pl) (Z.pos canonical_pl)).
      rewrite Z.log2_lor => //. rewrite shift_pos_correct Z.pow_pos_fold.
      rewrite /canonical_pl Eprec.
      rewrite_by (2 ^ Z.pos (precn - 2) * 1 = 1 * 2 ^ Z.pos (precn - 2))%Z.
      rewrite Z.log2_mul_pow2 => //.
      have Lpl: (Z.log2 (Z.pos pl) < prec - 1)%Z.
      {
        move: E. rewrite /Binary.nan_pl. move/Z.ltb_spec0.
        rewrite Digits.Zpos_digits2_pos.
        rewrite (Digits.Zdigits_unique _ _ (Z.succ (Z.log2 (Z.pos pl)))).
        - by lias.
        - rewrite_by (Z.succ (Z.log2 (Z.pos pl)) - 1
                      = Z.log2 (Z.pos pl)).
          apply Z.log2_spec. by lias.
      }
      rewrite_by (Z.pos (precn - 2) + Z.log2 1 = Z.pos (precn - 2))%Z.
      apply/eqP.
      have: (Z.max (Z.log2 (Z.pos pl)) (Z.pos (precn - 2)) = Z.pos precn - 2)%Z; last by lias.
      by rewrite Z.max_r; move: prec_gt_2; lias.
    + rewrite_by (Z.succ (Z.log2 (Z.pos (Pos.lor pl canonical_pl))) - 1
                  = Z.log2 (Z.pos (Pos.lor pl canonical_pl))).
      apply Z.log2_spec.
      by lias.
Defined.

Lemma make_arithmetic_arithmetic : forall pl, pl_arithmetic (sval (make_arithmetic pl)).
Proof.
  move=> pl. move: (proj2_sig (make_arithmetic pl)). by case.
Qed.

Lemma make_arithmetic_nan : forall pl, Binary.nan_pl prec (sval (make_arithmetic pl)).
Proof.
  move=> pl. move: (proj2_sig (make_arithmetic pl)). by case.
Qed.

(** An unspecified positive used in [unspec_nan], whose value is made opaque to
  avoid overspecification. **)
Definition unspec_nan_pl : { pl | Binary.nan_pl prec pl }.
Proof.
  have pl: { pl | Binary.nan_pl prec pl
                  /\ exists b E, sval default_nan = Binary.B754_nan _ _ b pl E }.
  { case: default_nan => z. case: z => // b pl Epl Inan. exists pl. split => //.
    repeat eexists. }
  case: pl. move=> pl [E _]. by exists pl.
Qed.

Definition unspec_arithmetic_nan_pl := make_arithmetic unspec_nan_pl.

Lemma unspec_arithmetic_nan_pl_canonical : pl_arithmetic (sval unspec_arithmetic_nan_pl).
Proof. by apply: make_arithmetic_arithmetic. Qed.

Lemma unspec_arithmetic_nan_pl_nan : Binary.nan_pl prec (sval unspec_arithmetic_nan_pl).
Proof. by apply: make_arithmetic_nan. Qed.

(** An unspecified arithmetic [NaN]. **)
Definition unspec_arithmetic_nan : T :=
  Binary.B754_nan _ _ ltac:(abstract exact true) _ unspec_arithmetic_nan_pl_nan.

(** An opaque definition for an unspecified [NaN]. **)
Definition unspec_nan_nan : {x : T | Binary.is_nan _ _ x = true}.
Proof. by refine (exist _ unspec_arithmetic_nan (eqxx true)). Qed.

(** An unspecified [NaN]. **)
Definition unspec_nan : T := sval unspec_nan_nan.

(** Taking the opposite of a floating point number.
  Its action on [NaN] is not specified. **)
Definition opp : T -> T.
Proof.
  refine (Binary.Bopp _ _ (fun _ => exist _ unspec_nan _)).
  by apply: (svalP unspec_nan_nan).
Defined.


(** Given a mantissa and an exponent (in radix two), produce a representation for a float.
  The sign is not specified if given 0 as a mantissa. **)
Definition normalise (m e : Z) : T :=
  Binary.binary_normalize _ _ prec_gt_0 Hmax
    BinarySingleNaN.mode_NE m e ltac:(abstract exact false).

(** As Flocq is unfortunately undocumented, let us introduce a unit test here, to check
  that indeed we have the correct understanding of definitions.
  We define [half] to be [0.5], adds it to itself, then check that the result is one.
  (Note that because of rounding errors, it may actually not be equal for some parameters,
  but it is fine here.)
  These unit tests are tested once the module is instantiated below, to be able to
  compute. **)
Local Definition normalise_unit_test :=
  let: half := normalise 1 (-1) in
  let: twice_half :=
    Binary.Bplus _ _ prec_gt_0 Hmax (fun _ _ => unspec_nan_nan)
      BinarySingleNaN.mode_NE half half : T in
  let: one := Binary.Bone _ _ prec_gt_0 Hmax in
  cmp Ceq twice_half one = true.

(** Following the specification about [NaN] propagation, we define the function [nans]
  below.
  In the Wasm specification, it took a set of values: we translate this here as a list
  for simplicity.
  To keep the specification readable, we made this function deterministic, always
  returning the opaque value [unspec_nan] when in doubt.
  Because the value is opaque, one can’t use its actual value in any proof, but it may
  be misused in tests.
  Note that the opaque mechanism can be reversed in Coq: we are assuming here that users
  won’t try to do this. **)
Definition nans (zs : list T) : T :=
  let: zs := seq.filter is_nan zs in
  if seq.all is_canonical zs then
    unspec_canonical_nan
  else unspec_arithmetic_nan.

Lemma nans_is_nan : forall zs,
  is_nan (nans zs) = true.
Proof.
  move=> zs. rewrite /nans.
  by case: (seq.all is_canonical (seq.filter is_nan zs)).
Qed.

(** Importing the square root of floats from the Flocq library with the
  round-to-nearest ties-to-even mode. **)
Definition sqrt (z : T) : T :=
  Binary.Bsqrt _ _ prec_gt_0 Hmax (fun z => exist _ _ (nans_is_nan [:: z])) BinarySingleNaN.mode_NE z.

(** Square root following the Wasm standard. **)

(** It seems that Flocq does not define any ceil and floor functions on
  floating point numbers (it does define some on the [R] type, but it is not
  really useful for us as they are only used for specifications of floating
  point operations).
  Inspired by CompCert’s [IEEE754_extra.ZofB], we build this operation,
  parameterised by two divisions functions (one for negative numbers and
  one for positive numbers).
  These divisions functions only differ in the way they round numbers (up,
  down, or nearest).
  Note that these parameters are used to compute the absolute value of the
  resulting integer. **)

Definition ZofB_param (divP divN : Z -> Z -> Z) (z : T) :=
  match z with
  | Binary.B754_zero _ => Some 0%Z
  | Binary.B754_finite s m 0%Z _ =>
    Some (cond_Zopp s (Z.pos m))
  | Binary.B754_finite s m (Z.pos e) _ =>
    Some (cond_Zopp s (Z.pos m) * Z.pow_pos radix2 e)%Z
  | Binary.B754_finite s m (Z.neg e) _ =>
    let: div := if s then divN else divP in
    Some (cond_Zopp s (div (Z.pos m) (Z.pow_pos radix2 e)))
  | _ => None
  end.

(** We now instantiate this function with the following three division operations, only
  differenciated in how they round numbers: [div_down] rounds down, [div_up] up, and
  [div_near] rounds to the nearest, ties to even. **)
Definition div_down : Z -> Z -> Z := Z.div.
Definition div_up (a b : Z) : Z :=
  ((if Zeq_bool (a mod b) 0 then 0 else 1) + a / b)%Z.
Definition div_near (a b : Z) : Z :=
  (if a mod b <? b / 2 then div_down a b
   else if a mod b >? b / 2 then div_up a b
   else (** Ties to even **)
     let: d := div_down a b in
     let: u := div_up a b in
     if Z.even d then d else u)%Z.

(** From these functions, we can define the usual ceil, floor, trunc, and nearest functions.
  A -o suffix has been added as these function return an option type (returning [None] for
  non-finite and [NaN] values). **)
Definition ceilo := ZofB_param div_up div_down.
Definition flooro := ZofB_param div_down div_up.
Definition trunco := ZofB_param div_down div_down.
Definition nearesto := ZofB_param div_near div_near.

(** CompCert’s function [IEEE754_extra.ZofB] is exactly [trunco]. **)
Lemma trunco_is_ZofB : forall z,
  trunco z = IEEE754_extra.ZofB _ _ z.
Proof.
  move=> z. case: z => // s m e. by case: s.
Qed.

(** This function does the countrary: it translates an integer to floating point number. **)
Definition BofZ : Z -> T :=
  IEEE754_extra.BofZ _ _ prec_gt_0 Hmax.

(** [BofZ] is actually just the same thing than calling [normalise] with an empty exponent. **)
Lemma BofZ_normalise : forall i, BofZ i = normalise i 0.
Proof.
  rewrite /BofZ /IEEE754_extra.BofZ /normalise => i.
  f_equal; apply: Logic.Eqdep_dec.eq_proofs_unicity_on;
    move=> c; case: c; by [ left | right ]. (* LATER: Remove this bruteforce. *)
Qed.

(** We can then define versions of these operators directly from float to float,
  leaving the float as-is if not a finite value. **)
Definition floatify F (z : T) :=
  if F z is Some i then BofZ i else z.
Definition ceil := floatify ceilo.
Definition floor := floatify flooro.
Definition trunc := floatify trunco.
Definition nearest := floatify nearesto.

(** As above, here are some unit tests to be sure that we are indeed expecting
  the right thing. **)
Local Definition ceil_unit_test_1 : Prop :=
  let: half := normalise 1 (-1) in
  ceil half = BofZ 1.

Local Definition ceil_unit_test_2 : Prop :=
  let: mhalf := normalise (-1) (-1) in
  ceil mhalf = BofZ 0.

Local Definition floor_unit_test_1 : Prop :=
  let: half := normalise 1 (-1) in
  floor half = BofZ 0.

Local Definition floor_unit_test_2 : Prop :=
  let: mhalf := normalise (-1) (-1) in
  floor mhalf = BofZ (-1).

Local Definition trunc_unit_test_1 : Prop :=
  let: half := normalise 1 (-1) in
  trunc half = BofZ 0.

Local Definition trunc_unit_test_2 : Prop :=
  let: mhalf := normalise (-1) (-1) in
  trunc mhalf = BofZ 0.

Local Definition nearest_unit_test_1 : Prop :=
  let: half := normalise 1 (-1) in
  nearest half = BofZ 0.

Local Definition nearest_unit_test_2 : Prop :=
  let: mhalf := normalise (-1) (-1) in
  nearest mhalf = BofZ 0.

Local Definition nearest_unit_test_3 : Prop :=
  let: one_pfive := normalise 3 (-1) in
  nearest one_pfive = BofZ 2.

Local Definition nearest_unit_test_4 : Prop :=
  let: mone_pfive := normalise (-3) (-1) in
  nearest mone_pfive = BofZ (-2).

(** Set the sign of a float. **)
Definition set_sign s (z : T) : T :=
  match z with
  | Binary.B754_zero _ => Binary.B754_zero _ _ s
  | Binary.B754_infinity _ => Binary.B754_infinity _ _ s
  | Binary.B754_nan _ pl ok => Binary.B754_nan _ _ s pl ok
  | Binary.B754_finite _ m e ok => Binary.B754_finite _ _ s m e ok
  end.

Lemma set_sign_sign : forall s z,
  sign (set_sign s z) = s.
Proof. move=> s. by case. Qed.

Lemma set_sign_opp : forall z,
  ~~ is_nan z ->
  opp z = set_sign (~~ sign z) z.
Proof. by case. Qed.


(** We now define the floating-point operators as defined in the Wasm standard. **)

Definition fadd (z1 z2 : T) :=
  if is_nan z1 || is_nan z2 then nans [:: z1; z2]
  else if is_infinity z1 && is_infinity z2 then
    if sign z1 != sign z2 then nans [:: ]
    else (** [z1 = z2 = ±∞] **) z1
  else if is_infinity z1 then z1
  else if is_infinity z2 then z2
  else if is_zero z1 && is_zero z2 then
    if sign z1 != sign z2 then pos_zero
    else (** [z1 = z2 = ±0] **) z1
  else if is_zero z1 then z2
  else if is_zero z2 then z1
  else if z1 == opp z2 then pos_zero
  else add z1 z2.

Definition fsub (z1 z2 : T) :=
  if is_nan z1 || is_nan z2 then nans [:: z1; z2]
  else if is_infinity z1 && is_infinity z2 then
    if sign z1 == sign z2 then nans [:: ]
    else (** [z1 = ±∞], [z2 = ∓∞] **) z1
  else if is_infinity z1 then z1
  else if is_infinity z2 then opp z2
  else if is_zero z1 && is_zero z2 then
    if sign z1 == sign z2 then pos_zero
    else (** [z1 = ±0], [z2 = ∓0] **) z1
  else if is_zero z2 then z1
  else if is_zero z1 then opp z2
  else if z1 == z2 then pos_zero
  else sub z1 z2.

Definition fmul (z1 z2 : T) :=
  if is_nan z1 || is_nan z2 then nans [:: z1; z2]
  else if is_infinity z1 && is_zero z2 then nans [:: ]
  else if is_infinity z2 && is_zero z1 then nans [:: ]
  else if is_infinity z1 && is_infinity z2 then
    if sign z1 == sign z2 then pos_infinity
    else neg_infinity
  else if is_infinity z2 && (sign z1 == sign z2) then pos_infinity
  else if is_infinity z1 && (sign z1 == sign z2) then pos_infinity
  else if is_infinity z2 && (sign z1 != sign z2) then neg_infinity
  else if is_infinity z1 && (sign z1 != sign z2) then neg_infinity
  else if is_zero z1 && is_zero z2 then
    if sign z1 == sign z2 then pos_zero
    else (** [z1 = ±0], [z2 = ∓0] **) neg_zero
  else mul z1 z2.

Definition fdiv (z1 z2 : T) :=
  if is_nan z1 || is_nan z2 then nans [:: z1; z2]
  else if is_infinity z1 && is_infinity z2 then nans [:: ]
  else if is_zero z2 && is_zero z1 then nans [:: z1; z2]
  else if is_infinity z1 && (sign z1 == sign z2) then pos_infinity
  else if is_infinity z1 && (sign z1 != sign z2) then neg_infinity
  else if is_infinity z2 && (sign z1 == sign z2) then pos_zero
  else if is_infinity z2 && (sign z1 != sign z2) then neg_zero
  else if is_zero z1 && (sign z1 == sign z2) then pos_zero
  else if is_zero z1 && (sign z1 != sign z2) then neg_zero
  else if is_zero z2 && (sign z1 == sign z2) then pos_infinity
  else if is_zero z2 && (sign z1 != sign z2) then pos_infinity
  else div z1 z2.

Definition fmin (z1 z2 : T) :=
  if is_nan z1 || is_nan z2 then nans [:: z1; z2]
  else if (z1 == neg_infinity) || (z2 == neg_infinity) then neg_infinity
  else if z1 == pos_infinity then z2
  else if z2 == pos_infinity then z1
  else if is_zero z1 && is_zero z2 && (sign z1 != sign z2) then neg_zero
  else if cmp Clt z1 z2 then z1 else z2.

Definition fmax (z1 z2 : T) :=
  if is_nan z1 || is_nan z2 then nans [:: z1; z2]
  else if (z1 == pos_infinity) || (z2 == pos_infinity) then pos_infinity
  else if z1 == neg_infinity then z2
  else if z2 == neg_infinity then z1
  else if is_zero z1 && is_zero z2 && (sign z1 != sign z2) then pos_zero
  else if cmp Cgt z1 z2 then z1 else z2.

Definition fcopysign (f1 f2 : T) :=
  if sign f1 == sign f2 then f1
  else opp f1.

Definition fabs (z : T) :=
  if is_nan z then set_sign false z
  else if is_infinity z then pos_infinity
  else if is_zero z then pos_zero
  else if cmp Cgt z pos_zero then z
  else opp z.

Definition fneg (z : T) :=
  if is_nan z then set_sign (~~ sign z) z
  else if is_infinity z then opp z
  else if is_zero z then opp z
  else opp z.

Definition fsqrt (z : T) :=
  if is_nan z then nans [:: z]
  else if sign z then nans [::]
  else if z == pos_infinity then pos_infinity
  else if is_zero z then z
  else sqrt z.

Definition fceil (z : T) :=
  if is_nan z then nans [:: z]
  else if is_infinity z then z
  else if is_zero z then z
  else if cmp Clt z neg_zero && cmp Cgt z (BofZ (-1)) then neg_zero
  else ceil z.

Definition ffloor (z : T) :=
  if is_nan z then nans [:: z]
  else if is_infinity z then z
  else if is_zero z then z
  else if cmp Cgt z pos_zero && cmp Clt z (BofZ 1) then pos_zero
  else floor z.

Definition ftrunc (z : T) :=
  if is_nan z then nans [:: z]
  else if is_infinity z then z
  else if is_zero z then z
  else if cmp Cgt z pos_zero && cmp Clt z (BofZ 1) then pos_zero
  else if cmp Clt z neg_zero && cmp Cgt z (BofZ (-1)) then neg_zero
  else trunc z.

Definition fnearest (z : T) :=
  if is_nan z then nans [:: z]
  else if is_infinity z then z
  else if is_zero z then z
  else if cmp Cgt z pos_zero && cmp Clt z (normalise 1 (-1)) then pos_zero
  else if cmp Clt z neg_zero && cmp Cgt z (normalise (-1) (-1)) then neg_zero
  else nearest z.

(** We also define the conversions to integers using the same operations. **)

(** The [trunc] operations are undefined if outside their respective range.
  This function thus checks these ranges. **)
Definition to_int_range t m (min max i : Z) : option t :=
  if (i >=? min)%Z && (i <=? max)%Z then
    Some (Wasm_int.int_of_Z m i)
  else None.

Definition ui32_trunc z :=
  Option.bind (to_int_range i32m 0 Wasm_int.Int32.max_unsigned) (trunco z).
Definition si32_trunc z :=
  Option.bind (to_int_range i32m Wasm_int.Int32.min_signed Wasm_int.Int32.max_signed) (trunco z).
Definition ui64_trunc z :=
  Option.bind (to_int_range i64m 0 Wasm_int.Int64.max_unsigned) (trunco z).
Definition si64_trunc z :=
  Option.bind (to_int_range i64m Wasm_int.Int64.min_signed Wasm_int.Int32.max_signed) (trunco z).

Definition convert_ui32 (i : i32) := BofZ (Wasm_int.Z_of_uint i32m i).
Definition convert_si32 (i : i32) := BofZ (Wasm_int.Z_of_sint i32m i).
Definition convert_ui64 (i : i64) := BofZ (Wasm_int.Z_of_uint i64m i).
Definition convert_si64 (i : i64) := BofZ (Wasm_int.Z_of_sint i64m i).

Definition Tmixin : mixin_of T := {|
    float_zero := pos_zero ;
    (** Unuary operators **)
    float_neg := fneg ;
    float_abs := fabs ;
    float_sqrt := fsqrt ;
    (** Rounding **)
    float_ceil := fceil ;
    float_floor := ffloor ;
    float_trunc := ftrunc ;
    float_nearest := fnearest ;
    (** Binary operators **)
    float_add := fadd ;
    float_sub := fsub ;
    float_mul := fmul ;
    float_div := fdiv ;
    float_min := fmin ;
    float_max := fmax ;
    float_copysign := fcopysign ;
    (** Comparisons **)
    float_eq := cmp Ceq ;
    float_lt := cmp Clt ;
    float_gt := cmp Cgt ;
    float_le := cmp Cle ;
    float_ge := cmp Cge ;
    (** Conversions **)
    float_ui32_trunc := ui32_trunc ;
    float_si32_trunc := si32_trunc ;
    float_ui64_trunc := ui64_trunc ;
    float_si64_trunc := si64_trunc ;
    float_convert_ui32 := convert_ui32 ;
    float_convert_si32 := convert_si32 ;
    float_convert_ui64 := convert_ui64 ;
    float_convert_si64 := convert_si64 ;
  |}.

Definition cT : type := Pack {| base := T_eqMixin; mixin := Tmixin |}.

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Local Definition xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Equality.class bT) b => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.

End Make.

(** ** Instantiations **)

Module Float32.
Include Make(FloatSize32).
End Float32.

Module Float64.
Include Make(FloatSize64).
End Float64.

(** ** Unit Tests **)

Lemma normalise_unit_test_64 : Float64.normalise_unit_test.
Proof. reflexivity. Qed.

Lemma ceil_unit_test_1_ok : Float64.ceil_unit_test_1.
Proof. reflexivity. Qed.

Lemma ceil_unit_test_2_ok : Float64.ceil_unit_test_2.
Proof. reflexivity. Qed.

Lemma floor_unit_test_1_ok : Float64.floor_unit_test_1.
Proof. reflexivity. Qed.

Lemma floor_unit_test_2_ok : Float64.floor_unit_test_2.
Proof. reflexivity. Qed.

Lemma trunc_unit_test_1_ok : Float64.trunc_unit_test_1.
Proof. reflexivity. Qed.

Lemma trunc_unit_test_2_ok : Float64.trunc_unit_test_2.
Proof. reflexivity. Qed.

Lemma nearest_unit_test_1_ok : Float64.nearest_unit_test_1.
Proof. reflexivity. Qed.

Lemma nearest_unit_test_2_ok : Float64.nearest_unit_test_2.
Proof. reflexivity. Qed.

Lemma nearest_unit_test_3_ok : Float64.nearest_unit_test_3.
Proof. reflexivity. Qed.

Lemma nearest_unit_test_4_ok : Float64.nearest_unit_test_4.
Proof. reflexivity. Qed.


End Wasm_float.

Definition f32 : eqType := Wasm_float.Float32.eqType.
Definition f32r : Wasm_float.class_of f32 := Wasm_float.Float32.class.
Definition f32t : Wasm_float.type := Wasm_float.Pack f32r.
Definition f32m := Wasm_float.mixin f32r.
Definition f64 : eqType := Wasm_float.Float64.eqType.
Definition f64r : Wasm_float.class_of f64 := Wasm_float.Float64.class.
Definition f64t : Wasm_float.type := Wasm_float.Pack f64r.
Definition f64m := Wasm_float.mixin f64r.

Definition wasm_demote (z : f64) : f32 :=
  if Wasm_float.Float64.is_canonical z then Wasm_float.Float32.nans [::]
  else if Wasm_float.Float64.is_nan z then
    Wasm_float.Float32.nans [:: Wasm_float.Float32.BofZ (BinIntDef.Z.of_nat 1)]
  else IEEE754_extra.Bconv _ _ _ _ Wasm_float.FloatSize32.prec_gt_0 Wasm_float.FloatSize32.Hmax
         (fun _ => Wasm_float.Float32.unspec_nan_nan) BinarySingleNaN.mode_NE z.

Definition wasm_promote (z : f32) : f64 :=
  if Wasm_float.Float32.is_canonical z then Wasm_float.Float64.nans [::]
  else if Wasm_float.Float32.is_nan z then
    Wasm_float.Float64.nans [:: Wasm_float.Float64.BofZ (BinIntDef.Z.of_nat 1)]
  else IEEE754_extra.Bconv _ _ _ _ Wasm_float.FloatSize64.prec_gt_0 Wasm_float.FloatSize64.Hmax
         (fun _ => Wasm_float.Float64.unspec_nan_nan) BinarySingleNaN.mode_NE z.

Definition wasm_bool (b : bool) : i32 :=
  if b then Wasm_int.Int32.one else Wasm_int.Int32.zero.

Definition int32_minus_one : i32 := Wasm_int.Int32.mone.
