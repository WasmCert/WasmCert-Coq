(** Properties about Wasm datatypes (mainly equality relations) **)

From Wasm Require Export datatypes.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition ascii_eq_dec : forall tf1 tf2 : Ascii.ascii,
  {tf1 = tf2} + {tf1 <> tf2}.
Proof. decidable_equality. Defined.

Definition ascii_eqb v1 v2 : bool := ascii_eq_dec v1 v2.
Definition eqasciiP : Equality.axiom ascii_eqb :=
  eq_dec_Equality_axiom ascii_eq_dec.

HB.instance Definition ascii_eqMixin := hasDecEq.Build Ascii.ascii eqasciiP.

Definition byte_eqb v1 v2 : bool := Byte.byte_eq_dec v1 v2.
Definition eqbyteP : Equality.axiom byte_eqb :=
  eq_dec_Equality_axiom Byte.byte_eq_dec.

HB.instance Definition byte_eqMixin := hasDecEq.Build Byte.byte eqbyteP.

Definition name_eq_dec : forall tf1 tf2 : name,
  {tf1 = tf2} + {tf1 <> tf2}.
Proof. decidable_equality. Defined.
Definition name_eqb v1 v2 := is_left (name_eq_dec v1 v2).
Definition eqnameP  : Equality.axiom name_eqb :=
  eq_dec_Equality_axiom name_eq_dec.

HB.instance Definition name_eqMixin := hasDecEq.Build name eqnameP.

Scheme Equality for number_type.
Definition number_type_eqb v1 v2 : bool := number_type_eq_dec v1 v2.
Definition eqnumber_typeP : Equality.axiom number_type_eqb :=
  eq_dec_Equality_axiom number_type_eq_dec.

HB.instance Definition number_type_eqMixin := hasDecEq.Build number_type eqnumber_typeP.

Scheme Equality for reference_type.
Definition reference_type_eqb v1 v2 : bool := reference_type_eq_dec v1 v2.
Definition eqreference_typeP : Equality.axiom reference_type_eqb :=
  eq_dec_Equality_axiom reference_type_eq_dec.

HB.instance Definition reference_type_eqMixin := hasDecEq.Build reference_type eqreference_typeP.

Scheme Equality for value_type.
Definition value_type_eqb v1 v2 : bool := value_type_eq_dec v1 v2.
Definition eqvalue_typeP : Equality.axiom value_type_eqb :=
  eq_dec_Equality_axiom value_type_eq_dec.

HB.instance Definition value_type_eqMixin := hasDecEq.Build value_type eqvalue_typeP.

Scheme Equality for packed_type.
Definition packed_type_eqb v1 v2 : bool := packed_type_eq_dec v1 v2.
Definition eqpacked_typeP : Equality.axiom packed_type_eqb :=
  eq_dec_Equality_axiom packed_type_eq_dec.

HB.instance Definition packed_type_eqMixin := hasDecEq.Build packed_type eqpacked_typeP.

Scheme Equality for mutability.
Definition mutability_eqb v1 v2 : bool := mutability_eq_dec v1 v2.
Definition eqmutabilityP : Equality.axiom mutability_eqb :=
  eq_dec_Equality_axiom mutability_eq_dec.

HB.instance Definition mutability_eqMixin := hasDecEq.Build mutability eqmutabilityP.

Scheme Equality for global_type.
Definition global_type_eqb v1 v2 : bool := global_type_eq_dec v1 v2.
Definition eqglobal_typeP : Equality.axiom global_type_eqb :=
  eq_dec_Equality_axiom global_type_eq_dec.

HB.instance Definition global_type_eqMixin := hasDecEq.Build global_type eqglobal_typeP.

Definition function_type_eq_dec : forall tf1 tf2 : function_type,
  {tf1 = tf2} + {tf1 <> tf2}.
Proof. decidable_equality. Defined.

Definition function_type_eqb v1 v2 : bool := function_type_eq_dec v1 v2.
Definition eqfunction_typeP : Equality.axiom function_type_eqb :=
  eq_dec_Equality_axiom function_type_eq_dec.

HB.instance Definition function_type_eqMixin := hasDecEq.Build function_type eqfunction_typeP.

Definition t_context_eq_dec : forall x y : t_context, {x = y} + {x <> y}.
Proof. decidable_equality. Defined.

Definition t_context_eqb v1 v2 : bool := t_context_eq_dec v1 v2.
Definition eqt_contextP : Equality.axiom t_context_eqb :=
  eq_dec_Equality_axiom t_context_eq_dec.

HB.instance Definition t_context_eqMixin := hasDecEq.Build t_context eqt_contextP.

Scheme Equality for sx.
Definition sx_eqb v1 v2 : bool := sx_eq_dec v1 v2.
Definition eqsxP : Equality.axiom sx_eqb :=
  eq_dec_Equality_axiom sx_eq_dec.

HB.instance Definition sx_eqMixin := hasDecEq.Build sx eqsxP.

Scheme Equality for unop_i.
Definition unop_i_eqb v1 v2 : bool := unop_i_eq_dec v1 v2.
Definition equnop_iP : Equality.axiom unop_i_eqb :=
  eq_dec_Equality_axiom unop_i_eq_dec.

HB.instance Definition unop_i_eqMixin := hasDecEq.Build unop_i equnop_iP.

Scheme Equality for unop_f.
Definition unop_f_eqb v1 v2 : bool := unop_f_eq_dec v1 v2.
Definition equnop_fP : Equality.axiom unop_f_eqb :=
  eq_dec_Equality_axiom unop_f_eq_dec.

HB.instance Definition unop_f_eqMixin := hasDecEq.Build unop_f equnop_fP.

Scheme Equality for binop_i.
Definition binop_i_eqb v1 v2 : bool := binop_i_eq_dec v1 v2.
Definition eqbinop_iP : Equality.axiom binop_i_eqb :=
  eq_dec_Equality_axiom binop_i_eq_dec.

HB.instance Definition binop_i_eqMixin := hasDecEq.Build binop_i eqbinop_iP.

Scheme Equality for binop_f.
Definition binop_f_eqb v1 v2 : bool := binop_f_eq_dec v1 v2.
Definition eqbinop_fP : Equality.axiom binop_f_eqb :=
  eq_dec_Equality_axiom binop_f_eq_dec.

HB.instance Definition binop_f_eqMixin := hasDecEq.Build binop_f eqbinop_fP.

Scheme Equality for testop.
Definition testop_eqb v1 v2 : bool := testop_eq_dec v1 v2.
Definition eqtestopP : Equality.axiom testop_eqb :=
  eq_dec_Equality_axiom testop_eq_dec.

HB.instance Definition testop_eqMixin := hasDecEq.Build testop eqtestopP.

Scheme Equality for relop_i.
Definition relop_i_eqb v1 v2 : bool := relop_i_eq_dec v1 v2.
Definition eqrelop_iP : Equality.axiom relop_i_eqb :=
  eq_dec_Equality_axiom relop_i_eq_dec.

HB.instance Definition relop_i_eqMixin := hasDecEq.Build relop_i eqrelop_iP.

Scheme Equality for relop_f.
Definition relop_f_eqb v1 v2 : bool := relop_f_eq_dec v1 v2.
Definition eqrelop_fP : Equality.axiom relop_f_eqb :=
  eq_dec_Equality_axiom relop_f_eq_dec.

HB.instance Definition relop_f_eqMixin := hasDecEq.Build relop_f eqrelop_fP.

Scheme Equality for cvtop.
Definition cvtop_eqb v1 v2 : bool := cvtop_eq_dec v1 v2.
Definition eqcvtopP : Equality.axiom cvtop_eqb :=
  eq_dec_Equality_axiom cvtop_eq_dec.

HB.instance Definition cvtop_eqMixin := hasDecEq.Build cvtop eqcvtopP.

Definition value_eq_dec : forall v1 v2 : value, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition value_eqb v1 v2 : bool := value_eq_dec v1 v2.
Definition eqvalueP : Equality.axiom value_eqb :=
  eq_dec_Equality_axiom value_eq_dec.

HB.instance Definition value_eqMixin := hasDecEq.Build value eqvalueP.

Definition value_num_eq_dec : forall v1 v2 : value_num, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition value_num_eqb v1 v2 : bool := value_num_eq_dec v1 v2.
Definition eqvalue_numP : Equality.axiom value_num_eqb :=
  eq_dec_Equality_axiom value_num_eq_dec.

HB.instance Definition value_num_eqMixin := hasDecEq.Build value_num eqvalue_numP.

Definition value_ref_eq_dec : forall v1 v2 : value_ref, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition value_ref_eqb v1 v2 : bool := value_ref_eq_dec v1 v2.
Definition eqvalue_refP : Equality.axiom value_ref_eqb :=
  eq_dec_Equality_axiom value_ref_eq_dec.

HB.instance Definition value_ref_eqMixin := hasDecEq.Build value_ref eqvalue_refP.

Definition extern_type_eq_dec : forall v1 v2 : extern_type, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition extern_type_eqb v1 v2 : bool := extern_type_eq_dec v1 v2.
Definition eqextern_typeP : Equality.axiom extern_type_eqb :=
  eq_dec_Equality_axiom extern_type_eq_dec.

HB.instance Definition extern_type_eqMixin := hasDecEq.Build extern_type eqextern_typeP.

Definition extern_value_eq_dec : forall v1 v2 : extern_value, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition extern_value_eqb v1 v2 : bool := extern_value_eq_dec v1 v2.
Definition eqextern_valueP : Equality.axiom extern_value_eqb :=
  eq_dec_Equality_axiom extern_value_eq_dec.

HB.instance Definition extern_value_eqMixin := hasDecEq.Build extern_value eqextern_valueP.

(** Induction scheme for [basic_instruction]. **)
Definition basic_instruction_rect' :=
  ltac:(rect'_build basic_instruction_rect).

Definition basic_instruction_ind' (P : basic_instruction -> Prop) :=
  @basic_instruction_rect' P.

Definition basic_instruction_eq_dec : forall e1 e2 : basic_instruction,
  {e1 = e2} + {e1 <> e2}.
Proof. decidable_equality_using basic_instruction_rect'. Defined.

Definition basic_instruction_eqb cl1 cl2 : bool :=
  basic_instruction_eq_dec cl1 cl2.
Definition eqbasic_instructionP : Equality.axiom basic_instruction_eqb :=
  eq_dec_Equality_axiom basic_instruction_eq_dec.

HB.instance Definition basic_instruction_eqMixin := hasDecEq.Build basic_instruction eqbasic_instructionP.

Definition moduleinst_eq_dec : forall (i1 i2 : moduleinst), {i1 = i2} + {i1 <> i2}.
Proof. decidable_equality. Defined.

Definition moduleinst_eqb i1 i2 : bool := moduleinst_eq_dec i1 i2.

Definition eqmoduleinstP : Equality.axiom moduleinst_eqb :=
  eq_dec_Equality_axiom moduleinst_eq_dec.

HB.instance Definition moduleinst_eqMixin := hasDecEq.Build moduleinst eqmoduleinstP.

Definition administrative_instruction_rect :=
  @administrative_instruction_rect
  : forall (P : administrative_instruction -> Type), _.

Section Host.

  Context `{host_function_class}.

Definition funcinst_eq_dec : forall (cl1 cl2 : funcinst),
  {cl1 = cl2} + {cl1 <> cl2}.
Proof. decidable_equality.
       by apply host_function_eq_dec.
Defined.

Definition funcinst_eqb cl1 cl2 : bool := funcinst_eq_dec cl1 cl2.
Definition eqfuncinstP : Equality.axiom funcinst_eqb :=
  eq_dec_Equality_axiom funcinst_eq_dec.

HB.instance Definition funcinst_eqMixin := hasDecEq.Build funcinst eqfuncinstP.

Definition tableinst_eq_dec : forall v1 v2 : tableinst, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.
  
Definition tableinst_eqb v1 v2 : bool := tableinst_eq_dec v1 v2.
Definition eqtableinstP : Equality.axiom tableinst_eqb :=
  eq_dec_Equality_axiom tableinst_eq_dec.

HB.instance Definition tableinst_eqMixin := hasDecEq.Build tableinst eqtableinstP.

Definition globalinst_eq_dec : forall v1 v2 : globalinst, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition globalinst_eqb v1 v2 : bool := globalinst_eq_dec v1 v2.
Definition eqglobalinstP : Equality.axiom globalinst_eqb :=
  eq_dec_Equality_axiom globalinst_eq_dec.

HB.instance Definition globalinst_eqMixin := hasDecEq.Build globalinst eqglobalinstP.

Definition eleminst_eq_dec : forall v1 v2 : eleminst, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition eleminst_eqb v1 v2 : bool := eleminst_eq_dec v1 v2.
Definition eqeleminstP : Equality.axiom eleminst_eqb :=
  eq_dec_Equality_axiom eleminst_eq_dec.

HB.instance Definition eleminst_eqMixin := hasDecEq.Build eleminst eqeleminstP.

Definition datainst_eq_dec : forall v1 v2 : datainst, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition datainst_eqb v1 v2 : bool := datainst_eq_dec v1 v2.
Definition eqdatainstP : Equality.axiom datainst_eqb :=
  eq_dec_Equality_axiom datainst_eq_dec.

HB.instance Definition datainst_eqMixin := hasDecEq.Build datainst eqdatainstP.

Definition exportinst_eq_dec : forall v1 v2 : exportinst, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition exportinst_eqb v1 v2 : bool := exportinst_eq_dec v1 v2.
Definition eqexportinstP : Equality.axiom exportinst_eqb :=
  eq_dec_Equality_axiom exportinst_eq_dec.

HB.instance Definition exportinst_eqMixin := hasDecEq.Build exportinst eqexportinstP.

Definition frame_eq_dec : forall v1 v2 : frame, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition frame_eqb v1 v2 : bool := frame_eq_dec v1 v2.
Definition eqframeP : Equality.axiom frame_eqb :=
  eq_dec_Equality_axiom frame_eq_dec.

HB.instance Definition frame_eqMixin := hasDecEq.Build frame eqframeP.

Definition module_export_desc_eq_dec : forall v1 v2 : module_export_desc, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition module_export_desc_eqb v1 v2 : bool := module_export_desc_eq_dec v1 v2.
Definition eqmodule_export_descP : Equality.axiom module_export_desc_eqb :=
  eq_dec_Equality_axiom module_export_desc_eq_dec.

HB.instance Definition module_export_desc_eqMixin := hasDecEq.Build module_export_desc eqmodule_export_descP.

Definition module_export_eq_dec : forall v1 v2 : module_export, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition module_export_eqb v1 v2 : bool := module_export_eq_dec v1 v2.
Definition eqmodule_exportP : Equality.axiom module_export_eqb :=
  eq_dec_Equality_axiom module_export_eq_dec.

HB.instance Definition module_export_eqMixin := hasDecEq.Build module_export eqmodule_exportP.

(** Induction scheme for [administrative_instruction]. **)
Definition administrative_instruction_rect' :=
  ltac:(rect'_build administrative_instruction_rect).

Definition administrative_instruction_ind' (P : administrative_instruction -> Prop) :=
  @administrative_instruction_rect' P.

(** Administrative instructions frequently come in lists.
  Here is the corresponding induction principle. **)
(* TODO: rect'_build_list fails to generate wellformed definitions on newer versions
   of Coq. Use manual versions for now *)
(*
Definition seq_administrative_instruction_rect' :=
  ltac:(rect'_build_list administrative_instruction_rect).

Definition seq_administrative_instruction_ind' (P : administrative_instruction -> Prop) :=
  @seq_administrative_instruction_rect' P.
*)

Definition administrative_instruction_eq_dec : forall e1 e2 : administrative_instruction,
  {e1 = e2} + {e1 <> e2}.
Proof. decidable_equality_using administrative_instruction_rect'. Defined.

Definition administrative_instruction_eqb cl1 cl2 : bool :=
  administrative_instruction_eq_dec cl1 cl2.
Definition eqadministrative_instructionP : Equality.axiom administrative_instruction_eqb :=
  eq_dec_Equality_axiom administrative_instruction_eq_dec.

HB.instance Definition administrative_instruction_eqMixin := hasDecEq.Build administrative_instruction eqadministrative_instructionP.

End Host.

(** Decidable equality of lholed without pulling in unnecessary 
    equality axioms **)
Section lholed_eqdec.

Definition lholed_cast {k k'} (lh: lholed k) (Heq: k = k'): lholed k' :=
  eq_rect k lholed lh k' Heq.

(* Some combinations of theorem from standard library should give these as well,
   but it's not clear which ones are axiom free *)
Theorem nat_eqdec_refl: forall k, PeanoNat.Nat.eq_dec k k = left (erefl k).
Proof.
  elim => //=.
  move => k IH.
  by rewrite IH.
Defined.

Definition nat_eqdec_canon k k' (H: k = k') : k = k' :=
  match (PeanoNat.Nat.eq_dec k k') with
  | left e => e
  | right ne => False_ind _ (ne H)
  end.

Theorem nat_eqdec_aux: forall (k: nat) (H: k = k), H = nat_eqdec_canon H.
Proof.
  move => k H.
  case H.
  unfold nat_eqdec_canon.
  by rewrite nat_eqdec_refl.
Defined.

Theorem nat_eqdec_unique: forall (k: nat) (H: k = k), H = erefl k.
Proof.
  move => k H.
  rewrite (nat_eqdec_aux H).
  unfold nat_eqdec_canon.
  by rewrite nat_eqdec_refl.
Defined.

Theorem lh_cast_eq {k} (lh: lholed k) (Heq: k = k):
  @lholed_cast k k lh Heq = lh.
Proof.
  by rewrite (nat_eqdec_unique Heq).
Qed.

Ltac decide_eq_arg x y :=
  let Heq := fresh "Heq" in
  let Hcontra := fresh "Hcontra" in
  destruct (x == y) eqn:Heq; move/eqP in Heq; subst; last by right; move => Hcontra; injection Hcontra.

(* Destruct principle for a (lh n).
   Usage: either direct application, or `destruct ... using lh_case.` *)
Definition lh_case: forall n (P: lholed n -> Type),
    (forall (H: 0 = n) vs es, P (lholed_cast (LH_base vs es) H)) ->
    (forall n' (H: S n' = n) vs k es (lh: lholed n') es', P (lholed_cast (LH_rec vs k es lh es') H)) ->
    (forall (lh: lholed n), P lh).
Proof.
  move => n P H0 Hrec lh.
  destruct lh as [lvs les | n lvs k les lh les'].
  - by specialize (H0 (erefl 0) lvs les).
  - by specialize (Hrec _ (erefl (S n)) lvs k les lh les'). 
Defined.

(* Decidable equality of lholed without eq_rect_eq *)
Definition lholed_eq_dec : forall k (lh1 lh2 : lholed k), {lh1 = lh2} + {lh1 <> lh2}.
Proof.
  elim.
  {
    move => lh1.
    eapply lh_case; last done.
    move => H vs es; rewrite lh_cast_eq.
    move: lh1.
    eapply lh_case; last done.
    move => H' vs' es'; rewrite lh_cast_eq.
    decide_equality_injection; by decidable_equality.
  }
  {
    move => n IH lh.
    eapply lh_case; first done.
    move => n1 H1 vs1 k1 es1 lh1 es1'; injection H1 as ->; rewrite lh_cast_eq.
    move: lh.
    eapply lh_case; first done.
    move => n2 H2 vs2 k2 es2 lh2 es2'; injection H2 as ->; rewrite lh_cast_eq.
    decide_eq_arg vs2 vs1.
    decide_eq_arg k2 k1.
    decide_eq_arg es2 es1.
    decide_eq_arg es2' es1'.
    destruct (IH lh1 lh2) as [ | Hneq]; subst; first by left.
    right. move => Hcontra; apply Hneq.
    clear - Hcontra.
    inversion Hcontra.
    (* This one is axiom free *)
    apply Eqdep_dec.inj_pair2_eq_dec in H0 => //.
    decide equality.
  }
Defined.

Definition lholed_eqb {k} (v1 v2: lholed k) : bool := lholed_eq_dec v1 v2.

Definition eqlholedP {k} :=
  eq_dec_Equality_axiom (@lholed_eq_dec k).

HB.instance Definition lholed_eqMixin {k} := hasDecEq.Build (lholed k) (@eqlholedP k).

End lholed_eqdec.

Definition limits_eq_dec : forall v1 v2 : limits, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.
Definition limits_eqb v1 v2 : bool := limits_eq_dec v1 v2.
Definition eqlimitsP : Equality.axiom limits_eqb :=
  eq_dec_Equality_axiom limits_eq_dec.

HB.instance Definition limits_eqMixin := hasDecEq.Build limits eqlimitsP.

Definition table_type_eq_dec : forall v1 v2 : table_type, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.
Definition table_type_eqb v1 v2 : bool := table_type_eq_dec v1 v2.
Definition eqtable_typeP : Equality.axiom table_type_eqb :=
  eq_dec_Equality_axiom table_type_eq_dec.

HB.instance Definition table_type_eqMixin := hasDecEq.Build table_type eqtable_typeP.

Definition memory_type_eq_dec : forall v1 v2 : memory_type, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.
Definition memory_type_eqb v1 v2 : bool := memory_type_eq_dec v1 v2.
Definition eqmemory_typeP : Equality.axiom memory_type_eqb :=
  eq_dec_Equality_axiom memory_type_eq_dec.

HB.instance Definition memory_type_eqMixin := hasDecEq.Build memory_type eqmemory_typeP.
