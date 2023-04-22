(** Properties about Wasm datatypes (mainly equality relations) **)
(* (C) M. Bodin, J. Pichon - see LICENSE.txt *)

Require Import bytes common.
Require Export datatypes.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Definition ascii_eq_dec : forall tf1 tf2 : Ascii.ascii,
  {tf1 = tf2} + {tf1 <> tf2}.
Proof. decidable_equality. Defined.

Definition ascii_eqb v1 v2 : bool := ascii_eq_dec v1 v2.
Definition eqasciiP : Equality.axiom ascii_eqb :=
  eq_dec_Equality_axiom ascii_eq_dec.

Canonical Structure ascii_eqMixin := EqMixin eqasciiP.
Canonical Structure ascii_eqType :=
  Eval hnf in EqType Ascii.ascii ascii_eqMixin.

Definition byte_eqb v1 v2 : bool := Byte.byte_eq_dec v1 v2.
Definition eqbyteP : Equality.axiom byte_eqb :=
  eq_dec_Equality_axiom Byte.byte_eq_dec.

Canonical Structure byte_eqMixin := EqMixin eqbyteP.
Canonical Structure byte_eqType :=
  Eval hnf in EqType Byte.byte byte_eqMixin.

Scheme Equality for number_type.
Definition number_type_eqb v1 v2 : bool := number_type_eq_dec v1 v2.
Definition eqnumber_typeP : Equality.axiom number_type_eqb :=
  eq_dec_Equality_axiom number_type_eq_dec.

Canonical Structure number_type_eqMixin := EqMixin eqnumber_typeP.
Canonical Structure number_type_eqType := Eval hnf in EqType number_type number_type_eqMixin.

Scheme Equality for reference_type.
Definition reference_type_eqb v1 v2 : bool := reference_type_eq_dec v1 v2.
Definition eqreference_typeP : Equality.axiom reference_type_eqb :=
  eq_dec_Equality_axiom reference_type_eq_dec.

Canonical Structure reference_type_eqMixin := EqMixin eqreference_typeP.
Canonical Structure reference_type_eqType := Eval hnf in EqType reference_type reference_type_eqMixin.

Scheme Equality for value_type.
Definition value_type_eqb v1 v2 : bool := value_type_eq_dec v1 v2.
Definition eqvalue_typeP : Equality.axiom value_type_eqb :=
  eq_dec_Equality_axiom value_type_eq_dec.

Canonical Structure value_type_eqMixin := EqMixin eqvalue_typeP.
Canonical Structure value_type_eqType := Eval hnf in EqType value_type value_type_eqMixin.

Scheme Equality for packed_type.
Definition packed_type_eqb v1 v2 : bool := packed_type_eq_dec v1 v2.
Definition eqpacked_typeP : Equality.axiom packed_type_eqb :=
  eq_dec_Equality_axiom packed_type_eq_dec.

Canonical Structure packed_type_eqMixin := EqMixin eqpacked_typeP.
Canonical Structure packed_type_eqType := Eval hnf in EqType packed_type packed_type_eqMixin.

Scheme Equality for mutability.
Definition mutability_eqb v1 v2 : bool := mutability_eq_dec v1 v2.
Definition eqmutabilityP : Equality.axiom mutability_eqb :=
  eq_dec_Equality_axiom mutability_eq_dec.

Canonical Structure mutability_eqMixin := EqMixin eqmutabilityP.
Canonical Structure mutability_eqType := Eval hnf in EqType mutability mutability_eqMixin.

Scheme Equality for global_type.
Definition global_type_eqb v1 v2 : bool := global_type_eq_dec v1 v2.
Definition eqglobal_typeP : Equality.axiom global_type_eqb :=
  eq_dec_Equality_axiom global_type_eq_dec.

Canonical Structure global_type_eqMixin := EqMixin eqglobal_typeP.
Canonical Structure global_type_eqType := Eval hnf in EqType global_type global_type_eqMixin.

Definition function_type_eq_dec : forall tf1 tf2 : function_type,
  {tf1 = tf2} + {tf1 <> tf2}.
Proof. decidable_equality. Defined.

Definition function_type_eqb v1 v2 : bool := function_type_eq_dec v1 v2.
Definition eqfunction_typeP : Equality.axiom function_type_eqb :=
  eq_dec_Equality_axiom function_type_eq_dec.

Canonical Structure function_type_eqMixin := EqMixin eqfunction_typeP.
Canonical Structure function_type_eqType :=
  Eval hnf in EqType function_type function_type_eqMixin.

Definition t_context_eq_dec : forall x y : t_context, {x = y} + {x <> y}.
Proof. decidable_equality. Defined.

Definition t_context_eqb v1 v2 : bool := t_context_eq_dec v1 v2.
Definition eqt_contextP : Equality.axiom t_context_eqb :=
  eq_dec_Equality_axiom t_context_eq_dec.

Canonical Structure t_context_eqMixin := EqMixin eqt_contextP.
Canonical Structure t_context_eqType := Eval hnf in EqType t_context t_context_eqMixin.

Scheme Equality for sx.
Definition sx_eqb v1 v2 : bool := sx_eq_dec v1 v2.
Definition eqsxP : Equality.axiom sx_eqb :=
  eq_dec_Equality_axiom sx_eq_dec.

Canonical Structure sx_eqMixin := EqMixin eqsxP.
Canonical Structure sx_eqType := Eval hnf in EqType sx sx_eqMixin.

Scheme Equality for unop_i.
Definition unop_i_eqb v1 v2 : bool := unop_i_eq_dec v1 v2.
Definition equnop_iP : Equality.axiom unop_i_eqb :=
  eq_dec_Equality_axiom unop_i_eq_dec.

Canonical Structure unop_i_eqMixin := EqMixin equnop_iP.
Canonical Structure unop_i_eqType := Eval hnf in EqType unop_i unop_i_eqMixin.

Scheme Equality for unop_f.
Definition unop_f_eqb v1 v2 : bool := unop_f_eq_dec v1 v2.
Definition equnop_fP : Equality.axiom unop_f_eqb :=
  eq_dec_Equality_axiom unop_f_eq_dec.

Canonical Structure unop_f_eqMixin := EqMixin equnop_fP.
Canonical Structure unop_f_eqType := Eval hnf in EqType unop_f unop_f_eqMixin.

Scheme Equality for binop_i.
Definition binop_i_eqb v1 v2 : bool := binop_i_eq_dec v1 v2.
Definition eqbinop_iP : Equality.axiom binop_i_eqb :=
  eq_dec_Equality_axiom binop_i_eq_dec.

Canonical Structure binop_i_eqMixin := EqMixin eqbinop_iP.
Canonical Structure binop_i_eqType := Eval hnf in EqType binop_i binop_i_eqMixin.

Scheme Equality for binop_f.
Definition binop_f_eqb v1 v2 : bool := binop_f_eq_dec v1 v2.
Definition eqbinop_fP : Equality.axiom binop_f_eqb :=
  eq_dec_Equality_axiom binop_f_eq_dec.

Canonical Structure binop_f_eqMixin := EqMixin eqbinop_fP.
Canonical Structure binop_f_eqType := Eval hnf in EqType binop_f binop_f_eqMixin.

Scheme Equality for testop.
Definition testop_eqb v1 v2 : bool := testop_eq_dec v1 v2.
Definition eqtestopP : Equality.axiom testop_eqb :=
  eq_dec_Equality_axiom testop_eq_dec.

Canonical Structure testop_eqMixin := EqMixin eqtestopP.
Canonical Structure testop_eqType := Eval hnf in EqType testop testop_eqMixin.

Scheme Equality for relop_i.
Definition relop_i_eqb v1 v2 : bool := relop_i_eq_dec v1 v2.
Definition eqrelop_iP : Equality.axiom relop_i_eqb :=
  eq_dec_Equality_axiom relop_i_eq_dec.

Canonical Structure relop_i_eqMixin := EqMixin eqrelop_iP.
Canonical Structure relop_i_eqType := Eval hnf in EqType relop_i relop_i_eqMixin.

Scheme Equality for relop_f.
Definition relop_f_eqb v1 v2 : bool := relop_f_eq_dec v1 v2.
Definition eqrelop_fP : Equality.axiom relop_f_eqb :=
  eq_dec_Equality_axiom relop_f_eq_dec.

Canonical Structure relop_f_eqMixin := EqMixin eqrelop_fP.
Canonical Structure relop_f_eqType := Eval hnf in EqType relop_f relop_f_eqMixin.

Scheme Equality for cvtop.
Definition cvtop_eqb v1 v2 : bool := cvtop_eq_dec v1 v2.
Definition eqcvtopP : Equality.axiom cvtop_eqb :=
  eq_dec_Equality_axiom cvtop_eq_dec.

Canonical Structure cvtop_eqMixin := EqMixin eqcvtopP.
Canonical Structure cvtop_eqType := Eval hnf in EqType cvtop cvtop_eqMixin.

Definition value_eq_dec : forall v1 v2 : value, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition value_eqb v1 v2 : bool := value_eq_dec v1 v2.
Definition eqvalueP : Equality.axiom value_eqb :=
  eq_dec_Equality_axiom value_eq_dec.

Canonical Structure value_eqMixin := EqMixin eqvalueP.
Canonical Structure value_eqType := Eval hnf in EqType value value_eqMixin.

Definition value_num_eq_dec : forall v1 v2 : value_num, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition value_num_eqb v1 v2 : bool := value_num_eq_dec v1 v2.
Definition eqvalue_numP : Equality.axiom value_num_eqb :=
  eq_dec_Equality_axiom value_num_eq_dec.

Canonical Structure value_num_eqMixin := EqMixin eqvalue_numP.
Canonical Structure value_num_eqType := Eval hnf in EqType value_num value_num_eqMixin.

Definition value_ref_eq_dec : forall v1 v2 : value_ref, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition value_ref_eqb v1 v2 : bool := value_ref_eq_dec v1 v2.
Definition eqvalue_refP : Equality.axiom value_ref_eqb :=
  eq_dec_Equality_axiom value_ref_eq_dec.

Canonical Structure value_ref_eqMixin := EqMixin eqvalue_refP.
Canonical Structure value_ref_eqType := Eval hnf in EqType value_ref value_ref_eqMixin.
(*
(* TODO: update *)
(** Some helper functions for [value] that can safely extract. **)
Definition value_rec_safe (P : Type)
           (i32 : Wasm_int.Int32.int -> P)
           (i64 : Wasm_int.Int64.int -> P)
           (f32 : Wasm_float.FloatSize32.T -> P)
           (f64 : Wasm_float.FloatSize64.T -> P) v : P :=
  value_rect i32 i64 f32 f64 v.
*)

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

Canonical Structure basic_instruction_eqMixin := EqMixin eqbasic_instructionP.
Canonical Structure basic_instruction_eqType :=
  Eval hnf in EqType basic_instruction basic_instruction_eqMixin.

Definition instance_eq_dec : forall (i1 i2 : instance), {i1 = i2} + {i1 <> i2}.
Proof. decidable_equality. Defined.

Definition instance_eqb i1 i2 : bool := instance_eq_dec i1 i2.

Definition eqinstanceP : Equality.axiom instance_eqb :=
  eq_dec_Equality_axiom instance_eq_dec.

Canonical Structure instance_eqMixin := EqMixin eqinstanceP.
Canonical Structure instance_eqType := Eval hnf in EqType instance instance_eqMixin.



Section Host.

Variable host_function : eqType.

Let function_closure := function_closure host_function.
Let store_record := store_record host_function.

Let administrative_instruction_rect :=
  @administrative_instruction_rect (*host_function*)
  : forall (P : administrative_instruction -> Type), _.

Definition function_closure_eq_dec : forall (cl1 cl2 : function_closure),
  {cl1 = cl2} + {cl1 <> cl2}.
Proof. decidable_equality. Defined.

Definition function_closure_eqb cl1 cl2 : bool := function_closure_eq_dec cl1 cl2.
Definition eqfunction_closureP : Equality.axiom function_closure_eqb :=
  eq_dec_Equality_axiom function_closure_eq_dec.

Canonical Structure function_closure_eqMixin := EqMixin eqfunction_closureP.
Canonical Structure function_closure_eqType :=
  Eval hnf in EqType function_closure function_closure_eqMixin.

Definition tableinst_eq_dec : forall v1 v2 : tableinst, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.
  
Definition tableinst_eqb v1 v2 : bool := tableinst_eq_dec v1 v2.
Definition eqtableinstP : Equality.axiom tableinst_eqb :=
  eq_dec_Equality_axiom tableinst_eq_dec.

Canonical Structure tableinst_eqMixin := EqMixin eqtableinstP.
Canonical Structure tableinst_eqType := Eval hnf in EqType tableinst tableinst_eqMixin.

Definition globalinst_eq_dec : forall v1 v2 : globalinst, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition globalinst_eqb v1 v2 : bool := globalinst_eq_dec v1 v2.
Definition eqglobalinstP : Equality.axiom globalinst_eqb :=
  eq_dec_Equality_axiom globalinst_eq_dec.

Canonical Structure globalinst_eqMixin := EqMixin eqglobalinstP.
Canonical Structure globalinst_eqType := Eval hnf in EqType globalinst globalinst_eqMixin.

Definition eleminst_eq_dec : forall v1 v2 : eleminst, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition eleminst_eqb v1 v2 : bool := eleminst_eq_dec v1 v2.
Definition eqeleminstP : Equality.axiom eleminst_eqb :=
  eq_dec_Equality_axiom eleminst_eq_dec.

Canonical Structure eleminst_eqMixin := EqMixin eqeleminstP.
Canonical Structure eleminst_eqType := Eval hnf in EqType eleminst eleminst_eqMixin.

Definition datainst_eq_dec : forall v1 v2 : datainst, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition datainst_eqb v1 v2 : bool := datainst_eq_dec v1 v2.
Definition eqdatainstP : Equality.axiom datainst_eqb :=
  eq_dec_Equality_axiom datainst_eq_dec.

Canonical Structure datainst_eqMixin := EqMixin eqdatainstP.
Canonical Structure datainst_eqType := Eval hnf in EqType datainst datainst_eqMixin.

Definition store_record_eq_dec : forall v1 v2 : store_record, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition store_record_eqb v1 v2 : bool := store_record_eq_dec v1 v2.
Definition eqstore_recordP : Equality.axiom store_record_eqb :=
  eq_dec_Equality_axiom store_record_eq_dec.

Canonical Structure store_record_eqMixin := EqMixin eqstore_recordP.
Canonical Structure store_record_eqType := Eval hnf in EqType store_record store_record_eqMixin.

Definition frame_eq_dec : forall v1 v2 : frame, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition frame_eqb v1 v2 : bool := frame_eq_dec v1 v2.
Definition eqframeP : Equality.axiom frame_eqb :=
  eq_dec_Equality_axiom frame_eq_dec.

Canonical Structure frame_eqMixin := EqMixin eqframeP.
Canonical Structure frame_eqType := Eval hnf in EqType frame frame_eqMixin.

Definition module_export_desc_eq_dec : forall v1 v2 : module_export_desc, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition module_export_desc_eqb v1 v2 : bool := module_export_desc_eq_dec v1 v2.
Definition eqmodule_export_descP : Equality.axiom module_export_desc_eqb :=
  eq_dec_Equality_axiom module_export_desc_eq_dec.

Canonical Structure module_export_desc_eqMixin := EqMixin eqmodule_export_descP.
Canonical Structure module_export_desc_eqType :=
  Eval hnf in EqType module_export_desc module_export_desc_eqMixin.

Definition module_export_eq_dec : forall v1 v2 : module_export, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition module_export_eqb v1 v2 : bool := module_export_eq_dec v1 v2.
Definition eqmodule_exportP : Equality.axiom module_export_eqb :=
  eq_dec_Equality_axiom module_export_eq_dec.

Canonical Structure module_export_eqMixin := EqMixin eqmodule_exportP.
Canonical Structure module_export_eqType := Eval hnf in EqType module_export module_export_eqMixin.

(** Induction scheme for [administrative_instruction]. **)
Definition administrative_instruction_rect' :=
  ltac:(rect'_build administrative_instruction_rect).

Definition administrative_instruction_ind' (P : administrative_instruction -> Prop) :=
  @administrative_instruction_rect' P.

(** Administrative instructions frequently come in lists.
  Here is the corresponding induction principle. **)
Definition seq_administrative_instruction_rect' :=
  ltac:(rect'_build_list administrative_instruction_rect).

Definition seq_administrative_instruction_ind' (P : administrative_instruction -> Prop) :=
  @seq_administrative_instruction_rect' P.

Definition administrative_instruction_eq_dec : forall e1 e2 : administrative_instruction,
  {e1 = e2} + {e1 <> e2}.
Proof. decidable_equality_using administrative_instruction_rect'. Defined.

Definition administrative_instruction_eqb cl1 cl2 : bool :=
  administrative_instruction_eq_dec cl1 cl2.
Definition eqadministrative_instructionP : Equality.axiom administrative_instruction_eqb :=
  eq_dec_Equality_axiom administrative_instruction_eq_dec.

Canonical Structure administrative_instruction_eqMixin := EqMixin eqadministrative_instructionP.
Canonical Structure administrative_instruction_eqType :=
  Eval hnf in EqType administrative_instruction administrative_instruction_eqMixin.


(* We use a known trick to avoid using UIP or JMeq for deciding dependently-typed lholed. *)

Lemma lholed_destructP: forall (k: nat) (P: lholed k -> Type),
    (forall vs es (pf: k = 0),
        P (eq_rect 0 lholed (LH_base vs es) k (Logic.eq_sym pf))) ->
    (forall k' vs n es lh' les (pf: k = S k'),
        P (eq_rect (S k') lholed (LH_rec vs n es lh' les) k (Logic.eq_sym pf))) ->
    (forall lh, P lh).
Proof.
  move => k P Hbase Hrec.
  destruct lh as [vs es | k vs n es lh' les] eqn:Hlh; subst.
  - by specialize (Hbase vs es Logic.eq_refl).
  - by specialize (Hrec k vs n es lh' les Logic.eq_refl).
Qed.

Ltac lholed_destruct lh :=
  pattern lh; apply lholed_destructP => //; clear lh.

Definition lholed_eq_dec : forall {k: nat} (lh1 lh2: lholed k), {lh1 = lh2} + {lh1 <> lh2}.
Proof.
  move => k lh1; induction lh1 as [vs es | k' vs n es lh' IHdec les]; move => lh2.
  - lholed_destruct lh2; move => vs2 es2 ?.
    rewrite <- Eqdep_dec.eq_rect_eq_dec; last by decidable_equality.
    destruct ((vs == vs2) && (es == es2)) eqn:Heqb;move/andP in Heqb.
    + destruct Heqb as [Heql1 Heql2]; move/eqP in Heql1; move/eqP in Heql2; subst; by left.
    + right. move => Hcontra; apply Heqb.
      inversion Hcontra; by subst.
  - lholed_destruct lh2; move => k2 vs2 n2 es2 lh'2 les2 Heqk.
    assert (k' = k2); first by lias. subst.
    rewrite <- Eqdep_dec.eq_rect_eq_dec; last by decidable_equality.
    specialize (IHdec lh'2).
    destruct IHdec as [ | Hneq]; subst.
    + destruct ((vs == vs2) && (n == n2) && (es == es2) && (les == les2)) eqn:Heqb.
      * move/andP in Heqb; destruct Heqb as [Heql1 Heql4]; move/eqP in Heql4.
      * move/andP in Heql1; destruct Heql1 as [Heql1 Heql3]; move/eqP in Heql3.
        move/andP in Heql1; destruct Heql1 as [Heql1 Heql2]; move/eqP in Heql1; move/eqP in Heql2; subst.
        by left.
      * move/andP in Heqb.
        right. move => Hcontra; apply Heqb.
        inversion Hcontra; subst; by lias.
    + right. move => Hcontra.
      inversion Hcontra as [[H1 H2 H3 H4 H5]].
      apply Eqdep_dec.inj_pair2_eq_dec in H4 => //.
      decide equality.
Qed.

Definition lholed_eqb {k: nat} (lh1 lh2: lholed k) : bool := lholed_eq_dec lh1 lh2.
Definition eqlholedP {k: nat}: Equality.axiom lholed_eqb :=
  eq_dec_Equality_axiom (@lholed_eq_dec k).

Canonical Structure lholed_eqMixin {k: nat} := EqMixin (@eqlholedP k).
Canonical Structure lholed_eqType {k: nat} := Eval hnf in EqType (lholed k) lholed_eqMixin.

Definition limits_eq_dec : forall v1 v2 : limits, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.
Definition limits_eqb v1 v2 : bool := limits_eq_dec v1 v2.
Definition eqlimitsP : Equality.axiom limits_eqb :=
  eq_dec_Equality_axiom limits_eq_dec.

Canonical Structure limits_eqMixin := EqMixin eqlimitsP.
Canonical Structure limits_eqType := Eval hnf in EqType limits limits_eqMixin.


Definition table_type_eq_dec : forall v1 v2 : table_type, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.
Definition table_type_eqb v1 v2 : bool := table_type_eq_dec v1 v2.
Definition eqtable_typeP : Equality.axiom table_type_eqb :=
  eq_dec_Equality_axiom table_type_eq_dec.

Canonical Structure table_type_eqMixin := EqMixin eqtable_typeP.
Canonical Structure table_type_eqType := Eval hnf in EqType table_type table_type_eqMixin.

Definition memory_type_eq_dec : forall v1 v2 : memory_type, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.
Definition memory_type_eqb v1 v2 : bool := memory_type_eq_dec v1 v2.
Definition eqmemory_typeP : Equality.axiom memory_type_eqb :=
  eq_dec_Equality_axiom memory_type_eq_dec.

Canonical Structure memory_type_eqMixin := EqMixin eqmemory_typeP.
Canonical Structure memory_type_eqType := Eval hnf in EqType memory_type memory_type_eqMixin.

Scheme Equality for res_crash.
Definition res_crash_eqb c1 c2 := is_left (res_crash_eq_dec c1 c2).
Definition eqres_crashP : Equality.axiom res_crash_eqb :=
  eq_dec_Equality_axiom res_crash_eq_dec.

Canonical Structure res_crash_eqMixin := EqMixin eqres_crashP.
Canonical Structure res_crash_eqType := Eval hnf in EqType res_crash res_crash_eqMixin.

Definition res_step_eq_dec : forall r1 r2 : res_step, {r1 = r2} + {r1 <> r2}.
Proof.
  (decidable_equality_step;
    last by apply: (eq_comparable (_ : seq administrative_instruction)));
    decidable_equality.
Defined.

Definition res_step_eqb (r1 r2 : res_step) : bool := res_step_eq_dec r1 r2.
Definition eqres_stepP : Equality.axiom res_step_eqb :=
  eq_dec_Equality_axiom res_step_eq_dec.

Canonical Structure res_step_eqMixin := EqMixin eqres_stepP.
Canonical Structure res_step_eqType := Eval hnf in EqType res_step res_step_eqMixin.

End Host.

