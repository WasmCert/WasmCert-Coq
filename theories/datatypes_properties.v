(** Properties about Wasm datatypes (mainly equality relations) **)
(* (C) M. Bodin - see LICENSE.txt *)

Require Import common.
Require Export datatypes.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


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

(* TODO: [basic_instruction_rect'] *)

(* TODO:
Scheme Equality for basic_instruction.
Definition eqglobal_typeP := eq_dec_Equality_axiom global_type_eq_dec.
*)
Parameter basic_instruction_eqb : basic_instruction -> basic_instruction -> bool.

Parameter eqbasic_instructionP : Equality.axiom basic_instruction_eqb.

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

Definition function_closure_eq_dec : forall (cl1 cl2 : function_closure),
  {cl1 = cl2} + {cl1 <> cl2}.
Proof. decidable_equality. Defined.

Definition function_closure_eqb cl1 cl2 : bool := function_closure_eq_dec cl1 cl2.
Definition eqfunction_closureP : Equality.axiom function_closure_eqb :=
  eq_dec_Equality_axiom function_closure_eq_dec.

Canonical Structure function_closure_eqMixin := EqMixin eqfunction_closureP.
Canonical Structure function_closure_eqType :=
  Eval hnf in EqType function_closure function_closure_eqMixin.

Definition global_eq_dec : forall v1 v2 : global, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition global_eqb v1 v2 : bool := global_eq_dec v1 v2.
Definition eqglobalP : Equality.axiom global_eqb :=
  eq_dec_Equality_axiom global_eq_dec.

Canonical Structure global_eqMixin := EqMixin eqglobalP.
Canonical Structure global_eqType := Eval hnf in EqType global global_eqMixin.

Definition store_record_eq_dec : forall v1 v2 : store_record, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition store_record_eqb v1 v2 : bool := store_record_eq_dec v1 v2.
Definition eqstore_recordP : Equality.axiom store_record_eqb :=
  eq_dec_Equality_axiom store_record_eq_dec.

Canonical Structure store_record_eqMixin := EqMixin eqstore_recordP.
Canonical Structure store_record_eqType := Eval hnf in EqType store_record store_record_eqMixin.

(** Induction scheme for [administrative_instruction]. **)
Section administrative_instruction_rect'.

Definition curry A B C (f : A -> B -> C) (ab : A * B) :=
  let: (a, b) := ab in
  f a b.

Definition uncurry A B C (f : A * B -> C) a b := f (a, b).

Lemma curry_uncurry : forall A B C (f : A * B -> C) ab,
  curry (uncurry f) ab = f ab.
Proof. by move=> A B C f [a b]. Qed.

Lemma uncurry_curry : forall A B C (f : A -> B -> C) a b,
  uncurry (curry f) a b = f a b.
Proof. by []. Qed.

(** Given an induction principle, return the number of cases of the type. **)
Ltac count_cases rect :=
  let rec count_args rectf :=
    lazymatch rectf with
    | forall a, False => constr:(0)
    | _ -> ?rectf' =>
      let r := count_args rectf' in
      constr:(r.+1)
    end in
  lazymatch type of rect with
  | forall P : ?t -> Type, @?rectf P =>
    let r := constr:(rectf (fun _ : t => False)) in
    let r := eval simpl in r in
    count_args r
  end.

Ltac rect'_type rect :=
  let added_hyp t ta :=
    lazymatch ta with
    | list t => constr:(@TProp.Forall t)
    | option t => constr:(fun P (o : ta) => forall a : t, o = Some a -> P a)
    | _ => constr:(fun (_ : t -> Type) (_ : ta) => True)
    end in
  let add_hyp t ta P a r :=
    let h := added_hyp t ta in
    let h := constr:(h P a) in
    let h := eval simpl in h in
    lazymatch h with
    | True => r
    | _ => constr:(h -> r)
    end in
  let set_hyp t ta P a r :=
    let r := add_hyp t ta P a r in
    exact r in
  let update_hyp t hyp :=
    lazymatch hyp with
    | fun P => P _ => constr:(hyp)
    | fun P => forall a1 : ?t1, P (?C a1) =>
      constr:(fun P : t -> Type => forall a1 : t1,
        ltac:(set_hyp t t1 P a1 (P (C a1))))
    | fun P => forall (a1 : ?t1) (a2 : ?t2), P (?C a1 a2) =>
      constr:(fun P : t -> Type => forall (a1 : t1) (a2 : t2),
        ltac:(set_hyp t t1 P a1
          ltac:(add_hyp t t2 P a2 (P (C a1 a2)))))
    | fun P => forall (a1 : ?t1) (a2 : ?t2) (a3 : ?t3), P (?C a1 a2 a3) =>
      constr:(fun P : t -> Type => forall (a1 : t1) (a2 : t2) (a3 : t3),
        ltac:(set_hyp t t1 P a1
          ltac:(add_hyp t t2 P a2
            ltac:(add_hyp t t3 P a3 (P (C a1 a2 a3))))))
    | fun P => forall (a1 : ?t1) (a2 : ?t2) (a3 : ?t3) (a4 : ?t4), P (?C a1 a2 a3 a4) =>
      constr:(fun P : t -> Type => forall (a1 : t1) (a2 : t2) (a3 : t3) (a4 : t4),
        ltac:(set_hyp t t1 P a1
          ltac:(add_hyp t t2 P a2
            ltac:(add_hyp t t3 P a3
              ltac:(add_hyp t t4 P a4 (P (C a1 a2 a3 a4)))))))
    | fun P => forall (a1 : ?t1) (a2 : ?t2) (a3 : ?t3) (a4 : ?t4) (a5 : ?t5), P (?C a1 a2 a3 a4 a5) =>
      constr:(fun P : t -> Type => forall (a1 : t1) (a2 : t2) (a3 : t3) (a4 : t4) (a5 : t5),
        ltac:(set_hyp t t1 P a1
          ltac:(add_hyp t t2 P a2
            ltac:(add_hyp t t3 P a3
              ltac:(add_hyp t t4 P a4
                ltac:(add_hyp t t4 P a4 (P (C a1 a2 a3 a4 a5))))))))
    | fun P => forall (a1 : ?t1) (a2 : ?t2) (a3 : ?t3) (a4 : ?t4) (a5 : ?t5) (a6 : ?t6), P (?C a1 a2 a3 a4 a5 a6) =>
      constr:(fun P : t -> Type => forall (a1 : t1) (a2 : t2) (a3 : t3) (a4 : t4) (a5 : t5) (a6 : t6),
        ltac:(set_hyp t t1 P a1
          ltac:(add_hyp t t2 P a2
            ltac:(add_hyp t t3 P a3
              ltac:(add_hyp t t4 P a4
                ltac:(add_hyp t t5 P a5
                  ltac:(add_hyp t t6 P a6 (P (C a1 a2 a3 a4 a5 a6)))))))))
    end in
  let rec map_hyps t rectf :=
    lazymatch rectf with
    | fun P => forall a : t, P a => constr:(rectf)
    | fun P => @?hyp P -> @?rectf' P =>
      let r := update_hyp t hyp in
      let r' := map_hyps t rectf' in
      constr:(fun P => r P -> r' P)
    end in
  lazymatch type of rect with
  | forall P : ?t -> Type, @?rectf P =>
    let r := map_hyps t rectf in
    let r := constr:(forall P, r P) in
    eval simpl in r
  end.

Ltac rect'_build rect :=
  let t :=
    lazymatch type of rect with
    | forall P : ?t -> Type, _ => t
    end in
  let g := rect'_type rect in
  refine (_ : g);
  let P := fresh "P" in
  intro P;
  repeat lazymatch goal with
  | |- forall a : t, P a => idtac
  | |- _ -> _ => intro
  end;
  let rect := fresh "rect" in
  fix rect 1;
  let rect_list := fresh "rect_list" in
  refine (
    let rect_list :=
      fix rect_list es : TProp.Forall P es :=
        match es with
        | [::] => TProp.Forall_nil _
        | e :: l => TProp.Forall_cons (rect e) (rect_list l)
        end in _);
  let do_it := clear rect rect_list; auto in
  let use_hyps :=
    intros;
    repeat match goal with
    | a : t |- _ =>
      lazymatch goal with
      | H : P a |- _ => fail
      | _ => move: (rect a) => ?
      end
    | l : list t |- _ =>
      lazymatch goal with
      | H : TProp.Forall P l |- _ => fail
      | _ => move: (rect_list l) => ?
      end
    | o : option t |- _ => destruct o
    end in
  case; try solve [ do_it | use_hyps; do_it ].
  
Definition administrative_instruction_rect' :=
  ltac:(rect'_build administrative_instruction_rect).

Definition administrative_instruction_ind' (P : administrative_instruction -> Prop) :=
  @administrative_instruction_rect' P.

Definition administrative_instruction_eq_dec : forall e1 e2 : administrative_instruction,
  {e1 = e2} + {e1 <> e2}.
Proof. decidable_equality_using administrative_instruction_rect'. Defined.

Definition administrative_instruction_eqb cl1 cl2 : bool := administrative_instruction_eq_dec cl1 cl2.
Definition eqadministrative_instructionP : Equality.axiom administrative_instruction_eqb :=
  eq_dec_Equality_axiom administrative_instruction_eq_dec.

Canonical Structure administrative_instruction_eqMixin := EqMixin eqadministrative_instructionP.
Canonical Structure administrative_instruction_eqType :=
  Eval hnf in EqType administrative_instruction administrative_instruction_eqMixin.

Definition lholed_eq_dec : forall v1 v2 : lholed, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition lholed_eqb v1 v2 : bool := lholed_eq_dec v1 v2.
Definition eqlholedP : Equality.axiom lholed_eqb :=
  eq_dec_Equality_axiom lholed_eq_dec.

Canonical Structure lholed_eqMixin := EqMixin eqlholedP.
Canonical Structure lholed_eqType := Eval hnf in EqType lholed lholed_eqMixin.
