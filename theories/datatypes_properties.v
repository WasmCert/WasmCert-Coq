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

Ltac count_cases rect :=
  let rec count_args rectf :=
    lazymatch rectf with
    | _ -> ?rectf' =>
      let r := count_args rectf' in
      constr:(r.+1)
    | _ => constr:(0)
    end in
  lazymatch type of rect with
  | forall P : ?t -> Type, @?rectf P =>
    let r := constr:(rectf (fun _ : t => False)) in
    let r := eval simpl in r in
    count_args r
  end.

Definition test :=
  ltac:(let n := count_cases administrative_instruction_rect in exact n).

Goal False.
  evar (a : Type).
  assert a.
  unfold a. clear a.

  intros P basic trap callcl label local.
  assert (G: forall a : administrative_instruction, P a); [| exact G ].
  intro a. elim a => {a}.
  - exact basic.
  - exact trap.
  - exact callcl.
  - intros n l1 l2.
    assert (G: TProp.Forall P l1 -> TProp.Forall P l2 -> P (Label n l1 l2)); [ apply label |].

Ltac rect'_type rect :=
  let n := count_cases rect in
  let 


  Fixpoint administrative_instruction_rect' e : P e :=
    let rect_list :=
      fix rect_list es : TProp.Forall P es :=
        match es with
        | [::] => TProp.Forall_nil _
        | e :: l => TProp.Forall_cons (administrative_instruction_rect' e) (rect_list l)
        end in
    match e with
    | Basic b => basic b
    | Trap => trap
    | Callcl f => callcl f
    | Label n es1 es2 => label n (rect_list es1) (rect_list es2)
    | Local n i vs es => local n i vs (rect_list es)
    end.


Ltac rect'_type rect :=
  let rec parse_arg t P hypf :=
    lazymatch hypf with
    | forall a : ?ta, _ (* @?hypf' a*) =>
      constr:(forall a : ta, False) (*ltac:(exact ltac:(parse_arg t P (hypf' a))))*)
    | _ => constr:(hypf)
    end in
  let rec parse_args t P rectf :=
    lazymatch rectf with
    | ?hypf -> ?rectf' =>
      let r' := parse_args t P rectf' in
      let r := parse_arg t P hypf in
      constr:(r -> r')
    | _ => constr:(rectf)
    end in
  lazymatch type of rect with
  | forall P : ?t -> Type, @?rectf P =>
    let r :=
      constr:(forall P : t -> Type,
        ltac:(let r := parse_args t P (rectf P) in exact r)) in
    eval simpl in r
  end.

Definition test :=
  ltac:(let n := rect'_type administrative_instruction_rect in exact n).

Ltac rect'_type rect :=
  let rec parse_argf t hypf :=
    lazymatch hypf with
    | fun P args => ?H -> forall a, @?hypf' P args a =>
      let f := constr:(fun P args => forall a, H -> hypf' P args a) in
      parse_argf t f
    | fun P (args : ?targs) => forall a : ?ta, @?hypf' P args a =>
      let hypf' :=
        lazymatch ta with
        | list t =>
          constr:(fun P args a => TProp.Forall P a -> hypf' P args a)
        | _ => hypf'
        end in
      let hypf'' :=
        constr:(fun P (args : (targs * _)%type) => hypf' P args.1 args.2) in
      let hypf'' := eval simpl in hypf'' in
      parse_argf t hypf''
    | _ => constr:(hypf)
    end in
  let parse_arg t hypf :=
    lazymatch hypf with
    | fun P => forall a, @?hypf' P a =>
      let r := parse_argf t hypf' in
      constr:(fun P => forall a, r P a)
    | _ => constr:(hypf)
    end in
  let rec parse_args t rectf :=
    lazymatch rectf with
    | fun P => @?hypf P -> @?rectf' P =>
      let r' := parse_args t rectf' in
      let r := parse_arg t hypf in
      constr:(fun P => r P -> r' P)
    | _ => constr:(rectf)
    end in
  lazymatch type of rect with
  | forall P : ?t -> Type, @?rectf P =>
    let r := parse_args t rectf in
    let r := constr:(forall P : t -> Type, r P) in
    eval simpl in r
  end.

Definition test :=
  ltac:(let n := rect'_type administrative_instruction_rect in exact n).

let rec curry f :=
    lazymatch f with
    | fun (args : _ * _)%type => let (arg1, args2) := args in @?f' arg1 args2 =>

  Variable P : administrative_instruction -> Type.

  Hypothesis basic : forall b, P (Basic b).
  Hypothesis trap : P Trap.
  Hypothesis callcl : forall f, P (Callcl f).
  Hypothesis label : forall n es1 es2,
    TProp.Forall P es1 ->
    TProp.Forall P es2 ->
    P (Label n es1 es2).
  Hypothesis local : forall n i vs es,
    TProp.Forall P es ->
    P (Local n i vs es).

  Fixpoint administrative_instruction_rect' e : P e :=
    let rect_list :=
      fix rect_list es : TProp.Forall P es :=
        match es with
        | [::] => TProp.Forall_nil _
        | e :: l => TProp.Forall_cons (administrative_instruction_rect' e) (rect_list l)
        end in
    match e with
    | Basic b => basic b
    | Trap => trap
    | Callcl f => callcl f
    | Label n es1 es2 => label n (rect_list es1) (rect_list es2)
    | Local n i vs es => local n i vs (rect_list es)
    end.

End administrative_instruction_rect'.

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

