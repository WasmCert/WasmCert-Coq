(** Properties about Wasm datatypes (mainly equality relations) **)
(* (C) M. Bodin, J. Pichon - see LICENSE.txt *)

Require Import bytes common.
Require Export datatypes.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition byte_eqb v1 v2 : bool := Byte.byte_eq_dec v1 v2.
Definition eqbyteP : Equality.axiom byte_eqb :=
  eq_dec_Equality_axiom Byte.byte_eq_dec.

Canonical Structure byte_eqMixin := EqMixin eqbyteP.
Canonical Structure byte_eqType :=
  Eval hnf in EqType Byte.byte byte_eqMixin.

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

(** Some helper functions for [value] that can safely extract. **)
Definition value_rec_safe (P : Type)
           (i32 : Wasm_int.Int32.int -> P)
           (i64 : Wasm_int.Int64.int -> P)
           (f32 : Wasm_float.FloatSize32.T -> P)
           (f64 : Wasm_float.FloatSize64.T -> P) v : P :=
  value_rect i32 i64 f32 f64 v.

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


Definition module_export_desc_eq_dec : forall v1 v2 : module_export_desc, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition module_export_desc_eqb v1 v2 : bool := module_export_desc_eq_dec v1 v2.
Definition eqmodule_export_descP : Equality.axiom module_export_desc_eqb :=
  eq_dec_Equality_axiom module_export_desc_eq_dec.

Canonical Structure module_export_desc_eqMixin := EqMixin eqmodule_export_descP.
Canonical Structure module_export_desc_eqType := Eval hnf in EqType module_export_desc module_export_desc_eqMixin.

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

(* FIXME *)
Inductive test :=
  | C : list test -> test.

Fixpoint f' (v : test) :=
  let f :=
    fix f l :=
      match l with
      | nil => 0
      | v :: _ => f' v
      end in
  match v with
  | C l => f l
  end.

Fixpoint f (l : list test) :=
  let f' :=
    fix f' (t : test) :=
      match t with
      | C l => f l
      end in
  match l with
  | nil => 0
  | v :: _ => f' v
  end.


Ltac rect'_build_projection' proj rect :=
  let t :=
    lazymatch type of rect with
    | forall P : ?t -> Type, _ => t
    end in
  let g := rect'_type_projection proj rect in
  refine (_ : g);
  let P := fresh "P" in
  intro P;
  repeat lazymatch goal with
  | |- forall a : proj t, P a => idtac
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
  let do_it := solve [ clear rect rect_list; auto ] in
  let use_hyps :=
    intros;
    repeat match goal with
    | v : proj t |- _ =>
      lazymatch goal with
      | H : P v |- _ => fail
      | _ => move: (rect v) => ?
      end
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
    | o : option t |- _ =>
      lazymatch proj with
      | option => fail
      | _ => destruct o
      end
    end in
  let go_on := first [ do_it | use_hyps; try do_it ] in
  let special_cases :=
    intros;
    lazymatch goal with
    | Split : forall l1 l2, P l1 -> P l2 -> P (l1 ++ l2) |- ?P (?a :: ?l) =>
      refine (Split [:: a] l _ (rect l));
      case a; go_on
    end in
  let a := fresh "v" in
  intro a; destruct a; first [ special_cases | go_on ].

Ltac rect'_build_list' rect := rect'_build_projection' list rect.

Definition seq_administrative_instruction_rect' : ltac:(set_rect'_type_list administrative_instruction_rect).

  refine (
((fun (P : seq administrative_instruction -> Type) 
    (X : P [::])
    (X0 : forall l1 l2 : seq administrative_instruction,
          P l1 -> P l2 -> P (l1 ++ l2))
    (X1 : forall b : basic_instruction, P [:: Basic b]) 
    (X2 : P [:: Trap]) (X3 : forall f : function_closure, P [:: Invoke f])
    (X4 : forall (n : nat) (l : seq administrative_instruction),
          P l ->
          forall l0 : seq administrative_instruction,
          P l0 -> P [:: Label n l l0])
    (X5 : forall (n : nat) (i : instance) (l : seq value)
            (l0 : seq administrative_instruction),
          P l0 -> P [:: Local n i l l0]) =>
  fix rect (l : seq administrative_instruction) : 
  P l :=
     match l as l0 return (P l0) with
     | [::] => X
     | a :: v0 =>
         X0 [:: a] v0
           match a as a0 return (P [:: a0]) with
           | Basic x => X1 x
           | Trap => X2
           | Invoke x => X3 x
           | Label n l0 l1 =>
               let r_rect_ := (rect l1) in
               let r_rect1_ := (rect l0) in
               _(*(*let _ := (rect v0) in*)
               X4 n l0 r_rect1_ l1 r_rect_*)
           | Local n i l0 l1 =>
               (*let r_rect_ := rect l1 in
               (*let _ := (rect v0) in*)
               X5 n i l0 l1 r_rect_*) _
           end (rect v0)
     end)
   : (forall P : seq administrative_instruction -> Type,
      P [::] ->
      (forall l1 l2 : seq administrative_instruction,
       P l1 -> P l2 -> P (l1 ++ l2)) ->
      (forall b : basic_instruction, P [:: Basic b]) ->
      P [:: Trap] ->
      (forall f : function_closure, P [:: Invoke f]) ->
      (forall (n : nat) (l : seq administrative_instruction),
       P l ->
       forall l0 : seq administrative_instruction,
       P l0 -> P [:: Label n l l0]) ->
      (forall (n : nat) (i : instance) (l : seq value)
         (l0 : seq administrative_instruction), P l0 -> P [:: Local n i l l0]) ->
      forall l : seq administrative_instruction, P l))).

clearbody r_rect_ r_rect1_. clear rect. auto.

Guarded.

  ltac:(rect'_build_list' administrative_instruction_rect).
Show Proof.
Defined.


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

Definition lholed_eq_dec : forall v1 v2 : lholed, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition lholed_eqb v1 v2 : bool := lholed_eq_dec v1 v2.
Definition eqlholedP : Equality.axiom lholed_eqb :=
  eq_dec_Equality_axiom lholed_eq_dec.

Canonical Structure lholed_eqMixin := EqMixin eqlholedP.
Canonical Structure lholed_eqType := Eval hnf in EqType lholed lholed_eqMixin.

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

