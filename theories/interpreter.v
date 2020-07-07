(* Wasm interpreter *)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From Wasm Require Import common.
From Coq Require Import ZArith.BinInt.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From ExtLib Require Import Structures.Monad.
From ITree Require Import ITree ITreeFacts.
From Wasm Require Export operations host type_checker.

Import Monads.
Import MonadNotation.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Universes.

Polymorphic Definition interp'' {E M : Type -> Type} (MM : Monad M) (*IM : MonadIter M*)
                                (iter : forall R I : Type, (I -> M (I + R)%type) -> I -> M R)
                                (h : forall X T R, E X -> (X -> T) -> M (_ + R)%type) R
  : itree E R -> (fun T => M T%type) R :=
  (*Basics.*)iter _ _
    (fun t : itree E R =>
      match observe t with
      | RetF r => ret (inr r)
      | TauF t0 => ret (inl t0)
      | VisF X e k => (*ret (inl tt)*) h X _ _ e k
        (*x <- h X e ;;
        ret (inl (k x))*)
      end).

Polymorphic Fixpoint interp_fuel {E M : Type -> Type} (MM : Monad M) (fail : forall R, M R)
                                 (h : E ~> M) (fuel : nat)
  : itree E ~> M := fun R t =>
  match fuel with
  | 0 => fail _
  | fuel.+1 =>
    match observe t with
    | RetF r => ret r
    | TauF t0 => interp_fuel MM fail h fuel t0
    | VisF X e k =>
      x <- h X e ;;
      interp_fuel MM fail h fuel (k x)
    end
  end.

Fixpoint interp_monad (E : Type -> Type) (ME : Monad E) (fail : forall R, E R) (fuel : nat) : itree E ~> E := fun R t =>
  match fuel with
  | 0 => fail _
  | fuel.+1 =>
    match observe t with
    | RetF r => ret r
    | TauF t0 => interp_monad ME fail fuel t0
    | VisF X e k =>
      x <- e ;;
      interp_monad ME fail fuel (k x)
    end
  end.

(*
Fixpoint interp_monad_option (E : Type -> Type) (ME : Monad E) (fuel : nat) : itree E ~> (fun T => option (E T)) := fun R t =>
  match fuel with
  | 0 => None
  | fuel.+1 =>
    match observe t with
    | RetF r => Some (ret r)
    | TauF t0 => interp_monad_option ME fuel t0
    | VisF X e k =>
      x <- e ;;
      interp_monad_option ME fuel (k x)
    end
  end.
 *)

Unset Printing Implicit Defensive.

Section Host.

Local Notation "x <- m1 ; m2" :=
  (bind m1 (fun x => m2))
  (at level 80, right associativity).

Variable host_function : eqType.

Let store_record := store_record host_function.
Let administrative_instruction := administrative_instruction host_function.
Let executable_host := executable_host host_function.

Variable executable_host_instance : executable_host.

Let host_event := host_event executable_host_instance.
Let host_monad : Monad host_event := host_monad _.
Let host_apply : store_record -> host_function -> seq value -> host_event (option (store_record * result)) :=
  @host_apply _ executable_host_instance.

Section ITreeExtract.
(** Some helper functions to extract an interactive tree to a simple-to-interact-with function,
  in order to reduce the shim. **)

Definition option_of_itree_void {A} (t : itree void1 A) : option A :=
  match observe t with
  | RetF r => Some r (** We got a return. **)
  | TauF i => None (** Exhaustion. **)
  | VisF _ a _ => match a with end (** Void, by definition. **)
  end.

(*Hypothesis MIe : MonadIter host_event.*)
(*Hypothesis FMe : Functor.Functor host_event.*)

Local Instance MO : Monad (OptionMonad.optionT host_event).
Proof.
  apply OptionMonad.Monad_optionT. apply host_monad.
Defined.

Unset Printing Universes.

Definition from_event_monad : nat -> itree host_event ~> (fun T => option (host_event T)).
  Fail apply interp_monad.
Abort.

Fail Definition from_event_monad : nat -> itree host_event ~> OptionMonad.optionT host_event :=
  interp_monad MO (fun T => @ret _ host_monad (option T) None : OptionMonad.optionT host_event T) _ (*fun X T R e f => x <- e ;; ret (inl (f x))*).
  (* FIXME: Universe inconsistency!
     - It seems that the issue has nothing to due with previous definitions:
       moving this definition doesn’t change the error or even re-copy/pasting the definition
       of interp here doesn’t change anything.
     - It seems that the issue is in the second argument of [interp] ([M] and not [E], despite
       both are here set to [host_event].
     - The universe of the argument of [M] must be less than its result.  This makes sense.
     - But who Coq doesn’t want the type of [host_event] to be like this?
   *)

(* FIXME: Testing with another event monad. *)
Variable executable_host_instance' : executable_host.
Let host_event' := host.host_event executable_host_instance'.
Let host_monad' := host.host_monad executable_host_instance'.
Fail Definition from_event_monad : itree host_event ~> host_event' :=
  interp (M := host_event') (MM := host_monad') _. (* Still failing *)

Section TestMonad.
(* FIXME: Testing with a completely different monad. *)
Variable m : Type -> Type.
Hypothesis M : Monad m.
Hypothesis MI : MonadIter m.
Variable f : host_event ~> m.
Fail Definition from_event_monad : itree host_event ~> m :=
  interp (M := m) (MM := M) f. (* Passes! *)
End TestMonad.

(* FIXME: Is it because they share the argument [host_function]? *)
Variable host_function'' : eqType.
Let executable_host'' := host.executable_host host_function''.
Variable executable_host_instance'' : executable_host''.
Let host_event'' := host.host_event executable_host_instance''.
Let host_monad'' := host.host_monad executable_host_instance''.
Fail Definition from_event_monad : itree host_event ~> host_event'' :=
  interp (M := host_event'') (MM := host_monad'') _. (* No, still failing. *)
(* It seems to really be [host.executable_host] that creates the conflict. *)

(* Let us test to do the know with a super generic monad. *)
Section Monad.

Variable m : Type -> Type.
Hypothesis M : Monad m.
Hypothesis MI : MonadIter m.

Set Universe Polymorphism.

Fail Definition from_event_monad : itree m ~> m :=
  interp (M := m) (MM := M) (fun _ => id). (* OK, I misunderstood, then: the issue is thus really the loop right here. *)

Unset Printing Universes.

(* What if we try to define a simpler version of [interp]? *)
Fail Definition interp' {E M : Type -> Type} (MM : Monad M) (h : E ~> (fun T => M (option T))) : itree E ~> (fun T => M (option T)) :=
  fun R t =>
    match observe t with
    | RetF r => ret (Some r)
    | TauF t => ret None (** exhaustion **)
    | VisF X e k => Functor.fmap (F := fun T => M (option T)) k (h X e) (* FIXME: To be worked on *)
    end.

Unset Universe Polymorphism.

End Monad.

End ITreeExtract.


(** * Types used by the interpreter **)

Inductive res_crash : Type :=
  | C_error : res_crash
  .

Scheme Equality for res_crash.
Definition res_crash_eqb c1 c2 := is_left (res_crash_eq_dec c1 c2).
Definition eqres_crashP : Equality.axiom res_crash_eqb :=
  eq_dec_Equality_axiom res_crash_eq_dec.

Canonical Structure res_crash_eqMixin := EqMixin eqres_crashP.
Canonical Structure res_crash_eqType := Eval hnf in EqType res_crash res_crash_eqMixin.

Inductive res : Type :=
  | R_crash : res_crash -> res
  | R_trap : res
  | R_value : seq value -> res
  .

Definition res_eq_dec : forall r1 r2 : res, {r1 = r2} + {r1 <> r2}.
Proof. decidable_equality. Defined.

Definition res_eqb (r1 r2 : res) : bool := res_eq_dec r1 r2.
Definition eqresP : Equality.axiom res_eqb :=
  eq_dec_Equality_axiom res_eq_dec.

Canonical Structure res_eqMixin := EqMixin eqresP.
Canonical Structure res_eqType := Eval hnf in EqType res res_eqMixin.

Inductive res_step : Type :=
  | RS_crash : res_crash -> res_step
  | RS_break : nat -> seq value -> res_step
  | RS_return : seq value -> res_step
  | RS_normal : seq administrative_instruction -> res_step
  .

Definition res_step_eq_dec : forall r1 r2 : res_step, {r1 = r2} + {r1 <> r2}.
Proof. decidable_equality. Defined.

Definition res_step_eqb (r1 r2 : res_step) : bool := res_step_eq_dec r1 r2.
Definition eqres_stepP : Equality.axiom res_step_eqb :=
  eq_dec_Equality_axiom res_step_eq_dec.

Canonical Structure res_step_eqMixin := EqMixin eqres_stepP.
Canonical Structure res_step_eqType := Eval hnf in EqType res_step res_step_eqMixin.

Definition crash_error := RS_crash C_error.

Definition depth := nat.

Definition config_tuple : Type := store_record * seq value * seq administrative_instruction.

Definition config_one_tuple_without_e : Type := store_record * seq value * seq value.

Definition res_tuple : Type := store_record * seq value * res_step.


(** * The interpreter itself. **)

Fixpoint split_vals (es : seq basic_instruction) : seq value * seq basic_instruction :=
  match es with
  | (EConst v) :: es' =>
    let: (vs', es'') := split_vals es' in
    (v :: vs', es'')
  | _ => ([::], es)
  end.

(** [split_vals_e es]: takes the maximum initial segment of [es] whose elements
    are all of the form [Basic (EConst v)];
    returns a pair of lists [(ves, es')] where [ves] are those [v]'s in that initial
    segment and [es] is the remainder of the original [es]. **)
Fixpoint split_vals_e (es : seq administrative_instruction) : seq value * seq administrative_instruction :=
  match es with
  | (Basic (EConst v)) :: es' =>
    let: (vs', es'') := split_vals_e es' in
    (v :: vs', es'')
  | _ => ([::], es)
  end.

Fixpoint split_n (es : seq value) (n : nat) : seq value * seq value :=
  match (es, n) with
  | ([::], _) => ([::], [::])
  | (_, 0) => ([::], es)
  | (e :: esX, n.+1) =>
    let: (es', es'') := split_n esX n in
    (e :: es', es'')
  end.

Definition expect {A B : Type} (ao : option A) (f : A -> B) (b : B) : B :=
  match ao with
  | Some a => f a
  | None => b
  end.

Definition vs_to_es (vs : seq value) : seq administrative_instruction :=
  v_to_e_list (rev vs).

Definition e_is_trap (e : administrative_instruction) : bool :=
  match e with
  | Trap => true
  | _ => false
  end.

Lemma e_is_trapP : forall e, reflect (e = Trap) (e_is_trap e).
Proof.
  case => //= >; by [ apply: ReflectF | apply: ReflectT ].
Qed.

(** [es_is_trap es] is equivalent to [es == [:: Trap]]. **)
Definition es_is_trap (es : seq administrative_instruction) : bool :=
  match es with
  | [::e] => e_is_trap e
  | _ => false
  end.

Lemma es_is_trapP : forall l, reflect (l = [::Trap]) (es_is_trap l).
Proof.
  case; first by apply: ReflectF.
  move=> // a l. case l => //=.
  - apply: (iffP (e_is_trapP _)); first by elim.
    by inversion 1.
  - move=> >. by apply: ReflectF.
Qed.

(** An inductive for the [mrec] fixed-point combinator, expressing the signature of the
   functions [run_step_base] and [run_one_step]. **)
Inductive run_stepE : Type -> Type :=
  | call_run_step_base :
    depth -> instance -> config_tuple ->
    run_stepE res_tuple
  | call_run_one_step :
    depth -> instance -> config_one_tuple_without_e -> administrative_instruction ->
    run_stepE res_tuple
  .

Section RunStep.

(** See ITree/tutorial/Imp.v: these commands are used to enable other events to be mangled in. **)
Context {eff : Type -> Type}.
Context {eff_has_host_event : host_event -< eff}.

Definition run_step_base (call : run_stepE ~> itree (run_stepE +' eff))
    (d : depth) (i : instance) (cgf : config_tuple)
  : itree (run_stepE +' eff) res_tuple :=
  let: (s, vs, es) := cgf in
  let: (ves, es') := split_vals_e es in (** Framing out constants. **)
  match es' with
  | [::] => ret (s, vs, crash_error)
  | e :: es'' =>
    if e_is_trap e
    then
      if (es'' != [::]) || (ves != [::])
      then ret (s, vs, RS_normal [::Trap])
      else ret (s, vs, crash_error)
    else
      '(s', vs', r) <- call _ (call_run_one_step d i (s, vs, (rev ves)) e) ;;
      if r is RS_normal res
      then ret (s', vs', RS_normal (res ++ es''))
      else ret (s', vs', r)
  end.

Definition run_one_step (call : run_stepE ~> itree (run_stepE +' eff))
      (d : depth) (i : instance) (cgf : config_one_tuple_without_e) (e : administrative_instruction)
    : itree (run_stepE +' eff) res_tuple :=
  let: (s, vs, ves) := cgf in
  match e with

  (** unop **)
  | Basic (Unop_i T_i32 iop) =>
    if ves is ConstInt32 c :: ves' then
      ret (s, vs, RS_normal (vs_to_es ((ConstInt32 (@app_unop_i i32t iop c)) :: ves')))
    else ret (s, vs, crash_error)
  | Basic (Unop_i T_i64 iop) =>
    if ves is (ConstInt64 c) :: ves' then
      ret (s, vs, RS_normal (vs_to_es ((ConstInt64 (@app_unop_i i64t iop c)) :: ves')))
    else ret (s, vs, crash_error)
  | Basic (Unop_i _ _) => ret (s, vs, crash_error)
  | Basic (Unop_f T_f32 iop) =>
    if ves is (ConstFloat32 c) :: ves' then
      ret (s, vs, RS_normal (vs_to_es ((ConstFloat32 (@app_unop_f f32t iop c)) :: ves')))
    else ret (s, vs, crash_error)
  | Basic (Unop_f T_f64 iop) =>
    if ves is (ConstFloat64 c) :: ves' then
      ret (s, vs, RS_normal (vs_to_es ((ConstFloat64 (@app_unop_f f64t iop c)) :: ves')))
    else ret (s, vs, crash_error)
  | Basic (Unop_f _ _) => ret (s, vs, crash_error)

  (** binop **)
  | Basic (Binop_i T_i32 iop) =>
    if ves is (ConstInt32 c2) :: (ConstInt32 c1) :: ves' then
      expect (@app_binop_i i32t iop c1 c2) (fun c =>
          ret (s, vs, RS_normal (vs_to_es ((ConstInt32 c) :: ves'))))
        (ret (s, vs, RS_normal ((vs_to_es ves') ++ [::Trap])))
    else ret (s, vs, crash_error)
  | Basic (Binop_i T_i64 iop) =>
    if ves is (ConstInt64 c2) :: (ConstInt64 c1) :: ves' then
      expect (@app_binop_i i64t iop c1 c2) (fun c =>
          ret (s, vs, RS_normal (vs_to_es ((ConstInt64 c) :: ves'))))
        (ret (s, vs, RS_normal ((vs_to_es ves') ++ [::Trap])))
    else ret (s, vs, crash_error)
  | Basic (Binop_i _ _) => ret (s, vs, crash_error)
  | Basic (Binop_f T_f32 fop) =>
    if ves is (ConstFloat32 c2) :: (ConstFloat32 c1) :: ves' then
      expect (@app_binop_f f32t fop c1 c2) (fun c =>
          ret (s, vs, RS_normal (vs_to_es ((ConstFloat32 c) :: ves'))))
        (ret (s, vs, RS_normal ((vs_to_es ves') ++ [::Trap])))
    else ret (s, vs, crash_error)
  | Basic (Binop_f T_f64 fop) =>
    if ves is (ConstFloat64 c2) :: (ConstFloat64 c1) :: ves' then
      expect (@app_binop_f f64t fop c1 c2) (fun c =>
           ret (s, vs, RS_normal (vs_to_es ((ConstFloat64 c) :: ves'))))
        (ret (s, vs, RS_normal ((vs_to_es ves') ++ [::Trap])))
    else ret (s, vs, crash_error)
  | Basic (Binop_f _ _) => ret (s, vs, crash_error)

  (** testops **)
  | Basic (Testop T_i32 testop) =>
    if ves is (ConstInt32 c) :: ves' then
      ret (s, vs, RS_normal (vs_to_es ((ConstInt32 (wasm_bool (@app_testop_i i32t testop c))) :: ves')))
    else ret (s, vs, crash_error)
  | Basic (Testop T_i64 testop) =>
    if ves is (ConstInt64 c) :: ves' then
      ret (s, vs, RS_normal (vs_to_es ((ConstInt32 (wasm_bool (@app_testop_i i64t testop c))) :: ves')))
    else ret (s, vs, crash_error)
  | Basic (Testop _ _) => ret (s, vs, crash_error)

  (** relops **)
  | Basic (Relop_i T_i32 iop) =>
    if ves is (ConstInt32 c2) :: (ConstInt32 c1) :: ves' then
      ret (s, vs, RS_normal (vs_to_es (ConstInt32 (wasm_bool (@app_relop_i i32t iop c1 c2)) :: ves')))
    else ret (s, vs, crash_error)
  | Basic (Relop_i T_i64 iop) =>
    if ves is (ConstInt64 c2) :: (ConstInt64 c1) :: ves' then
      ret (s, vs, RS_normal (vs_to_es (ConstInt32 (wasm_bool (@app_relop_i i64t iop c1 c2)) :: ves')))
    else ret (s, vs, crash_error)
  | Basic (Relop_i _ _) => ret (s, vs, crash_error)
  | Basic (Relop_f T_f32 iop) =>
    if ves is (ConstFloat32 c2) :: (ConstFloat32 c1) :: ves' then
      ret (s, vs, RS_normal (vs_to_es (ConstInt32 (wasm_bool (@app_relop_f f32t iop c1 c2)) :: ves')))
    else ret (s, vs, crash_error)
  | Basic (Relop_f T_f64 iop) =>
    if ves is (ConstFloat64 c2) :: (ConstFloat64 c1) :: ves' then
      ret (s, vs, RS_normal (vs_to_es (ConstInt32 (wasm_bool (@app_relop_f f64t iop c1 c2)) :: ves')))
    else ret (s, vs, crash_error)
  | Basic (Relop_f _ _) => ret (s, vs, crash_error)

  (** convert and reinterpret **)
  | Basic (Cvtop t2 Convert t1 sx) =>
    if ves is v :: ves' then
      if types_agree t1 v
      then
        expect (cvt t2 sx v) (fun v' =>
             ret (s, vs, RS_normal (vs_to_es (v' :: ves'))))
          (ret (s, vs, RS_normal ((vs_to_es ves') ++ [::Trap])))
      else ret (s, vs, crash_error)
    else ret (s, vs, crash_error)
  | Basic (Cvtop t2 Reinterpret t1 sx) =>
    if ves is v :: ves' then
      if types_agree t1 v && (sx == None)
      then ret (s, vs, RS_normal (vs_to_es (wasm_deserialise (bits v) t2 :: ves')))
      else ret (s, vs, crash_error)
    else ret (s, vs, crash_error)

  (** control-flow instructions **)
  | Basic Unreachable => ret (s, vs, RS_normal ((vs_to_es ves) ++ [::Trap]))
  | Basic Nop => ret (s, vs, RS_normal (vs_to_es ves))
  | Basic Drop =>
    if ves is v :: ves' then
      ret (s, vs, RS_normal (vs_to_es ves'))
    else ret (s, vs, crash_error)
  | Basic Select =>
    if ves is (ConstInt32 c) :: v2 :: v1 :: ves' then
      if c == Wasm_int.int_zero i32m
      then ret (s, vs, RS_normal (vs_to_es (v2 :: ves')))
      else ret (s, vs, RS_normal (vs_to_es (v1 :: ves')))
    else ret (s, vs, crash_error)
  | Basic (Block (Tf t1s t2s) es) =>
    if length ves >= length t1s
    then
      let: (ves', ves'')  := split_n ves (length t1s) in
      ret (s, vs, RS_normal (vs_to_es ves''
                            ++ [::Label (length t2s) [::] (vs_to_es ves' ++ to_e_list es)]))
    else ret (s, vs, crash_error)
  | Basic (Loop (Tf t1s t2s) es) =>
    if length ves >= length t1s
    then
      let: (ves', ves'') := split_n ves (length t1s) in
      ret (s, vs, RS_normal (vs_to_es ves''
                            ++ [::Label (length t1s) [::Basic (Loop (Tf t1s t2s) es)]
                                    (vs_to_es ves' ++ to_e_list es)]))
    else ret (s, vs, crash_error)
  | Basic (If tf es1 es2) =>
    if ves is ConstInt32 c :: ves' then
      if c == Wasm_int.int_zero i32m
      then ret (s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Block tf es2)]))
      else ret (s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Block tf es1)]))
    else ret (s, vs, crash_error)
  | Basic (Br j) => ret (s, vs, RS_break j ves)
  | Basic (Br_if j) =>
    if ves is ConstInt32 c :: ves' then
      if c == Wasm_int.int_zero i32m
      then ret (s, vs, RS_normal (vs_to_es ves'))
      else ret (s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Br j)]))
    else ret (s, vs, crash_error)
  | Basic (Br_table js j) =>
    if ves is ConstInt32 c :: ves' then
      let: k := Wasm_int.nat_of_uint i32m c in
      if k < length js
      then
        expect (List.nth_error js k) (fun js_at_k =>
            ret (s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Br js_at_k)])))
          (ret (s, vs, crash_error))
      else ret (s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Br j)]))
    else ret (s, vs, crash_error)
  | Basic (Call j) =>
    if sfunc s i j is Some sfunc_i_j then
      ret (s, vs, RS_normal (vs_to_es ves ++ [::Invoke sfunc_i_j]))
    else ret (s, vs, crash_error)
  | Basic (Call_indirect j) =>
    if ves is ConstInt32 c :: ves' then
      match stab s i (Wasm_int.nat_of_uint i32m c) with
      | Some cl =>
        if stypes s i j == Some (cl_type cl)
        then ret (s, vs, RS_normal (vs_to_es ves' ++ [::Invoke cl]))
        else ret (s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
      | None => ret (s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
      end
    else ret (s, vs, crash_error)
  | Basic Return => ret (s, vs, RS_return ves)
  | Basic (Get_local j) =>
    if j < length vs
    then
      expect (List.nth_error vs j) (fun vs_at_j =>
          ret (s, vs, RS_normal (vs_to_es (vs_at_j :: ves))))
        (ret (s, vs, crash_error))
    else ret (s, vs, crash_error)
  | Basic (Set_local j) =>
    if ves is v :: ves' then
      if j < length vs
      then ret (s, update_list_at vs j v, RS_normal (vs_to_es ves'))
      else ret (s, vs, crash_error)
    else ret (s, vs, crash_error)
  | Basic (Tee_local j) =>
    if ves is v :: ves' then
      ret (s, vs, RS_normal (vs_to_es (v :: ves) ++ [::Basic (Set_local j)]))
    else ret (s, vs, crash_error)
  | Basic (Get_global j) =>
    if sglob_val s i j is Some xx
    then ret (s, vs, RS_normal (vs_to_es (xx :: ves)))
    else ret (s, vs, crash_error)
  | Basic (Set_global j) =>
    if ves is v :: ves' then
      if supdate_glob s i j v is Some xx
      then ret (xx, vs, RS_normal (vs_to_es ves'))
      else ret (s, vs, crash_error)
    else ret (s, vs, crash_error)
  | Basic (Load t None a off) =>
    if ves is ConstInt32 k :: ves' then
      expect
        (smem_ind s i)
        (fun j =>
           if List.nth_error s.(s_mems) j is Some mem_s_j then
             expect
               (load (mem_s_j) (Wasm_int.nat_of_uint i32m k) off (t_length t))
               (fun bs =>
                  ret (s, vs, RS_normal (vs_to_es (wasm_deserialise bs t :: ves'))))
               (ret (s, vs, RS_normal (vs_to_es ves' ++ [::Trap])))
           else ret (s, vs, crash_error))
        (ret (s, vs, crash_error))
    else ret (s, vs, crash_error)
  | Basic (Load t (Some (tp, sx)) a off) =>
    if ves is ConstInt32 k :: ves' then
      expect
        (smem_ind s i)
        (fun j =>
           if List.nth_error s.(s_mems) j is Some mem_s_j then
             expect
               (load_packed sx (mem_s_j) (Wasm_int.nat_of_uint i32m k) off (tp_length tp) (t_length t))
               (fun bs =>
                  ret (s, vs, RS_normal (vs_to_es (wasm_deserialise bs t :: ves'))))
               (ret (s, vs, RS_normal (vs_to_es ves' ++ [::Trap])))
           else ret (s, vs, crash_error))
        (ret (s, vs, crash_error))
    else ret (s, vs, crash_error)
  | Basic (Store t None a off) =>
    if ves is v :: ConstInt32 k :: ves' then
      if types_agree t v
      then
        expect
          (smem_ind s i)
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (store mem_s_j (Wasm_int.nat_of_uint i32m k) off (bits v) (t_length t))
                 (fun mem' =>
                    ret (upd_s_mem s (update_list_at s.(s_mems) j mem'), vs, RS_normal (vs_to_es ves')))
                 (ret (s, vs, RS_normal (vs_to_es ves' ++ [::Trap])))
             else ret (s, vs, crash_error))
          (ret (s, vs, crash_error))
      else ret (s, vs, crash_error)
    else ret (s, vs, crash_error)
  | Basic (Store t (Some tp) a off) =>
    if ves is v :: ConstInt32 k :: ves' then
      if types_agree t v
      then
        expect
          (smem_ind s i)
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (store_packed mem_s_j (Wasm_int.nat_of_uint i32m k) off (bits v) (tp_length tp))
                 (fun mem' =>
                    ret (upd_s_mem s (update_list_at s.(s_mems) j mem'), vs, RS_normal (vs_to_es ves')))
                 (ret (s, vs, RS_normal (vs_to_es ves' ++ [::Trap])))
             else ret (s, vs, crash_error))
          (ret (s, vs, crash_error))
      else ret (s, vs, crash_error)
    else ret (s, vs, crash_error)
  | Basic Current_memory =>
    expect
      (smem_ind s i)
      (fun j =>
         if List.nth_error s.(s_mems) j is Some s_mem_s_j then
           ret (s, vs, RS_normal (vs_to_es (ConstInt32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j))) :: ves)))
         else ret (s, vs, crash_error))
      (ret (s, vs, crash_error))
  | Basic Grow_memory =>
    if ves is ConstInt32 c :: ves' then
      expect (smem_ind s i) (fun j =>
          if List.nth_error s.(s_mems) j is Some s_mem_s_j then
            let: l := mem_size s_mem_s_j in
            let: mem' := mem_grow s_mem_s_j (Wasm_int.nat_of_uint i32m c) in
            if mem' is Some mem'' then
              ret (upd_s_mem s (update_list_at s.(s_mems) j mem''), vs,
                   RS_normal (vs_to_es (ConstInt32 (Wasm_int.int_of_Z i32m (Z.of_nat l)) :: ves')))
            else ret (s, vs, crash_error)
          else ret (s, vs, crash_error))
        (ret (s, vs, crash_error))
    else ret (s, vs, crash_error)
  | Basic (EConst _) => ret (s, vs, crash_error)
  | Invoke cl =>
    match cl with
    | Func_native i' (Tf t1s t2s) ts es =>
      let: n := length t1s in
      let: m := length t2s in
      if length ves >= n
      then
        let: (ves', ves'') := split_n ves n in
        let: zs := n_zeros ts in
        ret (s, vs, RS_normal (vs_to_es ves''
                      ++ [::Local m i' (rev ves' ++ zs) [::Basic (Block (Tf [::] t2s) es)]]))
      else ret (s, vs, crash_error)
    | Func_host (Tf t1s t2s) f =>
      let: n := length t1s in
      let: m := length t2s in
      if length ves >= n
      then
        let (ves', ves'') := split_n ves n in
        r <- trigger (host_apply s f (rev ves')) ;;
          match r with
          | Some (s', r) =>
            (** We here double-check the types.
            Note that this is not a requirement of the Wasm specification. **)
            if result_types_agree t2s r
            then
              let: rves := result_to_stack r in
              ret (s', vs, RS_normal (vs_to_es ves'' ++ rves))
            else ret (s, vs, crash_error)
          | None => ret (s, vs, RS_normal (vs_to_es ves'' ++ [::Trap]))
          end
      else ret (s, vs, crash_error)
    end
  | Label ln les es =>
    if es_is_trap es
    then ret (s, vs, RS_normal (vs_to_es ves ++ [::Trap]))
    else
      '(s', vs', res) <- call _ (call_run_step_base d i (s, vs, es)) ;;
      match res with
      | RS_break 0 bvs =>
        if length bvs >= ln
        then ret (s', vs', RS_normal ((vs_to_es ((take ln bvs) ++ ves)) ++ les))
        else ret (s', vs', crash_error)
      | RS_break (n.+1) bvs => ret (s', vs', RS_break n bvs)
      | RS_return rvs => ret (s', vs', RS_return rvs)
      | RS_normal es' =>
        ret (s', vs', RS_normal (vs_to_es ves ++ [::Label ln les es']))
      | RS_crash error => ret (s', vs', RS_crash error)
      end
  | Local ln j vls es =>
    if es_is_trap es
    then ret (s, vs, RS_normal (vs_to_es ves ++ [::Trap]))
    else
      if const_list es
      then
        if length es == ln
        then ret (s, vs, RS_normal (vs_to_es ves ++ es))
        else ret (s, vs, crash_error)
      else
        '(s', vls', res) <- call _ (call_run_step_base d j (s, vls, es)) ;;
        match res return itree (run_stepE +' eff) res_tuple with
        | RS_return rvs =>
          if length rvs >= ln
          then ret (s', vs, RS_normal (vs_to_es (take ln rvs ++ ves)))
          else ret (s', vs, crash_error)
        | RS_normal es' =>
          ret (s', vs, RS_normal (vs_to_es ves ++ [::Local ln j vls' es']))
        | RS_crash error => ret (s', vs, RS_crash error)
        | RS_break _ _ => ret (s', vs, crash_error)
        end
  | Trap => ret (s, vs, crash_error)
  end.

Definition run_step_call : run_stepE ~> itree eff :=
  mrec (fun T (f : run_stepE T) =>
    let call _ f := trigger f in
    match f with
    | call_run_step_base d i cgf =>
      run_step_base call d i cgf
    | call_run_one_step d i cgf e =>
      run_one_step call d i cgf e
    end).

(** Enough fuel so that [run_one_step] does not run out of exhaustion. **)
Definition run_one_step_fuel : administrative_instruction -> nat.
Proof.
  move=> es. induction es using administrative_instruction_rect';
    let rec aux v :=
      lazymatch goal with
      | F : TProp.Forall _ _ |- _ =>
        apply TProp.max in F;
        move: F;
        let n := fresh "n" in
        move=> n;
        aux (n + v)
      | |- _ => exact (v.+1)
      end in
    aux (1 : nat).
Defined.

(** Enough fuel so that [run_step] does not run out of exhaustion. **)
Definition run_step_fuel (cfg : config_tuple) : nat :=
  let: (s, vs, es) := cfg in
  1 + List.fold_left max (List.map run_one_step_fuel es) 0.

(** [run_step] is defined by calling [run_step_base], whilst burning enough fuel
   for it to be fully computed. **)
Definition run_step (d : depth) (inst : instance) (cfg : config_tuple) : itree eff res_tuple :=
  burn (run_step_fuel cfg) (run_step_call (call_run_step_base d inst cfg)).

End RunStep.

Section Run.

Context {eff : Type -> Type}.
Context {eff_has_host_event : host_event -< eff}.

Definition run_v : depth -> instance -> config_tuple -> itree eff (store_record * res) :=
  let run_v :=
    rec-fix run_v (d, i, (s, vs, es)) :=
      if es_is_trap es
      then ret (s, R_trap)
      else
      if const_list es
      then ret (s, R_value (fst (split_vals_e es)))
        else
          '(s', vs', r) <- run_step d i (s, vs, es) ;;
          match r with
          | RS_normal es' => run_v (d, i, (s', vs', es'))
          | RS_crash error => ret (s, R_crash error)
          | _ => ret (s, R_crash C_error)
          end in
  fun d i cfg => run_v (d, i, cfg).

End Run.

End Host.

(* TODO: Here are our current assumptions.
Print Assumptions run_step.
[[
wasm_deserialise : bytes -> value_type -> value
serialise_i64 : i64 -> bytes
serialise_i32 : i32 -> bytes
serialise_f64 : f64 -> bytes
serialise_f32 : f32 -> bytes
Classical_Prop.classic : forall P : Prop, P \/ ~ P
(* Lots of axioms from Flocq. *)
]]
*)

Arguments RS_crash [_].
Arguments RS_break [_].
Arguments RS_return [_].

