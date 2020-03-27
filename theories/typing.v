(** Wasm typing rules **)
(* (C) J. Pichon - see LICENSE.txt *)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import operations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition convert_helper (sxo : option sx) t1 t2 : bool :=
  (sxo == None) ==
  ((is_float_t t1 && is_float_t t2) || (is_int_t t1 && is_int_t t2 && (t_length t1 < t_length t2))).

Definition convert_cond t1 t2 (sxo : option sx) : bool :=
  (t1 != t2) && convert_helper sxo t1 t2.

Definition upd_label C lab :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    (tc_local C)
    lab
    (tc_return C).

Definition plop2 C i ts :=
  List.nth_error (tc_label C) i == Some ts.

Inductive be_typing : t_context -> list basic_instruction -> function_type -> Prop :=
| bet_const : forall C v, be_typing C [::EConst v] (Tf [::] [::typeof v])
| bet_unop_i : forall C t op, is_int_t t -> be_typing C [::Unop_i t op] (Tf [::t] [::t])
| bet_unop_f : forall C t op, is_float_t t -> be_typing C [::Unop_f t op] (Tf [::t] [::t])
| bet_binop_i : forall C t op, is_int_t t -> be_typing C [::Binop_i t op] (Tf [::t; t] [::t])
| bet_binop_f : forall C t op, is_float_t t -> be_typing C [::Binop_i t op] (Tf [::t; t] [::t])
| bet_testop : forall C t op, is_int_t t -> be_typing C [::Testop t op] (Tf [::t] [::T_i32])
| bet_relop_i : forall C t op, is_int_t t -> be_typing C [::Relop_i t op] (Tf [::t; t] [::T_i32])
| bet_relop_f : forall C t op, is_float_t t -> be_typing C [::Relop_f t op] (Tf [::t; t] [::T_i32])
| bet_convert : forall C t1 t2 sx, t1 != t2 -> convert_helper sx t1 t2 ->
  be_typing C [::Cvtop t1 Convert t2 sx] (Tf [::t2] [::t1]) (* FIXME: Difference from the Isabelle formalisation: why merge the two rules here? *)
| bet_reinterpret : forall C t1 t2, t1 != t2 -> Nat.eqb (t_length t1) (t_length t2) ->
  be_typing C [::Cvtop t1 Reinterpret t2 None] (Tf [::t2] [::t1])
| bet_unreachable : forall C ts ts',
  be_typing C [::Unreachable] (Tf ts ts')
| bet_nop : forall C, be_typing C [::Nop] (Tf [::] [::])
| bet_drop : forall C t, be_typing C [::Drop] (Tf [::t] [::])
| bet_select : forall C t, be_typing C [::Select] (Tf [::t; t; T_i32] [::t])
| bet_block : forall C tn tm es,
  let tf := Tf tn tm in
  be_typing (upd_label C (app [::tm] (tc_label C))) es (Tf tn tm) ->
  be_typing C [::Block tf es] (Tf tn tm)
| bet_loop : forall C tn tm es,
  be_typing (upd_label C (app [::tm] (tc_label C))) es (Tf tn tm) ->
  be_typing C [::Loop (Tf tn tm) es] (Tf tn tm)
| bet_if_wasm : forall C tn tm es1 es2,
  be_typing (upd_label C (app [::tm] (tc_label C))) es1 (Tf tn tm) ->
  be_typing (upd_label C (app [::tm] (tc_label C))) es2 (Tf tn tm) ->
  be_typing C [::If (Tf tn tm) es1 es2] (Tf (app tn [::T_i32]) tm)
| bet_br : forall C i t1s ts t2s,
  i < length (tc_label C) ->
  plop2 C i ts ->
  be_typing C [::Br i] (Tf (app t1s ts) t2s)
| bet_br_if : forall C i ts,
  i < length (tc_label C) ->
  plop2 C i ts ->
  be_typing C [::Br_if i] (Tf (app ts [::T_i32]) ts)
| bet_br_table : forall C i ins ts t1s t2s,
  all (fun i => (i < length (tc_label C)) && (plop2 C i ts)) (app ins [::i])  ->
  be_typing C [::Br_table ins i] (Tf (app t1s (app ts [::T_i32])) t2s)
| bet_return : forall C ts t1s t2s,
  (tc_return C) == (Some ts) ->
  be_typing C [::Return] (Tf (app t1s ts) t2s)
| bet_call : forall C i tf,
  i < length (tc_func_t C) ->
  (List.nth_error (tc_func_t C) i) = (Some tf) ->
  be_typing C [::Call i] tf
| bet_call_indirect : forall C i t1s t2s,
  i < length (tc_types_t C) ->
  (List.nth_error (tc_types_t C) i) == (Some (Tf t1s t2s)) ->
  (tc_table C) != None ->
  be_typing C [::Call_indirect i] (Tf (app t1s [::T_i32]) t2s)
| bet_get_local : forall C i t,
  i < length (tc_local C) ->
  (List.nth_error (tc_local C) i) == (Some t) ->
  be_typing C [::Get_local i] (Tf [::] [::t])
| bet_set_local : forall C i t,
  i < length (tc_local C) ->
  (List.nth_error (tc_local C) i) == (Some t) ->
  be_typing C [::Set_local i] (Tf [::t] [::])
| bet_tee_local : forall C i t,
  i < length (tc_local C) ->
  (List.nth_error (tc_local C) i) == (Some t) ->
  be_typing C [::Tee_local i] (Tf [::t] [::t])
| bet_get_global : forall C i t,
  i < length (tc_global C) ->
  (option_map tg_t (List.nth_error (tc_global C) i)) = (Some t) ->
  be_typing C [::Get_global i] (Tf [::] [::t])
| bet_set_global : forall C i t,
  i < length (tc_global C) ->
  (option_map tg_t (List.nth_error (tc_global C) i)) = (Some t) ->
  be_typing C [::Set_global i] (Tf [::t] [::])
| bet_load : forall C n a off tp_sx t,
  (tc_memory C) = (Some n) ->
  load_store_t_bounds a (option_projl tp_sx) t ->
  be_typing C [::Load t tp_sx a off] (Tf [::T_i32] [::t])
| bet_store : forall C n a off tp t,
  (tc_memory C) = (Some n) ->
  load_store_t_bounds a tp t ->
  be_typing C [::Store t tp a off] (Tf [::T_i32; t] [::]) (* FIXME: Same here: two Isabelle rules have been merged here. *)
| bet_current_memory : forall C n,
  (tc_memory C) = (Some n) ->
  be_typing C [::Current_memory] (Tf [::] [::T_i32])
| bet_grow_memory : forall C n,
  (tc_memory C) = (Some n) ->
  be_typing C [::Grow_memory] (Tf [::T_i32] [::T_i32])
| bet_empty : forall C,
  be_typing C [::] (Tf [::] [::])
| bet_composition : forall C es e t1s t2s t3s,
  be_typing C es (Tf t1s t2s) ->
  be_typing C [::e] (Tf t2s t3s) ->
  be_typing C (app es [::e]) (Tf t1s t3s)
| bet_weakening : forall C es ts t1s t2s,
  be_typing C es (Tf t1s t2s) ->
  be_typing C es (Tf (app ts t1s) (app ts t2s)).



Definition upd_local_return C loc ret :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    loc
    (tc_label C)
    ret.

Definition upd_local_label_return C loc lab ret :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    loc
    lab
    ret.

Definition glob_agree (g : global) (tg : global_type) : bool :=
  (tg_mut tg == g_mut g) && (tg_t tg == typeof (g_val g)).

Definition globi_agree (gs : list global) (n : nat) (tg : global_type) : bool :=
  (n < length gs) && (option_map (fun g => glob_agree g tg) (List.nth_error gs n) == Some true).

Definition memi_agree (sm : list memory) (j : option nat) (m : option nat) : bool :=
  match j, m with
  | None, None => true
  | None, Some _ => false
  | Some _, None => false
  | Some j', Some m' =>
    (j' < length sm) && (option_map (@length byte) (List.nth_error sm j') == Some m')
  end.

Definition funci_agree (fs : list function_closure) (n : nat) (f : function_type) : bool :=
  (n < length fs) && (option_map cl_type (List.nth_error fs n) == Some f).

Definition inst_typing (s : store_record) (inst : instance) (C : t_context) :=
  if (inst, C) is (Build_instance ts fs i j gs, Build_t_context ts' tfs tgs n m [::] [::] None)
  then
    (ts == ts') &&
       (all2 (funci_agree (s_funcs s)) fs tfs) &&
       (all2 (globi_agree (s_globs s)) gs tgs) &&
          (match i, n with
             | None, None => true
             | None, Some _ => false
             | Some _, None => false
             | Some i', Some n' => (i' < length (s_tab s)) && (option_map (@length (option function_closure)) (List.nth_error (s_tab s) i') == Some n')
             end) &&
          (memi_agree (s_memory s) j m)
  else false.

Inductive cl_typing : store_record -> function_closure -> function_type -> Prop :=
| cl_typing_native : forall i s C ts t1s t2s es tf,
  inst_typing s i C ->
  tf = Tf t1s t2s ->
  let C' := upd_local_label_return C (app (tc_local C) (app t1s ts)) (app [::t2s] (tc_label  C)) (Some t2s) in
  be_typing C' es (Tf [::] t2s) ->
  cl_typing s (Func_native i tf ts es) (Tf t1s t2s)
| cl_typing_host : forall s tf h,
    cl_typing s (Func_host tf h) tf.

Definition cl_typing_self (s : store_record) (fc : function_closure) : Prop :=
  cl_typing s fc (cl_type fc).

Lemma cl_typing_unique : forall s cl tf, cl_typing s cl tf -> tf = cl_type cl.
Proof.
  move => s.
  case.
  { move => i tf ts bes t H.
    rewrite /=.
    inversion H.
    done. }
  { move => f h tf H.
    inversion H.
    by rewrite /=. }
Qed.

