(** Wasm typing rules **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import operations.
From Coq Require Import NArith.

(**
There are three files related to typing:
  -- typing.v (this file): gives inductive definition of typing;
  -- type_checker.v: gives a fixpoint that determines whether something is of 
     a given type. This is somewhat like the interpreter, except that we need
     to prove that typing is unique. I think it is already done for this
     inductive definition but not for the type_checker yet? But that will follow
     from the following..
  -- type_checker_reflects_typing.v: gives a lemma that says the two above agree
     with each other.

  After all of these, we will need to prove preservation + progress with respect
    to definitions in opsem.v. This should be in a separate file.
**)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Variable host_function : eqType.

Let function_closure := function_closure host_function.
Let store_record := store_record host_function.
(*Let administrative_instruction := administrative_instruction host_function.
Let lholed := lholed host_function.*)


(* TODO: Documentation *)

(* FIXME: To which function in the Wasm specification does this correspond to? *)

(** Answer to above

  I searched through the specification but couldn't find a direct link to this either.
    After some thoughts I think the only possibility is that this
    is related to section 2.4.1, where all possible Convert operations are defined.

  From my understanding, Cvtop is just a proxy for all the conversion operations, which
    are the following (given in 2.4.1):
    - i32.wrap_i64
    - i64.extend_i32_sx
    - inn.trunc_fmm_sx
    - f32.demote_f64
    - f64.promote_f32
    - fnn.convert_imm_sx
    - inn.reinterpret_fnn
    - fnn.reinterpret_inn

    where sx means the numbers are signed.

    I think the original author wrote this convert_helper function for:
      given two types t1, t2 and the sign option sx, if the function returns true,
      then there is one of the above eight conversion operations that is
      of the corresponding type (in fact one of the first six -- see below). 

    For example, consider when will convert_helper be true if sxo is not None. In that
      case we must have:
      - at least one of t1 or t2 is not float;
      - at least one of t1 or t2 is not int -- or if they are both int, then t1
          should have length at least equal to t2.

    Considering the fact that there are only 4 choices for t1,t2 (i/f 32/64), there
      are only the following possible combinations that will make this function true
      (noting that we need to have t1 and t2 being different):
      - t1 = fnn, t2 = imm;
      - t1 = inn, t2 = fmm;
      - t1 = i64, t2 = i32.
    These three combinations correspond exactly to the three signed conversions 
      among the eight listed above (to trunc/convert/extend respectively).

    When sx is unsigned, the helper function gives the three other conversions
      that are not reinterpret operations. This is where we've been doing
      differently from the official convention, since the official spec considers
      reinterpret to be part of the conversion operations under the same proxy
      (see 2.4.1.1). In our approach, Cvtop is only the proxy for the first 6 
      conversion operations; we deal with the reinterpret operations in a separate
      case (this is the case in both opsem.v and the be_typing function below).
    
    I guess it's fine if we keep it consistent within our own work, but I don't think
      I'm the best person to decide this.

    This might also answer some of the FIXMEs below.
   
**)
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

(* FIXME: Change name *)
(** This definition corresponds to the sentence
    “The label C.labels[l] must be defined in the context.”
    in the specification. **)
Definition plop2 C i ts :=
  List.nth_error (tc_label C) i == Some ts.

Inductive result_typing : result -> result_type -> Prop :=
  | result_typing_values : forall vs, result_typing (result_values vs) (map typeof vs)
  | result_typing_trap : forall ts, result_typing result_trap ts
  .

Inductive unop_type_agree: value_type -> unop -> Prop :=
  | Unop_i32_agree: forall op, unop_type_agree T_i32 (Unop_i op)
  | Unop_i64_agree: forall op, unop_type_agree T_i64 (Unop_i op)
  | Unop_f32_agree: forall op, unop_type_agree T_f32 (Unop_f op)
  | Unop_f64_agree: forall op, unop_type_agree T_f64 (Unop_f op)
  .
   
Inductive binop_type_agree: value_type -> binop -> Prop :=
  | Binop_i32_agree: forall op, binop_type_agree T_i32 (Binop_i op)
  | Binop_i64_agree: forall op, binop_type_agree T_i64 (Binop_i op)
  | Binop_f32_agree: forall op, binop_type_agree T_f32 (Binop_f op)
  | Binop_f64_agree: forall op, binop_type_agree T_f64 (Binop_f op)
  .
  
Inductive relop_type_agree: value_type -> relop -> Prop :=
  | Relop_i32_agree: forall op, relop_type_agree T_i32 (Relop_i op)
  | Relop_i64_agree: forall op, relop_type_agree T_i64 (Relop_i op)
  | Relop_f32_agree: forall op, relop_type_agree T_f32 (Relop_f op)
  | Relop_f64_agree: forall op, relop_type_agree T_f64 (Relop_f op)
  .
  
Inductive be_typing : t_context -> seq basic_instruction -> function_type -> Prop :=
(** Corresponding to section 3.3 **)
| bet_const : forall C v, be_typing C [::BI_const v] (Tf [::] [::typeof v])
| bet_unop : forall C t op,
    unop_type_agree t op -> be_typing C [::BI_unop t op] (Tf [::t] [::t])
| bet_binop : forall C t op,
    binop_type_agree t op -> be_typing C [::BI_binop t op] (Tf [::t; t] [::t])
| bet_testop : forall C t op, is_int_t t -> be_typing C [::BI_testop t op] (Tf [::t] [::T_i32])
| bet_relop: forall C t op,
    relop_type_agree t op -> be_typing C [::BI_relop t op] (Tf [::t; t] [::T_i32])
| bet_convert : forall C t1 t2 sx, t1 <> t2 -> convert_helper sx t1 t2 ->
  be_typing C [::BI_cvtop t1 CVO_convert t2 sx] (Tf [::t2] [::t1]) (* FIXME: Difference from the Isabelle formalisation: why merge the two rules here? *)
| bet_reinterpret : forall C t1 t2, t1 <> t2 -> Nat.eqb (t_length t1) (t_length t2) ->
  be_typing C [::BI_cvtop t1 CVO_reinterpret t2 None] (Tf [::t2] [::t1])
| bet_unreachable : forall C ts ts',
  be_typing C [::BI_unreachable] (Tf ts ts')
| bet_nop : forall C, be_typing C [::BI_nop] (Tf [::] [::])
| bet_drop : forall C t, be_typing C [::BI_drop] (Tf [::t] [::])
| bet_select : forall C t, be_typing C [::BI_select] (Tf [::t; t; T_i32] [::t])
| bet_block : forall C tn tm es,
  let tf := Tf tn tm in
  be_typing (upd_label C (app [::tm] (tc_label C))) es (Tf tn tm) ->
  be_typing C [::BI_block tf es] (Tf tn tm)
| bet_loop : forall C tn tm es,
  be_typing (upd_label C (app [::tn] (tc_label C))) es (Tf tn tm) ->
  be_typing C [::BI_loop (Tf tn tm) es] (Tf tn tm)
| bet_if_wasm : forall C tn tm es1 es2,
  be_typing (upd_label C (app [::tm] (tc_label C))) es1 (Tf tn tm) ->
  be_typing (upd_label C (app [::tm] (tc_label C))) es2 (Tf tn tm) ->
  be_typing C [::BI_if (Tf tn tm) es1 es2] (Tf (app tn [::T_i32]) tm)
| bet_br : forall C i t1s ts t2s,
  i < length (tc_label C) ->
  plop2 C i ts ->
  be_typing C [::BI_br i] (Tf (app t1s ts) t2s)
| bet_br_if : forall C i ts,
  i < length (tc_label C) ->
  plop2 C i ts ->
  be_typing C [::BI_br_if i] (Tf (app ts [::T_i32]) ts)
| bet_br_table : forall C i ins ts t1s t2s,
  all (fun i => (i < length (tc_label C)) && (plop2 C i ts)) (app ins [::i])  ->
  be_typing C [::BI_br_table ins i] (Tf (app t1s (app ts [::T_i32])) t2s)
| bet_return : forall C ts t1s t2s,
  tc_return C = Some ts ->
  be_typing C [::BI_return] (Tf (app t1s ts) t2s)
| bet_call : forall C i tf,
  i < length (tc_func_t C) ->
  List.nth_error (tc_func_t C) i = Some tf ->
  be_typing C [::BI_call i] tf
| bet_call_indirect : forall C i t1s t2s,
  i < length (tc_types_t C) ->
  List.nth_error (tc_types_t C) i = Some (Tf t1s t2s) ->
  tc_table C <> nil -> (* TODO: this is redundant with the length check *)
  be_typing C [::BI_call_indirect i] (Tf (app t1s [::T_i32]) t2s)
| bet_get_local : forall C i t,
  i < length (tc_local C) ->
  List.nth_error (tc_local C) i = Some t ->
  be_typing C [::BI_get_local i] (Tf [::] [::t])
| bet_set_local : forall C i t,
  i < length (tc_local C) ->
  List.nth_error (tc_local C) i = Some t ->
  be_typing C [::BI_set_local i] (Tf [::t] [::])
| bet_tee_local : forall C i t,
  i < length (tc_local C) ->
  List.nth_error (tc_local C) i = Some t ->
  be_typing C [::BI_tee_local i] (Tf [::t] [::t])
| bet_get_global : forall C i t,
  i < length (tc_global C) ->
  option_map tg_t (List.nth_error (tc_global C) i) = Some t ->
  be_typing C [::BI_get_global i] (Tf [::] [::t])
| bet_set_global : forall C i g t,
  i < length (tc_global C) ->
  List.nth_error (tc_global C) i = Some g ->  
  tg_t g = t ->
  is_mut g ->
  be_typing C [::BI_set_global i] (Tf [::t] [::])
| bet_load : forall C a off tp_sx t,
  tc_memory C <> nil ->
  load_store_t_bounds a (option_projl tp_sx) t ->
  be_typing C [::BI_load t tp_sx a off] (Tf [::T_i32] [::t])
| bet_store : forall C a off tp t,
  tc_memory C <> nil ->
  load_store_t_bounds a tp t ->
  be_typing C [::BI_store t tp a off] (Tf [::T_i32; t] [::]) (* FIXME: Same here: two Isabelle rules have been merged here. *)
| bet_current_memory : forall C,
  tc_memory C <> nil ->
  be_typing C [::BI_current_memory] (Tf [::] [::T_i32])
| bet_grow_memory : forall C,
  tc_memory C <> nil ->
  be_typing C [::BI_grow_memory] (Tf [::T_i32] [::T_i32])
| bet_empty : forall C,
  be_typing C [::] (Tf [::] [::])
| bet_composition : forall C es e t1s t2s t3s,
  be_typing C es (Tf t1s t2s) ->
  be_typing C [::e] (Tf t2s t3s) ->
  be_typing C (app es [::e]) (Tf t1s t3s)
| bet_weakening : forall C es ts t1s t2s,
  be_typing C es (Tf t1s t2s) ->
  be_typing C es (Tf (app ts t1s) (app ts t2s))
.



Definition upd_local C loc :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    loc
    (tc_label C)
    (tc_return C).

Definition upd_return C ret :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    (tc_local C)
    (tc_label C)
    ret.

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

(**
 g_mut says whether the global is mutable; then it has another field g_val
   specifying the value (with type).
 **)

Definition global_agree (g : global) (tg : global_type) : bool :=
  (tg_mut tg == g_mut g) && (tg_t tg == typeof (g_val g)).

(**
 Determines if the nth element of gs is of global type tg. I felt that the first
   condition isn't necessary since List.nth_error take care of it. This has been
   the case for many other places as well. Maybe it's for eyeball-closeness?
**)
Definition globals_agree (gs : seq global) (n : nat) (tg : global_type) : bool :=
  (n < length gs) && (option_map (fun g => global_agree g tg) (List.nth_error gs n) == Some true).

Definition mem_typing (m : memory) (m_t : memory_type) : bool :=
  (N.leb m_t.(lim_min) (mem_size m)) &&
  (m.(mem_max_opt) == m_t.(lim_max)) (* TODO: mismatch *).

Definition memi_agree (ms : list memory) (n : nat) (mem_t : memory_type) : bool :=
  (n < length ms) &&
  match List.nth_error ms n with
  | Some mem => mem_typing mem mem_t
  | None => false
  end.

Definition functions_agree (fs : seq function_closure) (n : nat) (f : function_type) : bool :=
  (n < length fs) && (option_map cl_type (List.nth_error fs n) == Some f).

(*
  This is the main point where the typing context in the typing system and the 
    store in the operational semantics are connected. Writting my understanding down
    for future reference since I'll definitely forget the meaning of some of them
    at a point.

  store_record and instance are from the operational semantics. 
  Store_record contains 4 
    components: 
     - s_funcs, a sequence of function_closure;
        function_closure is either a host, whose behaviour seems to be out of our
          control; or a native function, which is of the form (Func_native i tf ts es).
          here i is an instance, tf is the function type of this closure, ts is a 
          sequence of value type (?) and es is a sequence of basic instruction.
        Currently I don't see what this ts does (since basic instruction has EConst).
          
     - s_tab, a sequence of tabinst (tables);
        Each table instance is basically a sequence of nat, with a limit on size.

     - s_memory, a sequence of memory;
        Similar to the above, though each memory is a sequence of byte instead of nat.

     - s_glob, a sequence of global (global variables).
        I think each is just one variable, could be either mutable/immutable, and could
          be of the four wasm basic types (i/f 32/64).

   Instance is for some reason very similar. It also has funcs, tab, memory and globs,
     although they are all natural numbers or sequence of natural numbers (and for
     some reason was named 'immediate'. There's an additional i_types which is a 
     sequence of function_type (Tf t1s t2s).

   t_context is the typing context used for the typing predicate. It contains
     tc_types_t and tc_func_t which are both sequence of function_type; it also
     contains tc_global, tc_table and tc_memory, although in t_context we only need
     to know the types of these components. Tables and memories are typed by its 
     size limit (TODO: need to update the definition in t_context), therefore 
     tc_table and tc_memory are option of nat. tc_global is a sequence of global_type,
     where each global_type is the type of one global (mutability + type).
   The main difference is that t_context also contains tc_local, tc_label and tc_return.
     I think this is what makes is really a 'context', as this implies that the current
     sequence of instructions were taken from a larger overall picture. tc_local is 
     a sequence of value_type (which turns out to be the 4 wasm basic types);
     tc_label is a sequence of sequence of value_type (????), and tc_return is an
     option on sequence of value_type.
   I think we can try to deduce that by looking at the typing predicate above.
   For tc_local we should probably look at instructions that manipulate local storage,
     e.g. get/set/tee_local. We see in bet_get_local that get_local i would result in
     function type [] -> [t] if the ith element of (tc_local C) is of type t. So
     t_local stores the type of all local variables.
   For tc_label, we should look at some control flow instructions that introduce new
     labels. From the instruction 'Block': if we have an instruction 'Block tf es', and
     tf = Tf tn tm, then the type of 'Block tf es' under context C is tn -> tm: but
     this is at the condition that, in the modified typing context C', where we prepend
     a 'tm' to tc_label of C, the instruction list es must be of type (Tf tn tm) as 
     well. So it seems that tc_label keeps track of the resulting type of each label
     in a stack?
   It's probably better to look at where it is actually used. Check 'br': when we
     see a 'Br i', we need that the length of tc_label C to be at least (i+1). This is
     consistent with the above understanding since we need to have at least i+1 labels
     present for the Br i instruction to be valid. We know Br i breaks from i labels and
     continue execution at the continuation of the (i+1)th label. Then we find the 
     ith entry of tc_label (0-indexed here), call it ts. The type of the break command
     is then actually Tf (t1s ++ ts) t2s for arbitrary t1s and t2s!!?? This is actually
     not a mistake (3.3.5.6). It is also weird that br_if doesn't have this 
     polymorphism: it is always of type ts ++ [i32] -> ts. br_table is, however,
     polymorphic again.
  The reason for above is that  br_if is the only command that might not actually
     break: if the top value is zero then we don't break. I think in Wasm, any if
     command of this type must have the same type in both cases, therefore the case
     that it actually breaks must also have the same type. The ts at the top of the
     consumption is only there to demonstrate that this label indeed finishes with
     a type of ts. The t2s can be whatever type that fits which makes the overall typing
     consistent (I think): it is like in the separation logic course, where we give
     br a reduction result of False (basically meaning that we never reach there, and
     false deduces everything -- so if there are later commands we could be consistent).
     The t1s part is to fit the accumulated type of the previous instructions, due to
     definition of types of instruction sequences (3.3.6.2). In practice t1s will only
     have one appropriate value that makes the overall typing work (and t2s also, if 
     I'm correct). I think I'm indeed correct: later in the proof I should be able to
     choose the correct t1s and t2s for the proof to work.

   Ok now tc_return becomes obvious: it is the return type of the current function.
     There is an analogy in the type of the return instruction which is very similar
     to the 'Br i' instruction, being also polymorphic.
 *)

(*
  This basically says: an instance of a store_record has type C iff:
  - i_types of instance is the same as tc_types_t of C;
    It is unclear what this component actually is. What is this sequence of types?
  - i_funcs of instance are indices of functions in the store. The type of the
      each corresponding function in the store needs to have the same type as the
      function in the typing_context;
  - i_globs of instance are indices of globals in the store, and the same requirement
      must be satisfied;
  - i_tab specifies one index in the table sequence of the store. This table must be
      of the same type as the table type in the typing context (typed by size limit);
  - i_memory specifies one index in the memory sequence of the store, and the same
      requirement must be satisfied;
  - Then, the typing context has local vars, labels, and returns to be all empty.
 *)

Definition tab_typing (t : tableinst) (tt : table_type) : bool :=
  (tt.(tt_limits).(lim_min) <= tab_size t) &&
  (t.(table_max_opt) < tt.(tt_limits).(lim_max)).

Definition tabi_agree ts (n : nat) (tab_t : table_type) : bool :=
  (n < List.length ts) &&
  match List.nth_error ts n with
  | None => false
  | Some x => tab_typing x tab_t
  end.

Definition inst_typing (s : store_record) (inst : instance) (C : t_context) : bool :=
  let '{| inst_types := ts; inst_funcs := fs; inst_tab := tbs; inst_memory := ms; inst_globs := gs; |} := inst in
  match C with
  | {| tc_types_t := ts'; tc_func_t := tfs; tc_global := tgs; tc_table := tabs_t; tc_memory := mems_t; tc_local := nil; tc_label := nil; tc_return := None |} =>
    (ts == ts') &&
    (all2 (functions_agree s.(s_funcs)) fs tfs) &&
    (all2 (globals_agree s.(s_globals)) gs tgs) &&
    (all2 (tabi_agree s.(s_tables)) tbs tabs_t) &&
    (all2 (memi_agree s.(s_mems)) ms mems_t)
  | _ => false
  end.

Inductive frame_typing: store_record -> frame -> t_context -> Prop :=
| mk_frame_typing: forall s i tvs C f,
    inst_typing s i C ->
    f.(f_inst) = i ->
    map typeof f.(f_locs) = tvs ->
    frame_typing s f (upd_local C (tc_local C ++ tvs))
  .

Lemma functions_agree_injective: forall s i t t',
  functions_agree s i t ->
  functions_agree s i t' ->
  t = t'.
Proof.
  move => s i t t' H1 H2.
  unfold functions_agree in H1. unfold functions_agree in H2.
  (*move/andP in H1. move/andP in H2.*)
  move/andP: H1 => [_ H1].
  move/andP: H2 => [_ H3].
  move/eqP in H1. move/eqP in H3.
  rewrite H3 in H1 => {H3}.
  by move: H1 => [H1].
Qed.

(*
Print Func_native.

  Here we're typing a function closure. The second case where we have a host function
    is obvious: it can be anything.
  However, if it is a native function, then we should be able to deduce its type.
    Suppose we have a store s. The function is based on an instance i, and claims to
    have type tf = (T1s -> T2s). It also comes with a sequence of local variables of
    type ts (think parameters). The body of the function is es.
  Let C be a typing context for the instance i of the store s. Because of the local
    variables, we append ts to the local part of the typing context C. Then we 
    prepend a t1s in the local section and a t2s in the label section since that is the
    outermost block (think reduction result of admin instruction [::Local ...]). The
    result, which is t2s, is also updated into the typing context. Let this modified
    typing context be C' (I'm not sure why these are necessary though).
  Then, this native function Func_native i tf ts es indeed has its claimed type 
    t1s -> t2s iff under this typing context C', its function body es has type
    [::] -> t2s, i.e. consuming nothing (since there's nothing in the stack) and 
    producing some results with type t2s. The type of the body es is fully determined
    by be_typing.

  I think the main use of this is for typing the Callcl (now renamed to Invoke)
    instructions.
 *)
Inductive cl_typing : store_record -> function_closure -> function_type -> Prop :=
  | cl_typing_native : forall i s C C' ts t1s t2s es tf,
    inst_typing s i C ->
    tf = Tf t1s t2s ->
    C' = upd_local_label_return C (tc_local C ++ t1s ++ ts) ([::t2s] ++ tc_label C) (Some t2s) ->
    be_typing C' es (Tf [::] t2s) ->
    cl_typing s (FC_func_native i tf ts es) (Tf t1s t2s)
  | cl_typing_host : forall s tf h,
    cl_typing s (FC_func_host tf h) tf
  .

(*
  e_typing is the extension of typing to administrative instructions. See appendix 5 for
    some of them.
*)

Inductive e_typing : store_record -> t_context -> seq administrative_instruction -> function_type -> Prop :=
| ety_a : forall s C bes tf,
  be_typing C bes tf -> e_typing s C (to_e_list bes) tf
| ety_composition : forall s C es e t1s t2s t3s,
  e_typing s C es (Tf t1s t2s) ->
  e_typing s C [::e] (Tf t2s t3s) ->
  e_typing s C (es ++ [::e]) (Tf t1s t3s)
| ety_weakening : forall s C es ts t1s t2s,
  e_typing s C es (Tf t1s t2s) ->
  e_typing s C es (Tf (ts ++ t1s) (ts ++ t2s))
| ety_trap : forall s C tf,
  e_typing s C [::AI_trap] tf
| ety_local : forall s C n f es ts,
  s_typing s (Some ts) f es ts ->
  length ts = n ->
  e_typing s C [::AI_local n f es] (Tf [::] ts)
| ety_invoke : forall s a C cl tf,
  List.nth_error s.(s_funcs) a = Some cl ->
  cl_typing s cl tf ->
  e_typing s C [::AI_invoke a] tf
| ety_label : forall s C e0s es ts t2s n,
  e_typing s C e0s (Tf ts t2s) ->
  e_typing s (upd_label C ([::ts] ++ tc_label C)) es (Tf [::] t2s) ->
  length ts = n ->
  e_typing s C [::AI_label n e0s es] (Tf [::] t2s)

with s_typing : store_record -> option (seq value_type) -> frame -> seq administrative_instruction -> seq value_type -> Prop :=
| mk_s_typing : forall s f es rs ts C C0,
  frame_typing s f C0 ->
  C = upd_return C0 rs ->
  e_typing s C es (Tf [::] ts) ->
  (rs = Some ts \/ rs = None) ->
  s_typing s rs f es ts
.

Scheme e_typing_ind' := Induction for e_typing Sort Prop
  with s_typing_ind' := Induction for s_typing Sort Prop.

Definition cl_typing_self (s : store_record) (fc : function_closure) : Prop :=
  cl_typing s fc (cl_type fc).

Lemma cl_typing_unique : forall s cl tf, cl_typing s cl tf -> tf = cl_type cl.
Proof.
  move=> s + tf. case.
  - move => i ts bes t H /=; by inversion H.
  - move => f h H; by inversion H.
Qed.

Definition cl_type_check_single (s:store_record) (f:function_closure):=
  exists tf, cl_typing s f tf.

Definition tabcl_agree (s : store_record) (tcl_index : option nat) : Prop :=
  match tcl_index with
  | None => True
  | Some n => n < size s.(s_funcs)
(*  let tcl := List.nth_error (s_funcs s) n in
    match tcl with
    | None => False
    | Some cl => cl_type_check_single s cl
    end*)
  end.

Definition tabsize_agree (t: tableinst) : Prop :=
  match table_max_opt t with
  | None => True
  | Some n => tab_size t <= n
  end.

Definition tab_agree (s: store_record) (t: tableinst): Prop :=
  List.Forall (tabcl_agree s) (t.(table_data)) /\
  tabsize_agree t.

Definition mem_agree (m : memory) : Prop :=
  match (mem_max_opt m) with
  | None => True
  | Some n => N.le (mem_size m) n
  end.

Definition store_typing (s : store_record) : Prop :=
  match s with
  | Build_store_record fs tclss mss gs =>
    List.Forall (cl_type_check_single s) fs /\
    List.Forall (tab_agree s) tclss /\
    List.Forall mem_agree mss
  end.

Inductive config_typing : store_record -> frame -> seq administrative_instruction -> seq value_type -> Prop :=
| mk_config_typing :
  forall s f es ts,
  store_typing s ->
  s_typing s None f es ts ->
  config_typing s f es ts.


End Host.

