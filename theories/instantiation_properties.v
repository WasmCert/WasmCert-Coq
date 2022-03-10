From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From ITree Require Import ITree.
From ITree Require ITreeFacts.
From Wasm Require Import list_extra datatypes datatypes_properties
                         interpreter binary_format_parser operations
                         typing opsem type_checker memory memory_list instantiation.
From Coq Require Import BinNat.

Section Host.

Variable host_function : eqType.
Let host := host host_function.

Variable host_instance : host.

Let store_record_eq_dec := @store_record_eq_dec host_function.
Let store_record_eqType := @store_record_eqType host_function.

Local Canonical Structure name_eqType := Eval hnf in EqType name (seq_eqMixin _).

Let store_record := store_record host_function.
Let host_state := host_state host_instance.

Let store_typing := @store_typing host_function.

Let external_typing := @external_typing host_function.

Let executable_host := executable_host host_function.
Variable executable_host_instance : executable_host.
Let host_event := host_event executable_host_instance.

Let instantiate := instantiate host_function host_instance.
Let instantiate_simpl := instantiate_simpl host_function.
(*
Let tab_agree := @typing.tab_agree host_function.
*)
Inductive ext_typing_list: store_record -> seq module_export -> seq extern_t -> Prop :=
| ext_typing_list_nil: forall s,
    ext_typing_list s [::] [::]
| ext_typing_list_cons: forall s v_exp v_exps te tes,
    ext_typing_list s v_exps tes ->
    external_typing s (modexp_desc v_exp) te ->
    ext_typing_list s (v_exp :: v_exps) (te :: tes).


Lemma instantiation_sound (s: store_record) m v_imps s' inst v_exps start:
  store_typing s ->
  instantiate s m v_imps ((s', inst, v_exps), start) ->
  (store_typing s') /\
  (exists C, inst_typing s' inst C) /\
  (exists tes, ext_typing_list s' v_exps tes) /\
  (pred_option (fun i => i < length s'.(s_funcs)) start).
  (* /\ store_extension s s' *)
Proof.
Admitted.

Let tab_agree := @tab_agree host_function.

Lemma tab_agree_aux s_funcs s_tables s_mems s_globals tab func:
  tab_agree {| s_funcs := s_funcs; s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |} tab ->
  tab_agree {| s_funcs := List.app s_funcs [:: func]; s_tables := s_tables; s_mems := s_mems;
               s_globals := s_globals |} tab .
Proof.
  rewrite /tab_agree /typing.tab_agree.
  move => Htb.
  destruct Htb as [Htable Hs_tables]; subst.
  constructor.
  - (* forall tabcl_agree (table_data tab) *)
    induction (table_data tab) as [| hd tl IH]; first by constructor.
    (* forall tabcl_agree hd :: tl *)
    inversion Htable as [| x y Hhd Htl]; subst.
    constructor.
    (* tabcl_agree hd *)
    destruct hd => //=. 
    rewrite /tabcl_agree in Hhd. simpl in Hhd.
    rewrite size_cat. by rewrite ltn_addr.
    (* forall tabcl_agree tl *)
    apply IH. exact Htl.
  - (* tabsize_agree table *)
    assumption.
Qed.

Let functions_agree := @functions_agree host_function.

Lemma functions_agree_aux s_funcs func f tf: 
  functions_agree s_funcs f tf ->
  functions_agree (List.app s_funcs [:: func]) f tf.
Proof.
  rewrite /functions_agree /typing.functions_agree.
  move/andP => [H1 H2]. move/eqP in H2.
  apply/andP. split.
  + (* f < length (s_funcs [::func])  *)
    rewrite List.app_length.
    by rewrite ltn_addr.
  + (* option_map cl_type (List.nth_error (s_funcs [::func]) f) == Some tf *)
    apply/eqP.
    rewrite <-H2.
    apply f_equal.
    apply List.nth_error_app1.
    by apply/ltP.
Qed.


Lemma all2_forward: forall A B (f1 f2 : A -> B -> bool) l1 l2,
  (forall a b, f1 a b -> f2 a b) ->
  (all2 f1 l1 l2 -> all2 f2 l1 l2).
Proof.
  move=> A B f1 f2. elim.
  - by case.
  - move=> h1 l1 IH. case=> //= h2 l2 E.
    move/andP => [H1 H2].
    apply/andP. split.
    + by apply E.
    + by apply IH => //=.
Qed.

Let cl_type_check_single := @cl_type_check_single host_function.

Lemma cl_type_check_single_aux1 s_funcs s_tables s_mems s_globals inst m_f func:
  cl_type_check_single {| s_funcs := s_funcs; s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |} func ->
  cl_type_check_single {| s_funcs := s_funcs ++ 
                                     [:: FC_func_native inst
                                         (List.nth match modfunc_type m_f with
                                            | Mk_typeidx n => n
                                            end (inst_types inst) (Tf [::] [::])) (modfunc_locals m_f) 
                                         (modfunc_body m_f)]; 
                          s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |} func.
Proof.
  move => Hcl.
  destruct Hcl as [tf' Hcl_typing].
  exists tf'.
  destruct func as [i tf ts es | tf h].
  + (* cl_typing_native *)
    inversion Hcl_typing; subst.
    rename H4 into Hinst_typing. rename H8 into Hbe_typing.
    apply cl_typing_native
      with (C := C)
           (C' := upd_local_label_return C (tc_local C ++ t1s ++ ts) ([::t2s] ++ tc_label C) (Some t2s))
          => //=.
    destruct C.
    rewrite /inst_typing. simpl.
    rewrite /inst_typing in Hinst_typing. simpl in Hinst_typing.
    destruct tc_local => //=.
    destruct tc_label => //=.
    destruct tc_return => //=.
    destruct i.
    move/andP in Hinst_typing. destruct Hinst_typing as [Hinst_typing Hmem].
    move/andP in Hinst_typing. destruct Hinst_typing as [Hinst_typing Htab].
    move/andP in Hinst_typing. destruct Hinst_typing as [Hinst_typing Hglb].
    move/andP in Hinst_typing. destruct Hinst_typing as [Hty Hfunc].
    move/eqP in Hty; subst.
    apply/andP. split => //=.
    apply/andP. split => //=.
    apply/andP. split => //=.
    apply/andP. split => //=.
    eapply all2_forward.
    apply functions_agree_aux.
    by exact Hfunc.
  + (* cl_typing_host *)
    inversion Hcl_typing; subst.
    by apply cl_typing_host.
Qed.

Axiom Forall_app
     : forall (A : Type) (P : A -> Prop) (l1 l2 : seq A),
       List.Forall P (l1 ++ l2)%list <-> List.Forall P l1 /\ List.Forall P l2.

Lemma store_typing_preserve_add_func : forall s_funcs s_tables s_mems s_globals inst m_f,
    store_typing
      {| s_funcs := s_funcs; s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |} ->
    (*
    module_func_typing 
    add_func s _ _ ...
*)
    store_typing
      {| s_funcs :=
        List.app s_funcs
                 [:: FC_func_native
                     inst
                     (List.nth (match m_f.(modfunc_type) with | Mk_typeidx n => n end) inst.(inst_types) (Tf nil nil))
                     m_f.(modfunc_locals)
                     m_f.(modfunc_body)]
      ; s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |}.
Proof.
  move=> s_funcs s_tables s_mems s_globals inst m_f HSTyping.
  Print store_typing.
  inversion HSTyping as [Hcl [ Htb Hmem ]].
  constructor.
  - (* cl_typing *)
    rewrite Forall_app.
    split.
    + (* forall cl_type_check_single s_funcs *) 
      apply List.Forall_forall => func Hin.
      rewrite -> List.Forall_forall in Hcl.
      apply cl_type_check_single_aux1.
      by apply Hcl.
    + (* cl_typing_check_single func *) {
        constructor => //=.
        remember (List.nth match modfunc_type m_f with
                           | Mk_typeidx n => n
                           end (inst_types inst) (Tf [::] [::])) as tf.
        exists tf.
        destruct tf as [t1s t2s]. Check List.map.  Search (N).
        eapply cl_typing_native => //.
        * admit.
        * admit.
          Admitted. (*
        remember ({| tc_types_t := inst.(inst_types);
                     tc_func_t := (List.map cl_type s_funcs) ++ [:: (Tf t1s t2s)];
                     tc_global := List.map (fun g => Build_global_type (g_mut g) (typeof (g_val g))) s_globals;
                     tc_table := List.map
                                 (fun t => {| tt_limits := {| lim_min := N.of_nat(tab_size t);
                                                              lim_max := Some (N.of_nat(t.(table_max_opt) + 1)) |};
                                              tt_elem_type := ELT_funcref |})
                                 s_tables;
                     tc_memory := List.map
                                  (fun m => {| lim_min := (mem_size m); lim_max := m.(mem_max_opt) |})
                                s_mems;
                     tc_local := nil;
                     tc_label := nil;
                    tc_return := None |}) as C.
        apply cl_typing_native with
          (C := C)
          (C' := upd_local_label_return C (tc_local C ++ t1s ++ (modfunc_locals m_f)) ([::t2s] ++ tc_label C) (Some t2s)) => //=.
        * (* inst_typing *)
          destruct inst. destruct C. simpl.
          destruct tc_local => //=.
          destruct tc_label => //=.
          destruct tc_return => //=.
          inversion HeqC; subst.
          destruct HeqC. 
          apply/andP. split.
          apply/andP. split.
          apply/andP. split.
          apply/andP. split => //=.
          -- (* functions_agree *) {
            admit.
          }
          -- (* globals_agree *) {
              rewrite /globals_agree.
            }
            
      }
  split.
  - (* tab_agree *)
    apply List.Forall_forall => tab Hin.
    rewrite -> List.Forall_forall in Htb.
    apply tab_agree_aux.
    by apply Htb.
  - (* mem_agree *)
    assumption.
Admitted.*)

Print module_typing.

Print alloc_Xs.

Print module_typing.
Print module_func_typing.

Lemma instantiation_sound_aux s s0 m inst l t_imps t_exps:
  module_typing m t_imps t_exps ->
  store_typing s ->
  (s0, l) = alloc_Xs host_function 
            (fun s m_f => alloc_func host_function s m_f inst) s (mod_funcs m) ->
  (*
  (s0, l) =
           (let
            '(s', fas) :=
             List.fold_left
               (fun '(s, ys) (x : module_func)
                  => let '(s', y) := alloc_func host_function s x inst in (s', y :: ys))
               (mod_funcs m) (s, acc) in (s', List.rev fas)) ->*)
  store_typing s0.
Proof.
  move => Hmodule.
  unfold module_typing in Hmodule.
  destruct Hmodule as [fts [gts Hmodule]].
  destruct m.
  destruct Hmodule as [Hmodfunc _].
  generalize dependent s.
  generalize dependent mod_funcs.
  induction mod_funcs => //; move => Hmodfunc s HType H0.
  - simpl in H0.
    by inversion H0; subst.
  - simpl in H0.
    destruct fts as [|ft fts']; first by inversion Hmodfunc.
    inversion Hmodfunc; subst; clear Hmodfunc.
    eapply IHmod_funcs with (s := s) => //.
    + admit.
    + unfold add_func. 
      apply store_typing_preserve_add_func.
      by destruct s => //.
Admitted.
  
Lemma instantiation_sound_simpl:  forall (s: store_record) m v_imps s' inst v_exps start,
  store_typing s ->
  instantiate_simpl s m v_imps ((s', inst, v_exps), start) ->
  (store_typing s').
  (* (exists C, inst_typing s' inst C) /\
  (exists tes, ext_typing_list s' v_exps tes) /\
  (pred_option (fun i => i < length s'.(s_funcs)) start).*)
  (* /\ store_extension s s' *)
Proof.
  move=> s m v_imps s' inst v_exps start HType HInst. inversion HInst as [t_imps [t_exps [Hmodule H0]]].
  unfold alloc_funcs_bool in H0.
  remember (alloc_funcs host_function s (mod_funcs m) inst) as psi.
  destruct psi.
  rewrite /alloc_funcs in Heqpsi. (*/alloc_Xs in Heqpsi.*)
  move/andP in H0.
  destruct H0 as [Heqs Heqinst].
  move/eqP in Heqs; subst.
  move/eqP in Heqinst.
  apply instantiation_sound_aux in Heqpsi => //.
Qed.



From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From ITree Require Import ITree.
From ITree Require ITreeFacts.
From Wasm Require Import list_extra datatypes datatypes_properties
                         interpreter binary_format_parser operations
                         typing opsem type_checker memory memory_list instantiation.
From Coq Require Import BinNat.

Section Host.

Variable host_function : eqType.
Let host := host host_function.

Variable host_instance : host.

Let store_record_eq_dec := @store_record_eq_dec host_function.
Let store_record_eqType := @store_record_eqType host_function.

Local Canonical Structure name_eqType := Eval hnf in EqType name (seq_eqMixin _).

Let store_record := store_record host_function.
Let host_state := host_state host_instance.

Let store_typing := @store_typing host_function.

Let external_typing := @external_typing host_function.

Let executable_host := executable_host host_function.
Variable executable_host_instance : executable_host.
Let host_event := host_event executable_host_instance.

Let instantiate := instantiate host_function host_instance.


Inductive ext_typing_list: store_record -> seq module_export -> seq extern_t -> Prop :=
| ext_typing_list_nil: forall s,
    ext_typing_list s [::] [::]
| ext_typing_list_cons: forall s v_exp v_exps te tes,
    ext_typing_list s v_exps tes ->
    external_typing s (modexp_desc v_exp) te ->
    ext_typing_list s (v_exp :: v_exps) (te :: tes).


Lemma instantiation_sound (s: store_record) m v_imps s' inst v_exps start:
  store_typing s ->
  instantiate s m v_imps ((s', inst, v_exps), start) ->
  (store_typing s') /\
  (exists C, inst_typing s' inst C) /\
  (exists tes, ext_typing_list s' v_exps tes) /\
  (pred_option (fun i => i < length s'.(s_funcs)) start).
  (* /\ store_extension s s' *)
Proof.
Admitted.
