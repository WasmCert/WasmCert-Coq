From mathcomp Require Import ssreflect ssrbool eqtype seq.
From mathcomp Require ssrnat.
From ITree Require Import ITree.
From ITree Require ITreeFacts.
From stdpp Require Import list fin_maps gmap base.
From Wasm Require Import list_extra datatypes datatypes_properties properties
     interpreter binary_format_parser operations type_preservation
                         typing opsem type_checker memory memory_list instantiation instantiation_properties.
Require Export stdpp_aux.
From Coq Require Import BinNat.
Require Import Coq.Program.Equality.

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

Inductive ext_typing_list: store_record -> seq.seq module_export -> seq.seq extern_t -> Prop :=
| ext_typing_list_nil: forall s,
    ext_typing_list s [::] [::]
| ext_typing_list_cons: forall s v_exp v_exps te tes,
    ext_typing_list s v_exps tes ->
    external_typing s (modexp_desc v_exp) te ->
    ext_typing_list s (v_exp :: v_exps) (te :: tes).

Lemma Forall2_all2: forall A B (R : A -> B -> bool ) (l1 : seq.seq A) (l2 : seq.seq B),
    List.Forall2 R l1 l2 <-> all2 R l1 l2.
Proof.
  move => A B R l1.
  split.
  - move: l2.
    induction l1; move => l2 HForall2.
    * by inversion HForall2.
    * inversion HForall2; subst.
      specialize (IHl1 l' H3).
      apply/andP. split => //.
  - move: l2.
    induction l1; move => l2 Hall2.
    * inversion Hall2. by destruct l2 => //.
    * inversion Hall2. destruct l2 => //.
      move/andP in H0. destruct H0.
      specialize (IHl1 l2 H0).
      apply Forall2_cons => //.
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

Lemma all2_and: forall A B (f g h : A -> B -> bool) l1 l2,
    (forall a b, f a b = (g a b) && (h a b)) -> 
    all2 g l1 l2 /\ all2 h l1 l2 -> 
    all2 f l1 l2.
Proof.
  move => A B f g h l1.
  induction l1; move => l2 Hf Hgh.
  - destruct Hgh. inversion H. destruct l2 => //.
  - destruct Hgh.
    inversion H. destruct l2 => //.
    inversion H0.
    move/andP in H2. destruct H2.
    move/andP in H3. destruct H3.
    specialize (conj H2 H4) as H5.
    simpl. apply/andP. split.
    + specialize (Hf a b). rewrite Hf. apply/andP.
      split => //.
    + apply IHl1 => //.
Qed.

Lemma Forall2_nth_error: forall A B R (l1 : seq.seq A) (l2 : seq.seq B) n m k,
    List.Forall2 R l1 l2 ->
    List.nth_error l1 n = Some m ->
    List.nth_error l2 n = Some k ->
    R m k.
Proof.
  move => A B R l1 l2 n m k HForall2 Hnth1 Hnth2.
  rewrite nth_error_lookup in Hnth1.
  rewrite nth_error_lookup in Hnth2.
  by eapply Forall2_lookup_lr.
Qed.

(* similar to Forall2_same_length_lookup_2
Forall2_same_length_lookup_2:
  ∀ (A B : Type) (P : A → B → Prop) (l : seq.seq A) (k : seq.seq B),
    length l = length k
    → (∀ (i : nat) (x : A) (y : B), l !! i = Some x → k !! i = Some y → P x y) → Forall2 P l k
*)
Lemma Forall2_lift: forall A B (R : A -> B -> Prop) (l1 : seq.seq A) (l2 : seq.seq B),
    List.length l1 = List.length l2 -> 
    (forall n m k,
    List.nth_error l1 n = Some m -> 
    List.nth_error l2 n = Some k ->
    R m k) ->
    List.Forall2 R l1 l2.
Proof.
  move => A B R l1 l2 Hlen HR.
  apply Forall2_same_length_lookup_2 => //.
  move => i x y Hl1 Hl2.
  rewrite <- nth_error_lookup in Hl1.
  rewrite <- nth_error_lookup in Hl2.
  by eapply HR.
Qed.

Lemma nth_error_Some_length:
  forall A (l : seq.seq A) (i : nat) (m : A),
  nth_error l i = Some m -> 
  i < length l.
Proof.
  move => A l i m H1.
  assert (H2 : nth_error l i ≠ None) by rewrite H1 => //.
  by apply List.nth_error_Some in H2.
Qed.

Lemma nth_error_same_length_list:
  forall (A B : Type) (l1 : seq.seq A) (l2 : seq.seq B) (i : nat) (m : A),
     length l1 = length l2 ->
     nth_error l1 i = Some m -> 
     exists n, nth_error l2 i = Some n.
Proof.
  move => A B l1 l2 i m Hlen Hl1.
  apply nth_error_Some_length in Hl1.
  rewrite Hlen in Hl1.
  apply lookup_lt_is_Some_2 in Hl1.
  rewrite /is_Some in Hl1. destruct Hl1.
  exists x.
  by rewrite nth_error_lookup.
Qed.

Lemma gen_index_len offset len:
  length (gen_index offset len) = len.
Proof.
  unfold gen_index.
  rewrite imap_length.
  by rewrite repeat_length.
Qed.

Lemma gen_index_in n i offset len:
  (gen_index offset len) !! n = Some i  ->
  i < offset + len.
Proof.
  move => H.
  specialize (lookup_lt_Some _ _ _ H) as Hlen.
  rewrite gen_index_len in Hlen.
  specialize (gen_index_lookup offset _ _  Hlen) as H2.
  rewrite H2 in H. inversion H; subst.
  by apply plus_lt_compat_l.
Qed.

Lemma fold_left_preserve {A B: Type} (P: A -> Prop) (f: A -> B -> A) (l: list B) (acc: A) :
  P acc ->
  (forall (x:A) (act: B), P x -> P (f x act)) ->
  P (fold_left f l acc).
Proof.
  rewrite -fold_left_rev_right.
  revert acc.
  induction l;simpl;auto.
  intros acc Ha Hnext.
  rewrite foldr_snoc /=. apply IHl =>//. 
  apply Hnext=>//.
Qed. 

Let functions_agree := @functions_agree host_function.

Lemma functions_agree_aux s_funcs funcs f tf: 
  functions_agree s_funcs f tf ->
  functions_agree (List.app s_funcs funcs) f tf.
Proof.
  rewrite /functions_agree /typing.functions_agree.
  move/andP => [H1 H2]. move/eqP in H2.
  apply/andP. split.
  + (* f < length (s_funcs [::func])  *)
    rewrite app_length.
    by rewrite ssrnat.ltn_addr.
  + (* option_map cl_type (List.nth_error (s_funcs [::func]) f) == Some tf *)
    apply/eqP.
    rewrite <-H2.
    apply f_equal.
    apply nth_error_app1.
    by apply/ssrnat.ltP.
Qed.

Lemma globals_agree_aux s_globs globs n tg: 
  globals_agree s_globs n tg ->
  globals_agree (s_globs ++ globs) n tg.
Proof.
  rewrite /globals_agree.
  move/andP => [H1 H2]. move/eqP in H2.
  apply/andP. split.
  + rewrite app_length.
    by rewrite ssrnat.ltn_addr.
  + apply/eqP.
    rewrite <- H2.
    apply f_equal.
    apply nth_error_app1.
    by apply/ssrnat.ltP.
Qed.

Lemma tabi_agree_aux s_tabs tabs n tt:
  tabi_agree s_tabs n tt -> 
  tabi_agree (s_tabs ++ tabs) n tt.
Proof.
  rewrite /tabi_agree.
  move/andP => [H1 H2].
  apply/andP. split.
  + rewrite app_length.
    by rewrite ssrnat.ltn_addr.
  + assert (H: nth_error (s_tabs ++ tabs) n = nth_error s_tabs n).
    { apply nth_error_app1. by apply/ssrnat.ltP. }
    by rewrite -> H.
Qed.

Lemma memi_agree_aux s_mems mems n tm:
  memi_agree s_mems n tm -> 
  memi_agree (s_mems ++ mems) n tm.
Proof.
  rewrite /memi_agree.
  move/andP => [H1 H2].
  apply/andP. split.
  + rewrite app_length.
    by rewrite ssrnat.ltn_addr.
  + assert (H: nth_error (s_mems ++ mems) n = nth_error s_mems n).
    { apply nth_error_app1. by apply/ssrnat.ltP. }
    by rewrite -> H.
Qed.


Let cl_type_check_single := @cl_type_check_single host_function.

Lemma cl_type_check_single_aux s_funcs s_tables s_mems s_globals func funcs tabs mems globs:
  cl_type_check_single {| s_funcs := s_funcs; s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |} func ->
  cl_type_check_single {| s_funcs := s_funcs ++ funcs; 
                          s_tables := s_tables ++ tabs;
                          s_mems := s_mems ++ mems;
                          s_globals := s_globals ++ globs|} func.
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
    - (* functions_agree *)
      eapply all2_forward.
      apply functions_agree_aux.
      by exact Hfunc.
    - (* globals_agree *)
      eapply all2_forward.
      apply globals_agree_aux.
      by exact Hglb.
    - (* tabi_agree *)
      eapply all2_forward.
      apply tabi_agree_aux.
      by exact Htab.
    - (* memi_agree *)
      eapply all2_forward.
      apply memi_agree_aux.
      by exact Hmem.
  + (* cl_typing_host *)
    inversion Hcl_typing; subst.
    by apply cl_typing_host.
Qed.

Let tab_agree := @tab_agree host_function.

Lemma tab_agree_aux s_funcs s_tables s_mems s_globals tab funcs tabs mems globs:
  tab_agree {| s_funcs := s_funcs; s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |} tab ->
  tab_agree {| s_funcs := s_funcs ++ funcs;
               s_tables := s_tables ++ tabs;
               s_mems := s_mems ++ mems;
               s_globals := s_globals ++ globs |} tab .
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
    rewrite size_cat. by rewrite ssrnat.ltn_addr.
    (* forall tabcl_agree tl *)
    apply IH. exact Htl.
  - (* tabsize_agree table *)
    assumption.
Qed.


Lemma external_typing_aux s v_imps t_imps:
  Forall2 (instantiation.external_typing host_function s) v_imps t_imps -> 
  length (ext_funcs v_imps) = length (ext_t_funcs t_imps) /\
  length (ext_globs v_imps) = length (ext_t_globs t_imps) /\
  length (ext_tabs v_imps) = length (ext_t_tabs t_imps) /\
  length (ext_mems v_imps) = length (ext_t_mems t_imps).
Proof.
  generalize t_imps.
  induction v_imps as [| v_imp v_imps' IH ].
  - move => t_imps' H.
    apply Forall2_length in H.
    simpl in H. symmetry in H.
    apply nil_length_inv in H.
    by rewrite H.
  - clear t_imps. move => t_imps H.
    inversion H; subst.
    rewrite /ext_funcs /ext_t_funcs.
    repeat split; inversion H2; subst; simpl; f_equal; by apply IH.
Qed.

Lemma tab_agree_from_typing mod_tables s_tabs s :
  all module_tab_typing mod_tables -> 
  s_tabs = (λ '{| tt_limits := {| lim_min := min; lim_max := maxo |} |},
               {| table_data := repeat None (ssrnat.nat_of_bin min); table_max_opt := maxo |})
                 <$> map (λ t : module_table, modtab_type t) mod_tables ->
  Forall (typing.tab_agree (host_function:=host_function) s) s_tabs.
Proof.
  move => HTabType Heqs_tabs_new.
  rewrite List.Forall_forall => ti Hin.
      
  rewrite -> Heqs_tabs_new in Hin.
  eapply List.In_nth_error in Hin.
  destruct Hin as [n Hnth].
  rewrite Coqlib.list_map_nth in Hnth.
  rewrite /Coqlib.option_map in Hnth.
  destruct (nth_error (map (λ t : module_table, modtab_type t) mod_tables) n) eqn: Heqt => //=.
  inversion Hnth. clear Hnth.
  rename H0 into Heq_ti.

  assert (Hex_tab: exists tab, nth_error mod_tables n = Some tab).
  {
    eapply nth_error_same_length_list with (l1 := (map (λ t : module_table, modtab_type t) mod_tables)) => //.
    by rewrite map_length.
  }
  destruct Hex_tab as [tab Htab].

  rewrite /module_tab_typing in HTabType.
  eapply list_all_forall in HTabType; last by apply Coqlib.nth_error_in in Htab.

  apply map_nth_error with (f := (λ t : module_table, modtab_type t)) in Htab.
  rewrite Heqt in Htab.
  inversion Htab. 
  rewrite <- H0 in HTabType. rewrite <- H0.
  clear Htab H0.

  rewrite /limit_typing in HTabType.

  destruct t. simpl in HTabType.
  destruct tt_limits.

  move/andP in HTabType. destruct HTabType as [Hmax Hmin].

  rewrite /typing.tab_agree. simpl.
  split.
  * (* tabcl_agree *)
    apply Forall_forall => lim Hin.
    apply repeat_spec in Hin.
    rewrite /tabcl_agree.
    by rewrite Hin.
  * (* tabsize_agree *)
    rewrite /tabsize_agree. simpl.
    destruct lim_max as [max | ] => //.
    rewrite /tab_size. simpl.
    rewrite repeat_length.
    destruct lim_min as [ | min].
    -- simpl.
       by apply ssrnat.leq0n.
    -- apply/ssrnat.leP.
       move/N.leb_spec0 in Hmin.
       repeat rewrite nat_bin.
       by lias.
Qed.

Lemma mem_agree_from_typing mod_mems s_mems:
  all module_mem_typing mod_mems ->
  s_mems = (λ '{| lim_min := min; lim_max := maxo |},
               {| mem_data := mem_make #00 match min with
                                      | 0%N => 0%N
                                      | N.pos q => N.pos (64 * 1024 * q)
                                      end;
                  mem_max_opt := maxo |}) <$> mod_mems ->
  Forall mem_agree s_mems.
Proof.
  move => HMemType Heqs_mems.

  rewrite List.Forall_forall => mi Hin.

  rewrite -> Heqs_mems in Hin.
  eapply List.In_nth_error in Hin.
  destruct Hin as [n Hnth].
  rewrite Coqlib.list_map_nth in Hnth.
  rewrite /Coqlib.option_map in Hnth.
  simpl in Hnth.
  destruct (nth_error mod_mems n) eqn: Heqm; last by rewrite Heqm in Hnth; inversion Hnth.
    
  rewrite /module_mem_typing in HMemType.
  eapply list_all_forall in HMemType; last by apply Coqlib.nth_error_in in Heqm.
  rewrite Heqm in Hnth.
  inversion Hnth; subst. clear Hnth.

  rewrite /limit_typing in HMemType.
  destruct m. simpl in HMemType.

  rewrite /mem_agree. simpl.
  destruct lim_max as [max | ] => //.
  rewrite /mem_size /operations.mem_length /memory_list.mem_length.
  simpl.
  rewrite repeat_length.
  rewrite N2Nat.id.
  rewrite /page_size.
  destruct lim_min as [ | min].
  + rewrite N.div_0_l => //.
    by apply N.le_0_l.
  + replace (N.pos (64 * 1024 * min)) with (N.mul (N.pos (64 * 1024)) (N.pos min)); last by simpl.
    rewrite N.mul_comm.
    replace (N.div (N.pos min * N.pos (64 * 1024)) (64 * 1024)) with (N.pos min); last by symmetry; apply N.div_mul.
    move/andP in HMemType. destruct HMemType as [_ HMemType].
    by apply/N.leb_spec0.
Qed.



Lemma external_typing_func s v_imps t_imps n v_imp t_imp:
  nth_error (map (λ '(Mk_funcidx i), i) (ext_funcs v_imps)) n = Some v_imp ->
  nth_error (ext_t_funcs t_imps) n = Some t_imp -> 
  instantiation.external_typing host_function s (MED_func (Mk_funcidx v_imp)) (ET_func t_imp) ->
  option_map cl_type (nth_error (s_funcs s) v_imp) = Some t_imp.
Proof.
  move => Hvimp Htimp Htyping.
  inversion Htyping; subst.
  by rewrite H3.
Qed.


Lemma external_typing_tab s v_imps t_imps n v_imp t_imp:
  nth_error (map (λ '(Mk_tableidx i), i) (ext_tabs v_imps)) n = Some v_imp ->
  nth_error (ext_t_tabs t_imps) n = Some t_imp -> 
  instantiation.external_typing host_function s (MED_table (Mk_tableidx v_imp)) (ET_tab t_imp) ->
  exists ti, (nth_error (s_tables s) v_imp = Some ti) /\
          tab_typing ti t_imp.
Proof.
  move => Hvimp Htimp Htyping.
  inversion Htyping; subst.
  exists ti. split => //=.
Qed.


Definition module_export_entity_relate (R : module_export_desc → extern_t → Prop) : Prop :=
  forall vi ti, R vi ti ->
           match vi with
           | MED_func _ => match ti with
                          | ET_func _ => True
                          | _ => False
                          end
           | MED_table _ => match ti with
                           | ET_tab _ => True
                           | _ => False
                           end                             
           | MED_mem _ => match ti with
                         | ET_mem _ => True
                         | _ => False
                         end
           | MED_global _ => match ti with
                            | ET_glob _ => True
                            | _ => False
                            end                            
           end.

Lemma external_typing_relate s :
  module_export_entity_relate (instantiation.external_typing host_function s).
Proof.
  rewrite /module_export_entity_relate => vi ti HR.
  inversion HR => //.
Qed.
  
Lemma vt_imps_funcs_lookup R v_imps t_imps fn ft (k: nat):
  module_export_entity_relate R ->
  Forall2 R v_imps t_imps ->
  (ext_funcs v_imps) !! k = Some fn ->
  (ext_t_funcs t_imps) !! k = Some ft ->
  exists n, v_imps !! n = Some (MED_func fn) /\ t_imps !! n = Some (ET_func ft).
Proof.
  move: t_imps k.
  induction v_imps; move => t_imps k HR HForall2 Hext_vl Hext_tl => //=.
  inversion HForall2; subst.
  specialize (HR a y H1) as H2.
  destruct a; destruct y; simpl in * => //.
  { destruct k => //.
    + exists 0. simpl in *.      
      inversion Hext_vl; subst.
      by inversion Hext_tl.
    + simpl in *.
      specialize (IHv_imps l' k HR H3 Hext_vl Hext_tl).
      destruct IHv_imps as [n Hvimp Htimp].
      by exists (S n).
  }
  all: specialize (IHv_imps l' k HR H3 Hext_vl Hext_tl).
  all: destruct IHv_imps as [n Hvimp Htimp].
  all: by exists (S n).
Qed.

Lemma vt_imps_funcs_relate v_imps t_imps fn ft (k: nat) R:
  module_export_entity_relate R ->
  Forall2 R v_imps t_imps ->
  (ext_funcs v_imps) !! k = Some fn ->
  (ext_t_funcs t_imps) !! k = Some ft ->
  R (MED_func fn) (ET_func ft).
Proof.
  move => HR HForall2 Hvl Htl.
  eapply vt_imps_funcs_lookup in Hvl => //.
  destruct Hvl as [n [Hvl' Htl']].
  rewrite -> Forall2_lookup in HForall2.
  specialize (HForall2 n).
  rewrite Hvl' Htl' in HForall2 => //.
  by inversion HForall2.
Qed.

Lemma external_typing_funcs_aux s n v_imps v_imp t_imps t_imp:
  Forall2 (instantiation.external_typing host_function s) v_imps t_imps ->
  nth_error (map (λ '(Mk_funcidx i), i) (ext_funcs v_imps)) n = Some v_imp ->
  nth_error (ext_t_funcs t_imps) n = Some t_imp -> 
  option_map cl_type (nth_error (s_funcs s) v_imp) = Some t_imp. 
Proof.
  move => Htyping Hmvimps_nth Htimps_nth.
  rewrite Coqlib.list_map_nth in Hmvimps_nth.
  rewrite /Coqlib.option_map in Hmvimps_nth.
  destruct (nth_error (ext_funcs v_imps) n) eqn: Hvimps_nth => //.
  destruct f as [fidx]. inversion Hmvimps_nth.
  rewrite <- H0 in *. clear Hmvimps_nth H0.
  rewrite nth_error_lookup in Htimps_nth.
  rewrite nth_error_lookup in Hvimps_nth.
  specialize (external_typing_relate s) as HR.
  specialize (vt_imps_funcs_relate _ _ _ _ _ _ HR Htyping Hvimps_nth Htimps_nth) as Htyping_n.
  inversion Htyping_n; subst.
  rewrite /option_map.
  by rewrite H3.
Qed.

Lemma vt_imps_globs_lookup v_imps t_imps gn gt (k: nat) R:
  module_export_entity_relate R ->
  Forall2 R v_imps t_imps ->
  (ext_globs v_imps) !! k = Some gn ->
  (ext_t_globs t_imps) !! k = Some gt ->
  exists n, v_imps !! n = Some (MED_global gn) /\ t_imps !! n = Some (ET_glob gt).
Proof.
  move: t_imps k.
  induction v_imps; move => t_imps k HR HForall2 Hext_vl Hext_tl => //=.
  inversion HForall2; subst.
  specialize (HR a y H1) as H2.
  destruct a; destruct y; simpl in * => //.
  4 : { destruct k => //.
        + exists 0. simpl in *.      
          inversion Hext_vl; subst.
          by inversion Hext_tl; subst.
        + simpl in *.
          specialize (IHv_imps l' k HR H3 Hext_vl Hext_tl).
          destruct IHv_imps as [n Hvimp Htimp].
          by exists (S n).
  }
  all: specialize (IHv_imps l' k HR H3 Hext_vl Hext_tl).
  all: destruct IHv_imps as [n Hvimp Htimp].
  all: by exists (S n).
Qed.

Lemma vt_imps_globs_relate v_imps t_imps gn gt (k: nat) R:
  module_export_entity_relate R ->
  Forall2 R v_imps t_imps ->
  (ext_globs v_imps) !! k = Some gn ->
  (ext_t_globs t_imps) !! k = Some gt ->
  R (MED_global gn) (ET_glob gt).
Proof.
  move => HR HForall2 Hvl Htl.
  eapply vt_imps_globs_lookup in Hvl => //.
  destruct Hvl as [n [Hvl' Htl']].
  rewrite -> Forall2_lookup in HForall2.
  specialize (HForall2 n).
  rewrite Hvl' Htl' in HForall2 => //.
  by inversion HForall2.
Qed.

Lemma external_typing_globs_aux s n v_imps v_imp t_imps t_imp:
  Forall2 (instantiation.external_typing host_function s) v_imps t_imps ->
  nth_error (map (λ '(Mk_globalidx i), i) (ext_globs v_imps)) n = Some v_imp ->
  nth_error (ext_t_globs t_imps) n = Some t_imp ->
  option_map (λ g : global, global_agree g t_imp) (nth_error (s_globals s) v_imp) = Some true. 
Proof.
  move => Htyping Hmvimps_nth Htimps_nth.
  rewrite Coqlib.list_map_nth in Hmvimps_nth.
  rewrite /Coqlib.option_map in Hmvimps_nth.
  destruct (nth_error (ext_globs v_imps) n) eqn: Hvimps_nth => //.
  destruct g as [gidx]. inversion Hmvimps_nth.
  rewrite <- H0 in *. clear Hmvimps_nth H0.
  rewrite nth_error_lookup in Htimps_nth.
  rewrite nth_error_lookup in Hvimps_nth.
  specialize (external_typing_relate s) as HR.
  specialize (vt_imps_globs_relate _ _ _ _ _ _ HR Htyping Hvimps_nth Htimps_nth) as Htyping_n.
  inversion Htyping_n; subst.
  rewrite /option_map.
  rewrite H3. by rewrite H4.
Qed.

Lemma vt_imps_tabs_lookup v_imps t_imps tn tt (k: nat) R:
  module_export_entity_relate R ->
  Forall2 R v_imps t_imps ->
  (ext_tabs v_imps) !! k = Some tn ->
  (ext_t_tabs t_imps) !! k = Some tt ->
  exists n, v_imps !! n = Some (MED_table tn) /\ t_imps !! n = Some (ET_tab tt).
Proof.
  move: t_imps k.
  induction v_imps; move => t_imps k HR HForall2 Hext_vl Hext_tl => //=.
  inversion HForall2; subst.
  specialize (HR a y H1) as H2.
  destruct a; destruct y; simpl in * => //.
  2 : { destruct k => //.
        + exists 0. simpl in *.      
          inversion Hext_vl; subst.
          by inversion Hext_tl; subst.
        + simpl in *.
          specialize (IHv_imps l' k HR H3 Hext_vl Hext_tl).
          destruct IHv_imps as [n Hvimp Htimp].
          by exists (S n).
  }
  all: specialize (IHv_imps l' k HR H3 Hext_vl Hext_tl).
  all: destruct IHv_imps as [n Hvimp Htimp].
  all: by exists (S n).
Qed.

Lemma vt_imps_tabs_relate v_imps t_imps tn tt (k: nat) R:
  module_export_entity_relate R ->
  Forall2 R v_imps t_imps ->
  (ext_tabs v_imps) !! k = Some tn ->
  (ext_t_tabs t_imps) !! k = Some tt ->
  R (MED_table tn) (ET_tab tt).
Proof.
  move => HR HForall2 Hvl Htl.
  eapply vt_imps_tabs_lookup in Hvl => //.
  destruct Hvl as [n [Hvl' Htl']].
  rewrite -> Forall2_lookup in HForall2.
  specialize (HForall2 n).
  rewrite Hvl' Htl' in HForall2 => //.
  by inversion HForall2.
Qed.

Lemma external_typing_tabs_aux s n v_imps v_imp t_imps t_imp:
  Forall2 (instantiation.external_typing host_function s) v_imps t_imps ->
  nth_error (map (λ '(Mk_tableidx i), i) (ext_tabs v_imps)) n = Some v_imp ->
  nth_error (ext_t_tabs t_imps) n = Some t_imp ->
  tabi_agree (s_tables s) v_imp t_imp.
Proof.
  move => Htyping Hmvimps_nth Htimps_nth.
  rewrite Coqlib.list_map_nth in Hmvimps_nth.
  rewrite /Coqlib.option_map in Hmvimps_nth.
  destruct (nth_error (ext_tabs v_imps) n) eqn: Hvimps_nth => //.
  destruct t as [tidx]. inversion Hmvimps_nth.
  rewrite <- H0 in *. clear Hmvimps_nth H0.
  rewrite nth_error_lookup in Htimps_nth.
  rewrite nth_error_lookup in Hvimps_nth.
  specialize (external_typing_relate s) as HR.
  specialize (vt_imps_tabs_relate _ _ _ _ _ _ HR Htyping Hvimps_nth Htimps_nth) as Htyping_n.
  inversion Htyping_n; subst.
  rewrite /option_map.
  rewrite /tabi_agree.
  apply/andP. split => //.
  by rewrite H3.
Qed.

Lemma vt_imps_mems_lookup v_imps t_imps tn tt (k: nat) R:
  module_export_entity_relate R ->
  Forall2 R v_imps t_imps ->
  (ext_mems v_imps) !! k = Some tn ->
  (ext_t_mems t_imps) !! k = Some tt ->
  exists n, v_imps !! n = Some (MED_mem tn) /\ t_imps !! n = Some (ET_mem tt).
Proof.
  move: t_imps k.
  induction v_imps; move => t_imps k HR HForall2 Hext_vl Hext_tl => //=.
  inversion HForall2; subst.
  specialize (HR a y H1) as H2.
  destruct a; destruct y; simpl in * => //.
  3 : { destruct k => //.
        + exists 0. simpl in *.      
          inversion Hext_vl; subst.
          by inversion Hext_tl; subst.
        + simpl in *.
          specialize (IHv_imps l' k HR H3 Hext_vl Hext_tl).
          destruct IHv_imps as [n Hvimp Htimp].
          by exists (S n).
  }
  all: specialize (IHv_imps l' k HR H3 Hext_vl Hext_tl).
  all: destruct IHv_imps as [n Hvimp Htimp].
  all: by exists (S n).
Qed.

Lemma vt_imps_mems_relate v_imps t_imps mn mt (k: nat) R:
  module_export_entity_relate R ->
  Forall2 R v_imps t_imps ->
  (ext_mems v_imps) !! k = Some mn ->
  (ext_t_mems t_imps) !! k = Some mt ->
  R (MED_mem mn) (ET_mem mt).
Proof.
  move => HR HForall2 Hvl Htl.
  eapply vt_imps_mems_lookup in Hvl => //.
  destruct Hvl as [n [Hvl' Htl']].
  rewrite -> Forall2_lookup in HForall2.
  specialize (HForall2 n).
  rewrite Hvl' Htl' in HForall2 => //.
  by inversion HForall2.
Qed.

Lemma external_typing_mems_aux s n v_imps v_imp t_imps t_imp:
  Forall2 (instantiation.external_typing host_function s) v_imps t_imps ->
  nth_error (map (λ '(Mk_memidx i), i) (ext_mems v_imps)) n = Some v_imp ->
  nth_error (ext_t_mems t_imps) n = Some t_imp ->
  memi_agree (s_mems s) v_imp t_imp.
Proof.
  move => Htyping Hmvimps_nth Htimps_nth.
  rewrite Coqlib.list_map_nth in Hmvimps_nth.
  rewrite /Coqlib.option_map in Hmvimps_nth.
  destruct (nth_error (ext_mems v_imps) n) eqn: Hvimps_nth => //.
  destruct m as [midx]. inversion Hmvimps_nth.
  rewrite <- H0 in *. clear Hmvimps_nth H0.
  rewrite nth_error_lookup in Htimps_nth.
  rewrite nth_error_lookup in Hvimps_nth.
  specialize (external_typing_relate s) as HR.
  specialize (vt_imps_mems_relate _ _ _ _ _ _ HR Htyping Hvimps_nth Htimps_nth) as Htyping_n.
  inversion Htyping_n; subst.
  rewrite /memi_agree.
  apply/andP. split => //.
  by rewrite H3.
Qed. 

Lemma alloc_module_sound s s' m v_imps t_imps v_exps t_exps inst gvs hs: 
  alloc_module host_function s m v_imps gvs (s', inst, v_exps) ->
  module_typing m t_imps t_exps ->
  Forall2 (instantiation.external_typing host_function s) v_imps t_imps -> 
  instantiate_globals host_function host_instance inst hs s' m gvs -> 
  store_typing s ->
  store_typing s'.
Proof.
  move => Halloc Hmod_typing Himp_typing Hinit_globs Hstore_typing.
  rewrite /module_typing in Hmod_typing.
  destruct m.
  destruct Hmod_typing as [fts [gts [HFuncType [HTabType [HMemType [HGlobType [HElemType [HDataType [HStartValid [HImpValid HExpValid]]]]]]]]]].

  rewrite /alloc_module in Halloc. simpl in *.
  remember (alloc_funcs host_function s mod_funcs inst) as s_ifs.
  destruct s_ifs as [s1 ifs].
  remember (alloc_tabs host_function s1 (map (λ t : module_table, modtab_type t) mod_tables)) as s_its.
  destruct s_its as [s2 its].
  remember (alloc_mems host_function s2 mod_mems) as s_ims.
  destruct s_ims as [s3 ims].
  remember (alloc_globs host_function s3 mod_globals gvs) as s_igs.
  destruct s_igs as [s_end igs].

  destruct inst. simpl in *.
  
  repeat (move/andP in Halloc; destruct Halloc as [Halloc ?]).
  move/eqP in H; subst.
  move/eqP in H0; subst.
  move/eqP in H1; subst.
  move/eqP in H2; subst.
  move/eqP in H3; subst.
  move/eqP in H4; subst.
  move/eqP in Halloc; subst.
  
  destruct s_end. destruct s. simpl in *. destruct Hstore_typing as [Hcl [Htab_agree Hmem_agree]].
  specialize (alloc_func_gen_index _ _ _ _ _ _ (symmetry Heqs_ifs)) as Hfuncidx.
  destruct Hfuncidx as [Hfunidx [Hfunc1 [Htab1 [Hmem1 Hglob1]]]]; simpl in *.
  specialize (alloc_tab_gen_index _ _ _ _ _ (symmetry Heqs_its)) as Htabidx.
  destruct Htabidx as [Htabidx [Htab2 [Hfunc2 [Hmem2 Hglob2]]]]; simpl in *.
  specialize (alloc_mem_gen_index _ _ _ _ _ (symmetry Heqs_ims)) as Hmemidx.
  destruct Hmemidx as [Hmemidx [Hmem3 [Hfunc3 [Htab3 Hglob3]]]]; simpl in *.

  assert (Hgvs_len : length gvs = length mod_globals).
  {
    rewrite /instantiate_globals in Hinit_globs.
    simpl in Hinit_globs.
    apply Forall2_length in Hinit_globs.
    by symmetry in Hinit_globs.
  }
  specialize (alloc_glob_gen_index _ _ _ _ _ _ Hgvs_len (symmetry Heqs_igs)) as Hglobidx.
  destruct Hglobidx as [Hglobidx [Hglob4 [Hfunc4 [Htab4 Hmem4]]]]; simpl in *.
  
  rewrite <- Hfunc4 in *. rewrite <- Hfunc3 in *. rewrite <- Hfunc2 in *. rewrite -> Hfunc1 in *.
  rewrite <- Htab4 in *. rewrite <- Htab3 in *. rewrite -> Htab2 in *. rewrite <- Htab1 in *.
  rewrite <- Hmem4 in *. rewrite -> Hmem3 in *. rewrite <- Hmem2 in *. rewrite <- Hmem1 in *.
  rewrite -> Hglob4 in *. rewrite <- Hglob3 in *. rewrite <- Hglob2 in *. rewrite <- Hglob1 in *.

  clear Hfunc1 Hfunc2 Hfunc3 Hfunc4.
  clear Htab1 Htab2 Htab3 Htab4.
  clear Hmem1 Hmem2 Hmem3 Hmem4.
  clear Hglob1 Hglob2 Hglob3 Hglob4.
  clear Heqs_ifs Heqs_its Heqs_ims Heqs_igs.

  remember ((λ mf : module_func, gen_func_instance _ mf _) <$> mod_funcs) as s_funcs_new.
  remember (_ <$> map _ mod_tables) as s_tabs_new.
  remember ((λ '{| lim_min := min; lim_max := maxo |}, _) <$> mod_mems) as s_mems_new.
  remember (_ <$> combine mod_globals gvs) as s_globs_new.

  split.
  - (* cl_type *)
    rewrite -> List.Forall_app.
    split.
    + (* forall cl_type_check s' s_funcs0 *)
      apply List.Forall_forall => fc Hin.
      apply cl_type_check_single_aux.
      rewrite -> List.Forall_forall in Hcl.
      by apply Hcl.
    + (* forall cl_type_check s' s_funcs_new *)
      rewrite List.Forall_forall => fc Hin.

      rewrite -> Heqs_funcs_new in Hin.
      rewrite /gen_func_instance in Hin.
      simpl in Hin.
      eapply List.In_nth_error in Hin.
      destruct Hin as [n Hnth].
      rewrite Coqlib.list_map_nth in Hnth.
      rewrite /Coqlib.option_map in Hnth.
      destruct (nth_error mod_funcs n) eqn: Heqm => //=.
      inversion Hnth. clear Hnth.
      rename H0 into Heq_fc. 

      assert (Hex_ty: exists ty, List.nth_error fts n = Some ty).
      {
        rewrite nth_error_lookup in Heqm.
        specialize (Forall2_lookup_l _ _ _ _ _  HFuncType Heqm) as H1.
        destruct H1 as [ty [Heqy _]].
        rewrite <- nth_error_lookup in Heqy.
        by exists ty.
      }

      destruct Hex_ty as [ty Hty].
      specialize (Forall2_nth_error _ _ _ _ _ n m ty HFuncType Heqm Hty) as HFuncType_n.

      rewrite /typing.cl_type_check_single.
      destruct ty as [t1s t2s].
      exists (Tf t1s t2s).
      remember (Build_t_context mod_types _ _ _ _ nil nil None) as C.

      eapply cl_typing_native with (C := C) => //=.
      * (* inst_typing *)
        destruct C.
        destruct tc_local => //=.
        destruct tc_label => //=.
        destruct tc_return => //=.

        inversion HeqC; subst.
        clear n m Heqm t1s t2s Hty HFuncType_n.

        specialize (external_typing_aux _ _ _ Himp_typing) as Hvimps_len.
        destruct Hvimps_len as [Himps_func_len [Himps_glob_len [Himps_tab_len Himps_mem_len]]].
        
        apply/andP. split.
        apply/andP. split.
        apply/andP. split.
        apply/andP. split => //=.

        -- (* functions_agree *) 
           rewrite /gen_func_instance /typing.functions_agree. simpl.
           eapply all2_and with (g := (fun n0 f => ssrnat.leq (S n0) _)) => //.
           assert (Hifs_len: length (map (λ '(Mk_funcidx i), i) ifs) = length mod_funcs).
           {
             rewrite <- gen_index_len with (offset := (length s_funcs0)).
             by rewrite Hfunidx.
           }
           specialize (external_typing_aux _ _ _ Himp_typing) as Hvimps_len.
           split.
           ++ (* n < length fs *)
              rewrite <- Forall2_all2. 
              rewrite List.app_length.
              rewrite fmap_length.
              apply Forall_Forall2_l.
              ** (* v_imps & t_imps *)
                 rewrite map_length.
                 repeat rewrite -> app_length.
                 rewrite Himps_func_len. f_equal.
                 replace (length ifs) with (length (map (λ '(Mk_funcidx i), i) ifs)); last by rewrite map_length.
                 rewrite Hifs_len.
                 by apply Forall2_length in HFuncType.
              ** rewrite map_app.
                 rewrite Forall_app.
                 split.
                 *** rewrite Forall_lookup.
                     move => i n0 Hnth _.
                     
                     rewrite ->  Forall2_lookup in Himp_typing.
                     rewrite map_fmap in Hnth.
                     rewrite list_lookup_fmap in Hnth.
                     destruct (ext_funcs v_imps !! i) eqn: Hvimp => //.
                     simpl in Hnth.
                     apply ext_funcs_lookup_exist in Hvimp.
                     destruct Hvimp as [k Hvimp].
                     specialize (Himp_typing k).
                     rewrite Hvimp in Himp_typing.
                     inversion Himp_typing; subst.
                     destruct f.
                     inversion Hnth; subst.
                     inversion H1; subst.
                     simpl in H2.
                     apply/ssrnat.ltP. move/ssrnat.ltP in H2.
                     by lias.
                 *** rewrite Hfunidx.
                     rewrite Forall_lookup => n i H _.
                     apply gen_index_in in H.
                     by apply/ssrnat.ltP.
           ++ (* cl_type *)
              rewrite <- Forall2_all2.
              rewrite map_app.
              apply Forall2_app.
              ** apply Forall2_lift; first by rewrite map_length.
                 move => i v_imp t_imp Hvimps_nth Htimps_nth.
                 apply/eqP. 
                 specialize (external_typing_funcs_aux _ _ _ _ _ _ Himp_typing Hvimps_nth Htimps_nth) as Hext_typing. simpl in Hext_typing.
                 rewrite <- Hext_typing.
                 f_equal.
                 apply nth_error_app1.
                 rewrite /option_map in Hext_typing.
                 destruct (nth_error s_funcs0 v_imp) eqn: Hfuncs_nth => //.
                 by eapply nth_error_Some_length.
              ** rewrite /module_func_typing in HFuncType. simpl in HFuncType.
                 apply Forall2_lift.
                 *** (* length (map (λ '(Mk_funcidx i), i) ifs) = length fts *)
                     rewrite Hifs_len.
                     by apply Forall2_length in HFuncType.
                 *** move => i fidx ft Hidxs_nth Hfts_nth.
                     
                     specialize (nth_error_same_length_list _ _ _ _ _ _ Hifs_len Hidxs_nth) as Hfuncs_nth.
                     destruct Hfuncs_nth as [func Hfuncs_nth].
                     specialize (Forall2_nth_error _ _ _ _ _ _ _ _ HFuncType Hfuncs_nth Hfts_nth) as HFuncType_n.
                     simpl in HFuncType_n.
                     destruct func. destruct modfunc_type. destruct ft as [t1s t2s].
                     destruct HFuncType_n as [_ [Hft _]].
                     
                     rewrite Hfunidx in Hidxs_nth.
                     rewrite nth_error_lookup in Hidxs_nth.
                     rewrite gen_index_lookup in Hidxs_nth; last by eapply nth_error_Some_length.
                     inversion Hidxs_nth; subst. clear Hidxs_nth.

                     rewrite nth_error_app2; last by lias.
                     replace (length s_funcs0 + i - length s_funcs0) with i; last by lias.

                     rewrite nth_error_lookup.
                     rewrite list_lookup_fmap.
                     rewrite nth_error_lookup in Hfuncs_nth.
                     by rewrite Hfuncs_nth.
        -- (* globals_agree *)
           rewrite /globals_agree.
           eapply all2_and with (g := (fun n tg => ssrnat.leq (S n) _)) => //.
           assert (Higs_len: length (map (λ '(Mk_globalidx i), i) igs) = length mod_globals).
           {
             rewrite <- gen_index_len with (offset := length s_globals0).
             by rewrite Hglobidx.
           }
           assert (Hcombine_len: length (combine mod_globals gvs) = length mod_globals).
           {
             rewrite combine_length.
             rewrite Hgvs_len.
             by rewrite Nat.min_id.
           }
           split.
           ++ (* n < length gs *)
             rewrite <- Forall2_all2.
             rewrite List.app_length.
             rewrite fmap_length.
             apply Forall_Forall2_l.
             ** rewrite map_length.
                repeat rewrite -> app_length.
                rewrite Himps_glob_len. f_equal.
                replace (length igs) with (length (map (λ '(Mk_globalidx i), i) igs)); last by rewrite map_length.
                rewrite Higs_len.
                by apply Forall2_length in HGlobType.
             ** rewrite map_app.
                rewrite Forall_app.
                split.
                *** rewrite Forall_lookup.
                    move => i n0 Hnth _.
                    
                    rewrite map_fmap in Hnth.
                    rewrite list_lookup_fmap in Hnth.
                    destruct (ext_globs v_imps !! i) eqn: Hvimp => //.
                    simpl in Hnth.
                    apply ext_globs_lookup_exist in Hvimp.
                    destruct Hvimp as [k Hvimp].

                    rewrite -> Forall2_lookup in Himp_typing.
                    specialize (Himp_typing k).
                    rewrite Hvimp in Himp_typing.
                    inversion Himp_typing; subst.
                    
                    destruct g.
                    inversion Hnth; subst.
                    inversion H1; subst.
                    simpl in H2.
                    apply/ssrnat.ltP. move/ssrnat.ltP in H2.
                    by lias.
                *** rewrite Hglobidx.
                    rewrite Forall_lookup => i x H _.
                    apply gen_index_in in H.
                    rewrite Hcombine_len.
                    by apply/ssrnat.ltP.
           ++ (* global_agree *) 
              rewrite <- Forall2_all2.
              rewrite map_app.
              apply Forall2_app.
              ** apply Forall2_lift; first by rewrite map_length.
                 move => i v_imp t_imp Hvimps_nth Htimps_nth.
                 apply/eqP.
                 specialize (external_typing_globs_aux _ _ _ _ _ _ Himp_typing Hvimps_nth Htimps_nth) as Hext_typing. simpl in Hext_typing.
                 rewrite <- Hext_typing.
                 f_equal.
                 apply nth_error_app1.
                 rewrite /option_map in Hext_typing.
                 destruct (nth_error s_globals0 v_imp) eqn: Hglobs_nth => //.
                 by eapply nth_error_Some_length.
              ** rewrite /module_glob_typing in HGlobType. simpl in HGlobType.
                 apply Forall2_lift.
                 *** (* length (map (λ '(Mk_globalidx i), i) igs) = length gts *)
                     rewrite Higs_len.
                     by apply Forall2_length in HGlobType.
                 *** move => i gidx gt Hidxs_nth Hgts_nth.

                     specialize (nth_error_same_length_list _ _ _ _ _ _ Higs_len Hidxs_nth) as Hglobs_nth.
                     destruct Hglobs_nth as [glob Hglobs_nth].
                     specialize (Forall2_nth_error _ _ _ _ _ _ _ _ HGlobType Hglobs_nth Hgts_nth) as HGlobType_n.
                     simpl in HGlobType_n.
                     destruct glob.
                     destruct HGlobType_n as [_ [Hgt _]]. subst.

                     rewrite Hglobidx in Hidxs_nth.
                     rewrite nth_error_lookup in Hidxs_nth.
                     rewrite gen_index_lookup in Hidxs_nth; last by eapply nth_error_Some_length.
                     inversion Hidxs_nth; subst. clear Hidxs_nth.

                     rewrite nth_error_app2; last by lias.
                     replace (length s_globals0 + i - length s_globals0) with i; last by lias.
                     
                     rewrite nth_error_lookup.
                     rewrite list_lookup_fmap.

                     specialize (nth_error_same_length_list _ _ _ _ _ _ (symmetry Hgvs_len) Hglobs_nth) as Hgvs_nth.
                     destruct Hgvs_nth as [gv Hgvs_nth].
                     assert (Hcombine : (combine mod_globals gvs) !! i = Some ({| modglob_type := modglob_type; modglob_init := modglob_init |}, gv)).
                     {
                       rewrite <- nth_error_lookup.
                       rewrite -> nth_error_nth' with (d := ({| modglob_type := modglob_type; modglob_init := modglob_init |}, gv)); last by rewrite Hcombine_len; eapply nth_error_Some_length.
                       rewrite combine_nth => //.
                       by repeat erewrite nth_error_nth => //. 
                     }
                     rewrite Hcombine. simpl.
                     rewrite /global_agree. simpl.
                     apply/eqP. f_equal.
                     apply/andP. split => //.
                     apply/eqP.
                     
                     rewrite /instantiate_globals in Hinit_globs. simpl in Hinit_globs.
                     rewrite -> Forall2_lookup in Hinit_globs.
                     specialize (Hinit_globs i).
                     rewrite nth_error_lookup in Hglobs_nth.
                     rewrite nth_error_lookup in Hgvs_nth.
                     rewrite Hglobs_nth in Hinit_globs.
                     rewrite Hgvs_nth in Hinit_globs.
                     inversion Hinit_globs; subst. clear Hinit_globs.
                     simpl in H1.
                     
                     rewrite -> Forall2_lookup in HGlobType.
                     specialize (HGlobType i).
                     rewrite nth_error_lookup in Hgts_nth.
                     rewrite Hgts_nth in HGlobType.
                     rewrite Hglobs_nth in HGlobType.
                     inversion HGlobType; subst. clear HGlobType.

                     destruct H2 as [Hconst_exprs [_ Hbe_typing]].
                     specialize (const_exprs_impl host_function host_instance _ _ _ Hconst_exprs Hbe_typing) as Hexprs.
                     clear Hconst_exprs.
                     destruct Hexprs as [expr [Hexpr Hconst]].
                     rewrite /const_expr in Hconst. simpl in Hconst.
                     rewrite -> Hexpr in *.  clear Hexpr.
                     destruct expr; simpl in * => //.
                     { (* modglob_init = [BI_get_global i0] *)

                       (* [BI_get_global i0] ->* gv *)
                       apply reduce_trans_get_global in H1.
                       rewrite /sglob_val /sglob /sglob_ind in H1.
                       simpl in H1.
                       rewrite /option_map in H1.
                       destruct (option_bind _ _) eqn: Heq1 => //.
                       inversion H1.
                       rewrite <- H0 in *. clear H1 H0.
                       rewrite /option_bind in Heq1.
                       destruct (nth_error (map _ _) i0) eqn: Heq2 => //.

                       (* [BI_get_global i0] has type modglob_type *)
                       eapply Get_global_typing in Hbe_typing => //.
                       simpl in Hbe_typing.
                       destruct Hbe_typing as [ty [H1 [H2 _]]].
                       inversion H2; subst.
                       rewrite /option_map in H1.
                       destruct (nth_error (ext_t_globs t_imps) i0) eqn: Htl => //.

                       (* todo: create a lemma nth_error (map f l) i = f <$> l !! i*)
                       rewrite nth_error_lookup in Heq2.
                       rewrite map_fmap in Heq2.
                       rewrite list_lookup_fmap in Heq2.
                       assert (Heq3: (ext_globs v_imps ++ igs) !! i0 = ext_globs v_imps !! i0).
                       { apply nth_error_Some_length in Htl.
                         rewrite <- Himps_glob_len in Htl.
                         eapply nth_error_app1 with (l' := igs) in Htl.
                         by repeat rewrite nth_error_lookup in Htl.
                       }
                       replace ((ext_globs v_imps ++ igs) !! i0) with (ext_globs v_imps !! i0) in Heq2.
                       rewrite <- list_lookup_fmap in Heq2.
                       rewrite <- map_fmap in Heq2.
                       rewrite <- nth_error_lookup in Heq2.
                       specialize (external_typing_globs_aux _ _ _ _ _ _ Himp_typing Heq2 Htl) as Htyping. simpl in Htyping.
                       rewrite /option_map in Htyping.
                       destruct (nth_error s_globals0 g0) eqn: Heq4 => //.
                       inversion Htyping. clear Htyping.
                       rewrite /global_agree in H0.
                       specialize (nth_error_Some_length _ _ _ _ Heq4) as Hg0.
                       rewrite nth_error_lookup lookup_app_l in Heq1 => //.
                       rewrite <- nth_error_lookup in Heq1.
                       rewrite Heq4 in Heq1. inversion Heq1; subst.
                       inversion H1; subst.
                       move/andP in H0. destruct H0 as [_ H0].
                       by move/eqP in H0.                     
                     }
                     { (* modglob_init = [BI_const v] *)
                       apply reduce_trans_const in H1. subst.
                       apply BI_const_typing in Hbe_typing.
                       simpl in Hbe_typing. by inversion Hbe_typing.
                     }
        -- (* tabi_agree *) 
           rewrite <- Forall2_all2.
           rewrite map_app.
           apply Forall2_app.
           ** apply Forall2_lift; first by rewrite map_length.
              move => i v_imp t_imp Hvimps_nth Htimps_nth.
              specialize (external_typing_tabs_aux _ _ _ _ _ _ Himp_typing Hvimps_nth Htimps_nth) as Hext_typing. simpl in Hext_typing.
              by eapply tabi_agree_aux.
           ** assert (Hits_len: length (map (λ '(Mk_tableidx i), i) its) = length mod_tables).
              {
                rewrite <- gen_index_len with (offset := length s_tables0).
                rewrite Htabidx.
                by rewrite map_length.
              }
              apply Forall2_lift.
              *** rewrite Hits_len.
                  by rewrite map_length.
              *** move => i tidx tt Hidxs_nth Htts_nth.

                  rewrite Htabidx in Hidxs_nth.
                  rewrite nth_error_lookup in Hidxs_nth.
                  rewrite gen_index_lookup in Hidxs_nth; last by eapply nth_error_Some_length.
                  inversion Hidxs_nth; subst. clear Hidxs_nth.
                  
                  rewrite /tabi_agree.
                  apply/andP. split.

                  {
                    apply /ssrnat.ltP.
                    rewrite app_length.
                    apply plus_lt_compat_l.
                    rewrite fmap_length.
                    by eapply nth_error_Some_length.
                  }
                  {
                    rewrite nth_error_app2; last by lias.
                    replace (length s_tables0 + i - length s_tables0) with i; last by lias.

                    rewrite nth_error_lookup.
                    rewrite list_lookup_fmap.
                    rewrite <- nth_error_lookup.
                    rewrite Htts_nth.
                    
                    destruct tt. destruct tt_limits. simpl.
                    rewrite /tab_typing. simpl.
                    apply/andP. split => //=.
                    rewrite /tab_size. simpl. 
                    by rewrite repeat_length.
                  }
        -- (* memi_agree *)
           rewrite <- Forall2_all2.
           rewrite map_app.
           assert (Hims_len: length (map (λ '(Mk_memidx i), i) ims) = length mod_mems).
           {
             rewrite <- gen_index_len with (offset := length s_mems0).
             by rewrite Hmemidx.
           }
           apply Forall2_app.
           ** apply Forall2_lift; first by rewrite map_length.
              move => i v_imp t_imp Hvimps_nth Htimps_nth.
              specialize (external_typing_mems_aux _ _ _ _ _ _ Himp_typing Hvimps_nth Htimps_nth) as Hext_typing. simpl in Hext_typing.
              by eapply memi_agree_aux.            
           ** rewrite /module_mem_typing in HMemType.
              apply Forall2_lift; first by rewrite Hims_len.
              move => i midx mt Hidxs_nth Hmts_nth.

              rewrite Hmemidx in Hidxs_nth.
              rewrite nth_error_lookup in Hidxs_nth.
              rewrite gen_index_lookup in Hidxs_nth; last by eapply nth_error_Some_length.
              inversion Hidxs_nth; subst. clear Hidxs_nth.

              rewrite /memi_agree.
              apply/andP. split.

              {
                apply /ssrnat.ltP.
                rewrite app_length.
                apply plus_lt_compat_l.
                rewrite fmap_length.
                by eapply nth_error_Some_length.
              }
              {
                rewrite nth_error_app2; last by lias.
                replace (length s_mems0 + i - length s_mems0) with i; last by lias.

                rewrite nth_error_lookup.
                rewrite list_lookup_fmap.
                rewrite <- nth_error_lookup.
                (* todo: nth_error (f <$> l) i = f <$> nth_error l i *)
                rewrite Hmts_nth.

                destruct mt. 
                rewrite /mem_typing. simpl.
                apply/andP. split => //=.
                rewrite /mem_size /operations.mem_length /memory_list.mem_length. simpl.
                destruct lim_min => //.
                rewrite /page_size. simpl.
                rewrite repeat_length.
                rewrite positive_nat_N. 

                assert (Hdiv: N.div (N.pos (64 * 1024 * p)) (N.pos (64 * 1024)) = N.pos p).
                {
                  replace (N.pos (64 * 1024 * p)) with (N.mul (N.pos (64 * 1024)) (N.pos p)); last by simpl.
                  rewrite N.mul_comm.
                  by apply N.div_mul => //.
                }
                rewrite Hdiv.
                by rewrite N.leb_refl.
              }
      * (* the type index of function m references type (Tf t1s t2s) in mod_types *)
        rewrite /module_func_typing in HFuncType_n.
        destruct m. simpl.
        destruct modfunc_type as [i].
        destruct HFuncType_n as [_ [Hnth _]].
        move/eqP in Hnth.
        rewrite <- Hnth.
        by inversion HeqC.
      * (* be_typing *)
        rewrite /module_func_typing in HFuncType_n.
        rewrite /upd_local_label_return.
        destruct m. simpl.
        destruct modfunc_type.
        destruct HFuncType_n as [_ [_ Hbe_typing]].
        by apply Hbe_typing. 
  split.
  - (* tab_agree *)
    rewrite Forall_app.
    split.
    + (* forall tab_agree s' s_tables0 *)
      apply Forall_forall => ti Hin.
      rewrite -> Forall_forall in Htab_agree.
      apply tab_agree_aux.
      by apply Htab_agree.
    + (* forall tab_agree s' s_tabs_new *)
      by eapply tab_agree_from_typing.
  - (* mem_agree *)
    rewrite Forall_app.
    split.
    + (* forall mem_agree s_mems0 *)
      by exact Hmem_agree.
    + (* forall mem_agree s_mems_new *)
      by eapply mem_agree_from_typing.
Qed.

Lemma init_tab_preserve ws inst e_inits melem ws':
  init_tab host_function ws inst e_inits melem = ws' ->
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  move => Hinit.
  rewrite /init_tab in Hinit.
  destruct ws'.
  destruct (nth _ _) eqn: Hl => /=.
  by inversion Hinit.
Qed.

Lemma init_tabs_preserve ws inst e_inits melem ws':
  init_tabs host_function ws inst e_inits melem = ws' ->
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  move => Hinit.
  unfold init_tabs in Hinit.
  rewrite - Hinit.
  apply fold_left_preserve => //.
  move => x [n me] Heq.
  destruct ws, x.
  simpl in *.
  destruct Heq as [-> [-> ->]].
  unfold init_tab => /=.
  by destruct (nth _ _) eqn:Hl => /=.
Qed.

Lemma insert_at_insert {T: Type} v n (l: list T):
  n < length l ->
  insert_at v n l = <[ n := v ]> l.
Proof.
  move : v n.
  induction l; intros; simpl in H; destruct n => /=; try by inversion H.
  - specialize (IHl v n).
    unfold insert_at.
    simpl.
    f_equal.
    rewrite <- IHl; last by lias.
    by unfold insert_at.
Qed.

Lemma init_tab_preserve_typing s inst mod_elem e_off:
  store_typing s ->
  Forall (λ n : nat, n < length (s_funcs s)) (inst_funcs inst) ->
  (λ s : seq.seq funcidx, all (λ '(Mk_funcidx i), ssrnat.leq (S i) (length (inst_funcs inst))) s) (modelem_init mod_elem) -> 
  match nth_error (inst_tab inst) match modelem_table mod_elem with
                                  | Mk_tableidx i => i
                                  end with
  | Some i =>
      match nth_error (s_tables s) i with
      | Some ti => (N_of_int e_off + N.of_nat (length (modelem_init mod_elem)) <=? N.of_nat (length (table_data ti)))%N
      | None => false
      end
  | None => false
  end ->
  store_typing (init_tab host_function s inst (Z.to_nat (Wasm_int.Int32.intval e_off)) mod_elem).
Proof.
  move => Htyping Hinst_typing Hinit_typing Hbound.
  
  rewrite /init_tab.
  destruct mod_elem. simpl in *.
  destruct modelem_table.
  destruct (nth_error (inst_tab inst) n) as [taddr | ] eqn: Htaddr => //.
  destruct (nth_error (s_tables s) taddr) as [tinst | ] eqn: Htinst => //.

  rewrite -> nth_error_nth with (x := taddr) => //.
  erewrite -> nth_error_nth => //.

  destruct tinst. simpl in Hbound.

  rewrite /store_typing /typing.store_typing in Htyping.
  destruct s. simpl in *.
  destruct Htyping as [Hcl_type [Htab_agree Hmem_agree]].
  assert (Hle: taddr < length s_tables). { by eapply nth_error_Some_length. }.
  rewrite insert_at_insert => //.
  split.
  - (* cl_type_check *)
    apply Forall_lookup_2 => i fc Hfuns_nth.
    eapply Forall_lookup_1 in Hcl_type => //.
    
    rewrite /typing.cl_type_check_single in Hcl_type.
    destruct Hcl_type as [tf Hcl_typing].
    rewrite /typing.cl_type_check_single.
    exists tf.

    eapply store_extension_cl_typing => //.
    rewrite /store_extension. simpl.
    apply/andP. split. 2 : { by apply all2_glob_extension_same. }.
    apply/andP. split. 2 : { by apply all2_mem_extension_same. }.
    apply/andP. split; first by apply/eqP.

    rewrite /tab_extension.
    rewrite <- Forall2_all2.
    (* clear - host host_function host_function Hbound Htaddr Htinst Hle. *)
    rewrite Forall2_lookup => taddr'.
    destruct (decide (taddr = taddr')) as [Heq | Hneq].
    + (* taddr = taddr' *)
      rewrite <- Heq.
      rewrite list_lookup_insert => //.
      
      rewrite nth_error_lookup in Htinst.
      rewrite Htinst.

      apply Some_Forall2. simpl.
      apply/andP. split => //.
      rewrite /tab_size. simpl.

      repeat rewrite app_length.
      rewrite take_length map_length drop_length.

      replace (Z.to_nat (Wasm_int.Int32.intval e_off) `min` length table_data) with (Z.to_nat (Wasm_int.Int32.intval e_off)).
      2 : { move/N.leb_spec0 in Hbound.
            rewrite /N_of_int in Hbound.
            by lias. }
      by lias.
    + (* taddr /= taddr' *)
      rewrite list_lookup_insert_ne => //.
      destruct (s_tables !! taddr').
      * (* Some *)
        apply Some_Forall2.
        apply/andP. by split => //.
      * (* None *)
        by apply None_Forall2.
    split.
  - (* tab_agree *)
    clear Hcl_type Hmem_agree.
    rewrite /typing.tab_agree in Htab_agree.
    rewrite -> Forall_lookup in Htab_agree.
    rewrite /typing.tab_agree.
    apply Forall_lookup_2 => taddr' tinst' Htinst'.    
    destruct (decide (taddr = taddr')) as [Heq | Hneq].
    + (* taddr = taddr' *)
      rewrite nth_error_lookup in Htinst.
      specialize (Htab_agree taddr {| table_data := table_data; table_max_opt := table_max_opt |} Htinst).
      destruct Htab_agree as [Htabcl Htabsize]. simpl in Htabcl.
      rewrite <- Heq in Htinst'.
      rewrite list_lookup_insert in Htinst' => //.
      inversion Htinst'; subst. clear Htinst'.
      simpl. split.
      * (* tabcl_agree *)
        apply Forall_app_2.
        ** (* Forall tabcl_agree (take ... table_data) *)
           by apply Forall_take.
        apply Forall_app_2.
        ** (* Forall tabcl_agree (the new written table)*)
           rewrite /tabcl_agree. simpl.
           apply Forall_lookup_2 => i addr Haddr.
           rewrite list_lookup_fmap in Haddr.
           destruct (modelem_init !! i) eqn: Hinit_nth => //.
           destruct f as [fidx]. simpl in Haddr.
           inversion Haddr; subst. clear Haddr.
           destruct (nth_error (inst_funcs inst) fidx) eqn: Hinst_nth => //.
           rewrite nth_error_lookup in Hinst_nth.
           eapply Forall_lookup_1 in Hinst_typing => //.
           apply/ssrnat.ltP. 
           by rewrite <- length_is_size.
        ** (* Forall tabcl_agree (drop ... table_data) *)
           by apply Forall_drop.
      * (* tabsize_agree *)
        rewrite /tabsize_agree /tab_size.
        simpl.

        rewrite /tabsize_agree /tab_size in Htabsize.
        simpl in Htabsize.
        destruct table_max_opt => //.
        
        repeat rewrite app_length.
        rewrite take_length map_length drop_length.

        rewrite /N_of_int in Hbound.
        move/N.leb_spec0 in Hbound. 
        replace (Z.to_nat (Wasm_int.Int32.intval e_off) `min` length table_data) with (Z.to_nat (Wasm_int.Int32.intval e_off)).
        2 : { by lias. }
        rewrite Nat.add_assoc.
        replace (ssrnat.addn (Z.to_nat (Wasm_int.Int32.intval e_off)) (length modelem_init)) with (Z.to_nat (Wasm_int.Int32.intval e_off) + length modelem_init).
        2 : { by lias. }
        
        rewrite le_plus_minus_r => //.
        by lias.
    + (* taddr /= taddr' *)
      rewrite list_lookup_insert_ne in Htinst' => //.
      specialize (Htab_agree taddr' tinst' Htinst').
      destruct Htab_agree as [Htabcl Htabsize].

      destruct tinst' as [table_data' table_max_opt'].
      simpl in *.
      
      split => //.
  - (* mem_agree *)
    exact Hmem_agree.
Qed.

Lemma init_tabs_preserve_typing s s' inst m x:
  store_typing s ->
  Forall (λ n : nat, n < length (s_funcs s)) (inst_funcs inst) ->
  Forall
    (λ s : seq.seq funcidx, all (λ '(Mk_funcidx i), ssrnat.leq (S i) (length (inst_funcs inst))) s)
    (map modelem_init (mod_elem m)) ->
  check_bounds_elem host_function inst s m x ->
  s' = (init_tabs host_function s inst [seq Z.to_nat (Wasm_int.Int32.intval o) | o <- x] (mod_elem m)) ->
  store_typing s'.
Proof.
  rewrite /check_bounds_elem. destruct m. simpl.
  clear mod_types mod_funcs mod_tables mod_mems mod_globals mod_data mod_start mod_imports mod_exports.
  move: s s' x.
  induction mod_elem as [ | mod_elem mod_elems];
  move => s s' e_offs Htyping Hinsts_typing Hinits_typing Hbounds Heqs;
  rewrite <- Forall2_all2 in Hbounds.
  - inversion Hbounds; subst.
    by rewrite /init_tabs.
  - inversion Hbounds; subst.
    rename x into e_off. rename l into e_offs.

    simpl in Hinits_typing. inversion Hinits_typing; subst.
    rename H1 into Hinit_typing. rename H4 into Hinits_typing'.
    
    rewrite /init_tabs. simpl.
    remember (init_tab host_function s inst (Z.to_nat (Wasm_int.Int32.intval e_off)) mod_elem) as s1 eqn:Heqs1.
    
    (* store_typing s1 *)
    eapply init_tab_preserve_typing in Htyping => //.
    rewrite <- Heqs1 in Htyping.
    
    (* recover invariant *)
    eapply IHmod_elems with (s := s1) (x := e_offs) => //.
    + (* Forall (λ n : nat, n < length (s_funcs s1)) (inst_funcs inst) *)
      symmetry in Heqs1.
      apply init_tab_preserve in Heqs1.
      destruct Heqs1 as [Heqfuncs _].
      by rewrite <- Heqfuncs.
    + (* check_bounds *)
      rewrite <- Forall2_all2.
      rewrite Forall2_same_length_lookup.
      split; first by eapply Forall2_length.
      move => i e_off1 mod_elem1 Hoffs_nth Helems_nth.
    
      rewrite -> Forall2_lookup in H3.
      specialize (H3 i).
      rewrite Hoffs_nth Helems_nth in H3.
      inversion H3; subst. clear H3.

      destruct mod_elem1. simpl in *.
      destruct modelem_table.

      destruct (nth_error (inst_tab inst) n) as [taddr0 | ] eqn: Haddr0 => //.
      destruct (nth_error (s_tables s) taddr0) as [tinst0 | ] eqn: Hinst0 => //.
    
      rewrite /init_tab.
      destruct mod_elem. simpl in *.
      destruct modelem_table.
      
      destruct (nth_error (inst_tab inst) n0) as [taddr1 | ] eqn: Haddr1 => //.
      destruct (nth_error (s_tables s) taddr1) as [tinst1 | ] eqn: Hinst1 => //.
      
      rewrite -> nth_error_nth with (x := taddr1) => //.
      erewrite nth_error_nth => //.
      
      destruct tinst1. simpl in *.
      assert (H3: taddr1 < length (s_tables s)).
      { by eapply nth_error_Some_length .}
      erewrite insert_at_insert => //.
      destruct (decide (taddr0 = taddr1)).
      * (* taddr0 = taddr1 *)
        rewrite e in Hinst0.
        rewrite Hinst0 in Hinst1.
        inversion Hinst1.
        rewrite H0 in H1. simpl in H1.

        rewrite e.
        rewrite nth_error_lookup.
        rewrite list_lookup_insert => //.
        simpl.

        repeat rewrite app_length.
        rewrite take_length map_length drop_length.

        move/N.leb_spec0 in H2.
        rewrite /N_of_int in H2.

        move/N.leb_spec0 in H1.
        rewrite /N_of_int in H1.

        replace (Z.to_nat (Wasm_int.Int32.intval e_off) `min` length table_data) with (Z.to_nat (Wasm_int.Int32.intval e_off)).
        2 : { by lias. }

        apply/N.leb_spec0.

        rewrite Nat.add_assoc.
        replace (ssrnat.addn (Z.to_nat (Wasm_int.Int32.intval e_off)) (length modelem_init0)) with (Z.to_nat (Wasm_int.Int32.intval e_off) + length modelem_init0).
        2 : { by lias. }
        
        rewrite le_plus_minus_r => //.
        by lias.
      * (* taddr0 /= taddr1 *)
        rewrite nth_error_lookup.
        rewrite list_lookup_insert_ne => //.
        rewrite nth_error_lookup in Hinst0.
        by rewrite Hinst0.
Qed.
    
Lemma init_mems_preserve ws inst d_inits mdata ws':
  init_mems host_function ws inst d_inits mdata = ws' ->
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  move => Hinit.
  unfold init_mems in Hinit.
  rewrite - Hinit.
  apply fold_left_preserve => //.
  move => x [n md] Heq.
  destruct ws, x.
  simpl in *.
  destruct Heq as [-> [-> ->]].
  by unfold init_mem => /=.
Qed.

Lemma init_mem_preserve_typing s inst mod_data d_off:
  store_typing s ->
  match nth_error (inst_memory inst) match moddata_data mod_data with
                                  | Mk_memidx i => i
                                  end with
  | Some i =>
      match nth_error (s_mems s) i with
      | Some mem => (N_of_int d_off + N.of_nat (length (moddata_init mod_data)) <=? mem_length mem)%N
      | None => false
      end
  | None => false
  end ->
  store_typing (init_mem host_function s inst (Z.to_N (Wasm_int.Int32.intval d_off)) mod_data).
Proof.
  move => Htyping Hbound.

  rewrite /init_mem.
  destruct mod_data. simpl in *.
  destruct moddata_data.
  destruct (nth_error (inst_memory inst)) as [maddr | ] eqn: Hmaddr => //.
  destruct (nth_error (s_mems s) maddr) as [minst | ] eqn: Hinst => //.

  rewrite -> nth_error_nth with (x := maddr) => //.
  erewrite -> nth_error_nth => //.

  destruct minst. simpl.

  rewrite /store_typing /typing.store_typing in Htyping.
  destruct s. simpl in *.
  destruct Htyping as [Hcl_type [Htab_agree Hmem_agree]].

  assert (Hle: maddr < length s_mems).
  { by eapply nth_error_Some_length. }
  
  rewrite insert_at_insert => //.
  split.
  - (* cl_type *) {
    apply Forall_lookup_2 => i fc Hfuncs_nth.
    eapply Forall_lookup_1 in Hcl_type => //.
    
    rewrite /typing.cl_type_check_single in Hcl_type.
    destruct Hcl_type as [tf Hcl_typing].
    rewrite /typing.cl_type_check_single.
    exists tf.

    eapply store_extension_cl_typing => //.
    rewrite /store_extension. simpl.
    apply/andP. split. 2 : { by apply all2_glob_extension_same. }.
    apply/andP. split.
    apply/andP. split; [ by apply/eqP | by apply all2_tab_extension_same ].

    rewrite /mem_extension.
    rewrite <- Forall2_all2.

    rewrite Forall2_lookup => maddr'.
    destruct (decide (maddr = maddr')) as [Heq | Hneq].
    + (* maddr = maddr' *)
      rewrite <- Heq.
      rewrite list_lookup_insert => //.

      rewrite nth_error_lookup in Hinst.
      rewrite Hinst.

      apply Some_Forall2. simpl.
      apply/andP. split => //.

      rewrite /mem_size /operations.mem_length /memory_list.mem_length.
      simpl.

      repeat rewrite app_length.
      rewrite take_length map_length drop_length.

      (* using Hbound *)
      rewrite /mem_length /memory_list.mem_length in Hbound.
      simpl in Hbound.

      move/N.leb_spec0 in Hbound.
      replace (ssrnat.nat_of_bin (Z.to_N (Wasm_int.Int32.intval d_off)) `min` length (ml_data mem_data)) with (ssrnat.nat_of_bin (Z.to_N (Wasm_int.Int32.intval d_off))).
      2 : { rewrite /N_of_int in Hbound.
            repeat rewrite nat_bin.
            by lias. }
      apply/N.leb_spec0.
      apply N.eq_le_incl. repeat f_equal.
      rewrite /N_of_int in Hbound. 
      rewrite nat_bin.
      by lias.
    + (* maddr /= maddr' *)
      rewrite list_lookup_insert_ne => //.
      destruct (s_mems !! maddr').
      * (* Some *)
        apply Some_Forall2.
        apply/andP.
        split; [ by rewrite N.leb_refl | by apply/eqP ].
      * (* None *)
        by apply None_Forall2.
  }
  split.
  - (* tab_agree *)
    exact Htab_agree.
  - (* mem_agree *)
    clear Hcl_type Htab_agree.
    rewrite /mem_agree in Hmem_agree.
    rewrite -> Forall_lookup in Hmem_agree.
    rewrite /mem_agree.
    apply Forall_lookup_2 => maddr' inst' Hinst'.
    destruct (decide (maddr = maddr')) as [Heq | Hneq].
    + (* maddr = maddr' *)
      rewrite nth_error_lookup in Hinst.
      rewrite <- Heq in Hinst'.
      rewrite list_lookup_insert in Hinst' => //.
      inversion Hinst'; subst. clear Hinst'.
      simpl.

      specialize (Hmem_agree maddr' {| mem_data := mem_data; mem_max_opt := mem_max_opt |} Hinst).
      simpl in Hmem_agree.

      rewrite /mem_size /operations.mem_length /memory_list.mem_length. simpl.
      rewrite /mem_size /operations.mem_length /memory_list.mem_length in Hmem_agree.
      simpl in Hmem_agree.

      destruct mem_max_opt => //.

      repeat rewrite app_length.
      rewrite take_length map_length drop_length.

      rewrite /mem_length /memory_list.mem_length in Hbound.
      simpl in Hbound.

      move/N.leb_spec0 in Hbound.
      rewrite /N_of_int in Hbound.

      rewrite nat_bin.

      replace (N.to_nat (Z.to_N (Wasm_int.Int32.intval d_off)) `min` length (ml_data mem_data)) with (N.to_nat (Z.to_N (Wasm_int.Int32.intval d_off))).
      2 : { by lias. }

      rewrite plus_assoc.
      replace (ssrnat.addn (N.to_nat (Z.to_N (Wasm_int.Int32.intval d_off))) (length moddata_init)) with (N.to_nat (Z.to_N (Wasm_int.Int32.intval d_off)) + length moddata_init).
      2 : { by lias. }

      rewrite le_plus_minus_r => //.      
      by lias.
    + (* maddr /= maddr' *)
      rewrite list_lookup_insert_ne in Hinst' => //.
      by specialize (Hmem_agree maddr' inst' Hinst').
Qed.

Lemma init_mems_preserve_typing s s' inst m x:
  store_typing s ->
  (* instantiate_data host_function host_instance inst hs' s m x -> *)
  check_bounds_data host_function inst s m x ->
  s' = (init_mems host_function s inst [seq Z.to_N (Wasm_int.Int32.intval o) | o <- x] (mod_data m)) ->
  store_typing s'.
Proof.
  rewrite /check_bounds_data. destruct m. simpl.
  clear mod_types mod_funcs mod_tables mod_mems mod_globals mod_elem mod_start mod_imports mod_exports. 
  move: s s' x.
  induction mod_data as [ | mod_data mod_datas]; move => s s' d_offs Htyping Hbounds Heqs;
  rewrite <- Forall2_all2 in Hbounds.
  - inversion Hbounds; subst.
    by rewrite /init_mems.
  - inversion Hbounds; subst.
    rename x into d_off. rename l into d_offs.
    rewrite /init_mems. simpl.
    (* d_off & mod_data represent the altered mem segment during s -> s1 *)
    remember (init_mem host_function s inst (Z.to_N (Wasm_int.Int32.intval d_off)) mod_data) as s1 eqn: Heqs1.

    (* store_typing s1 *)
    eapply init_mem_preserve_typing in Htyping => //.
    rewrite <- Heqs1 in Htyping.

    (* recover invariant - check_bound *)
    eapply IHmod_datas with (s := s1) (x := d_offs) => //.
    clear Htyping Hbounds.
    rewrite <- Forall2_all2.
    rewrite Forall2_same_length_lookup.
    split.
    + by eapply Forall2_length.
    + move => i d_off1 mod_data1 Hoffs_nth Helems_nth.

      rewrite -> Forall2_lookup in H3.
      specialize (H3 i).
      rewrite Hoffs_nth Helems_nth in H3.
      inversion H3; subst. clear H3.

      destruct mod_data1. simpl in *.
      destruct moddata_data.

      destruct (nth_error (inst_memory inst) n) as [maddr1 | ] eqn: Haddr1 => //.
      destruct (nth_error (s_mems s) maddr1) as [minst1 | ] eqn: Hinst1 => //.

      destruct mod_data. simpl in *.
      destruct moddata_data.

      destruct (nth_error (inst_memory inst) n0) as [maddr | ] eqn: Haddr => //.
      destruct (nth_error (s_mems s) maddr) as [minst | ] eqn: Hminst => //.

      rewrite -> nth_error_nth with (x := maddr) => //.
      erewrite nth_error_nth => //.

      destruct minst. simpl.

      assert (H3 : maddr < length (s_mems s)).
      { by eapply nth_error_Some_length. }
      erewrite insert_at_insert => //.

      destruct (decide (maddr = maddr1)).
      * (* maddr = maddr1 *)
        rewrite <- e.
        rewrite nth_error_lookup => //.
        rewrite list_lookup_insert => //.
        rewrite /instantiation.mem_length /memory_list.mem_length.
        simpl.

        (* from addr = addr1, we could know that minst1 = minst0 (has been destructed) *)
        rewrite <- e in Hinst1.
        rewrite Hinst1 in Hminst.
        inversion Hminst; subst. clear Hminst.
        rewrite /instantiation.mem_length /memory_list.mem_length in H1.
        simpl in H1.

        rewrite /instantiation.mem_length /memory_list.mem_length in H2.
        simpl in H2.
        
        repeat rewrite app_length.
        rewrite take_length map_length drop_length.

        move/N.leb_spec0 in H1.
        rewrite /N_of_int in H1.
        
        move/N.leb_spec0 in H2.
        rewrite /N_of_int in H2.
        
        apply/N.leb_spec0.
        
        rewrite nat_bin.
        
        replace (N.to_nat (Z.to_N (Wasm_int.Int32.intval d_off)) `min` length (ml_data mem_data)) with (N.to_nat (Z.to_N (Wasm_int.Int32.intval d_off))).
        2 : { by lias. }

        rewrite plus_assoc.
        replace (ssrnat.addn (N.to_nat (Z.to_N (Wasm_int.Int32.intval d_off))) (length moddata_init0)) with (N.to_nat (Z.to_N (Wasm_int.Int32.intval d_off)) + length moddata_init0).
        2 : { by lias. }
        rewrite le_plus_minus_r => //. 
        by lias.
      * (* maddr /= maddr1 *)
        rewrite nth_error_lookup.
        rewrite list_lookup_insert_ne => //.
        rewrite nth_error_lookup in Hinst1.
        by rewrite Hinst1.
Qed.


Lemma elem_typing_proj_is m t_imps t_exps:
  module_typing m t_imps t_exps ->
  Forall
    (all (λ '(Mk_funcidx i), ssrnat.leq (S i) (length (ext_t_funcs t_imps) + length (mod_funcs m))))
    (map modelem_init (mod_elem m)). 
Proof.
  move => [fts [gts H]].
  destruct m. simpl in *.
  destruct H as [HFuncTyping [_ [_ [_ [HElemTyping _]]]]].
  apply Forall2_length in HFuncTyping.
  rewrite HFuncTyping.
  
  rewrite /module_elem_typing in HElemTyping.
  simpl in HElemTyping.
  rewrite Forall_lookup => i fidx Hinit_nth.
  
  rewrite list_lookup_fmap in Hinit_nth.
  destruct (mod_elem !! i) eqn: Helem_nth => //.

  eapply Forall_lookup_1 in HElemTyping => //.
  destruct m. destruct modelem_table.
  simpl in Hinit_nth.
  inversion Hinit_nth; subst. clear Hinit_nth.
  destruct HElemTyping as [_ [_ [_ H]]].
  by rewrite app_length in H.
Qed.


Lemma init_tabs_preserve_typing_aux s s' m v_imps t_imps v_exps t_exps inst gvs hs: 
  alloc_module host_function s m v_imps gvs (s', inst, v_exps) ->
  module_typing m t_imps t_exps ->
  Forall2 (instantiation.external_typing host_function s) v_imps t_imps -> 
  instantiate_globals host_function host_instance inst hs s' m gvs ->
  store_typing s -> 
  length (inst_funcs inst) = length (ext_t_funcs t_imps) + length (mod_funcs m) /\
    Forall (fun n => n < length (s_funcs s')) (inst_funcs inst).
Proof.
  move => Halloc Hmod_typing Himp_typing Hinit_globs Hstore_typing.
  rewrite /module_typing in Hmod_typing.
  destruct m.
  destruct Hmod_typing as [fts [gts [HFuncType [HTabType [HMemType [HGlobType [HElemType [HDataType [HStartValid [HImpValid HExpValid]]]]]]]]]].

  rewrite /alloc_module in Halloc. simpl in *.
  remember (alloc_funcs host_function s mod_funcs inst) as s_ifs.
  destruct s_ifs as [s1 ifs].
  remember (alloc_tabs host_function s1 (map (λ t : module_table, modtab_type t) mod_tables)) as s_its.
  destruct s_its as [s2 its].
  remember (alloc_mems host_function s2 mod_mems) as s_ims.
  destruct s_ims as [s3 ims].
  remember (alloc_globs host_function s3 mod_globals gvs) as s_igs.
  destruct s_igs as [s_end igs].

  destruct inst. simpl in *.
  
  repeat (move/andP in Halloc; destruct Halloc as [Halloc ?]).
  move/eqP in H; subst.
  move/eqP in H0; subst.
  move/eqP in H1; subst.
  move/eqP in H2; subst.
  move/eqP in H3; subst.
  move/eqP in H4; subst.
  move/eqP in Halloc; subst.
  
  destruct s_end. destruct s. simpl in *. destruct Hstore_typing as [Hcl [Htab_agree Hmem_agree]].
  specialize (alloc_func_gen_index _ _ _ _ _ _ (symmetry Heqs_ifs)) as Hfuncidx.
  destruct Hfuncidx as [Hfunidx [Hfunc1 [Htab1 [Hmem1 Hglob1]]]]; simpl in *.
  specialize (alloc_tab_gen_index _ _ _ _ _ (symmetry Heqs_its)) as Htabidx.
  destruct Htabidx as [Htabidx [Htab2 [Hfunc2 [Hmem2 Hglob2]]]]; simpl in *.
  specialize (alloc_mem_gen_index _ _ _ _ _ (symmetry Heqs_ims)) as Hmemidx.
  destruct Hmemidx as [Hmemidx [Hmem3 [Hfunc3 [Htab3 Hglob3]]]]; simpl in *.

  assert (Hgvs_len : length gvs = length mod_globals).
  {
    rewrite /instantiate_globals in Hinit_globs.
    simpl in Hinit_globs.
    apply Forall2_length in Hinit_globs.
    by symmetry in Hinit_globs.
  }
  specialize (alloc_glob_gen_index _ _ _ _ _ _ Hgvs_len (symmetry Heqs_igs)) as Hglobidx.
  destruct Hglobidx as [Hglobidx [Hglob4 [Hfunc4 [Htab4 Hmem4]]]]; simpl in *.
  
  rewrite <- Hfunc4 in *. rewrite <- Hfunc3 in *. rewrite <- Hfunc2 in *. rewrite -> Hfunc1 in *.
  rewrite <- Htab4 in *. rewrite <- Htab3 in *. rewrite -> Htab2 in *. rewrite <- Htab1 in *.
  rewrite <- Hmem4 in *. rewrite -> Hmem3 in *. rewrite <- Hmem2 in *. rewrite <- Hmem1 in *.
  rewrite -> Hglob4 in *. rewrite <- Hglob3 in *. rewrite <- Hglob2 in *. rewrite <- Hglob1 in *.

  clear Hfunc1 Hfunc2 Hfunc3 Hfunc4.
  clear Htab1 Htab2 Htab3 Htab4.
  clear Hmem1 Hmem2 Hmem3 Hmem4.
  clear Hglob1 Hglob2 Hglob3 Hglob4.
  clear Heqs_ifs Heqs_its Heqs_ims Heqs_igs.

  remember ((λ mf : module_func, gen_func_instance _ mf _) <$> mod_funcs) as s_funcs_new.
  remember (_ <$> map _ mod_tables) as s_tabs_new.
  remember ((λ '{| lim_min := min; lim_max := maxo |}, _) <$> mod_mems) as s_mems_new.
  remember (_ <$> combine mod_globals gvs) as s_globs_new.
  
  split.
  - rewrite map_length app_length.
    eapply external_typing_aux in Himp_typing.
    destruct Himp_typing as [Hext_funcs_len _].
    rewrite Hext_funcs_len. f_equal.
    rewrite <- gen_index_len with (offset := (length s_funcs0)) (len := length mod_funcs).
    rewrite <- Hfunidx.
    by rewrite map_length.
  - rewrite map_app Forall_app.
    split.
    + rewrite Forall_lookup.
      move => i n0 Hnth.
      rewrite ->  Forall2_lookup in Himp_typing.
      rewrite map_fmap in Hnth.
      rewrite list_lookup_fmap in Hnth.
      destruct (ext_funcs v_imps !! i) eqn: Hvimp => //.
      simpl in Hnth.
      apply ext_funcs_lookup_exist in Hvimp.
      destruct Hvimp as [k Hvimp].
      specialize (Himp_typing k).
      rewrite Hvimp in Himp_typing.
      inversion Himp_typing; subst.
      destruct f.
      inversion Hnth; subst.
      inversion H1; subst.
      simpl in H2.
      move/ssrnat.ltP in H2.
      rewrite app_length. 
      by lias.
    + rewrite Hfunidx.
      rewrite Heqs_funcs_new.
      rewrite app_length fmap_length.
      rewrite Forall_lookup => i x H.
      by apply gen_index_in in H.  
Qed.

Lemma instantiation_sound_simpl:  forall (s: store_record) m v_imps s' inst v_exps start,
  store_typing s ->
  instantiate s m v_imps ((s', inst, v_exps), start) ->
  (store_typing s').
  (* (exists C, inst_typing s' inst C) /\
  (exists tes, ext_typing_list s' v_exps tes) /\
  (pred_option (fun i => i < length s'.(s_funcs)) start).*)
  (* /\ store_extension s s' *)
Proof.
  move => s m v_imps s' inst v_exps start HStoreType HInst.

  unfold instantiate, instantiation.instantiate in HInst.
  destruct HInst as [t_imps [t_exps [hs' [s'_end [g_inits [e_offs [d_offs [HModType [HImpType [HAllocModule H]]]]]]]]]].

  destruct H as [HInstGlob [HInstElem [HInstData [HBoundElem [HBoundData [HStart HStore]]]]]].
  simpl in *.

  specialize (alloc_module_sound _ _ _ _ _ _ _ _ _ _ HAllocModule HModType HImpType HInstGlob HStoreType) as Htyping. rename s'_end into s1.

  specialize (init_tabs_preserve_typing_aux _ _ _ _ _ _ _ _ _ _  HAllocModule HModType HImpType HInstGlob HStoreType) as Hinit_tabs_aux.
  destruct Hinit_tabs_aux as [Hinst_funcs_len Hinst_func_typing].

  specialize (elem_typing_proj_is _ _ _ HModType) as Hinit_typing.
  rewrite <- Hinst_funcs_len in Hinit_typing.
  
  remember (init_tabs host_function s1 inst [seq Z.to_nat (Wasm_int.Int32.intval o) | o <- e_offs] (mod_elem m)) as s2. 
  specialize (init_tabs_preserve _ _ _ _ _ (symmetry Heqs2)) as Hs2.
  destruct Hs2 as [_[Hs2_mems _]].
  
  eapply init_tabs_preserve_typing with (s' := s2) in Htyping => //.
  
  move/eqP in HStore.

  rewrite /check_bounds_data in HBoundData.
  rewrite Hs2_mems in HBoundData.

  by eapply init_mems_preserve_typing => //.
Qed.
