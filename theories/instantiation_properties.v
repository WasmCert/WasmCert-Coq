From mathcomp Require Import ssreflect ssrbool eqtype seq.
From mathcomp Require ssrnat.
From ITree Require Import ITree.
From ITree Require ITreeFacts.
From stdpp Require Import list fin_maps gmap base.
From Wasm Require Import list_extra datatypes datatypes_properties properties
     interpreter binary_format_parser operations type_preservation
                         typing opsem type_checker memory memory_list instantiation.
Require Export stdpp_aux.
From Coq Require Import BinNat.

Section Host.

Check seq.

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

Print alloc_funcs.

Print alloc_func.

Print module_func.

Definition gen_index offset len : list nat :=
  imap (fun i x => i+offset+x) (repeat 0 len).

Lemma gen_index_len offset len:
  length (gen_index offset len) = len.
Proof.
  unfold gen_index.
  rewrite imap_length.
  by rewrite repeat_length.
Qed.
  
Lemma gen_index_lookup offset len k:
  k < len ->
  (gen_index offset len) !! k = Some (offset + k).
Proof.
  move => Hlen.
  unfold gen_index.
  rewrite list_lookup_imap => /=.
  eapply repeat_lookup with (x := 0) in Hlen.
  rewrite Hlen.
  simpl.
  f_equal.
  by lias.
Qed.

Lemma gen_index_extend offset len:
  gen_index offset (len+1) = gen_index offset len ++ [::offset+len].
Proof.
  unfold gen_index.
  rewrite repeat_app => /=.
  induction len => //=.
  f_equal => //.
  do 2 rewrite - fmap_imap.
  rewrite IHlen.
  rewrite fmap_app => /=.
  repeat f_equal.
  by lias.
Qed.

Lemma gen_index_in x offset len:
  In x (gen_index offset len) ->
  x < offset + len.
Proof.
Admitted.

Definition gen_func_instance mf inst : function_closure host_function :=
  let ft := nth match modfunc_type mf with
                | Mk_typeidx n => n
                end (inst_types inst) (Tf [] []) in
  FC_func_native inst ft (modfunc_locals mf) (modfunc_body mf).

Lemma alloc_func_gen_index modfuncs ws inst ws' l:
  alloc_funcs host_function ws modfuncs inst = (ws', l) ->
  map (fun x => match x with | Mk_funcidx i => i end) l = gen_index (length (s_funcs ws)) (length modfuncs) /\
  ws'.(s_funcs) = ws.(s_funcs) ++ fmap (fun mf => gen_func_instance mf inst) modfuncs /\
 (* length ws'.(s_funcs) = length ws.(s_funcs) + length modfuncs /\*)
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  unfold alloc_funcs, alloc_Xs.
  generalize dependent l.
  generalize dependent ws'.
  generalize dependent ws.
  induction modfuncs using List.rev_ind; move => ws ws' l Hallocfuncs.
  -
    inversion Hallocfuncs; subst; clear Hallocfuncs.
    simpl.
    repeat split => //.
    by rewrite app_nil_r.
  - rewrite fold_left_app in Hallocfuncs.
    remember (fold_left _ modfuncs (ws,[])) as fold_res.
    simpl in Hallocfuncs.
    destruct fold_res as [ws0 l0].
    symmetry in Heqfold_res. (* ? *)
    unfold add_func in Hallocfuncs.

    inversion Hallocfuncs; subst; clear Hallocfuncs.
    rewrite map_app app_length /=. (* (rev l0 ++ [Mk_funcidx (length (s_funcs ws0))]) *)
    rewrite gen_index_extend.
    specialize (IHmodfuncs ws ws0 (rev l0)).
    destruct IHmodfuncs as [? [? [? [? ?]]]]; first by rewrite Heqfold_res.
    
    repeat split => //; try by eapply IHmodfuncs; rewrite Heqfold_res.
    + rewrite H.
      rewrite H0.
      Locate "^~".
      by rewrite app_length map_length.
    + rewrite H0.
      rewrite - app_assoc.
      f_equal.
      by rewrite -> list_fmap_app.
Qed.

Lemma alloc_tab_gen_index modtabtypes ws ws' l:
  alloc_tabs host_function ws modtabtypes = (ws', l) ->
  map (fun x => match x with | Mk_tableidx i => i end) l = gen_index (length (s_tables ws)) (length modtabtypes) /\
  ws'.(s_tables) = ws.(s_tables) ++ fmap (fun '{| tt_limits := {| lim_min := min; lim_max := maxo |} |} => {| table_data := repeat None (ssrnat.nat_of_bin min); table_max_opt := maxo |}) modtabtypes /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  unfold alloc_tabs, alloc_Xs.
  generalize dependent l.
  generalize dependent ws'.
  generalize dependent ws.
  induction modtabtypes using List.rev_ind; move => ws ws' l Halloc.
  - inversion Halloc; subst; clear Halloc.
    repeat split => //.
    simpl.
    by rewrite app_nil_r.
  - rewrite fold_left_app in Halloc.
    remember (fold_left _ modtabtypes (ws,[])) as fold_res.
    simpl in Halloc.
    destruct fold_res as [ws0 l0].
    symmetry in Heqfold_res.
    unfold alloc_tab, add_table in Halloc.
    destruct x => /=.
    destruct tt_limits => /=.
    specialize (IHmodtabtypes ws ws0 (rev l0)).
    rewrite Heqfold_res in IHmodtabtypes.
    inversion Halloc; subst; clear Halloc.
    simpl in *.
    rewrite map_app app_length /=.
    rewrite gen_index_extend.
    destruct IHmodtabtypes as [? [? [? [? ?]]]] => //.
    repeat split => //.
    + rewrite H.
      rewrite H0.
      by rewrite app_length map_length.
    + rewrite H0.
      rewrite - app_assoc.
      f_equal.
      by rewrite -> list_fmap_app => /=.
Qed.

Lemma alloc_mem_gen_index modmemtypes ws ws' l:
  alloc_mems host_function ws modmemtypes = (ws', l) ->
  map (fun x => match x with | Mk_memidx i => i end) l = gen_index (length (s_mems ws)) (length modmemtypes) /\
  ws'.(s_mems) = ws.(s_mems) ++ fmap (fun '{| lim_min := min; lim_max := maxo |} => {| mem_data := memory_list.mem_make #00%byte (page_size * min)%N; mem_max_opt := maxo |}) modmemtypes /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_globals) = ws'.(s_globals).
Proof.
  unfold alloc_mems, alloc_Xs.
  generalize dependent l.
  generalize dependent ws'.
  generalize dependent ws.
  induction modmemtypes using List.rev_ind; move => ws ws' l Halloc.
  - inversion Halloc; subst; clear Halloc.
    repeat split => //=.
    by rewrite app_nil_r.
  - rewrite fold_left_app in Halloc.
    remember (fold_left _ modmemtypes (ws,[])) as fold_res.
    simpl in Halloc.
    destruct fold_res as [ws0 l0].
    symmetry in Heqfold_res.
    unfold alloc_mem, add_mem in Halloc.
    destruct x => /=.
    specialize (IHmodmemtypes ws ws0 (rev l0)).
    rewrite Heqfold_res in IHmodmemtypes.
    inversion Halloc; subst; clear Halloc.
    simpl in *.
    rewrite map_app app_length /=.
    rewrite gen_index_extend.
    destruct IHmodmemtypes as [? [? [? [? ?]]]] => //.
    repeat split => //.
    + rewrite H.
      rewrite H0.
      by rewrite app_length fmap_length.
    + rewrite H0.
      rewrite - app_assoc.
      f_equal.
      by rewrite -> list_fmap_app => /=.
Qed.

Lemma alloc_glob_gen_index modglobs ws g_inits ws' l:
  length g_inits = length modglobs ->
  alloc_globs host_function ws modglobs g_inits = (ws', l) ->
  map (fun x => match x with | Mk_globalidx i => i end) l = gen_index (length (s_globals ws)) (length modglobs) /\
  ws'.(s_globals) = ws.(s_globals) ++ fmap (fun '({| modglob_type := gt; modglob_init := ge |}, v) => {| g_mut := gt.(tg_mut); g_val := v |} ) (combine modglobs g_inits) /\
 (* length ws'.(s_globals) = length ws.(s_globals) + length modglobs /\*)
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_mems) = ws'.(s_mems).
Proof.
  (*
  unfold alloc_globs, alloc_Xs.
  generalize dependent l.
  generalize dependent ws'.
  generalize dependent ws.
  generalize dependent g_inits.
  induction modglobs using List.rev_ind; move => g_inits ws ws' l Hlen Halloc.
  - inversion Halloc; subst; clear Halloc.
    repeat split => //=.
    by rewrite app_nil_r.
  - destruct g_inits using List.rev_ind; first by destruct modglobs => /=.
    repeat rewrite app_length in Hlen; simpl in Hlen.
    repeat rewrite - cat_app in Halloc.
    rewrite combine_app in Halloc; last by lias.
    simpl in Halloc.
    rewrite fold_left_app in Halloc.
    lazymatch goal with
    | _: context C [fold_left ?f (combine modglobs g_inits) (ws, [])] |- _ =>
      remember (fold_left f (combine modglobs g_inits) (ws, [])) as fold_res
    end.
    (* rewrite - Heqfold_res in Halloc. *)
    destruct fold_res as [ws0 l0].
    symmetry in Heqfold_res.
    unfold alloc_glob, add_glob in Halloc.
    simpl in Halloc.
    inversion Halloc; subst; clear Halloc.
    rewrite map_app app_length /=.
    rewrite gen_index_extend.
    specialize (IHmodglobs g_inits ws ws0 (rev l0)).
    destruct IHmodglobs as [? [? [? [? ?]]]] => //.
    + by lias.
    + by rewrite Heqfold_res.
    repeat split => //.
    + rewrite H.
      rewrite H0.
      rewrite app_length fmap_length combine_length.
      repeat f_equal.
      by lias.
    + rewrite H0.
      rewrite - app_assoc.
      f_equal.
      rewrite combine_app => /=.
      rewrite -> list_fmap_app => /=.
      repeat f_equal.
      destruct x => //.
      by lias.
Qed. *) Admitted.


Lemma fold_left_preserve {A B: Type} (P: A -> Prop) (f: A -> B -> A) (l: list B) (acc: A) :
  P acc ->
  (forall (x:A) (act: B), P x -> P (f x act)) ->
  P (fold_left f l acc).
Proof.
(*
  (* Check fold_left_rev_right. *)
  rewrite -fold_left_rev_right.
  revert acc.
  induction l;simpl;auto.
  intros acc Ha Hnext.
  Locate for
  rewrite stdpp.list.foldr_snoc /=. apply IHl =>//.
  apply Hnext=>//.
Qed.    *)
 
Admitted.

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

Lemma init_tabs_preserve_typing s s' inst m x:
  store_typing s ->
  (* instantiate_elem host_function host_instance inst hs' s m x -> *)
  check_bounds_elem host_function inst s m x ->
  s' = (init_tabs host_function s inst [seq Z.to_nat (Wasm_int.Int32.intval o) | o <- x] (mod_elem m)) ->
  store_typing s'.
Proof.
Admitted.
    
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

Lemma init_mems_preserve_typing s inst m x:
  store_typing s ->
  (* instantiate_data host_function host_instance inst hs' s m x -> *)
  check_bounds_data host_function inst s m x ->
  store_typing (init_mems host_function s inst [seq Z.to_N (Wasm_int.Int32.intval o) | o <- x] (mod_data m)).
Proof.
Admitted.

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
Admitted.

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

Lemma nth_error_lookup {T: Type} (l: list T) i:
  nth_error l i = l !! i.
Proof.
  move: i.
  by induction l; move => i; destruct i => //=.
Qed.


(* similar to Forall2_lookup_lr 
Forall2_lookup_lr:
  ∀ (A B : Type) (P : A → B → Prop) (l : seq.seq A) (k : seq.seq B) (i : nat) (x : A) (y : B),
    Forall2 P l k → l !! i = Some x → k !! i = Some y → P x y
*)
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


Search Forall2.
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

Lemma Forall2_all2: forall A B (R : A -> B -> bool ) (l1 : seq.seq A) (l2 : seq.seq B),
    List.Forall2 R l1 l2 = all2 R l1 l2.
Proof.
  move => A B R l1.
  induction l1.
  - destruct l2.
Admitted.


Lemma nth_error_same_length_list:
  forall (A B : Type) (l1 : seq.seq A) (l2 : seq.seq B) (i : nat) (m : A),
     length l1 = length l2 ->
     nth_error l1 i = Some m -> 
     exists n, nth_error l2 i = Some n.
Proof.
  move => A B l1 l2 i m.
Admitted.


Check nth_error_Some.

Lemma nth_error_Some_length:
  forall A (l : seq.seq A) (i : nat) (m : A),
  nth_error l i = Some m -> 
  i < length l.
Proof.
  move => A l i m H1.
  assert (H2 : nth_error l i ≠ None) by rewrite H1 => //.
  by apply List.nth_error_Some in H2.
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

(*
Lemma external_typing_proj s n v_imps v_imp t_imps t_imp:
  Forall2 (instantiation.external_typing host_function s) v_imps t_imps ->
  Forall2 (instantiation.external_typing host_function s) (map (λ '(MED_func (Mk_funcidx i)), i) (ext_funcs v_imps)) (map (λ '(ET_func tf), tf) (ext_t_funcs t_imps)).
Proof.
Admitted.
 *)

      

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
Admitted.


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

Lemma ext_funcs_lookup_exist (modexps: list module_export_desc) n fn:
  (ext_funcs modexps) !! n = Some fn ->
  exists k, modexps !! k = Some (MED_func fn).
Proof.
  move: n fn.
  induction modexps; move => n tn Hextfunclookup => //=.
  simpl in Hextfunclookup.
  destruct a => //. 
  { simpl in *.
       destruct n; simpl in *; first by inversion Hextfunclookup; subst; exists 0.
       apply IHmodexps in Hextfunclookup.
       destruct Hextfunclookup as [k ?].
       by exists (S k).
  }
  all: simpl in *. 
  all: apply IHmodexps in Hextfunclookup.
  all: destruct Hextfunclookup as [k ?].
  all: by exists (S k).
Qed.

Lemma ext_tabs_lookup_exist (modexps: list module_export_desc) n tn:
  (ext_tabs modexps) !! n = Some tn ->
  exists k, modexps !! k = Some (MED_table tn).
Proof.
  move: n tn.
  induction modexps; move => n tn Hexttablookup => //=.
  simpl in Hexttablookup.
  destruct a => //. 
  2: { simpl in *.
       destruct n; simpl in *; first by inversion Hexttablookup; subst; exists 0.
       apply IHmodexps in Hexttablookup.
       destruct Hexttablookup as [k ?].
       by exists (S k).
  }
  all: simpl in *. 
  all: apply IHmodexps in Hexttablookup.
  all: destruct Hexttablookup as [k ?].
  all: by exists (S k).
Qed.

Lemma ext_mems_lookup_exist (modexps: list module_export_desc) n mn:
  (ext_mems modexps) !! n = Some mn ->
  exists k, modexps !! k = Some (MED_mem mn).
Proof.
  move: n mn.
  induction modexps; move => n mn Hextmemlookup => //=.
  simpl in Hextmemlookup.
  destruct a => //. 
  3: { simpl in *.
       destruct n; simpl in *; first try by inversion Hextmemlookup; subst; exists 0.
       apply IHmodexps in Hextmemlookup.
       destruct Hextmemlookup as [k ?].
       by exists (S k).
  }
  all: simpl in *. 
  all: apply IHmodexps in Hextmemlookup.
  all: destruct Hextmemlookup as [k ?].
  all: by exists (S k).
Qed.

Lemma ext_globs_lookup_exist (modexps: list module_export_desc) n fn:
  (ext_globs modexps) !! n = Some fn ->
  exists k, modexps !! k = Some (MED_global fn).
Proof.
  move: n fn.
  induction modexps; move => n tn Hextgloblookup => //=.
  simpl in Hextgloblookup.
  destruct a => //. 
  4: { simpl in *.
       destruct n; simpl in *; first by inversion Hextgloblookup; subst; exists 0.
       apply IHmodexps in Hextgloblookup.
       destruct Hextgloblookup as [k ?].
       by exists (S k).
  }
  all: simpl in *. 
  all: apply IHmodexps in Hextgloblookup.
  all: destruct Hextgloblookup as [k ?].
  all: by exists (S k).
Qed.

Lemma bet_const_exprs_len tc es t1 t2:
  const_exprs tc es ->
  be_typing tc es (Tf t1 t2) ->
  length t2 = length es + length t1.
Proof.
  (*
  move: t1 t2.
  induction es; move => t1 t2 Hconst Hbet; destruct t2 => //=.
  { apply empty_typing in Hbet. by subst. }
  { apply empty_typing in Hbet. by subst. }
  { rewrite <- cat1s in Hbet.
    apply composition_typing in Hbet.
    destruct Hbet as [ts [t1s [t2s [t3s [-> [Heqt2 [Hbet1 Hbet2]]]]]]].
    destruct ts, t2s => //=.
    simpl in Hconst.
    move/andP in Hconst.
    destruct Hconst as [Hconst Hconsts].
    apply IHes in Hbet2 => //.
    destruct es, t3s => //=.
    unfold const_expr in Hconst.
    destruct a => //.
    { apply Get_global_typing in Hbet1.
      destruct Hbet1 as [t [? [HContra ?]]].
      by destruct t1s.
    }
    { apply BI_const_typing in Hbet1.
      by destruct t1s.
    }
  }
  { rewrite <- cat1s in Hbet.
    apply composition_typing in Hbet.
    destruct Hbet as [ts [t1s [t2s [t3s [-> [Heqt2 [Hbet1 Hbet2]]]]]]].
    simpl in Hconst.
    move/andP in Hconst.
    destruct Hconst as [Hconst Hconsts].
    eapply IHes in Hconsts => //.
    f_equal.
    assert (length t2 + 1 = length ts + length t2s) as Hlent2.
    { rewrite <- app_length.
      rewrite <- cat_app.
      rewrite <- Heqt2.
      by lias.
    }
    unfold const_expr in Hconst.
    destruct a => //.
    { apply Get_global_typing in Hbet1.
      destruct Hbet1 as [t [? [HContra ?]]].
      subst.
      rewrite -> app_length in *.
      simpl in *.
      by lias.
    }
    { apply BI_const_typing in Hbet1.
      subst.
      rewrite -> app_length in *.
      simpl in *.
      by lias.
    }
  }
Qed.*) Admitted.
  
Lemma const_exprs_impl tc es t:
  const_exprs tc es ->
  be_typing tc es (Tf [] [::t]) ->
  exists e, es = [:: e] /\ const_expr tc e.
Proof.
  move => Hconst Hbet.
  eapply bet_const_exprs_len in Hbet => //.
  do 2 destruct es => //=.
  exists b; split => //.
  unfold const_exprs in Hconst.
  simpl in Hconst.
  move/andP in Hconst.
  by destruct Hconst.
Qed.

Check reduce_trans.
Lemma reduce_trans_const hs s1 f1 v1 s2 f2 v2:
  reduce_trans (host_instance:=host_instance) (hs, s1, f1, [AI_basic (BI_const v1)]) (hs, s2, f2, [AI_basic (BI_const v2)]) ->
  v1 = v2.
Proof.
  (*
  move => Hred.
  unfold reduce_trans in Hred.
  apply Operators_Properties.clos_rt_rt1n_iff in Hred.
  inversion Hred => //.
  unfold reduce_tuple in H.
  destruct y as [[??]?].
  by apply const_no_reduce in H.
Qed.
   *) Admitted.
Check sglob_val. Locate sglob_val.

Lemma reduce_trans_get_global hs s f s' f' i v:
  reduce_trans (host_instance:=host_instance) (hs, s, f, [AI_basic (BI_get_global i)]) (hs, s', f', [AI_basic (BI_const v)]) ->
  sglob_val s (f_inst f) i = Some v.
Proof.
  (*
  move => Hred.
  unfold reduce_trans in *.
  apply Operators_Properties.clos_rt_rt1n_iff in Hred.
  inversion Hred; subst; clear Hred.
  destruct y as [[??]?].
  unfold reduce_tuple in H.
  apply reduce_get_global in H.
  destruct H as [v' [Hsgv ->]].
  inversion H0; subst; clear H0 => //.
  unfold reduce_tuple in H.
  destruct y as [[??]?].
  by apply const_no_reduce in H.
Qed. *) Admitted.

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
  specialize (alloc_func_gen_index _ _ _ _ _ (symmetry Heqs_ifs)) as Hfuncidx.
  destruct Hfuncidx as [Hfunidx [Hfunc1 [Htab1 [Hmem1 Hglob1]]]]; simpl in *.
  specialize (alloc_tab_gen_index _ _ _ _ (symmetry Heqs_its)) as Htabidx.
  destruct Htabidx as [Htabidx [Htab2 [Hfunc2 [Hmem2 Hglob2]]]]; simpl in *.
  specialize (alloc_mem_gen_index _ _ _ _ (symmetry Heqs_ims)) as Hmemidx.
  destruct Hmemidx as [Hmemidx [Hmem3 [Hfunc3 [Htab3 Hglob3]]]]; simpl in *.

  assert (Hgvs_len : length gvs = length mod_globals).
  {
    rewrite /instantiate_globals in Hinit_globs.
    simpl in Hinit_globs.
    apply Forall2_length in Hinit_globs.
    by symmetry in Hinit_globs.
  }
  specialize (alloc_glob_gen_index _ _ _ _ _ Hgvs_len (symmetry Heqs_igs)) as Hglobidx.
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

  remember ((λ mf : module_func, gen_func_instance mf _) <$> mod_funcs) as s_funcs_new.
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
              Check Forall_Forall2_l.
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
                     rewrite Forall_forall.
                     move => x Hin _.
                     apply gen_index_in in Hin.
                     by move/ssrnat.ltP in Hin.
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
                    rewrite Forall_forall.
                    move => x Hin _.
                    apply gen_index_in in Hin.
                    rewrite Hcombine_len.
                    by move/ssrnat.ltP in Hin.
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
                     specialize (const_exprs_impl _ _ _ Hconst_exprs Hbe_typing) as Hexprs.
                     clear Hconst_exprs.
                     destruct Hexprs as [expr [Hexpr Hconst]].
                     rewrite /const_expr in Hconst. simpl in Hconst.
                     rewrite -> Hexpr in *.  clear Hexpr.
                     destruct expr; simpl in * => //.
                     { (* modglob_init = [BI_get_global i0] *)

                       Search BI_get_global.

                       (* [BI_get_global i0] ->* gv *)
                       Search s_globals.
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
                       Check nth_error_Some_length.
                       specialize (nth_error_Some_length _ _ _ _ Heq4) as Hg0.
                       eapply nth_error_app1 in Hg0. rewrite Hg0 in Heq1.
                       rewrite Heq4 in Heq1. inversion Heq1; subst.
                       inversion H1; subst.
                       move/andP in H0. destruct H0 as [_ H0].
                       by move/eqP in H0.                     
                     }
                     { (* modglob_init = [BI_const v] *)
                       apply reduce_trans_const in H1. subst.
                       Search BI_const.
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
Admitted.

  
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
  
  remember (init_tabs host_function s1 inst [seq Z.to_nat (Wasm_int.Int32.intval o) | o <- e_offs] (mod_elem m)) as s2. 
  specialize (init_tabs_preserve _ _ _ _ _ (symmetry Heqs2)) as Hs2.
  destruct Hs2 as [_[Hs2_mems _]].
  
  eapply init_tabs_preserve_typing with (s' := s2) in Htyping => //.
  rewrite Heqs2 in Htyping. 
  
  move/eqP in HStore.

  rewrite /check_bounds_data in HBoundData.
  rewrite Hs2_mems in HBoundData.
  rewrite HStore.
  eapply init_mems_preserve_typing => //.
  by rewrite Heqs2.
Qed.

