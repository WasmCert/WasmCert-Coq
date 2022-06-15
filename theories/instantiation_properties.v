From mathcomp Require Import ssreflect ssrbool eqtype seq.
From mathcomp Require ssrnat.
From ITree Require Import ITree.
From ITree Require ITreeFacts.
From stdpp Require Import list fin_maps gmap base.
From Wasm Require Import list_extra datatypes datatypes_properties properties
                         interpreter binary_format_parser operations
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

(* This is the key definition: we should really be able to tell what the allocated new function closures are from the information of alloc_funcs. However, we need to formulate this in a way that is convenient for the other parts of the proofs. *)
Definition alloc_funcs_new_closures (modfuncs: list module_func) (inst: instance) : list (function_closure host_function) :=
  List.map (fun (mf: module_func) => 
              (FC_func_native inst
                              (List.nth match mf.(modfunc_type) with
                                        | Mk_typeidx n => n
                                        end
                                        (inst.(inst_types)) (Tf [::] [::]))
                              mf.(modfunc_locals)
                              mf.(modfunc_body))) modfuncs.

(* Same for this, but this is easier to define -- we should also be able to tell what the allocated function indices are. *)

(*
Fixpoint nat_list (acc: list nat) (n : nat) : list nat :=
  match n with
  | O => acc
  | (S n') => nat_list (n' :: acc) n'
  end.
 
Lemma nat_list_length: forall acc n,
  length (nat_list acc n) = length acc + n.
Proof.
Admitted.

Lemma 

i < n -> 
List.nth_error (nat_list acc n) i = Some i.

Lemma 
i >= n -> 
List.nth_error (nat_list acc n) i = List.nth_error acc (i - n).
*)

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

(*
Definition alloc_funcs_new_indices (ws: store_record) (modfuncs: list module_func) : list funcidx :=
  List.map (fun n => Mk_funcidx (n + List.length ws.(s_funcs))) (nat_list nil (List.length modfuncs)).
 *)

(*
Definition alloc_funcs_new_indices (ws : store_record) (modfuncs: list module_func) : list funcidx :=
  List.map Mk_funcidx (gen_index (length (s_funcs ws)) (length modfuncs)).

Lemma alloc_func_ws_res modfuncs ws inst ws' l:
  (ws', l) = alloc_funcs host_function ws modfuncs inst ->
  ws'.(s_funcs) = ws.(s_funcs) ++ alloc_funcs_new_closures modfuncs inst /\
  ws'.(s_tables) = ws.(s_tables) /\
  ws'.(s_mems) = ws.(s_mems) /\
  ws'.(s_globals) = ws.(s_globals).
Proof.
  move: l ws' ws. Check List.rev_ind.
  induction modfuncs using List.rev_ind; move => l ws' ws Halloc => /=.

  (* modfuncs = nil *)
  - inversion Halloc; subst.
    split => //=; first by rewrite -> List.app_nil_r.

  (* modfuncs = modfuncs ++ [:: x] *)
  - rewrite /alloc_funcs /alloc_Xs in Halloc.
    
    rewrite List.fold_left_app in Halloc.
    remember (List.fold_left _ modfuncs (ws, [::])) as temp_ws_l.
    destruct temp_ws_l as [ws_i l_i].
    
    simpl in Halloc.
    specialize (IHmodfuncs (List.rev l_i) ws_i ws). 
    destruct IHmodfuncs as [Hfunc [Htab [Hmem Hglob]]].
    {
      rewrite /alloc_funcs /alloc_Xs.
      by rewrite <- Heqtemp_ws_l.
    }
    {
      rewrite /add_func in Halloc.
      inversion Halloc. simpl.
      split.     
      + (* s_funcs ws_i ++ x_func_inst = s_funcs ws ++ alloc_funcs_new (modfuncs ++ [:: x]) *)
        rewrite /alloc_funcs_new_closures.
        rewrite List.map_app. simpl.
        rewrite -> List.app_assoc.
        f_equal. exact Hfunc.
      + (* s_tables /\ s_mems /\ s_globals *)
        by split => //=.
    }
Qed.
 *)

Definition gen_func_instance mf inst : function_closure host_function :=
  let ft := nth match modfunc_type mf with
                | Mk_typeidx n => n
                end (inst_types inst) (Tf [] []) in
  FC_func_native inst ft (modfunc_locals mf) (modfunc_body mf).

Lemma alloc_func_gen_index (modfuncs : list module_func)  ws inst ws' l:
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
(* 
all2 g l1 l2 /\ all2 h l1 l2 -> 
all2 (fun a b => (g a b) && (h a b)) l1 l2 

 *)

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

Let cl_type_check_single := @cl_type_check_single host_function.

Lemma cl_type_check_single_aux s_funcs s_tables s_mems s_globals func funcs:
  cl_type_check_single {| s_funcs := s_funcs; s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |} func ->
  cl_type_check_single {| s_funcs := s_funcs ++ funcs; 
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

Let tab_agree := @tab_agree host_function.

Lemma tab_agree_aux s_funcs s_tables s_mems s_globals tab funcs:
  tab_agree {| s_funcs := s_funcs; s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |} tab ->
  tab_agree {| s_funcs := s_funcs ++ funcs; s_tables := s_tables; s_mems := s_mems;
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
    rewrite size_cat. by rewrite ssrnat.ltn_addr.
    (* forall tabcl_agree tl *)
    apply IH. exact Htl.
  - (* tabsize_agree table *)
    assumption.
Qed.

(*
Lemma forall2_length: forall A B R (l1 : seq.seq A) (l2 : seq.seq B),
    List.Forall2 R l1 l2 -> List.length l1 = List.length l2.
Proof.
Admitted.
 *)



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
Admitted.


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
Admitted.


Lemma Forall2_all2: forall A B (R : A -> B -> bool ) (l1 : seq.seq A) (l2 : seq.seq B),
    List.Forall2 R l1 l2 = all2 R l1 l2.
Proof.
Admitted.


Lemma alloc_func_sound s s' ifs mod_funcs mod_types fts inst t_context: 
  (s', ifs) = alloc_funcs host_function s mod_funcs inst ->
  List.Forall2 (module_func_typing t_context) mod_funcs fts ->
  t_context.(tc_func_t) = fts ->
  t_context.(tc_types_t) = mod_types ->
  t_context.(tc_global) = nil ->
  t_context.(tc_table) = nil -> 
  t_context.(tc_memory) = nil ->
  t_context.(tc_local) = nil ->
  t_context.(tc_label) = nil ->
  t_context.(tc_return) = None ->
  inst.(inst_types) = mod_types ->
  inst.(inst_funcs) = List.map (fun '(Mk_funcidx i) => i) ifs ->
  inst.(inst_globs) = nil ->
  inst.(inst_tab) = nil ->
  inst.(inst_memory) = nil -> 
  store_typing s ->
  store_typing s'.
Proof.
  destruct inst, t_context.
  move => Halloc Hftstype ? ? ? ? ? ? ? ? ? ? ? ? ? Hstoretype; simpl in *; subst.
  
  (* Doing induction on mod_funcs is hard since we only have the module validity result for the original module. 
     Instead, note that we can explicitly evaluate what the new store s' is -- intuitively, it should only differ with the original store in the function component, where a few functions are appended. *)
  
  specialize (alloc_func_gen_index _ _ _ _ _ (symmetry Halloc)) as Hfuncidx.
  destruct Hfuncidx as [Hidx [Hfunc [Htab [Hmem Hglob]]]].

  (* We have established a relationship between the new store and the old store without using fold_left. We now have to prove the rest. Some of the lemmas proven previously commented out for now) is applicable, but need to be in a more generalised form. *)
  
  destruct s'. destruct s. simpl in *. destruct Hstoretype as [Hcl [Htab_agree Hmem_agree]].
  split; rewrite -> Hfunc; subst.
  - (* cl_type *)
    remember ((λ mf : module_func, gen_func_instance mf _) <$> mod_funcs) as s_funcs_new.
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
        specialize (Forall2_lookup_l _ _ _ _ _  Hftstype Heqm) as H1.
        destruct H1 as [ty [Heqy _]].
        rewrite <- nth_error_lookup in Heqy.
        by exists ty.
      }

      destruct Hex_ty as [ty Hty].
      specialize (Forall2_nth_error _ _ _ _ _ n m ty Hftstype Heqm Hty) as Hftstype_n.

      rewrite /typing.cl_type_check_single.
      destruct ty as [t1s t2s]. 
      exists (Tf t1s t2s).
      remember (Build_t_context mod_types fts nil nil nil nil nil None) as C.

      eapply cl_typing_native with (C := C) => //=.

      { (* inst_typing store inst C *)
        destruct C.
        destruct tc_local => //=.
        destruct tc_label => //=.
        destruct tc_return => //=.
        inversion HeqC; subst.
        destruct HeqC. 
        apply/andP. split => //=.
        apply/andP. split => //=.
        apply/andP. split => //=.
        apply/andP. split => //=.
        { (* functions_agree *)
          rewrite /gen_func_instance. simpl.
          rewrite /typing.functions_agree.
          eapply all2_and with (g := (fun n0 f => ssrnat.leq (S n0) _)) => //=.
          split.
          {
            rewrite <- Forall2_all2.
            rewrite List.app_length.
            rewrite fmap_length.
            rewrite Hidx.
            apply Forall_Forall2_l.
            (*
              Forall_Forall2_l: ∀ (A B : Type) (P : A → B → Prop) (l : seq.seq A) (k : seq.seq B),
                length l = length k → Forall (λ x : A, ∀ y : B, P x y) l → Forall2 P l k
             *)
            - rewrite gen_index_len.
              by apply Forall2_length in Hftstype.
            - rewrite Forall_forall.
              move => x Hin _.
              apply gen_index_in in Hin.
              by move/ssrnat.ltP in Hin.
          }
          {
            clear n m Heqm t1s t2s Hty Hftstype_n.
            rewrite /module_func_typing in Hftstype; simpl in Hftstype.
            rewrite <- Forall2_all2.
            assert (Hlen: length ifs = length mod_funcs).
            {
              rewrite <- gen_index_len with (offset := (length s_funcs0)).
              rewrite <- Hidx.
              by rewrite map_length.
            }
            apply Forall2_lift.
            - (* length (map (λ '(Mk_funcidx i), i) ifs) = length fts *)
              rewrite map_length.
              rewrite Hlen.
              by apply Forall2_length in Hftstype.
            - 
              move => i fidx ft Hfuncs_nth Hfts_nth.
              assert (Hnth: i < length mod_funcs).
              {
                rewrite Coqlib.list_map_nth in Hfuncs_nth.
                destruct (List.nth_error ifs i) eqn:Hnth_i => //=.
                assert (H: List.nth_error ifs i <> None) by rewrite Hnth_i => //.
                apply List.nth_error_Some in H.
                by rewrite <- Hlen.
              }
              rewrite Hidx in Hfuncs_nth.
              rewrite nth_error_lookup in Hfuncs_nth.
              rewrite gen_index_lookup in Hfuncs_nth => //.
              (* todo: length l1 = length l2 -> l1 !! i = Some m -> exists, l2 !! i = Some n *)
              apply List.nth_error_Some in Hnth.
              destruct (List.nth_error mod_funcs i) eqn: Hmod_funcs_i => //=.
              clear Hnth.
              specialize (Forall2_nth_error _ _ _ _ _ _ _ _ Hftstype Hmod_funcs_i Hfts_nth) as Hftstype_n.
              simpl in Hftstype_n.
              simpl in Hfuncs_nth.
              destruct m. destruct modfunc_type. destruct ft as [t1s t2s].
              destruct Hftstype_n as [_ [Hft _]].
              inversion Hfuncs_nth; subst.
              clear Hfuncs_nth.
              rewrite nth_error_app2; last by lias.
              Search "-".
              replace (length s_funcs0 + i - length s_funcs0) with i; last by lias.
              Search fmap lookup.
              rewrite nth_error_lookup.
              rewrite list_lookup_fmap.
              rewrite nth_error_lookup in Hmod_funcs_i.
              rewrite Hmod_funcs_i. by simpl.
          }
        }
    }
    { (* the type index of function m references type (Tf t1s t2s) in mod_types *)
      rewrite /module_func_typing in Hftstype_n.
      destruct m. simpl.
      destruct modfunc_type as [i].
      destruct Hftstype_n as [_ [Hnth _]].
      move/eqP in Hnth.
      rewrite <- Hnth.
      by inversion HeqC.
    }
    { (* be_typing *)
      rewrite /module_func_typing in Hftstype_n.
      rewrite /upd_local_label_return.
      destruct m. simpl.
      destruct modfunc_type.
      destruct Hftstype_n as [_ [_ Hbe_typing]].
      by apply Hbe_typing.
    }
  split.
  - (* tab_agree *)
    apply List.Forall_forall => tab Hin.
    rewrite -> List.Forall_forall in Htab_agree.
    apply tab_agree_aux.
    by apply Htab_agree.
  - (* mem_agree *)
    assumption. 
Admitted.

Definition module_restriction (m: module) : Prop :=
  m.(mod_tables) = [::] /\
  m.(mod_mems) = [::] /\
  m.(mod_globals) = [::] /\
  m.(mod_elem) = [::] /\
  m.(mod_data) = [::] /\
  m.(mod_start) = None /\
  m.(mod_imports) = [::] /\
  m.(mod_exports) = [::].

Lemma instantiation_sound_simpl:  forall (s: store_record) m v_imps s' inst v_exps start,
  store_typing s ->
  module_restriction m ->
  instantiate s m v_imps ((s', inst, v_exps), start) ->
  (store_typing s').
  (* (exists C, inst_typing s' inst C) /\
  (exists tes, ext_typing_list s' v_exps tes) /\
  (pred_option (fun i => i < length s'.(s_funcs)) start).*)
  (* /\ store_extension s s' *)
Proof.
  move => s m v_imps s' inst v_exps start HStoreType HRestr HInst.

  (* Extract the artificial constraints we're imposing on the module *)
  unfold module_restriction in HRestr.
  destruct m => /=.
  simpl in HRestr.
  destruct HRestr as [-> [-> [-> [-> [-> [-> [-> ->]]]]]]].

  unfold instantiate, instantiation.instantiate in HInst.
  destruct HInst as [t_imps [t_exps [hs' [s'_end [? [? [? [HModType [HImpType [HAllocModule H]]]]]]]]]].

  destruct H as [HInstGlob [HInstElem [HInstData [HBoundElem [HBoundData [HStart HStore]]]]]].
  simpl in *.

  (* There are a lot of hypotheses here, but almost all of them simplify to a trivial condition due to the current constraint on the module. *)

  (* HInstGlob *)
  unfold instantiate_globals in HInstGlob.
  simpl in HInstGlob.
  inversion HInstGlob; subst; clear HInstGlob.

  (* HInstElem *)
  unfold instantiate_elem in HInstElem.
  simpl in HInstElem.
  inversion HInstElem; subst; clear HInstElem.

  (* HInstData *)
  unfold instantiate_data in HInstData.
  simpl in HInstData.
  inversion HInstData; subst; clear HInstData.

  (* HBoundData *)
  unfold check_bounds_data in HBoundData.
  simpl in HBoundData.
  (* this is vacuously true. *)
  clear HBoundData.

  (* HBoundElem *)
  unfold check_bounds_elem in HBoundElem.
  simpl in HBoundElem.
  clear HBoundElem.

  (* HCheckStart *)
  unfold check_start in HStart.
  simpl in HStart.
  move/eqP in HStart; subst.

  (* HStore *)
  unfold init_mems, init_tabs in HStore.
  simpl in HStore.
  move/eqP in HStore; subst.

  (* HModType *)
  (* This is an important part -- it gives a lot of validity information of the function references. *)
  unfold module_typing in HModType.
  destruct HModType as [fts [gts [HFuncType [_ [_ [HGlobType [_ [_ [_ [HImpValid _]]]]]]]]]].
  simpl in *.
  inversion HGlobType; subst; clear HGlobType.
  inversion HImpValid; subst; clear HImpValid.
  repeat rewrite List.app_nil_r in HFuncType.

  (* We know v_imps is empty as well *)
  inversion HImpType; subst; clear HImpType.
  simpl in *.
  

  (* Now, extract information from alloc_module. *)
  remember (alloc_funcs host_function s mod_funcs inst) as s_ifs.
  destruct s_ifs as [s' ifs].
  destruct inst.
  repeat (move/andP in HAllocModule; destruct HAllocModule as [HAllocModule ?]).
  simpl in *.
  move/eqP in H; subst.
  move/eqP in H0; subst.
  move/eqP in H1; subst.
  move/eqP in H2; subst.
  move/eqP in H3; subst.
  move/eqP in H4; subst.
  move/eqP in HAllocModule; subst.
  repeat rewrite List.app_nil_r in Heqs_ifs.

  (* We've reached the original simplified version we want, but with a much better shape of the lemma now for future extension. *)

  by eapply alloc_func_sound; eauto => //.
  
 
Admitted.

