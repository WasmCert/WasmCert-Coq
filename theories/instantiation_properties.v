From mathcomp Require Import ssreflect eqtype seq ssrbool ssrfun.
Require Export datatypes host operations properties opsem instantiation.
From stdpp Require Import list fin_maps gmap.
Require Export stdpp_aux.
(* We need a few helper lemmas from preservation. *)
Require Export type_preservation.

Section module_typing_det.

Lemma module_typing_det_import_aux m it1 et1 it2 et2:
  module_typing m it1 et1 ->
  module_typing m it2 et2 ->
  it1 = it2.
Proof.
  move => Hmt1 Hmt2.
  unfold module_typing in Hmt1, Hmt2.
  destruct m.
  destruct Hmt1 as [fts1 [gts1 [Hmft1 [Hmtt1 [Hmmt1 [Hmgt1 [Hmet1 [Hmdt1 [Hmst1 [Hmimt1 Hmext1]]]]]]]]]].
  destruct Hmt2 as [fts2 [gts2 [Hmft2 [Hmtt2 [Hmmt2 [Hmgt2 [Hmet2 [Hmdt2 [Hmst2 [Hmimt2 Hmext2]]]]]]]]]].
  
  clear - Hmimt1 Hmimt2.
  apply list_eq.
  move => i.
  rewrite -> Forall2_lookup in Hmimt1.
  specialize (Hmimt1 i).
  rewrite -> Forall2_lookup in Hmimt2.
  specialize (Hmimt2 i).    
  destruct (it1 !! i) eqn:Hitl1; destruct (it2 !! i) eqn:Hitl2; inversion Hmimt1; inversion Hmimt2; subst => //=.
  - rewrite <- H in H2.
    inversion H2; subst; clear H2.
    destruct x; simpl in *.
    unfold module_import_typing in *.
    destruct imp_desc; simpl in *; destruct e; destruct e0 => //.
    { (* func *)
      move/andP in H1; destruct H1.
      move/andP in H4; destruct H4.
      destruct (nth_error mod_types n) => //.
      move/eqP in H1.
      move/eqP in H3.
      by subst.
    }
    { (* table *)
      move/andP in H1; destruct H1.
      move/andP in H4; destruct H4.
      move/eqP in H0.
      move/eqP in H2.
      by subst.
    }
    { (* memory *)
      move/andP in H1; destruct H1.
      move/andP in H4; destruct H4.
      move/eqP in H0.
      move/eqP in H2.
      by subst.
    }
    { (* global *)
      move/eqP in H1.
      move/eqP in H4.
      by subst.
    }
  - by rewrite <- H in H3.
  - by rewrite <- H in H0.
Qed.


Lemma module_typing_det m it1 et1 it2 et2:
  module_typing m it1 et1 ->
  module_typing m it2 et2 ->
  (it1, et1) = (it2, et2).
Proof.
  move => Hmt1 Hmt2.
  specialize (module_typing_det_import_aux _ _ _ _ _ Hmt1 Hmt2) as ->.
  unfold module_typing in Hmt1, Hmt2.
  destruct m.
  destruct Hmt1 as [fts1 [gts1 [Hmft1 [Hmtt1 [Hmmt1 [Hmgt1 [Hmet1 [Hmdt1 [Hmst1 [Hmimt1 Hmext1]]]]]]]]]].
  destruct Hmt2 as [fts2 [gts2 [Hmft2 [Hmtt2 [Hmmt2 [Hmgt2 [Hmet2 [Hmdt2 [Hmst2 [Hmimt2 Hmext2]]]]]]]]]].

  (* Function types *)
  assert (fts1 = fts2) as Heqfts.
  { clear - Hmft1 Hmft2.
    apply list_eq.
    move => i.
    rewrite -> Forall2_lookup in Hmft1.
    specialize (Hmft1 i).
    rewrite -> Forall2_lookup in Hmft2.
    specialize (Hmft2 i).
    destruct (mod_funcs !! i) eqn: Hfli; inversion Hmft1; inversion Hmft2; subst => //=.
    destruct m, modfunc_type, y, y0; simpl in *.
    destruct H1 as [_ [Heqtf1 _]].
    destruct H4 as [_ [Heqtf2 _]].
    move/eqP in Heqtf1.
    move/eqP in Heqtf2.
    rewrite Heqtf1 in Heqtf2.
    by rewrite Heqtf2.
  }
  subst.

  (* Global types *)
  assert (gts1 = gts2) as Heqgts.
  { clear - Hmgt1 Hmgt2.
    apply list_eq.
    move => i.
    rewrite -> Forall2_lookup in Hmgt1.
    specialize (Hmgt1 i).
    rewrite -> Forall2_lookup in Hmgt2.
    specialize (Hmgt2 i).
    destruct (mod_globals !! i) eqn: Hgli; inversion Hmgt1; inversion Hmgt2; subst => //=.
    destruct m, modglob_type, y, y0; simpl in *.
    destruct H1 as [_ [Heqgt1 _]].
    destruct H4 as [_ [Heqgt2 _]].
    inversion Heqgt1.
    inversion Heqgt2.
    by subst.
  }
  subst.
  
  f_equal.
  clear - Hmext1 Hmext2.
  apply list_eq.
  move => i.
  rewrite -> Forall2_lookup in Hmext1.
  specialize (Hmext1 i).
  rewrite -> Forall2_lookup in Hmext2.
  specialize (Hmext2 i).    
  destruct (et1 !! i) eqn:Hetl1; destruct (et2 !! i) eqn:Hetl2; inversion Hmext1; inversion Hmext2; subst => //=.
  - rewrite <- H in H2.
    inversion H2; subst; clear H2.
    destruct x; simpl in *.
    unfold module_export_typing in *.
    destruct modexp_desc; [destruct f | destruct t | destruct m | destruct g]; simpl in *; destruct e; destruct e0 => //=.
    { (* func *)
      move/andP in H1; destruct H1.
      move/andP in H4; destruct H4.
      destruct (nth_error _ n) => //.
      move/eqP in H1.
      move/eqP in H3.
      by subst.
    }
    { (* table *)
      move/andP in H1; destruct H1.
      move/andP in H4; destruct H4.
      destruct (nth_error _ n) => //.
      move/eqP in H1.
      move/eqP in H3.
      by subst.
    }
    { (* memory *)
      move/andP in H1; destruct H1.
      move/andP in H4; destruct H4.
      destruct (nth_error _ n) => //.
      move/eqP in H1.
      move/eqP in H3.
      by subst.
    }
    { (* global *)
      move/andP in H1; destruct H1.
      move/andP in H4; destruct H4.
      destruct (nth_error _ n) => //.
      move/eqP in H1.
      move/eqP in H3.
      by subst.
    }
  - by rewrite <- H in H3.
  - by rewrite <- H in H0.
Qed.    
  
End module_typing_det.

Lemma N_nat_bin n:
  n = N.of_nat (ssrnat.nat_of_bin n).
Proof.
  destruct n => //=.
  replace (ssrnat.nat_of_pos p) with (Pos.to_nat p); first by rewrite positive_nat_N.
  induction p => //=.
  - rewrite Pos2Nat.inj_xI.
    f_equal.
    rewrite IHp.
    rewrite ssrnat.NatTrec.doubleE.
    rewrite - ssrnat.mul2n.
    by lias.
  - rewrite Pos2Nat.inj_xO.
    rewrite IHp.
    rewrite ssrnat.NatTrec.doubleE.
    rewrite - ssrnat.mul2n.
    by lias.
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

Section Instantiation_properties.

Definition assert_const1 (es: expr) : option value :=
  match es with
  | [:: BI_const v] => Some v
  | _ => None
  end.

Definition assert_const1_i32 (es: expr) : option i32 :=
  match es with
  | [:: BI_const (VAL_int32 v)] => Some v
  | _ => None
  end.

Definition assert_const1_i32_to_nat (es:expr) : nat :=
  match assert_const1_i32 es with
  | Some v => nat_of_int v
  | _ => 0
  end.

Definition ext_func_addrs := (map (fun x => match x with | Mk_funcidx i => i end)) ∘ ext_funcs.
Definition ext_tab_addrs := (map (fun x => match x with | Mk_tableidx i => i end)) ∘ ext_tabs.
Definition ext_mem_addrs := (map (fun x => match x with | Mk_memidx i => i end)) ∘ ext_mems.
Definition ext_glob_addrs := (map (fun x => match x with | Mk_globalidx i => i end)) ∘ ext_globs.

(* Getting the count of each type of imports from a module. This is to calculate the correct shift for indices of the exports in the Wasm store later. *)
Definition get_import_func_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | ID_func id => Some id
                                                                   | _ => None
                                                                    end) m.(mod_imports)).

Definition get_import_table_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | ID_table id => Some id
                                                                   | _ => None
                                                                    end) m.(mod_imports)).
Definition get_import_mem_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | ID_mem id => Some id
                                                                   | _ => None
                                                                    end) m.(mod_imports)).
Definition get_import_global_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | ID_global id => Some id
                                                                   | _ => None
                                                                      end) m.(mod_imports)).


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

Lemma ext_funcs_lookup_exist_inv (modexps: list module_export_desc) n idx:
  modexps !! n = Some (MED_func idx) ->
  exists k, ((ext_funcs modexps) !! k = Some idx).
Proof.
  move : n idx.
  induction modexps; move => n idx H => //=.
  destruct n; simpl in *.
  { inversion H; subst; by exists 0 => /=. }
  apply IHmodexps in H.
  destruct H as [k Hl].
  destruct a; try by exists k.
  by exists (S k).
Qed.

Lemma ext_tabs_lookup_exist_inv (modexps: list module_export_desc) n idx:
  modexps !! n = Some (MED_table idx) ->
  exists k, ((ext_tabs modexps) !! k = Some idx).
Proof.
  move : n idx.
  induction modexps; move => n idx H => //=.
  destruct n; simpl in *.
  { inversion H; subst; by exists 0 => /=. }
  apply IHmodexps in H.
  destruct H as [k Hl].
  destruct a; try by exists k.
  by exists (S k).
Qed.

Lemma ext_mems_lookup_exist_inv (modexps: list module_export_desc) n idx:
  modexps !! n = Some (MED_mem idx) ->
  exists k, ((ext_mems modexps) !! k = Some idx).
Proof.
  move : n idx.
  induction modexps; move => n idx H => //=.
  destruct n; simpl in *.
  { inversion H; subst; by exists 0 => /=. }
  apply IHmodexps in H.
  destruct H as [k Hl].
  destruct a; try by exists k.
  by exists (S k).
Qed.

Lemma ext_globs_lookup_exist_inv (modexps: list module_export_desc) n idx:
  modexps !! n = Some (MED_global idx) ->
  exists k, ((ext_globs modexps) !! k = Some idx).
Proof.
  move : n idx.
  induction modexps; move => n idx H => //=.
  destruct n; simpl in *.
  { inversion H; subst; by exists 0 => /=. }
  apply IHmodexps in H.
  destruct H as [k Hl].
  destruct a; try by exists k.
  by exists (S k).
Qed.

Definition gen_index offset len : list nat :=
  imap (fun i x => i+offset+x) (repeat 0 len).

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

Definition gen_func_instance mf inst : function_closure :=
  let ft := nth match modfunc_type mf with
                | Mk_typeidx n => n
                end (inst_types inst) (Tf [] []) in
  FC_func_native inst ft (modfunc_locals mf) (modfunc_body mf).
                

(* This is an actual interesting proof, technically *)
(* TODO: see if it's possible to refactor the 4 proofs into one *)
Lemma alloc_func_gen_index modfuncs ws inst ws' l:
  alloc_funcs ws modfuncs inst = (ws', l) ->
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
  - inversion Hallocfuncs; subst; clear Hallocfuncs.
    simpl.
    repeat split => //.
    by rewrite app_nil_r.
  - rewrite fold_left_app in Hallocfuncs.
    remember (fold_left _ modfuncs (ws,[])) as fold_res.
    simpl in Hallocfuncs.
    destruct fold_res as [ws0 l0].
    symmetry in Heqfold_res.
    unfold add_func in Hallocfuncs.
    inversion Hallocfuncs; subst; clear Hallocfuncs.
    rewrite map_app app_length /=.
    rewrite gen_index_extend.
    specialize (IHmodfuncs ws ws0 (rev l0)).
    destruct IHmodfuncs as [? [? [? [? ?]]]]; first by rewrite Heqfold_res.
    repeat split => //; try by eapply IHmodfuncs; rewrite Heqfold_res.
    + rewrite H.
      rewrite H0.
      by rewrite app_length map_length.
    + rewrite H0.
      rewrite - app_assoc.
      f_equal.
      by rewrite -> list_fmap_app.
Qed.

Lemma alloc_tab_gen_index modtabtypes ws ws' l:
  alloc_tabs ws modtabtypes = (ws', l) ->
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
  alloc_mems ws modmemtypes = (ws', l) ->
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
  alloc_globs ws modglobs g_inits = (ws', l) ->
  map (fun x => match x with | Mk_globalidx i => i end) l = gen_index (length (s_globals ws)) (length modglobs) /\
  ws'.(s_globals) = ws.(s_globals) ++ fmap (fun '({| modglob_type := gt; modglob_init := ge |}, v) => {| g_mut := gt.(tg_mut); g_val := v |} ) (combine modglobs g_inits) /\
 (* length ws'.(s_globals) = length ws.(s_globals) + length modglobs /\*)
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_mems) = ws'.(s_mems).
Proof.
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
Qed.

Lemma init_tabs_preserve ws inst e_inits melem ws':
  init_tabs ws inst e_inits melem = ws' ->
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

Lemma init_mems_preserve ws inst d_inits mdata ws':
  init_mems ws inst d_inits mdata = ws' ->
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

Lemma mod_imps_len_t m t_imps t_exps:
  module_typing m t_imps t_exps ->
  get_import_func_count m = length (ext_t_funcs t_imps) /\
  get_import_table_count m = length (ext_t_tabs t_imps) /\
  get_import_mem_count m = length (ext_t_mems t_imps) /\
  get_import_global_count m = length (ext_t_globs t_imps).
Proof.
  unfold get_import_func_count, get_import_table_count, get_import_mem_count, get_import_global_count.
  unfold module_typing.
  move => Hmt.
  destruct m.
  destruct Hmt as [fts [gts [? [? [? [? [? [? [? [Himptype ?]]]]]]]]]].
  simpl in *.
  clear - mod_imports Himptype.
  move : Himptype.
  move : t_imps fts gts.
  induction mod_imports; move => t_imps fts gts Himptype => //=.
  - apply Forall2_nil_inv_l in Himptype as ->.
    by simpl.
  - destruct t_imps; first by apply Forall2_nil_inv_r in Himptype.
    simpl in *.
    inversion Himptype; subst; clear Himptype.
    unfold module_import_typing in H2.
    destruct a, imp_desc => /=; simpl in H2; destruct e => //.
    all:
      try by (move/andP in H2;
      destruct H2 as [Hlen Hnth];
      move/eqP in Hnth; subst;
      simpl;
      apply IHmod_imports in H4 as [? [? [? ?]]] => //;
      repeat split => //;
      f_equal).
    move/eqP in H2; subst.
    simpl.
    apply IHmod_imports in H4 as [? [? [? ?]]] => //.
    repeat split => //.
    by f_equal.
Qed.

End Instantiation_properties.

