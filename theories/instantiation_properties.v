Require Import Coq.Program.Equality.
From mathcomp Require Import ssreflect eqtype seq ssrbool ssrfun.
Require Export datatypes host operations properties opsem instantiation.
From stdpp Require Import list fin_maps gmap.
Require Export stdpp_aux.
(* We need a few helper lemmas from preservation. *)
Require Export type_preservation type_progress.

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

Section Instantiation_det.

Lemma bet_const_exprs_len tc es t1 t2:
  const_exprs tc es ->
  be_typing tc es (Tf t1 t2) ->
  length t2 = length es + length t1.
Proof.
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
Qed.
  
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

Lemma const_no_reduce s f v s' f' e':
  reduce s f [AI_basic (BI_const v)] s' f' e' ->
  False.
Proof.
  move => Hred.
  dependent induction Hred; subst; try by repeat destruct vcs => //.
  { inversion H; subst; clear H; try by repeat destruct vs => //.
    by apply lfilled_implies_starts in H1 => //.
  }
  { move/lfilledP in H.
    inversion H; subst; clear H; last by repeat destruct vs => //.
    destruct vs => //=; last first.
    { destruct vs, es, es'0 => //=.
      by apply reduce_not_nil in Hred.
    }
    destruct es => //=; first by apply reduce_not_nil in Hred.
    destruct es, es'0 => //=.
    simpl in H1.
    inversion H1; subst; clear H1.
    by eapply IHHred.
  }
Qed.
  
Lemma reduce_trans_const s1 f1 v1 s2 f2 v2:
  reduce_trans (s1, f1, [AI_basic (BI_const v1)]) (s2, f2, [AI_basic (BI_const v2)]) ->
  v1 = v2.
Proof.
  move => Hred.
  unfold reduce_trans in Hred.
  apply Operators_Properties.clos_rt_rt1n_iff in Hred.
  inversion Hred => //.
  unfold reduce_tuple in H.
  destruct y as [[??]?].
  by apply const_no_reduce in H.
Qed.

Lemma reduce_get_global s f s' f' i e:
  reduce s f [AI_basic (BI_get_global i)] s' f' e ->
  exists v, sglob_val s (f_inst f) i = Some v /\ e = [AI_basic (BI_const v)].
Proof.
  move => Hred.
  dependent induction Hred; subst; try by repeat destruct vcs => //.
  { inversion H; subst; clear H; try by repeat destruct vs => //.
    by apply lfilled_implies_starts in H1 => //.
  }
  { by exists v. }
  { move/lfilledP in H.
    inversion H; subst; clear H; last by repeat destruct vs => //.
    destruct vs => //=; last first.
    { inversion H1; subst.
      by destruct vs => //=.
    }
    simpl in H1.
    destruct es => //=; first by apply reduce_not_nil in Hred.
    destruct es, es'0 => //=.
    simpl in H1.
    inversion H1; subst; clear H1.
    specialize (IHHred i).
    move/lfilledP in H0.
    inversion H0; subst; clear H0.
    simpl; rewrite cats0.
    by apply IHHred.
  }
Qed.
    
Lemma reduce_trans_get_global s f s' f' i v:
  reduce_trans (s, f, [AI_basic (BI_get_global i)]) (s', f', [AI_basic (BI_const v)]) ->
  sglob_val s (f_inst f) i = Some v.
Proof.
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
Qed.
  
Lemma module_glob_init_det m v_imps t_imps inst s1 s2 gi1 gi2:
  module_typing m v_imps t_imps ->
  instantiate_globals inst s1 m gi1 ->
  instantiate_globals inst s2 m gi2 ->
  (forall i, i < length (ext_t_globs v_imps) -> sglob_val s1 inst i = sglob_val s2 inst i) ->
  gi1 = gi2.
Proof.
  move => Hmt Hgi1 Hgi2 Hsgveq.
  unfold module_typing in Hmt.
  unfold instantiate_globals in *.
  destruct m; simpl in *.
  destruct Hmt as [fts [gts [_ [_ [_ [Hmgt _]]]]]].
  assert (length gi1 = length gi2) as Hlen; first by (apply Forall2_length in Hgi1; apply Forall2_length in Hgi2; rewrite Hgi1 in Hgi2).
  apply list_eq.
  move => i.
  destruct (gi1 !! i) as [v1 | ] eqn:Hg1; last first.
  { destruct (gi2 !! i) eqn:Hg2 => //; by apply lookup_lt_Some in Hg2; apply lookup_ge_None in Hg1; lias. }
  { destruct (gi2 !! i) as [v2 | ] eqn:Hg2 => //; last by apply lookup_lt_Some in Hg1; apply lookup_ge_None in Hg2; lias.
    rewrite -> Forall2_lookup in Hgi1.
    rewrite -> Forall2_lookup in Hgi2.
    rewrite -> Forall2_lookup in Hmgt.
    specialize (Hgi1 i).
    specialize (Hgi2 i).
    specialize (Hmgt i).
    rewrite Hg1 in Hgi1.
    rewrite Hg2 in Hgi2.
    inversion Hgi1; subst; clear Hgi1.
    inversion Hgi2; subst; clear Hgi2.
    rewrite <- H0 in H.
    inversion H; subst; clear H.
    rewrite <- H0 in Hmgt.
    inversion Hmgt; subst; clear Hmgt.
    destruct x0.
    unfold module_glob_typing in H4.
    destruct H4 as [Hconst [-> Hbet]].
    apply const_exprs_impl in Hbet => //.
    destruct Hbet as [e [-> Hconste]].
    unfold const_exprs, const_expr in Hconste.
    destruct e => //; simpl in *.
    { apply reduce_trans_get_global in H1.
      apply reduce_trans_get_global in H3.
      specialize (Hsgveq i0).
      simpl in H1, H3.
      move/andP in Hconst.
      destruct Hconst as [Hconst _].
      move/andP in Hconst.
      destruct Hconst as [Hilen _].
      move/ssrnat.ltP in Hilen.
      rewrite <- Hsgveq in H3 => //.
      by rewrite H3 in H1.
    }
    { apply reduce_trans_const in H1.
      apply reduce_trans_const in H3.
      by subst.
    }
  }
Qed.

Lemma module_elem_init_det m v_imps t_imps inst s eo1 eo2:
  module_typing m v_imps t_imps ->
  instantiate_elem inst s m eo1 ->
  instantiate_elem inst s m eo2 ->
  eo1 = eo2.
Proof.
  move => Hmt Heo1 Heo2.
  unfold module_typing in Hmt.
  unfold instantiate_elem in *.
  destruct m; simpl in *.
  destruct Hmt as [fts [gts [_ [_ [_ [_ [Hmet _]]]]]]].
  assert (length eo1 = length eo2) as Hlen; first by (apply Forall2_length in Heo1; apply Forall2_length in Heo2; rewrite Heo1 in Heo2).
  apply list_eq.
  move => i.
  destruct (eo1 !! i) as [v1 | ] eqn:He1; last first.
  { destruct (eo2 !! i) eqn:He2 => //; by apply lookup_lt_Some in He2; apply lookup_ge_None in He1; lias. }
  { destruct (eo2 !! i) as [v2 | ] eqn:He2 => //; last by apply lookup_lt_Some in He1; apply lookup_ge_None in He2; lias.
    rewrite -> Forall2_lookup in Heo1.
    rewrite -> Forall2_lookup in Heo2.
    rewrite -> Forall_lookup in Hmet.
    specialize (Heo1 i).
    specialize (Heo2 i).
    specialize (Hmet i).
    rewrite He1 in Heo1.
    rewrite He2 in Heo2.
    inversion Heo1; subst; clear Heo1.
    inversion Heo2; subst; clear Heo2.
    rewrite <- H0 in H.
    inversion H; subst; clear H.
    rewrite <- H0 in Hmet.
    specialize (Hmet x0).
    destruct x0, modelem_table; simpl in *.
    destruct Hmet as [Hconst [Hbet [Hlen1 Hlen2]]] => //.
    apply const_exprs_impl in Hbet => //.
    destruct Hbet as [e [-> Hconste]].
    unfold const_exprs, const_expr in Hconste.
    destruct e => //; simpl in *.
    { apply reduce_trans_get_global in H1.
      apply reduce_trans_get_global in H3.
      rewrite H1 in H3.
      by inversion H3.
    }
    { apply reduce_trans_const in H1.
      apply reduce_trans_const in H3.
      subst; by inversion H1.
    }
  }
Qed.

Lemma module_data_init_det m v_imps t_imps inst s do1 do2:
  module_typing m v_imps t_imps ->
  instantiate_data inst s m do1 ->
  instantiate_data inst s m do2 ->
  do1 = do2.
Proof.
  move => Hmt Hdo1 Hdo2.
  unfold module_typing in Hmt.
  unfold instantiate_data in *.
  destruct m; simpl in *.
  destruct Hmt as [fts [gts [_ [_ [_ [_ [_ [Hmdt _]]]]]]]].
  assert (length do1 = length do2) as Hlen; first by (apply Forall2_length in Hdo1; apply Forall2_length in Hdo2; rewrite Hdo1 in Hdo2).
  apply list_eq.
  move => i.
  destruct (do1 !! i) as [v1 | ] eqn:Hd1; last first.
  { destruct (do2 !! i) eqn:Hd2 => //; by apply lookup_lt_Some in Hd2; apply lookup_ge_None in Hd1; lias. }
  { destruct (do2 !! i) as [v2 | ] eqn:Hd2 => //; last by apply lookup_lt_Some in Hd1; apply lookup_ge_None in Hd2; lias.
    rewrite -> Forall2_lookup in Hdo1.
    rewrite -> Forall2_lookup in Hdo2.
    rewrite -> Forall_lookup in Hmdt.
    specialize (Hdo1 i).
    specialize (Hdo2 i).
    specialize (Hmdt i).
    rewrite Hd1 in Hdo1.
    rewrite Hd2 in Hdo2.
    inversion Hdo1; subst; clear Hdo1.
    inversion Hdo2; subst; clear Hdo2.
    rewrite <- H0 in H.
    inversion H; subst; clear H.
    rewrite <- H0 in Hmdt.
    specialize (Hmdt x0).
    destruct x0, moddata_data; simpl in *.
    destruct Hmdt as [Hconst [Hbet Hleni]] => //.
    apply const_exprs_impl in Hbet => //.
    destruct Hbet as [e [-> Hconste]].
    unfold const_exprs, const_expr in Hconste.
    destruct e => //; simpl in *.
    { apply reduce_trans_get_global in H1.
      apply reduce_trans_get_global in H3.
      rewrite H1 in H3.
      by inversion H3.
    }
    { apply reduce_trans_const in H1.
      apply reduce_trans_const in H3.
      subst; by inversion H1.
    }
  }
Qed.

Lemma vt_imps_comp_len s (v_imps: list v_ext) t_imps:
  Forall2 (external_typing s) v_imps t_imps ->
  (length (ext_funcs v_imps) = length (ext_t_funcs t_imps) /\
    length (ext_tabs v_imps) = length (ext_t_tabs t_imps) /\
    length (ext_mems v_imps) = length (ext_t_mems t_imps) /\
    length (ext_globs v_imps) = length (ext_t_globs t_imps)).
Proof.
  move: t_imps.
  induction v_imps; move => t_imps Hexttype; destruct t_imps; try by apply Forall2_length in Hexttype.
  inversion Hexttype; subst; clear Hexttype.
  apply IHv_imps in H4.
  destruct H4 as [Hft [Htt [Hmt Hgt]]].
  destruct a; inversion H2; subst; clear H2 => //=; by repeat split; lias.
Qed.
  
Lemma alloc_module_det s m v_imps t_imps t_exps g_inits g_inits' s_res1 s_res2 inst inst' exps exps':
  module_typing m t_imps t_exps ->
  Forall2 (external_typing s) v_imps t_imps ->
  length g_inits = length (mod_globals m) -> 
  length g_inits' = length (mod_globals m) -> 
  alloc_module s m v_imps g_inits (s_res1, inst, exps) ->
  alloc_module s m v_imps g_inits' (s_res2, inst', exps') ->
  instantiate_globals inst s_res1 m g_inits ->
  instantiate_globals inst' s_res2 m g_inits' ->
  (inst, exps) = (inst', exps') /\
  g_inits = g_inits' /\
  (s_res1 = s_res2).
Proof.
  move => Hmt Hexttype Hglen1 Hglen2 Ham1 Ham2 Hinitg1 Hinitg2.
  unfold alloc_module in *.
  remember (alloc_funcs s (mod_funcs m) inst) as res_f.
  destruct res_f as [s0 idf].
  remember (alloc_tabs s0 (map modtab_type (mod_tables m))) as res_t.
  destruct res_t as [s1 idt].
  remember (alloc_mems s1 (mod_mems m)) as res_m.
  destruct res_m as [s2 idm].
  remember (alloc_globs s2 (mod_globals m) g_inits) as res_g.
  destruct res_g as [s3 idg].
  symmetry in Heqres_f.
  symmetry in Heqres_t.
  symmetry in Heqres_m.
  symmetry in Heqres_g.
  apply alloc_func_gen_index in Heqres_f.
  apply alloc_tab_gen_index in Heqres_t.
  apply alloc_mem_gen_index in Heqres_m.
  apply alloc_glob_gen_index in Heqres_g => //.
  destruct s0, s1, s2, s3; simpl in *.
  destruct Heqres_f as [Hidf [-> [<- [<- <-]]]].
  destruct Heqres_t as [Hidt [-> [<- [<- <-]]]].
  destruct Heqres_m as [Hidm [-> [<- [<- <-]]]].
  destruct Heqres_g as [Hidg [-> [<- [<- <-]]]].
  
  remember (alloc_funcs s (mod_funcs m) inst') as res_f'.
  destruct res_f' as [s0' idf'].
  remember (alloc_tabs s0' (map modtab_type (mod_tables m))) as res_t'.
  destruct res_t' as [s1' idt'].
  remember (alloc_mems s1' (mod_mems m)) as res_m'.
  destruct res_m' as [s2' idm'].
  remember (alloc_globs s2' (mod_globals m) g_inits') as res_g'.
  destruct res_g' as [s3' idg'].
  symmetry in Heqres_f'.
  symmetry in Heqres_t'.
  symmetry in Heqres_m'.
  symmetry in Heqres_g'.
  apply alloc_func_gen_index in Heqres_f'.
  apply alloc_tab_gen_index in Heqres_t'.
  apply alloc_mem_gen_index in Heqres_m'.
  apply alloc_glob_gen_index in Heqres_g' => //.
  destruct s0', s1', s2', s3'; simpl in *.
  destruct Heqres_f' as [Hidf' [-> [<- [<- <-]]]].
  destruct Heqres_t' as [Hidt' [-> [<- [<- <-]]]].
  destruct Heqres_m' as [Hidm' [-> [<- [<- <-]]]].
  destruct Heqres_g' as [Hidg' [-> [<- [<- <-]]]].
  
  rewrite <- Hidf' in Hidf.

  assert (idf = idf').
  { clear - Hidf.
    move: Hidf.
    move: idf'.
    induction idf as [|fi ?]; move => idf'; destruct idf' => //=.
    move => H.
    destruct fi, f.
    inversion H; subst; clear H.
    f_equal.
    by apply IHidf.
  }
  subst.

  
  rewrite <- Hidt' in Hidt.

  assert (idt = idt').
  { clear - Hidt.
    move: Hidt.
    move: idt'.
    induction idt as [|ti ?]; move => idt'; destruct idt' => //=.
    move => H.
    destruct ti, t.
    inversion H; subst; clear H.
    f_equal.
    by apply IHidt.
  }
  subst.

  
  rewrite <- Hidm' in Hidm.

  assert (idm = idm').
  { clear - Hidm.
    move: Hidm.
    move: idm'.
    induction idm as [|mi ?]; move => idm'; destruct idm' => //=.
    move => H.
    destruct mi, m.
    inversion H; subst; clear H.
    f_equal.
    by apply IHidm.
  }
  subst.

  
  rewrite <- Hidg' in Hidg.

  assert (idg = idg').
  { clear - Hidg.
    move: Hidg.
    move: idg'.
    induction idg as [|gi ?]; move => idg'; destruct idg' => //=.
    move => H.
    destruct gi, g.
    inversion H; subst; clear H.
    f_equal.
    by apply IHidg.
  }
  subst.

  move/andP in Ham1; move/andP in Ham2.
  destruct Ham1 as [Ham1 Hsres1].
  destruct Ham2 as [Ham2 Hsres2].
  move/eqP in Hsres1; move/eqP in Hsres2; subst.
  move/andP in Ham1; move/andP in Ham2.
  destruct Ham1 as [Ham1 Hig1].
  destruct Ham2 as [Ham2 Hig2].
  move/eqP in Hig1.
  move/eqP in Hig2.
  move/andP in Ham1; move/andP in Ham2.
  destruct Ham1 as [Ham1 Him1].
  destruct Ham2 as [Ham2 Him2].
  move/eqP in Him1.
  move/eqP in Him2.
  move/andP in Ham1; move/andP in Ham2.
  destruct Ham1 as [Ham1 Hit1].
  destruct Ham2 as [Ham2 Hit2].
  move/eqP in Hit1.
  move/eqP in Hit2.
  move/andP in Ham1; move/andP in Ham2.
  destruct Ham1 as [Ham1 Hif1].
  destruct Ham2 as [Ham2 Hif2].
  move/eqP in Hif1.
  move/eqP in Hif2.
  move/andP in Ham1; move/andP in Ham2.
  destruct Ham1 as [Ham1 Hitype1].
  destruct Ham2 as [Ham2 Hitype2].
  move/eqP in Hitype1.
  move/eqP in Hitype2.
  rewrite <- Hif2 in Hif1.
  rewrite <- Hit2 in Hit1.
  rewrite <- Him2 in Him1.
  rewrite <- Hig2 in Hig1.
  rewrite <- Hitype2 in Hitype1.
  destruct inst, inst'.
  simpl in *.
  subst.
  split => //.

  move/eqP in Ham1; move/eqP in Ham2.
  assert (g_inits = g_inits') as Heqgi.
  {
    eapply module_glob_init_det => //.
    move => i Hilen.
    unfold sglob_val, sglob, sglob_ind => /=.
    repeat rewrite nth_error_lookup.
    repeat rewrite map_fmap.
    repeat rewrite list_lookup_fmap.
    remember ((ext_globs v_imps ++ idg') !! i) as gi.
    specialize (vt_imps_comp_len _ _ _ Hexttype) as Hcomplen.
    destruct Hcomplen as [_ [_ [_ Hglen]]].
    rewrite lookup_app in Heqgi.
    rewrite <- Hglen in Hilen.
    destruct (ext_globs v_imps !! i) eqn:Hgvi; last by apply lookup_ge_None in Hgvi; lias.
    subst gi.
    simpl.
    destruct g.
    assert (n < length (s_globals s)) as Hnlen.
    { unfold module_typing in Hmt.
      destruct m; simpl in *.
      destruct Hmt as [fts [gts [_ [_ [_ [_ [_ [_ [_ [Hit _]]]]]]]]]].
      rewrite -> Forall2_lookup in Hexttype.
      apply ext_globs_lookup_exist in Hgvi.
      destruct Hgvi as [k Hvi].
      specialize (Hexttype k).
      rewrite Hvi in Hexttype.
      inversion Hexttype; subst; clear Hexttype.
      inversion H1; subst; clear H1.
      by move/ssrnat.ltP in H2.
    }
    subst s_res1 s_res2 => /=.
    repeat rewrite nth_error_lookup.
    repeat rewrite lookup_app.
    destruct (s_globals s !! n) eqn:Hsgn => //=.
    exfalso. apply lookup_ge_None in Hsgn. by lias.
  }
  split => //; last by subst.
Qed.
  
Lemma instantiate_det s m vimps res res':
  instantiate s m vimps res ->
  instantiate s m vimps res' ->
  res = res'.
Proof.
  move => Hinst1 Hinst2.
  destruct res as [[[s1 inst1] exp1] start1].
  destruct res' as [[[s2 inst2] exp2] start2].
  unfold instantiate, instantiation.instantiate in *.
  destruct Hinst1 as (t_imps1 & t_exps1 & ws1 & g_inits1 & e_offs1 & d_offs1 & Hmodtype1 & Hexttype1 & Hallocmodule1 & Hinstglob1 & Hinstelem1 & Hinstdata1 & Hcbelem1 & Hcbdata1 & Hcstart1 & Hws1).
  destruct Hinst2 as [t_imps2 [t_exps2 [ws2 [g_inits2 [e_offs2 [d_offs2 [Hmodtype2 [Hexttype2 [Hallocmodule2 [Hinstglob2 [Hinstelem2 [Hinstdata2 [Hcbelem2 [Hcbdata2 [Hcstart2 Hws2]]]]]]]]]]]]]]].

  specialize (module_typing_det _ _ _ _ _ Hmodtype1 Hmodtype2) as Hvteq.
  inversion Hvteq; subst; clear Hvteq.

  (* Instance, alloc_module store, and exports *)
  eapply alloc_module_det in Hallocmodule1 => //.
  3: { by apply Forall2_length in Hinstglob1. }
  2: { by apply Forall2_length in Hinstglob2. }

  destruct Hallocmodule1 as [Hieeq [Hgieq Hwseq]].
  inversion Hieeq; subst; clear Hieeq.

  (* Start *)
  unfold check_start in *.
  move/eqP in Hcstart1; move/eqP in Hcstart2.
  rewrite Hcstart2 in Hcstart1; subst.
  repeat f_equal.

  (* Final store *)
  assert (e_offs1 = e_offs2) as Heoffeq.
  { by eapply module_elem_init_det. }
  
  assert (d_offs1 = d_offs2) as Hdoffeq.
  { by eapply module_data_init_det. }

  subst.
  move/eqP in Hws1.
  move/eqP in Hws2.
  by subst.
Qed.
  
End Instantiation_det.

End Instantiation_properties.

