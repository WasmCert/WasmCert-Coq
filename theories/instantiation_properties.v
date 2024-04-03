(** Properties of instantiation spec **)

From mathcomp Require Import ssreflect eqtype seq ssrbool ssrfun ssrnat.
Require Import Coq.Program.Equality NArith.
Require Export instantiation_spec.
Require Export type_preservation type_progress properties.

(* Some of the proofs were adapted from the Iris branch -- therefore the stdpp notations for now *)
Notation "l !! n" := (List.nth_error l n) (at level 10).

Section module_typing_det.

Lemma nth_error_same_length_list:
  forall (A B : Type) (l1 : seq.seq A) (l2 : seq.seq B) (i : nat) (m : A),
     length l1 = length l2 ->
     List.nth_error l1 i = Some m -> 
     exists n, List.nth_error l2 i = Some n.
Proof.
  move => A B l1 l2 i m Hlen Hl1.
  apply nth_error_Some_length in Hl1.
  rewrite Hlen in Hl1.
  apply List.nth_error_Some in Hl1.
  by destruct (l2 !! i) => //; eexists.
Qed.

Lemma repeat_lookup_Some {T: Type} (x y: T) n i:
  List.nth_error (List.repeat x n) i = Some y ->
  x = y /\ i < n.
Proof.
  move: i.
  induction n; destruct i => //=; move => H; try by inversion H; lias.
  apply IHn in H as [-> Hlt].
  split; by lias.
Qed.

Lemma NoDup_alt {T: Type} (l: list T):
  (forall i j x, l !! i = Some x -> l !! j = Some x -> i = j) -> List.NoDup l.
Proof.
  induction l; move => H => //; try by constructor.
  constructor.
  - move => Hin.
    apply List.In_nth_error in Hin as [n Hnth].
    specialize (H 0 (S n) a); simpl in H.
    by apply H in Hnth => //.
  - apply IHl.
    move => i j x Hnth1 Hnth2.
    specialize (H (S i) (S j) x); simpl in H.
    by apply H in Hnth1; lias.
Qed.

Lemma iota_lookup offset len k:
  k < len ->
  List.nth_error (iota offset len) k = Some (offset + k).
Proof.
  move : offset len.
  induction k; move => offset len; destruct len => //=; move => Hsize; try by lias.
  - by rewrite addn0.
  - rewrite addnS -addSn.
    by apply IHk.
Qed.

Lemma iota_lookup_Some offset len k x:
  List.nth_error (iota offset len) k = Some x ->
  x = offset + k /\ k < len.
Proof.
  move : offset len.
  induction k; move => offset len; destruct len => //=; move => Hsize; try by lias.
  - inversion Hsize; subst; clear Hsize.
    by rewrite addn0.
  - rewrite addnS -addSn.
    by apply IHk.
Qed.
    
Lemma iota_N_lookup offset len k:
  k < len ->
  List.nth_error (iota_N offset len) k = Some (N.of_nat (offset + k)).
Proof.
  move => Hlen.
  unfold iota_N.
  by rewrite nth_error_map' iota_lookup.
Qed.

Lemma iota_N_lookup_Some n l i x:
  List.nth_error (iota_N n l) i = Some x ->
  x = N.of_nat (n + i) /\ i < l.
Proof.
  unfold iota_N.
  move => Hl.
  apply nth_error_map in Hl as [v [Hnth Hmap]]; subst.
  by apply iota_lookup_Some in Hnth as [-> ?].
Qed.
 
Lemma iota_N_NoDup n l:
  List.NoDup (iota_N n l).
Proof.
  apply NoDup_alt.
  move => i j x Hli Hlj.
  apply iota_N_lookup_Some in Hli as [-> ?].
  apply iota_N_lookup_Some in Hlj as [? ?].
  by lias.
Qed.

Lemma iota_N_length n len:
  length (iota_N n len) = len.
Proof.
  unfold iota_N.
  by rewrite List.map_length length_is_size size_iota.
Qed.

Lemma iota_N_extend offset len:
  iota_N offset (len+1) = iota_N offset len ++ [::N.of_nat (offset+len)].
Proof.
  unfold iota_N.
  by rewrite iotaD map_cat => //=.
Qed.

Lemma iota_N_in n i offset len:
  List.nth_error (iota_N offset len) n = Some i  ->
  (i < N.of_nat (offset + len))%N.
Proof.
  move => H.
  apply iota_N_lookup_Some in H as [-> Hlt].
  repeat rewrite Nat2N.inj_add.
  rewrite <- N.add_lt_mono_l.
  by lias.
Qed.

Lemma iota_N_lookup_None: forall n m i,
  i >= m ->
  List.nth_error (iota_N n m) i = None.
Proof.
  move => n m i Hge.
  destruct (List.nth_error (iota_N n m) i) eqn:Hnth => //.
  exfalso.
  apply iota_N_lookup_Some in Hnth as [-> ?].
  by lias.
Qed.

(*
Lemma module_typing_det_import_aux m it1 et1 it2 et2:
  module_typing m it1 et1 ->
  module_typing m it2 et2 ->
  it1 = it2.
Proof.
  move => Hmt1 Hmt2.
  unfold module_typing in Hmt1, Hmt2.
  destruct m.
  destruct Hmt1 as [fts1 [tts1 [mts1 [gts1 [rts1 [Htt1 [Hmft1 [Hmtt1 [Hmmt1 [Hmgt1 [Hmet1 [Hmdt1 [Hmst1 [Hmimt1 Hmext1]]]]]]]]]]]]]].
  destruct Hmt2 as [fts2 [tts2 [mts2 [gts2 [rts2 [Htt2 [Hmft2 [Hmtt2 [Hmmt2 [Hmgt2 [Hmet2 [Hmdt2 [Hmst2 [Hmimt2 Hmext2]]]]]]]]]]]]]].
  
  clear - Hmimt1 Hmimt2.
  eapply Forall2_function_eq; eauto.
  move => x y z Heq1 Heq2; simpl in *.
  unfold module_import_typing, module_import_desc_typing in *.
  destruct x => /=; simpl in *.
  destruct imp_desc; simpl in *; destruct y, z => //; remove_bools_options => //.
  
  by subst.
Qed.
*)

(*
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
    eapply Forall2_function_eq; eauto.
    move => x y z Heq1 Heq2; simpl in *.
    unfold module_func_typing in *.
    simpl in *.
    destruct x, modfunc_type, y, z => /=; simpl in *.
    destruct Heq1 as [_ [Heq1 _]].
    destruct Heq2 as [_ [Heq2 _]].
    remove_bools_options.
    by rewrite - Heq1 Heq2.
  }
  subst.

  (* Global types *)
  assert (gts1 = gts2) as Heqgts.
  { clear - Hmgt1 Hmgt2.
    eapply Forall2_function_eq; eauto.
    move => x y z Heq1 Heq2; simpl in *.
    unfold module_func_typing in *.
    simpl in *.
    destruct x, modglob_type, y, z => /=; simpl in *.
    destruct Heq1 as [_ [Heq1 _]].
    destruct Heq2 as [_ [Heq2 _]].
    inversion Heq1; inversion Heq2; by subst. 
  }
  subst.
  
  f_equal.

  clear - Hmext1 Hmext2.
  eapply Forall2_function_eq; eauto.
  move => x y z Heq1 Heq2; simpl in *.
  unfold module_export_typing in *.
  simpl in *.
  destruct x, modexp_desc; [destruct f | destruct t | destruct m | destruct g]; destruct y, z; simpl in *; remove_bools_options; by subst => //.
Qed.    
*)
End module_typing_det.

Definition exp_default := MED_func 0%N.

(* Getting the count of each type of imports from a module. This is to calculate the correct shift for indices of the exports in the Wasm store later. *)
Definition get_import_func_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | MID_func id => Some id
                                                                   | _ => None
                                                                    end) m.(mod_imports)).

Definition get_import_table_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | MID_table id => Some id
                                                                   | _ => None
                                                                    end) m.(mod_imports)).
Definition get_import_mem_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | MID_mem id => Some id
                                                                   | _ => None
                                                                    end) m.(mod_imports)).
Definition get_import_global_count (m: module) := length (pmap (fun x => match x.(imp_desc) with
                                                                   | MID_global id => Some id
                                                                   | _ => None
                                                                      end) m.(mod_imports)).

Lemma ext_funcs_lookup_exist (modexps: list extern_value) n fn:
  (ext_funcs modexps) !! n = Some fn ->
  exists k, modexps !! k = Some (EV_func fn).
Proof.
  move: n fn.
  induction modexps; move => n tn Hextfunclookup; try by destruct n => //=.
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

Lemma ext_tables_lookup_exist (modexps: list extern_value) n tn:
  (ext_tables modexps) !! n = Some tn ->
  exists k, modexps !! k = Some (EV_table tn).
Proof.
  move: n tn.
  induction modexps; move => n tn Hexttablookup; try by destruct n => //=.
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

Lemma ext_mems_lookup_exist (modexps: list extern_value) n mn:
  (ext_mems modexps) !! n = Some mn ->
  exists k, modexps !! k = Some (EV_mem mn).
Proof.
  move: n mn.
  induction modexps; move => n mn Hextmemlookup; try by destruct n => //=.
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

Lemma ext_globals_lookup_exist (modexps: list extern_value) n fn:
  (ext_globals modexps) !! n = Some fn ->
  exists k, modexps !! k = Some (EV_global fn).
Proof.
  move: n fn.
  induction modexps; move => n tn Hextgloblookup; try by destruct n => //=.
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

Lemma ext_funcs_lookup_exist_inv (modexps: list extern_value) n idx:
  modexps !! n = Some (EV_func idx) ->
  exists k, ((ext_funcs modexps) !! k = Some idx).
Proof.
  move : n idx.
  induction modexps; move => n idx H; try by destruct n => //=.
  destruct n; simpl in *.
  { inversion H; subst; by exists 0 => /=. }
  apply IHmodexps in H.
  destruct H as [k Hl].
  destruct a; try by exists k.
  by exists (S k).
Qed.

Lemma ext_tables_lookup_exist_inv (modexps: list extern_value) n idx:
  modexps !! n = Some (EV_table idx) ->
  exists k, ((ext_tables modexps) !! k = Some idx).
Proof.
  move : n idx.
  induction modexps; move => n idx H; try by destruct n => //=.
  destruct n; simpl in *.
  { inversion H; subst; by exists 0 => /=. }
  apply IHmodexps in H.
  destruct H as [k Hl].
  destruct a; try by exists k.
  by exists (S k).
Qed.

Lemma ext_mems_lookup_exist_inv (modexps: list extern_value) n idx:
  modexps !! n = Some (EV_mem idx) ->
  exists k, ((ext_mems modexps) !! k = Some idx).
Proof.
  move : n idx.
  induction modexps; move => n idx H; try by destruct n => //=.
  destruct n; simpl in *.
  { inversion H; subst; by exists 0 => /=. }
  apply IHmodexps in H.
  destruct H as [k Hl].
  destruct a; try by exists k.
  by exists (S k).
Qed.

Lemma ext_globals_lookup_exist_inv (modexps: list extern_value) n idx:
  modexps !! n = Some (EV_global idx) ->
  exists k, ((ext_globals modexps) !! k = Some idx).
Proof.
  move : n idx.
  induction modexps; move => n idx H; try by destruct n => //=.
  destruct n; simpl in *.
  { inversion H; subst; by exists 0 => /=. }
  apply IHmodexps in H.
  destruct H as [k Hl].
  destruct a; try by exists k.
  by exists (S k).
Qed.

Section Host.

Context `{ho: host}.

(* Proving relations between stores obtained by alloc_Xs *)
Lemma alloc_Xs_IP {A B: Type} (f: store_record -> A -> store_record * B) s_init xs s_end ys (R: store_record -> store_record -> list A -> list B -> Prop) :
  alloc_Xs f s_init xs = (s_end, ys) ->
  (R s_init s_init [::] [::]) ->
  (forall s s0 x xs' ys' s' y,
    (s, y) = f s' x ->
    R s0 s' xs' ys' ->
    R s0 s (xs' ++ [::x]) (ys' ++ [::y])) ->
  R s_init s_end xs ys.
Proof.
  move: s_init s_end ys.
  induction xs using List.rev_ind => //=; move => s_init s_end ys Hallocxs Hinit IH; simpl in *.
  - unfold alloc_Xs in Hallocxs.
    simpl in Hallocxs.
    by injection Hallocxs as ->; subst.
  - unfold alloc_Xs in Hallocxs.
    rewrite List.fold_left_app in Hallocxs.
    simpl in Hallocxs.
    
    remember (List.fold_left _ xs _) as fold_res.
    destruct fold_res as [s0 ys0].
    remember (f s0 x) as sf.
    destruct sf as [s' y'].
    injection Hallocxs as ->; subst.
    eapply IH; eauto.
    apply IHxs; eauto.
    unfold alloc_Xs.
    by rewrite <- Heqfold_res.
Qed.

Lemma alloc_func_iota_N modfuncs ws inst ws' l:
  alloc_funcs ws modfuncs inst = (ws', l) ->
  l = iota_N (length (s_funcs ws)) (length modfuncs) /\
  ws'.(s_funcs) = ws.(s_funcs) ++ map (fun mf => gen_func_instance mf inst) modfuncs /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals) /\
  ws.(s_elems) = ws'.(s_elems) /\
  ws.(s_datas) = ws'.(s_datas).
Proof.
  unfold alloc_funcs.
  move => Halloc.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => ys = iota_N _ (length xs) /\ _))
    in Halloc; eauto => //=.
  - unfold iota_N => /=.
    repeat split.
    by rewrite cats0.
  - move => s s0 x xs' ys' s' y Hallocx [Hys [Hcomp [? [? [?[??]]]]]].
    repeat rewrite -> iota_N_iota_N in *.
    unfold alloc_func, add_func in Hallocx; injection Hallocx as ->; subst => /=.
    rewrite List.app_length map_cat iota_N_extend Hcomp => /=.
    repeat split => //=.
    + by rewrite List.app_length List.map_length.
    + by rewrite catA => /=.
Qed.

Lemma alloc_table_iota_N modtables ws ws' l:
  alloc_tabs ws modtables = (ws', l) ->
  l = iota_N (length (s_tables ws)) (length modtables) /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws'.(s_tables) = ws.(s_tables) ++ map (fun mf => gen_table_instance mf (VAL_ref_null (mf.(tt_elem_type)))) modtables /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals) /\
  ws.(s_elems) = ws'.(s_elems) /\
  ws.(s_datas) = ws'.(s_datas).
Proof.
  unfold alloc_tabs.
  move => Halloc.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => ys = iota_N _ (length xs) /\ _))
    in Halloc; eauto => //=.
  - unfold iota_N => /=.
    repeat split.
    by rewrite cats0.
  - move => s s0 x xs' ys' s' y Hallocx [Hys [? [Hcomp [? [?[??]]]]]].
    repeat rewrite -> iota_N_iota_N in *.
    unfold alloc_tab, alloc_tab_ref, add_table in Hallocx.
    destruct x, tt_limits.
    injection Hallocx as ->; subst => /=.
    rewrite List.app_length map_cat iota_N_extend Hcomp => /=.
    repeat split => //=.
    + by rewrite List.app_length List.map_length => /=.
    + by rewrite catA => /=.
Qed.

Lemma alloc_mem_iota_N modmems ws ws' l:
  alloc_mems ws modmems = (ws', l) ->
  l = iota_N (length (s_mems ws)) (length modmems) /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws'.(s_mems) = ws.(s_mems) ++ map (fun mf => gen_mem_instance mf) modmems /\
  ws.(s_globals) = ws'.(s_globals) /\
  ws.(s_elems) = ws'.(s_elems) /\
  ws.(s_datas) = ws'.(s_datas).
Proof.
  unfold alloc_mems.
  move => Halloc.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => ys = iota_N _ (length xs) /\ _))
    in Halloc; eauto => //=.
  - unfold iota_N => /=.
    repeat split.
    by rewrite cats0.
  - move => s s0 x xs' ys' s' y Hallocx [Hys [? [? [Hcomp [?[??]]]]]].
    repeat rewrite -> iota_N_iota_N in *.
    unfold alloc_mem, add_mem in Hallocx.
    destruct x.
    injection Hallocx as ->; subst => /=.
    rewrite List.app_length map_cat iota_N_extend Hcomp => /=.
    repeat split => //=.
    + by rewrite List.app_length List.map_length => /=.
    + by rewrite catA => /=.
Qed.

Lemma combine_snoc {T1 T2: Type}: forall (l1: list T1) (l2: list T2) lc x,
  lc ++ [::x] = List.combine l1 l2 ->
  length l1 = length l2 ->
  exists l1' l2' a b,
    (l1 = l1' ++ [::a] /\ l2 = l2' ++ [::b] /\ lc = List.combine l1' l2' /\ x = (a, b)).
Proof.
  induction l1 as [| a l1']; move => l2 lc x Hcomb Hlen; first by destruct lc.
  destruct l2 as [|b l2'], lc as [|p lc'] => //; simpl in *; try by rewrite combine_nil in Hcomb.
  - destruct l1', l2' => //; simpl in *.
    injection Hcomb as ->.
    by exists nil, nil, a, b.
  - simpl in *.
    injection Hlen as Hlen.
    injection Hcomb as ->.
    apply IHl1' in H => //.
    destruct H as [l1'' [l2'' [a' [b' [-> [-> [-> ->]]]]]]].
    by exists (a :: l1''), (b :: l2''), a', b'.
Qed.

Lemma alloc_global_iota_N modglobals g_inits ws ws' l:
  alloc_globs ws modglobals g_inits = (ws', l) ->
  length g_inits = length modglobals ->
  l = iota_N (length (s_globals ws)) (length modglobals) /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws'.(s_globals) = ws.(s_globals) ++ map (fun '({| modglob_type := gt; modglob_init := ge |}, v) => {| g_type := gt; g_val := v |} ) (List.combine modglobals g_inits) /\
  ws.(s_elems) = ws'.(s_elems) /\
  ws.(s_datas) = ws'.(s_datas).
Proof.
  unfold alloc_globs.
  move => Halloc.
  remember (List.combine modglobals g_inits) as comb.
  move : modglobals g_inits Heqcomb.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => forall globs g_inits, xs = List.combine globs g_inits -> length g_inits = length globs -> ys = iota_N _ _ /\ _))
    in Halloc; eauto => //=.
  - unfold iota_N => /=.
    repeat split; last by rewrite cats0.
    by destruct globs, g_inits => //.
  - repeat setoid_rewrite iota_N_iota_N.
    move => s s0 x xs' ys' s' y Hallocx Hind modglobs g_inits Hcomb Hgloblen.
    apply combine_snoc in Hcomb; last by lias.
    destruct Hcomb as [modglobs' [g_inits' [g [v [-> [-> [-> ->]]]]]]].
    destruct (Hind modglobs' g_inits') as [Hys [? [? [? [Hcomp [??]]]]]] => //; clear Hind.
    { repeat rewrite List.app_length in Hgloblen; simpl in Hgloblen. by lias. }
    unfold alloc_glob, add_glob in Hallocx. injection Hallocx as ->; subst => /=.
    rewrite map_cat List.app_length iota_N_extend Hcomp => /=.
    rewrite List.app_length.
    repeat split => //=.
    + do 3 f_equal.
      repeat rewrite List.app_length in Hgloblen; simpl in Hgloblen.
      rewrite List.map_length List.combine_length.
      by lias.
    + rewrite -catA.
      by destruct g.
Qed.

Lemma alloc_elem_iota_N modelems r_inits ws ws' l:
  alloc_elems ws modelems r_inits = (ws', l) ->
  length r_inits = length modelems ->
  l = iota_N (length (s_elems ws)) (length modelems) /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals) /\
  ws'.(s_elems) = ws.(s_elems) ++ map (fun '(elem, refs) => {| eleminst_type := elem.(modelem_type); eleminst_elem := refs |} ) (List.combine modelems r_inits) /\
  ws.(s_datas) = ws'.(s_datas).
Proof.
  unfold alloc_elems.
  move => Halloc.
  remember (List.combine modelems r_inits) as comb.
  move : modelems r_inits Heqcomb.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => forall elems r_inits, xs = List.combine elems r_inits -> length r_inits = length elems -> ys = iota_N _ _ /\ _))
    in Halloc; eauto => //=.
  - unfold iota_N => /=.
    repeat split; last by rewrite cats0.
    by destruct elems, r_inits => //.
  - repeat setoid_rewrite iota_N_iota_N.
    move => s s0 x xs' ys' s' y Hallocx Hind modelems r_inits Hcomb Helemlen.
    apply combine_snoc in Hcomb; last by lias.
    destruct Hcomb as [modelems' [r_inits' [r [v [-> [-> [-> ->]]]]]]].
    destruct (Hind modelems' r_inits') as [Hys [? [? [? [? [Hcomp ?]]]]]] => //; clear Hind.
    { repeat rewrite List.app_length in Helemlen; simpl in Helemlen. by lias. }
    unfold alloc_elem, add_elem in Hallocx. injection Hallocx as ->; subst => /=.
    rewrite map_cat List.app_length iota_N_extend Hcomp => /=.
    rewrite List.app_length.
    repeat split => //=.
    + do 3 f_equal.
      repeat rewrite List.app_length in Helemlen; simpl in Helemlen.
      rewrite List.map_length List.combine_length.
      by lias.
    + rewrite -catA.
      by destruct r.
Qed.

Lemma alloc_data_iota_N moddatas ws ws' l:
  alloc_datas ws moddatas = (ws', l) ->
  l = iota_N (length (s_datas ws)) (length moddatas) /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals) /\
  ws.(s_elems) = ws'.(s_elems) /\
  ws'.(s_datas) = ws.(s_datas) ++ map (fun md => {| datainst_data := md.(moddata_init) |} ) moddatas.
Proof.
  unfold alloc_datas.
  move => Halloc.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => ys = iota_N _ (length xs) /\ _))
    in Halloc; eauto => //=.
  - unfold iota_N => /=.
    repeat split.
    by rewrite cats0.
  - move => s s0 x xs' ys' s' y Hallocx [Hys [? [? [? [? [? Hcomp]]]]]].
    repeat rewrite -> iota_N_iota_N in *.
    unfold alloc_data, add_data in Hallocx.
    destruct x.
    injection Hallocx as ->; subst => /=.
    rewrite List.app_length map_cat iota_N_extend Hcomp => /=.
    repeat split => //=.
    + by rewrite List.app_length List.map_length => /=.
    + by rewrite catA => /=.
Qed.

(*
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
  get_import_table_count m = length (ext_t_tables t_imps) /\
  get_import_mem_count m = length (ext_t_mems t_imps) /\
  get_import_global_count m = length (ext_t_globals t_imps).
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
  - apply Forall2_length in Himptype.
    by destruct t_imps => //=.
  - destruct t_imps; first by apply Forall2_length in Himptype.
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
*)

Lemma bet_const_exprs_len tc es t1 t2:
  const_exprs tc es ->
  be_typing tc es (Tf t1 t2) ->
  length t2 = length es + length t1.
Proof.
  move: t1 t2.
  induction es; move => t1 t2 Hconst Hbet.
  { invert_be_typing; subst.
    apply values_subtyping_size in Hbet.
    by repeat rewrite length_is_size.
  }
  { rewrite <- cat1s in Hbet.
    invert_be_typing.
    simpl in Hconst; remove_bools_options.
    destruct tf_principal.
    eapply IHes in H2_comp => //.
    unfold const_expr in H.
    rewrite H2_comp => /=.
    destruct a => //; invert_be_typing; simpl in Hinvgoal.
    all: try by
      (injection Hinvgoal as -> ->;
      apply instr_subtyping_size_exact in Htisub; simpl in *;
      repeat rewrite length_is_size;
         by lias).
    all: by
      (extract_premise;
       injection Hconjl as -> ->;
      apply instr_subtyping_size_exact in Htisub; simpl in *;
      repeat rewrite length_is_size;
         by lias).
  }
Qed.
  
Lemma const_exprs_impl tc es t:
  const_exprs tc es ->
  be_typing tc es (Tf [::] [::t]) ->
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

Lemma value_no_reduce (hs hs': host_state) s f v s' f' e':
  reduce hs s f [::$V v] hs' s' f' e' ->
  False.
Proof.
  move => Hred.
  dependent induction Hred; subst; (try by repeat destruct vs => //; destruct v as [v | v | v]; destruct v => //); (try by repeat destruct vcs => //; destruct v as [v | v | v]; destruct v => //).
  { inversion H; subst; clear H; try by destruct v as [v | v | v]; destruct v => //.
    by destruct lh as [vs ? | ? vs]; simpl in H1; destruct v as [v | v | v]; destruct v; do 2 destruct vs => //.
  }
  { destruct lh as [vs ? | ? vs] => //=; simpl in H; last by destruct v as [v | v | v]; destruct v => //; do 2 destruct vs => //=.
    destruct vs => //=; last first.
    { destruct vs, es, l => //=.
      by apply reduce_not_nil in Hred.
    }
    destruct es => //=; first by apply reduce_not_nil in Hred.
    by destruct es, l => //=.
  }
Qed.

Lemma reduce_trans_value hs1 s1 f1 v1 hs2 s2 f2 v2:
  reduce_trans (hs1, s1, f1, [::$V v1]) (hs2, s2, f2, [::$V v2]) ->
  v1 = v2.
Proof.
  move => Hred.
  unfold reduce_trans in Hred.
  apply Operators_Properties.clos_rt_rt1n_iff in Hred.
  inversion Hred => //; first by apply ve_inj.
  unfold reduce_tuple in H.
  destruct y as [[[??]?]?].
  by apply value_no_reduce in H.
Qed.

Lemma reduce_ref_func hs s f hs' s' f' i e:
  reduce hs s f [::AI_basic (BI_ref_func i)] hs' s' f' e ->
  exists addr, lookup_N f.(f_inst).(inst_funcs) i = Some addr /\ e = [::$V (VAL_ref (VAL_ref_func addr))].
Proof.
  move => Hred.
  dependent induction Hred; subst; (try by repeat destruct vcs => //); (try by repeat destruct vs => //).
  { inversion H; subst; clear H; try by repeat destruct vs => //.
    destruct lh as [vs ? | ? vs]; simpl in H1; by do 2 destruct vs => //=.
  }
  { by exists addr. }
  { destruct lh as [vs ? | ? vs] => //=; simpl in H; last by do 2 destruct vs => //.
    destruct vs as [ | v ?]; last by destruct v as [v | v | v]; destruct v => //=.
    destruct es => //=; first by apply reduce_not_nil in Hred.
    destruct es, l => //=.
    simpl in *.
    inversion H; subst; clear H.
    rewrite cats0.
    by eapply IHHred.
  }
Qed.

Lemma reduce_trans_ref_func hs1 s1 f1 x hs2 s2 f2 vref:
  reduce_trans (hs1, s1, f1, [:: AI_basic (BI_ref_func x)]) (hs2, s2, f2, [::$V (VAL_ref vref)]) ->
  exists addr, lookup_N f1.(f_inst).(inst_funcs) x = Some addr /\ vref = VAL_ref_func addr.
Proof.
  move => Hred.
  unfold reduce_trans in Hred.
  apply Operators_Properties.clos_rt_rt1n_iff in Hred.
  inversion Hred; subst; clear Hred; first by destruct vref.
  destruct y as [[[??]?]?].
  unfold reduce_tuple, opsem.reduce_tuple in H.
  apply reduce_ref_func in H.
  destruct H as [addr [Hnth ->]].
  inversion H0; subst; clear H0 => //.
  - destruct vref => //; simpl in H4.
    injection H4 as <-.
    by exists addr.
  - unfold reduce_tuple, opsem.reduce_tuple in H.
    destruct y as [[[??]?]?].
    by apply value_no_reduce in H.
Qed.

Lemma reduce_global_get hs s f hs' s' f' i e:
  reduce hs s f [::AI_basic (BI_global_get i)] hs' s' f' e ->
  exists v, sglob_val s (f_inst f) i = Some v /\ e = [::$V v].
Proof.
  move => Hred.
  dependent induction Hred; subst; (try by repeat destruct vcs => //); (try by repeat destruct vs => //).
  { inversion H; subst; clear H; try by repeat destruct vs => //.
    destruct lh as [vs ? | ? vs]; simpl in H1; by do 2 destruct vs => //=.
  }
  { by exists v. }
  { destruct lh as [vs ? | ? vs] => //=; simpl in H; last by do 2 destruct vs => //.
    destruct vs as [ | v ?]; last by destruct v as [v | v | v]; destruct v => //=.
    destruct es => //=; first by apply reduce_not_nil in Hred.
    destruct es, l => //=.
    simpl in *.
    inversion H; subst; clear H.
    rewrite cats0.
    by eapply IHHred.
  }
Qed.
    
Lemma reduce_trans_global_get hs s f hs' s' f' i v:
  reduce_trans (hs, s, f, [::AI_basic (BI_global_get i)]) (hs', s', f', [::$V v]) ->
  sglob_val s (f_inst f) i = Some v.
Proof.
  move => Hred.
  unfold reduce_trans, opsem.reduce_trans in *.
  apply Operators_Properties.clos_rt_rt1n_iff in Hred.
  inversion Hred; subst; clear Hred; first by repeat destruct v.
  destruct y as [[[??]?]?].
  unfold reduce_tuple, opsem.reduce_tuple in H.
  apply reduce_global_get in H.
  destruct H as [v' [Hsgv ->]].
  inversion H0; subst; clear H0 => //.
  - uapply Hsgv; f_equal.
    by apply ve_inj.
  - unfold reduce_tuple, opsem.reduce_tuple in H.
    destruct y as [[[??]?]?].
    by apply value_no_reduce in H.
Qed.

(*
Section Instantiation_det.

Lemma modglobs_const: forall tc modglobs gt,
  Forall2 (module_glob_typing tc) modglobs gt ->
  Forall (fun g => exists e, g.(modglob_init) = [::e] /\ const_expr tc e) modglobs.
Proof.
  move => tc modglobs. move: tc.
  induction modglobs; move => tc gt Hall2; destruct gt => //=.
  - by apply Forall2_length in Hall2.
  - inversion Hall2 as [ | ???? Ha Hall2']; subst.
    constructor.
    + unfold module_glob_typing in Ha.
      destruct a => /=; destruct Ha as [Hconst [-> Hbet]].
      by apply const_exprs_impl in Hbet; eauto.
    + by eapply IHmodglobs; eauto.
Qed.

Local Definition instantiate_globals := instantiate_globals host_function host_instance.
Local Definition instantiate_elem := instantiate_elem host_function host_instance.
Local Definition instantiate_data := instantiate_data host_function host_instance.

Lemma module_glob_init_det m v_imps t_imps inst hs1 s1 hs2 s2 gi1 gi2:
  module_typing m v_imps t_imps ->
  instantiate_globals inst hs1 s1 m gi1 ->
  instantiate_globals inst hs2 s2 m gi2 ->
  (forall i, i < length (ext_t_globals v_imps) -> sglob_val s1 inst i = sglob_val s2 inst i) ->
  gi1 = gi2.
Proof.
  move => Hmt Hgi1 Hgi2 Hsgveq.
  unfold module_typing in Hmt.
  unfold instantiate_globals, instantiation_spec.instantiate_globals in *.
  destruct m; simpl in *.
  destruct Hmt as [fts [gts [_ [_ [_ [Hmgt _]]]]]].
  assert (length gi1 = length gi2) as Hlen; first by (apply Forall2_length in Hgi1; apply Forall2_length in Hgi2; rewrite Hgi1 in Hgi2).

  remember (Build_t_context _ _ _ _ _ _ _ _) as tc.
  apply modglobs_const in Hmgt.

  eapply Forall2_function_eq_cond; eauto => //.
  move => x y z Hconst Heq1 Heq2.
  simpl in *.

  destruct x as [gt gi]; simpl in *.
  destruct Hconst as [e [-> Hconst]]; simpl in *.
  unfold const_expr in Hconst.
  rewrite Heqtc in Hconst; simpl in Hconst.
  destruct e; simpl in * => //; remove_bools_options.
  { apply reduce_trans_global_get in Heq1.
    apply reduce_trans_global_get in Heq2.
    specialize (Hsgveq i).
    rewrite Hsgveq in Heq1; last by move/ssrnat.ltP in H; lias.
    rewrite Heq1 in Heq2.
    by injection Heq2.
  }
  { apply reduce_trans_const in Heq1.
    apply reduce_trans_const in Heq2.
    by subst.
  }
Qed.

Lemma module_elem_init_det m v_imps t_imps inst hs1 hs2 s eo1 eo2:
  module_typing m v_imps t_imps ->
  instantiate_elem inst hs1 s m eo1 ->
  instantiate_elem inst hs2 s m eo2 ->
  eo1 = eo2.
Proof.
  move => Hmt Heo1 Heo2.
  unfold module_typing in Hmt.
  unfold instantiate_elem, instantiation_spec.instantiate_elem in *.
  destruct m; simpl in *.
  destruct Hmt as [fts [gts [_ [_ [_ [_ [Hmet _]]]]]]].
  assert (length eo1 = length eo2) as Hlen; first by (apply Forall2_length in Heo1; apply Forall2_length in Heo2; rewrite Heo1 in Heo2).

  eapply Forall2_function_eq_cond; eauto => //.
  move => x y z Hconst Heq1 Heq2.
  simpl in *.

  destruct x as [[et] eo ei]; simpl in *.
  destruct Hconst as [Hconst [Hbet [Hilen Halllen]]].
  apply const_exprs_impl in Hbet => //; clear Hconst.
  destruct Hbet as [e [-> Hconst]].
  unfold const_expr in Hconst; simpl in Hconst.
  destruct e; simpl in * => //; remove_bools_options.
  { apply reduce_trans_global_get in Heq1.
    apply reduce_trans_global_get in Heq2.
    rewrite Heq1 in Heq2.
    by injection Heq2.
  }
  { apply reduce_trans_const in Heq1.
    apply reduce_trans_const in Heq2.
    rewrite Heq1 in Heq2.
    by injection Heq2.
  }
Qed.

Lemma module_data_init_det m v_imps t_imps inst hs1 hs2 s do1 do2:
  module_typing m v_imps t_imps ->
  instantiate_data inst hs1 s m do1 ->
  instantiate_data inst hs2 s m do2 ->
  do1 = do2.
Proof.
  move => Hmt Hdo1 Hdo2.
  unfold module_typing in Hmt.
  unfold instantiate_data, instantiation_spec.instantiate_data in *.
  destruct m; simpl in *.
  destruct Hmt as [fts [gts [_ [_ [_ [_ [_ [Hmdt _]]]]]]]].
  assert (length do1 = length do2) as Hlen; first by (apply Forall2_length in Hdo1; apply Forall2_length in Hdo2; rewrite Hdo1 in Hdo2).

  eapply Forall2_function_eq_cond; eauto => //.
  move => x y z Hconst Heq1 Heq2.
  simpl in *.

  destruct x as [[dm] d_o di]; simpl in *.
  destruct Hconst as [Hconst [Hbet Hilen]].
  apply const_exprs_impl in Hbet => //; clear Hconst.
  destruct Hbet as [e [-> Hconst]].
  unfold const_expr in Hconst; simpl in Hconst.
  destruct e; simpl in * => //; remove_bools_options.
  { apply reduce_trans_global_get in Heq1.
    apply reduce_trans_global_get in Heq2.
    rewrite Heq1 in Heq2.
    by injection Heq2.
  }
  { apply reduce_trans_const in Heq1.
    apply reduce_trans_const in Heq2.
    rewrite Heq1 in Heq2.
    by injection Heq2.
  }
Qed.
*)

Lemma vt_imps_comp_len s (v_imps: list extern_value) t_imps:
  List.Forall2 (external_typing s) v_imps t_imps ->
  (length (ext_funcs v_imps) = length (ext_t_funcs t_imps) /\
    length (ext_tables v_imps) = length (ext_t_tables t_imps) /\
    length (ext_mems v_imps) = length (ext_t_mems t_imps) /\
    length (ext_globals v_imps) = length (ext_t_globals t_imps)).
Proof.
  move: t_imps.
  induction v_imps; move => t_imps Hexttype; destruct t_imps; try by apply List.Forall2_length in Hexttype.
  inversion Hexttype; subst; clear Hexttype.
  apply IHv_imps in H4.
  destruct H4 as [Hft [Htt [Hmt Hgt]]].
  unfold external_typing, ext_typing in H2.
  destruct a, e; simpl in H2; remove_bools_options => //=; repeat split; try by f_equal.
Qed.

Lemma subtyping_comp_len t_imps1 t_imps2:
  List.Forall2 import_subtyping t_imps1 t_imps2->
  (length (ext_t_funcs t_imps1) = length (ext_t_funcs t_imps2) /\
    length (ext_t_tables t_imps1) = length (ext_t_tables t_imps2) /\
    length (ext_t_mems t_imps1) = length (ext_t_mems t_imps2) /\
    length (ext_t_globals t_imps1) = length (ext_t_globals t_imps2)).
Proof.
  move: t_imps2.
  induction t_imps1; move => t_imps2 Hexttype; destruct t_imps2; try by apply List.Forall2_length in Hexttype.
  inversion Hexttype; subst; clear Hexttype.
  apply IHt_imps1 in H4.
  destruct H4 as [Hft [Htt [Hmt Hgt]]].
  unfold import_subtyping in H2.
  destruct a, e; simpl in H2; remove_bools_options => //=; repeat split; try by lias.
Qed.

(*
Local Definition external_typing := external_typing host_function.

Lemma alloc_module_det hs1 hs2 s m v_imps t_imps t_exps g_inits g_inits' s_res1 s_res2 inst inst' exps exps':
  module_typing m t_imps t_exps ->
  Forall2 (external_typing s) v_imps t_imps ->
  length g_inits = length (mod_globals m) -> 
  length g_inits' = length (mod_globals m) -> 
  alloc_module s m v_imps g_inits (s_res1, inst, exps) ->
  alloc_module s m v_imps g_inits' (s_res2, inst', exps') ->
  instantiate_globals inst hs1 s_res1 m g_inits ->
  instantiate_globals inst' hs2 s_res2 m g_inits' ->
  (inst, exps) = (inst', exps') /\
  g_inits = g_inits' /\
  (s_res1 = s_res2).
Proof.
  move => Hmt Hexttype Hglen1 Hglen2 Ham1 Ham2 Hinitg1 Hinitg2.
  unfold alloc_module, instantiation_spec.alloc_module in *.
  remember (instantiation_spec.alloc_funcs host_function s (mod_funcs m) inst) as res_f.
  destruct res_f as [s0 idf].
  remember (instantiation_spec.alloc_tabs host_function s0 (map modtab_type (mod_tables m))) as res_t.
  destruct res_t as [s1 idt].
  remember (instantiation_spec.alloc_mems host_function s1 (mod_mems m)) as res_m.
  destruct res_m as [s2 idm].
  remember (instantiation_spec.alloc_globs host_function s2 (mod_globals m) g_inits) as res_g.
  destruct res_g as [s3 idg].
  symmetry in Heqres_f.
  symmetry in Heqres_t.
  symmetry in Heqres_m.
  symmetry in Heqres_g.
  apply alloc_func_iota_N in Heqres_f.
  apply alloc_tab_iota_N in Heqres_t.
  apply alloc_mem_iota_N in Heqres_m.
  apply alloc_glob_iota_N in Heqres_g => //.
  destruct s0, s1, s2, s3; simpl in *.
  destruct Heqres_f as [Hidf [-> [<- [<- <-]]]].
  destruct Heqres_t as [Hidt [-> [<- [<- <-]]]].
  destruct Heqres_m as [Hidm [-> [<- [<- <-]]]].
  destruct Heqres_g as [Hidg [-> [<- [<- <-]]]].
  
  remember (instantiation_spec.alloc_funcs host_function s (mod_funcs m) inst') as res_f'.
  destruct res_f' as [s0' idf'].
  remember (instantiation_spec.alloc_tabs host_function s0' (map modtab_type (mod_tables m))) as res_t'.
  destruct res_t' as [s1' idt'].
  remember (instantiation_spec.alloc_mems host_function s1' (mod_mems m)) as res_m'.
  destruct res_m' as [s2' idm'].
  remember (instantiation_spec.alloc_globs host_function s2' (mod_globals m) g_inits') as res_g'.
  destruct res_g' as [s3' idg'].
  symmetry in Heqres_f'.
  symmetry in Heqres_t'.
  symmetry in Heqres_m'.
  symmetry in Heqres_g'.
  apply alloc_func_iota_N in Heqres_f'.
  apply alloc_tab_iota_N in Heqres_t'.
  apply alloc_mem_iota_N in Heqres_m'.
  apply alloc_glob_iota_N in Heqres_g' => //.
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
    eapply module_glob_init_det; eauto => //.
    move => i Hilen.
    unfold sglob_val, sglob, sglob_ind => /=.
    repeat rewrite nth_error_lookup.
    repeat rewrite map_map.
    repeat rewrite list_lookup_map.
    remember ((ext_globals v_imps ++ idg') !! i) as gi.
    specialize (vt_imps_comp_len _ _ _ _ Hexttype) as Hcomplen.
    destruct Hcomplen as [_ [_ [_ Hglen]]].
    rewrite <- Hglen in Hilen.
    rewrite nth_error_app1 in Heqgi => //.
    destruct gi as [g |]; symmetry in Heqgi; last by rewrite -> nth_error_None in Heqgi; lias.
    destruct g.
    assert (n < length (s_globals s)) as Hnlen.
    { unfold module_typing in Hmt.
      destruct m; simpl in *.
      destruct Hmt as [fts [gts [_ [_ [_ [_ [_ [_ [_ [Hit _]]]]]]]]]].
      apply ext_globals_lookup_exist in Heqgi as [k Hvi].
      eapply Forall2_lookup in Hexttype; eauto.
      destruct Hexttype as [y [Hnth Hexttype]].
      inversion Hexttype; subst; clear Hexttype.
      by move/ssrnat.ltP in H0.
    }
    subst s_res1 s_res2 => /=.
    rewrite Coqlib.list_map_nth => /=.
    rewrite nth_error_app1 => //.
    rewrite Heqgi => /=.
    by repeat rewrite nth_error_app1 => //.
  }
  split => //; last by subst.
Qed.

Local Definition instantiate := instantiate host_function host_instance.

Lemma instantiate_det s m vimps res res':
  instantiate s m vimps res ->
  instantiate s m vimps res' ->
  res = res'.
Proof.
  move => Hinst1 Hinst2.
  destruct res as [[[s1 inst1] exp1] start1].
  destruct res' as [[[s2 inst2] exp2] start2].
  unfold instantiate, instantiation_spec.instantiate in *.
  destruct Hinst1 as (t_imps1 & t_exps1 & hs1 & ws1 & g_inits1 & e_offs1 & d_offs1 & Hmodtype1 & Hexttype1 & Hallocmodule1 & Hinstglob1 & Hinstelem1 & Hinstdata1 & Hcbelem1 & Hcbdata1 & Hcstart1 & Hws1).
  destruct Hinst2 as [t_imps2 [t_exps2 [hs2 [ws2 [g_inits2 [e_offs2 [d_offs2 [Hmodtype2 [Hexttype2 [Hallocmodule2 [Hinstglob2 [Hinstelem2 [Hinstdata2 [Hcbelem2 [Hcbdata2 [Hcstart2 Hws2]]]]]]]]]]]]]]]].

  specialize (module_typing_det _ _ _ _ _ Hmodtype1 Hmodtype2) as Hvteq.
  inversion Hvteq; subst; clear Hvteq.

  (* Instance, alloc_module store, and exports *)
  eapply alloc_module_det in Hallocmodule1; eauto => //.
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
  { by eapply module_elem_init_det; eauto. }
  
  assert (d_offs1 = d_offs2) as Hdoffeq.
  { by eapply module_data_init_det; eauto. }

  subst.
  move/eqP in Hws1.
  move/eqP in Hws2.
  by subst.
Qed.
  
End Instantiation_det.
*)
End Host.
