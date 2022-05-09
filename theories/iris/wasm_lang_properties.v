From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap proph_map.
Require Export iris iris_locations stdpp_aux.
Require Export datatypes host operations properties opsem.



Section wasm_lang_properties.
  Import DummyHosts.
  
  Let reducible := @reducible wasm_lang.
  Let reduce := @reduce host_function host_instance.

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.

  (* Note : the following lemma exists already in Coq's standard library, and 
   is ca  lled app_eq_unit *)
  Lemma app_eq_singleton: ∀ T (l1 l2 : list T) (a : T),
      l1 ++ l2 = [a] ->
      (l1 = [a] ∧ l2 = []) ∨ (l1 = [] ∧ l2 = [a]).
  Proof.
    move =>T.
    elim.
    move => l2 a Heq. right. by rewrite app_nil_l in Heq.
    move => a l l2 a0 a1 Heq. inversion Heq;subst.
    left. split. f_equiv.
    all: destruct l, a0;try done.
  Qed.

  Lemma rcons_eq (T: Type) (es1: list T) e1 es2 e2:
  es1 ++ [e1] = es2 ++ [e2] ->
  es1 = es2 /\ e1 = e2.
Proof.
  move: es2.
  induction es1 => //; move => es2 H.
  - destruct es2 => //=; first simpl in H; inversion H => //.
    by destruct es2.
  - destruct es2 => //=; first by destruct es1 => //.
    inversion H; subst; clear H.
    apply IHes1 in H2 as [-> ->].
    split => //.
Qed.
  

End wasm_lang_properties.

