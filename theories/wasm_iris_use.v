From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
Require Export wasm_iris.
Set Default Proof Using "Type". (* what is this? *)

Record loc := { loc_car : Z }.
Instance loc_eq_decision : EqDecision loc.
Proof. solve_decision. Qed.

Instance loc_inhabited : Inhabited loc := populate {|loc_car := 0 |}.

Instance loc_countable : Countable loc.
Proof. by apply (inj_countable' loc_car (λ i, {| loc_car := i |})); intros []. Qed.

Program Instance loc_infinite : Infinite loc :=
  inj_infinite (λ p, {| loc_car := p |}) (λ l, Some (loc_car l)) _.
Next Obligation. done. Qed.


Definition proph_id := positive.

From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export proph_map.
Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_gen_heapG :> gen_heapG loc val Σ;
  heapG_proph_mapG :> proph_mapG proph_id (val * val) Σ
}.

Instance heapG_irisG `{!heapG Σ} : irisG wasm_lang Σ := {
  iris_invG := heapG_invG;
  state_interp σ κs _ := True%I
(*    (gen_heap_ctx σ.(heap) ∗ proph_map_ctx κs σ.(used_proph_id))%I*);
  fork_post _ := True%I;
                                                       }.

Definition xx i := (ConstInt32 (Wasm_int.int_of_nat (Wasm_int.mixin wasm.i32_r) i)).

Definition my_add : wasm_iris.expr :=
  [Basic (EConst (xx 3));
     Basic (EConst (xx 2));
     Basic (Binop_i T_i32 Add)].

(* problem here :-( *)
Lemma myadd_spec `{!heapG Σ} (s : stuckness) (E : coPset) (Φ : iProp Σ) (v : val) :
  WP my_add @ s;E {{ fun v => exists v', v = xx 5 :: v' }}%I.
Proof.
Qed.
