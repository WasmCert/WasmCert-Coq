From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export iris_reduce_det_prelude.

Lemma unop_det v op t s f s' f' es:
  reduce s f [AI_basic (BI_const v); AI_basic (BI_unop t op)] s' f' es ->
  reduce_det_goal s f [AI_basic (BI_const (app_unop op v))] s' f' es [AI_basic (BI_const v); AI_basic (BI_unop t op)].
Proof.
  move => Hred.
  - (* example of a usage of [ only_one ] : in this subgoal, we know that Hred2 is
         the hypothesis [ [AI_basic (BI_const v) ; AI_basic (BI_unop t op) ] -> es2 ].
         [ only_one ] selects the left disjunct in the conclusion, meaning we wish
         to show that in this case, there was indeed determinism. Then it performs a 
         case analysis on Hred2. Most cases have a left-hand-side very different from
         [AI_basic (BI_const v) ; AI_basic (BI_unop t op)] and can thus be exfalsoed.
         Some cases, like the r_label case, require a little more effort, but the tactic
         can handle most difficulties. See the next comment for an example of when 
         [ only_one ] cannot exfalso all irrelevant cases *)
  by only_one [AI_basic (BI_const v) ; AI_basic (BI_unop t op)] Hred.
Qed.
