From stdpp Require Import base sets gmap.

From intdet.utils Require Export graph.
From intdet Require Import syntax head_semantics semantics.

(******************************************************************************)
(* Reducible at path relation. *)

Inductive reducible : expr -> store -> Prop :=
| RedHead : forall e σ σ' e',
  head_step e σ e' σ' ->
  reducible e σ
| RedCtx : forall K σ e,
    reducible e σ ->
    reducible (fill_item K e) σ
| RedPar : forall σ e1 e2,
    (¬ (is_val e1) ∨ ¬ (is_val e2)) ->
    (¬ is_val e1 -> reducible e1 σ) ->
    (¬ is_val e2 -> reducible e2 σ) ->
    reducible (RunPar e1 e2) σ.

Ltac solve_red_head :=
  eapply RedHead; eauto using head_step.

Lemma reducible_if σ (b:bool) e1 e2 :
  reducible (If b e1 e2) σ.
Proof. solve_red_head. Qed.

Lemma reducible_let_val σ x (v:val) e :
  reducible (Let x v e) σ.
Proof. solve_red_head. Qed.

Lemma reducible_join σ (v1 v2:val):
  reducible (RunPar v1 v2) σ.
Proof. solve_red_head. Qed.

Lemma reducible_fork σ e1 e2:
  reducible (Par e1 e2) σ.
Proof. solve_red_head. Qed.

Lemma reducible_code σ self arg code:
  reducible (Code self arg code) σ.
Proof. solve_red_head. Qed.

Lemma reducible_load σ vs (v:val) (l:loc) (i:Z) :
  σ !! l = Some vs ->
  (0 <= i < Z.of_nat (length vs))%Z ->
  vs !! (Z.to_nat i) = Some v ->
  reducible (Load l i) σ.
Proof. intros; solve_red_head. Qed.

Lemma reducible_store σ vs (v v':val) (i:Z) (l:loc) :
  σ !! l = Some vs ->
  (0 <= i < Z.of_nat (length vs))%Z ->
  reducible (Store l i v') σ.
Proof. intros; solve_red_head. Qed.

Lemma reducible_alloc σ (i:Z) :
  (0 <= i)%Z ->
  reducible (Alloc i) σ.
Proof.
  intros. eapply RedHead.
  apply HeadAlloc; eauto.
  { apply is_fresh. }
Qed.

Lemma reducible_call σ x1 x2 x3 x:
  reducible (Call (VCode x1 x2 x3) (Val x)) σ.
Proof. intros. solve_red_head. Qed.

Lemma reducible_call_prim σ p v1 v2 v :
  eval_call_prim p v1 v2 = Some v ->
  reducible (CallPrim p v1 v2) σ.
Proof. intros; solve_red_head. Qed.

Lemma reducible_cas σ (l:loc) vs (i:Z) (v0 v1 v2:val) :
  σ !! l = Some vs ->
  (0 <= i < Z.of_nat (length vs))%Z ->
  vs !! (Z.to_nat i) = Some v0 ->
  reducible (CAS l i v1 v2) σ.
Proof. intros; solve_red_head. Qed.

Lemma reducible_no_val σ e :
  reducible e σ ->
  ¬ is_val e.
Proof.
  inversion 1; subst.
  { eauto using head_step_no_val. }
  { intros ?; elim_ctx.  }
  { compute_done. }
Qed.

Lemma reducible_assert σ :
  reducible (Assert true) σ.
Proof. solve_red_head. Qed.

Lemma reducible_pair (v1 v2:val) σ :
  reducible (Pair v1 v2) σ.
Proof. solve_red_head. Qed.

Lemma reducible_fst (v1 v2:val) σ :
  reducible (Fst (VPair v1 v2)) σ.
Proof. solve_red_head. Qed.

Lemma reducible_snd (v1 v2:val) σ :
  reducible (Snd (VPair v1 v2)) σ.
Proof. solve_red_head. Qed.

Lemma reducible_length σ vs (l:loc) :
  σ !! l = Some vs ->
  reducible (Length l) σ.
Proof. intros; solve_red_head. Qed.
