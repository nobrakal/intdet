From stdpp Require Import base sets fin_sets.
From intdet.lang Require Import syntax semantics.

Ltac not_ctx K H := apply step_no_val in H; elim_ctx_sure.

Ltac inv_fst := inversion 1.

Lemma invert_step_if σ (v:val) e1 e2 σ' e' :
  step (If v e1 e2) σ e' σ' ->
  exists b, σ'=σ /\ v=VBool b /\ e'=(if b then e1 else e2).
Proof.
  inv_fst; subst; try now not_ctx K H1.
  inversion H0; subst. naive_solver.
Qed.

Lemma invert_step_let_val σ x (v:val) e σ' e' :
  step (Let x v e) σ e' σ' ->
  σ'=σ /\ e'=(subst' x v e).
Proof.
  inv_fst; subst; try now not_ctx K H1.
  inversion H0; subst. naive_solver.
Qed.

Lemma invert_step_code σ self arg code σ' e' :
  step (Code self arg code) σ e' σ' ->
  σ'=σ /\ e'=Val (VCode self arg code).
Proof.
  inv_fst; subst; try now not_ctx K H1.
  inversion H0; subst. naive_solver.
Qed.

Lemma invert_step_assert σ (v:val) σ' e' :
  step (Assert v) σ e' σ' ->
  σ'=σ /\ e'=VUnit /\ v=VBool true.
Proof.
  inv_fst; subst; try now not_ctx K H1.
  inversion H0; subst. naive_solver.
Qed.

Lemma invert_step_load σ (l:loc) (w:val) σ' e' :
  step (Load l w) σ e' σ' ->
  ∃ vs (v:val) i, w=VInt i /\ σ !! l = Some vs /\ (0 <= i < Z.of_nat (length vs))%Z /\
                 vs !! (Z.to_nat i) = Some v /\ e'=v /\ σ' = σ.
Proof.
  inv_fst; subst; try now not_ctx K H1.
  inversion H0; subst. naive_solver.
Qed.

Lemma invert_step_bind K el σl el' σl' :
  ¬ is_val el ->
  step (fill_item K el) σl el' σl' ->
  exists el0, el' = fill_item K el0 /\ step el σl el0 σl'.
Proof.
  intros ?. inv_fst; subst.
  { exfalso. by eapply head_step_no_ctx. }
  { eapply fill_item_inj in H1. naive_solver.
    all:eauto using step_no_val,step. }
  all:destruct K; inversion H1.
Qed.

Lemma invert_step_alloc (v:val) σ e' σ' :
  step (Alloc v) σ e' σ' ->
  exists (n:Z) (l:loc), v=VInt n /\ (0 <= n)%Z /\ l ∉ dom σ /\ σ' = <[l:= (replicate (Z.to_nat n) VUnit)]> σ /\ e'=l.
Proof.
  inv_fst; subst; try now not_ctx K H1.
  inversion H0; subst. naive_solver.
Qed.

Lemma invert_step_call self args code v σ e' σ' :
  step (Call (VCode self args code) (Val v)) σ  e' σ' ->
  σ'=σ /\ e'=subst' self (VCode self args code) (subst' args v code).
Proof.
  inv_fst; subst.
  2:{ exfalso. destruct K; try naive_solver; simpl in *.
      all:inversion H0; subst; eapply step_no_val; eauto using must_be_val. }
  inversion H0; subst. naive_solver.
Qed.

Lemma invert_step_store σ (l:loc) (w:val) (v:val) e' σ' :
  step (Store l w v) σ e' σ' ->
  exists vs i, w = VInt i /\ σ !! l = Some vs /\ (0 <= i < Z.of_nat (length vs))%Z /\ σ' = <[l := <[Z.to_nat i := v]> vs]> σ /\ e'=VUnit.
Proof.
  inv_fst; subst; try now not_ctx K H1.
  inversion H0; subst. naive_solver.
Qed.

Lemma invert_step_call_prim σ x (v1 v2:val)  e' σ' :
  step (CallPrim x v1 v2) σ e' σ' ->
  exists v, eval_call_prim x v1 v2 = Some v /\ e'=v /\ σ'=σ.
Proof.
  inv_fst; subst; try now not_ctx K H1.
  inversion H0; subst. naive_solver.
Qed.

Lemma invert_step_cas σ (l:loc) (w:val) (v v':val) e' σ' :
  step (CAS l w v v') σ  e' σ' ->
  ∃ i vs v0, w=VInt i /\ σ !! l = Some vs /\ (0 <= i < Z.of_nat (length vs))%Z /\ vs !! (Z.to_nat i) = Some v0 /\ σ' = (if bool_decide (v0 = v) then (insert l (<[Z.to_nat i := v']> vs) σ) else σ) /\ e' = Val (bool_decide (v0 = v)).
Proof.
  inv_fst; subst; try now not_ctx K H1.
  inversion H0; subst. naive_solver.
Qed.

Lemma invert_step_par σ e1 e2 σ' e'  :
  ¬ (is_val e1 ∧ is_val e2) ->
  step (RunPar e1 e2) σ e' σ' ->
  (exists e1', e'=RunPar e1' e2 /\ step e1 σ e1' σ') \/
  (exists e2', e'=RunPar e1 e2' /\ step e2 σ e2' σ').
Proof.
  intros ?.
  inv_fst; subst; elim_ctx; try done.
  { inversion H1; subst. inversion H1. exfalso. naive_solver. }
  all:naive_solver.
Qed.

Lemma invert_step_join σ (v1 v2:val) σ' e'  :
  step (RunPar v1 v2) σ e' σ' ->
  e'=VPair v1 v2 /\ σ'=σ.
Proof.
  inv_fst; subst; elim_ctx; only 2,3: (exfalso; by eapply step_no_val).
  inversion H0; subst. naive_solver.
Qed.

Lemma invert_step_fork e1 e2 σ e' σ' :
  step (Par e1 e2) σ e' σ' ->
  e'=RunPar e1 e2 /\ σ'=σ.
Proof.
  inv_fst; subst; elim_ctx. inversion H0; subst. done.
Qed.

Lemma invert_step_pair (v1 v2 : val) σ e' σ' :
  step (Pair v1 v2) σ e' σ' ->
  e'=VPair v1 v2 /\ σ'=σ.
Proof.
  inv_fst; subst; try now not_ctx K H1.
  inversion H0; subst. naive_solver.
Qed.

Lemma invert_step_fst (v1 v2 : val) σ e' σ' :
  step (Fst (VPair v1 v2)) σ e' σ' ->
  e'=v1 /\ σ'=σ.
Proof.
  inv_fst; subst; try now not_ctx K H1.
  inversion H0; subst. naive_solver.
Qed.

Lemma invert_step_snd (v1 v2 : val) σ e' σ' :
  step (Snd (VPair v1 v2)) σ e' σ' ->
  e'=v2 /\ σ'=σ.
Proof.
  inv_fst; subst; try now not_ctx K H1.
  inversion H0; subst. naive_solver.
Qed.

Lemma invert_step_length (l:loc) σ e' σ' :
  step (Length l) σ e' σ' ->
  exists vs, σ !! l = Some vs /\ e'=Z.of_nat (length vs) /\ σ'=σ.
Proof.
  inv_fst; subst; try now not_ctx K H1.
  inversion H0; subst. naive_solver.
Qed.
