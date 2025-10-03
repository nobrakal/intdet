From Coq.ssr Require Import ssreflect.
From stdpp Require Import ssreflect strings binders gmap.

From intdet.lang Require Export head_semantics.

(******************************************************************************)
(* Distant semantics. *)

Inductive step :
  expr -> store ->
  expr -> store -> Prop :=
| StepHead : forall e σ e' σ',
  head_step e σ e' σ' ->
  step e σ e' σ'
| StepBind : forall e σ e' σ' K,
  step e σ e' σ' ->
  step (fill_item K e) σ (fill_item K e') σ'
| StepParL : forall σ e1 e2 σ' e1',
  step e1 σ e1' σ' ->
  step (RunPar e1 e2) σ (RunPar e1' e2) σ'
| StepParR : forall σ e1 e2 σ' e2',
  step e2 σ e2' σ' ->
  step (RunPar e1 e2) σ (RunPar e1 e2') σ'
.

Lemma step_no_val e σ e' σ' :
  step e σ e' σ' ->
  ¬ is_val e.
Proof.
  inversion 1; subst; eauto using head_step_no_val.
  destruct K; eauto.
Qed.

(******************************************************************************)

Record config : Type :=
  mk_config { cexpr : expr; cstore : store }.

Definition step' : config -> config -> Prop :=
  fun '(mk_config x1 x2) '(mk_config y1 y2) =>
    step x1 x2 y1 y2.

Definition init e : config :=
  mk_config e ∅.


Section always.

Context {A:Type}.

Definition always (R:relation A) (P:A -> Prop) x :=
  forall y, rtc R x y -> P y.

Definition always_step (R:relation A) P x y  :
  always R P x ->
  R x y ->
  always R P y.
Proof. unfold always. eauto using rtc_l. Qed.

Definition always_steps (R:relation A) P x y  :
  always R P x ->
  rtc R x y ->
  always R P y.
Proof. intros X ???. eapply X. by etrans. Qed.

Lemma always_mono (R:relation A) P1 P2 x :
  (forall x, P1 x -> P2 x) ->
  always R P1 x -> always R P2 x.
Proof. intros ???. eauto. Qed.

End always.
