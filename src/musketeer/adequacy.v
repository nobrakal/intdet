From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.bi Require Export monpred.

From intdet.utils Require Import more_cmras.
From intdet.lang Require Import semantics.
From intdet.musketeer Require Import dwp lockstep dwp_adequacy.

Import Initialization.

Lemma triple_adequacy_open `{intdetPreG Σ} e :
  (∀ `{!intdetGS Σ},
     ⊢ triple (A:=unit) ⊤ True%I e (fun _ _ => True)) ->
  si_safety e e.
Proof.
  intros Htriple.
  eapply adequacy_open; try done.
  iIntros. iApply triple_dwpk. iApply Htriple.
Qed.

Lemma triple_adequacy e :
  (∀ `{!intdetGS Σ},
     ⊢ triple (A:=unit) ⊤ True%I e (fun _ _ => True)) ->
  si_safety e e.
Proof.
  intros. eapply triple_adequacy_open; eauto with typeclass_instances.
Qed.
