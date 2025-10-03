From iris.proofmode Require Import proofmode.
From iris Require Import gmap saved_prop invariants.
From iris.bi Require Import monpred.

From intdet.lang Require Import syntax utils substitution2.
From intdet.musketeer Require Import dwp lockstep.
From intdet.types Require Import utils.
From intdet.types.lvar Require Import typing logrel fundamental.

Lemma fundamental `{intdetGS Σ, savedPropG Σ} m e Γ τ :
  typed m Γ e τ ->
  match m with Weak => ⊢ log_typed Γ e τ | Strong => ⊢ log_typed_strong Γ e τ end.
Proof.
  induction 1.
  { destruct m.
    { by apply log_typed_var. }
    { by apply log_typed_strong_var. } }
  { intros. destruct m.
    { by apply log_typed_unit. }
    { by apply log_typed_strong_unit. } }
  { intros. destruct m.
    { by apply log_typed_bool. }
    { by apply log_typed_strong_bool. } }
  { intros. destruct m.
    { by apply log_typed_int. }
    { by apply log_typed_strong_int. } }
  { destruct m.
    { iApply log_typed_let. iApply IHtyped1. iApply IHtyped2. }
    { iApply log_typed_strong_let. iApply IHtyped1. iApply IHtyped2. } }
  { destruct m.
    { iApply log_typed_if. iApply IHtyped1. iApply IHtyped2. iApply IHtyped3. }
    { iApply log_typed_strong_if. iApply IHtyped1. iApply IHtyped2. iApply IHtyped3. } }
  { destruct m.
    { iApply log_typed_call_prim. done. iApply IHtyped1. iApply IHtyped2. }
    { iApply log_typed_strong_call_prim. done. iApply IHtyped1. iApply IHtyped2. } }
  { intros. destruct m.
    { destruct m'.
      { by iApply log_typed_abs. }
      { by iApply log_typed_abs_strong_from_weak. } }
    { assert (m'=Strong) by eauto. subst.
      by iApply log_typed_abs_strong_from_strong. } }
  { destruct m.
    { destruct m'.
      { iApply log_typed_call. iApply IHtyped1. iApply IHtyped2. }
      { assert (τ=TUnit) by eauto. subst.
        iApply log_typed_call_strong_from_weak. iApply IHtyped1. iApply IHtyped2. } }
    { assert (m'=Strong) by eauto. subst.
      by iApply log_typed_call_strong_from_strong. } }
  { intros. by iApply log_typed_alloc. }
  { intros. by iApply log_typed_strong_load. }
  { intros. by iApply log_typed_strong_cas. }
  { iApply log_typed_par. iApply IHtyped1. iApply IHtyped2. }
  { destruct m.
    { iApply log_typed_pair. iApply IHtyped1. iApply IHtyped2. }
    { iApply log_typed_pair_strong. iApply IHtyped1. iApply IHtyped2. } }
Qed.
