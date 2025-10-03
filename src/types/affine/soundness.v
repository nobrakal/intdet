From stdpp Require Import binders.

From iris.proofmode Require Import proofmode.
From iris Require Import gmap saved_prop invariants.
From iris.bi Require Import monpred.

From intdet.utils Require Import restrict more_cmras more_maps_and_sets.
From intdet.lang Require Import syntax utils substitution2 notations.
From intdet.musketeer Require Import dwp lockstep.
From intdet.types Require Import utils.
From intdet.types.affine Require Import typing syntactical.
From intdet.types.affine Require Import logrel fundamental fundamental_hashtbl fundamental_parfor fundamental_prods fundamental_array.

Lemma fundamental `{intdetGS Σ, typeG Σ} Γ e t Γ' :
  typed Γ e t Γ' ->
  ⊢ log_typed Γ e t Γ'.
Proof.
  induction 1.
  { apply log_typed_var. }
  { apply log_typed_unit. }
  { apply log_typed_bool. }
  { apply log_typed_int. }
  { iApply log_typed_assert. iApply IHtyped. }
  { iApply log_typed_let; [ | iApply IHtyped1 | iApply IHtyped2 ].
    apply typed_fv in H1_0. rewrite dom_binsert in H1_0. set_solver. }
  { iApply log_typed_abs. done. done. }
  { iApply log_typed_app; [ | iApply IHtyped1 | iApply IHtyped2 ].
    apply typed_fv in H1_0. set_solver. }
  { iApply log_typed_par. reflexivity.
    1,2:eauto using typed_fv.
    iApply IHtyped1. iApply IHtyped2. }
  { iApply log_typed_call_prim. eauto using typed_fv. done.
    iApply IHtyped1. iApply IHtyped2. }
  { iApply log_typed_if. 2:iApply IHtyped1.
    { apply typed_fv in H1_0, H1_1. set_solver. }
    iApply IHtyped2. iApply IHtyped3. }
  { iApply log_typed_frame. eauto using typed_fv. done. }
  { iApply log_typed_weak. 5:iApply IHtyped.
    all:eauto using typed_dom_subseteq, typed_fv. }
  { iApply log_typed_conseq. done. done. }
  { iApply log_typed_alloc. done. }
  { iApply log_typed_store. eauto using typed_dom_subseteq. all:done. }
  { iApply log_typed_load. }
  { iApply log_typed_parfor. set_solver. done. done. done.
    iModIntro. iIntros. iApply H6. }
  { iApply log_typed_length. }
  { iApply log_typed_intarr_load.
    eauto using typed_dom_subseteq. done.
    iApply IHtyped. }
  { iApply log_typed_intarr_alloc. 3:iApply IHtyped1.
    eauto using typed_dom_subseteq. eauto using typed_fv. iApply IHtyped2. }
  { iApply log_typed_intarr_store.
    { apply typed_dom_subseteq in H1_,H1_0.
      apply elem_of_dom_2 in H1. set_solver. }
    { by eapply typed_dom_subseteq. }
    { eauto using typed_fv. }
    { done. }
    { iApply IHtyped1. }
    { iApply IHtyped2. } }
  { by iApply log_typed_halloc. }
  { iApply log_typed_hinsert. eauto using typed_dom_subseteq. done.
    iApply IHtyped. }
  { iApply log_typed_helems. iApply IHtyped. }
  { iApply log_typed_prod. eauto using typed_fv.
    iApply IHtyped1. iApply IHtyped2. }
  { iApply log_typed_palloc. done. }
  { iApply log_typed_pwrite. eauto using typed_dom_subseteq. done. done. }
  { iApply log_typed_pread. }
Qed.

From intdet.musketeer Require Import dwp_adequacy adequacy.
From intdet.examples Require Import hashtbl hashtbl_pure.

Import Initialization.

Definition typeΣ : gFunctors :=
  #[ intdetΣ;
     savedPredΣ bool;
     priorityΣ;
     hashsetΣ;
     GFunctor (agreeR (leibnizO params))].

Global Instance subG_intdetPreG Σ :
  subG typeΣ Σ → intdetPreG Σ.
Proof. intros. apply subG_intdetPreG. solve_inG. Qed.

Global Instance intdetPreG_intdetΣ : intdetPreG typeΣ.
Proof. eauto with typeclass_instances. Qed.

Global Instance subG_typeΣ {Σ} : subG typeΣ Σ → typeG Σ.
Proof. solve_inG. Qed.

Lemma soundness e t Γ' :
  typed ∅ e t Γ' ->
  si_safety e e.
Proof.
  intros Htyped.
  apply (@triple_adequacy_open typeΣ). apply _.
  intros.
  eapply fundamental in Htyped.
  iIntros.
  iPoseProof Htyped as "#X".
  unshelve iSpecialize ("X" $! ∅ ∅). 1,2: apply _.
  rewrite msubsts_empty.
  iApply (triple_shift (fun _ => ())).
  iApply triple_conseq.
  3:iApply "X".
  { iIntros. rewrite /interp_env map_zip_empty big_sepM2_empty //. }
  { by iIntros. }
Qed.
