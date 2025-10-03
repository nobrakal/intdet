From stdpp Require Import relations.

From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates gen_heap ghost_map na_invariants.
From iris.program_logic Require Import weakestpre.
From iris.algebra Require Import gset gmap frac numbers.

From intdet.utils Require Import more_cmras more_maps_and_sets.
From intdet.lang Require Import semantics reducible atomic locations.
From intdet.musketeer Require Import wpg ininj dwp.

Section adequacy_pre.

Context `{intdetGS Σ}.

Definition interpr x y := interp x y.
Definition interpl x y := interp y x.

Lemma wpl_adequacy E a n c c' (v:val) Q :
  nsteps step' n c c' ->
  cexpr c' = v ->
  interpl a (cstore c) ∗
  wpl E (cexpr c) Q
  ={E,∅}=∗ |={∅}▷=>^n |={∅,E}=>
  interpl a (cstore c') ∗ Q v.
Proof.
  iIntros (Hsteps Hv) "(Hi&Hwp)".
  iInduction Hsteps as [] "IH".
  { destruct x as [e σ]. simpl in *. inversion Hv. subst.
    rewrite /wpl wpg_unfold /wpg_pre. simpl.
    iMod "Hwp" as "?".
    iApply fupd_mask_intro. set_solver. iIntros "Hclose".
    iMod "Hclose". iModIntro. by iFrame. }
  { destruct x as [e σ].
    destruct y as [e' σ']. simpl in *.
    rewrite /wpl (wpg_unfold _ e) /wpg_pre.
    assert (to_val e = None) as ->.
    { by eapply is_val_false, step_no_val. }
    iMod ("Hwp" with "Hi") as "(?&Hwp)". iModIntro.
    iMod ("Hwp" with "[%//]") as "Hwp". do 2 iModIntro.
    iMod "Hwp" as "(Hi&Hwp)".
    iApply ("IH" with "[%//] Hi Hwp"). }
Qed.

Definition not_stuck e σ :=
  is_val e \/ reducible e σ.

Definition not_stuck' c :=
  not_stuck (cexpr c) (cstore c).

Lemma wpgr_adequacy E a n c c' Q :
  nsteps step' n c c' ->
  interpr a (cstore c) ∗
  wpgr E (cexpr c) Q
  ={E,∅}=∗ |={∅}▷=>^n
  ⌜not_stuck' c'⌝.
Proof.
  iIntros (Hsteps) "(Hi&Hwp)".
  iInduction Hsteps as [] "IH".
  { destruct x as [e σ]. simpl in *.
    rewrite /wpgr wpg_unfold /wpg_pre.
    destruct (to_val e) eqn:Hv.
    { iMod "Hwp" as "?".
      destruct e; try done. inversion Hv. subst.
      intro_mod. iPureIntro. left. naive_solver. }
    { iMod ("Hwp" with "Hi") as "(%&_)". iPureIntro.
      by right. } }
  { destruct x as [e σ].
    destruct y as [e' σ']. simpl in *.
    rewrite /wpgr (wpg_unfold _ e) /wpg_pre.
    assert (to_val e = None) as ->.
    { by eapply is_val_false, step_no_val. }
    iMod ("Hwp" with "Hi") as "(_&Hwp)".
    iMod ("Hwp" with "[%//]") as "Hwp".
    do 3 iModIntro.
    iMod "Hwp" as "(Hi&Hwp)".
    iMod ("IH" with "Hi Hwp") as "X".
    done. }
Qed.

End adequacy_pre.

Import Initialization.

Definition safe e :=
  always step' not_stuck' (init e).

Definition si_safety e1 e2 := forall c,
  locs e2 = ∅ ->
  rtc step' (init e1) c ->
  is_val (cexpr c) ->
  safe e2.

Lemma adequacy_open `{intdetPreG Σ} e1 e2 :
  (∀ `{!intdetGS Σ},
     ⊢ dwp (A:=unit) ⊤ e1 (fun _ => True) e2 (fun _ _ => True%I) (fun _ _ => True%I)) ->
  si_safety e1 e2.
Proof.
  intros Hwp. intros c' ? E1 Hv ? E2.
  apply is_val_true in Hv. destruct Hv as (v&Hv).

  apply rtc_nsteps in E1.
  destruct E1 as (n,E1).
  apply rtc_nsteps in E2.
  destruct E2 as (n',E2).

  eapply uPred.pure_soundness.
  apply (@step_fupdN_soundness_no_lc Σ _ _ _ (n+S n') 0).

  iIntros.

  iMod intdet_init as "[%HinterpGS (%He&Hi)]".
  iDestruct Hwp as "Hwp".

  iDestruct (wpl_adequacy _ ∅ with "[Hi Hwp]") as "X".
  apply E1. done.
  { iFrame. simpl. iApply "Hwp". }

  rewrite He.
  rewrite step_fupdN_add.
  iApply (step_fupdN_mono with "X").

  iIntros "X". simpl. do 2 iModIntro.
  iMod "X" as "(Hi&[% (_&Hwp)])".
  iSpecialize ("Hwp" with "[%//][]").
  { by iApply eininj_refl. }
  iDestruct (wpgr_adequacy with "[Hi Hwp]") as "X".
  { apply E2. }
  { iFrame. }
  rewrite He //.
Qed.

Lemma adequacy e1 e2 :
  (∀ `{!intdetGS Σ},
     ⊢ dwp (A:=unit) ⊤ e1 (fun _ => True) e2 (fun _ _ => True%I) (fun _ _ => True%I)) ->
  si_safety e1 e2.
Proof.
  intros. eapply adequacy_open; eauto with typeclass_instances.
Qed.
