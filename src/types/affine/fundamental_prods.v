From stdpp Require Import binders.

From iris.proofmode Require Import proofmode.
From iris Require Import gmap saved_prop invariants.
From iris.bi Require Import monpred.

From intdet.utils Require Import restrict more_cmras more_maps_and_sets more_iris.
From intdet.lang Require Import syntax utils substitution2 notations.
From intdet.musketeer Require Import dwp lockstep.
From intdet.types Require Import utils.
From intdet.types.affine Require Import typing logrel op_related logrel_facts.

From intdet.examples Require Import tactics_triple.

Section fundamental.

Context `{intdetGS Σ, typeG Σ}.

Lemma log_typed_prod Γ1 e1 t1 Γ2 e2 t2 Γ3 :
  fv e2 ⊆ dom Γ2 ->
  log_typed Γ1 e1 t1 Γ2 -∗
  log_typed Γ2 e2 t2 Γ3 -∗
  log_typed Γ1 (Pair e2 e1) (TProd t2 t1) Γ3.
Proof.
  iIntros (?) "#X1 #X2 !>".
  iIntros (m vs). simpl.

  iApply (triple_bind (CtxPair1 _)).
  iApply "X1". iClear "X1".
  iIntros (v1 (s1,m2)). simpl.

  iApply triple_extract_pure_pre. iIntros ((?&?)).

  iApply (triple_use_pure_pre (dom Γ2 = dom m2)).
  { iIntros "(_&?)".
    iApply (interp_env_dom_12 with "[$]"). }
  iIntros.

  rewrite {2}(restrict_split (dom Γ2) vs) map_union_comm.
  2:{ apply map_disjoint_dom. rewrite !dom_restrict. set_solver. }
  rewrite !msubsts_union.
  rewrite (msubsts_not_in_fv _ e2).
  2:{ rewrite dom_restrict. set_solver. }

  iApply (triple_bind (CtxPair2 _)).
  { iApply triple_frame_wand.
    iApply triple_conseq_post. 2:iApply "X2".
    iIntros (? (?,?)) "((%&%)&?&?) ?".
    iDestruct (interp_env_dom_12 with "[$]") as "%".
    iDestruct (interp_env_dom_13 with "[$]") as "%Hd".
    rewrite !dom_restrict in Hd.
    rewrite restrict_restrict.
    replace (dom Γ3 ∩ dom Γ2) with (dom Γ3) by set_solver.
    Unshelve.
    2:exact (fun v '(s,g) => ⌜dom Γ3 ⊆ dom Γ2 /\ dom g ⊆ dom m2 /\ similar_env Γ2 Γ3 /\ similar_shape_env m2 g⌝ ∗ interp t2 s v ∗ interp t1 s1 v1 ∗ interp_env Γ3 g (restrict (dom Γ3) vs))%I.
    iFrame. iPureIntro. split_and !; try done. set_solver. set_solver. }
  iIntros (? (s2,m3)). simpl.
  iApply triple_pair.
  iApply (triple_resolve (SProd s2 s1,m3)).
  iApply triple_val'.
  iIntros "((%&%&%&%)&?&?&?)". iFrame. iSplitR; last done.
  iPureIntro. split.
  { eapply senv_trans. 3,4:done. apply similar_trans. done. }
  { eapply senv_trans. 3,4:done. apply similar_shape_trans. done. }
Qed.

End fundamental.
