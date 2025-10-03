From stdpp Require Import binders.

From iris.proofmode Require Import proofmode.
From iris Require Import gmap saved_prop invariants.
From iris.bi Require Import monpred.

From intdet.utils Require Import restrict more_cmras more_maps_and_sets more_iris.
From intdet.lang Require Import syntax utils substitution2 notations.
From intdet.musketeer Require Import dwp lockstep.
From intdet.types Require Import utils.
From intdet.types.affine Require Import typing logrel op_related logrel_facts.

From intdet.examples Require Import filter_compact hashtbl.

Section proof.

Context `{intdetGS Σ, typeG Σ}.

Lemma log_typed_halloc Γ (h c:val) e Γ' (hash0:val -> nat) (cmp0:val -> val -> bool) :
  TotalOrder cmp0 ->
  (forall {Σ} `{X:dwp.intdetGS Σ}, ⊢ @hash_spec Σ X hash0 h) ->
  (forall {Σ} `{wpapi.IsWP Σ pt wpx}, ⊢ @cmp_spec Σ wpx cmp0 c) ->
  log_typed Γ e TInt Γ' -∗
  log_typed Γ (htbl_init h c e)%E (THashSet 1)  Γ'.
Proof.
  iIntros (? Hh Hc) "#X". iIntros (m vs) "!>". simpl.
  iApply (triple_bind (CtxCall1 _)). iApply "X".
  iIntros (v (s,m')). simpl. iClear "X".

  iApply (triple_use_pure_pre (exists n, s=SNone /\ v=VInt n)).
  { iIntros "(_&X&_)".
    destruct s; try done.
    iDestruct "X" as "[% ->]". eauto. }
  iIntros ((n&(->&->))).

  iApply triple_extract_pure_pre.
  iIntros ((?&?)).

  iApply (triple_conseq_pre ((interp_env Γ' m' (restrict (dom Γ') vs) ∗ True)))%I.
  iIntros "(?&?)". iFrame.

  iApply triple_frame_wand.

  iApply triple_end.
  iApply (hstbl_alloc_spec n c h hash0 cmp0).
  { iIntros. iApply Hc. }
  { iApply Hh. }

  iIntros (v p).
  iApply (triple_resolve (SHashSet ∅,m')).
  iApply triple_val'.

  iIntros "? ?". iSplitR; first done. iFrame "#∗".
  by iApply big_sepS_empty.
Qed.

Lemma similar_shape_insert_shash_l m x g g' m' :
  similar_shape_env m (<[x:=SHashSet g]> m') ->
  similar_shape_env m (<[x:=SHashSet g']> m').
Proof.
  intros X i. specialize (X i).
  destruct (m !! i).
  2:{ by destruct (<[x:=SHashSet g']> m' !! i). }
  rewrite lookup_insert_case. rewrite lookup_insert_case in X.
  case_decide; subst; last done.
  simpl in *. by destruct s.
Qed.

Lemma log_typed_hinsert Γ Γ' e (x:string) q :
  dom Γ' ⊆ dom Γ -> (* will be fulfilled by the syntactical judgment *)
  Γ' !! x = Some (THashSet q) ->
  log_typed Γ e TInt Γ' -∗
  log_typed Γ (htbl_add x e) TUnit Γ'.
Proof.
  iIntros (? Hx) "#X". iIntros (m vs) "!>". simpl.

  iApply (triple_use_pure_pre (dom Γ = dom vs)).
  { iApply interp_env_dom_13. }

  iIntros "%".
  assert (x ∈ dom Γ') by by eapply elem_of_dom.
  assert (is_Some (vs !! x)) as (v&Hv). apply elem_of_dom. set_solver.
  rewrite Hv.

  iApply (triple_bind (CtxCall1 _)). iApply "X".
  iIntros (i (s,m')). simpl. iClear "X".

  iApply (triple_use_pure_pre (exists n, s=SNone /\ i=VInt n)).
  { iIntros "(_&X&_)".
    destruct s; try done.
    iDestruct "X" as "[% ->]". eauto. }
  iIntros ((n&(->&->))).

  iApply triple_extract_pure_pre.
  iIntros ((?&?)).

  assert (restrict (dom Γ') vs !! x = Some v) as Hvx.
  { rewrite lookup_restrict. rewrite decide_True //. }

  iApply (triple_conseq_pre (interp_env _ _ _)).
  { iIntros "(_&?)". done. }

  iApply (triple_use_pure_pre (exists g, m' !! x = Some (SHashSet g))).
  { iIntros "X".
    iDestruct (interp_env_dom_12 with "X") as "%Hd1".
    iDestruct (interp_env_dom_13 with "X") as "%Hd2".
    assert (is_Some (m' !! x)) as (?&Hx'). eapply elem_of_dom. set_solver.
    rewrite (insert_id_delete _ _ _ Hx') (insert_id_delete _ _ _ Hvx) {1}(insert_id_delete _ _ _ Hx).

    rewrite interp_env_insert //.
    2-4:rewrite dom_delete_L; set_solver.
    iDestruct "X" as "(X&?)". simpl.
    destruct x0; try done. subst.
    iPureIntro. rewrite lookup_insert. eauto. }
  iIntros "(%&%Hmx)".

  rewrite {1}(insert_id_delete _ _ _ Hx) (insert_id_delete _ _ _ Hmx) (insert_id_delete _ _ _ Hvx).

  rewrite interp_env_insert.
  2-4:rewrite dom_delete_L; set_solver.
  simpl. rewrite /interp_hashset.

  iApply (triple_resolve (SNone,<[x:=SHashSet ({[VInt n]} ∪ g)]>m')).

  rewrite  -!assoc.
  iApply triple_frame_wand_r.
  iApply (triple_use_pure_pre (can_insert v n)).
  { iApply (vdeduce_can_insert1 v (VInt n) q g). simpl. naive_solver. }
  iIntros "%".

  iApply triple_conseq_post.
  2:by iApply triple_insert.

  iIntros (? []) "(->&?)".
  iIntros "(?&?&?)".
  iSplitR.
  { iPureIntro. split; first done.
    eapply similar_shape_insert_shash_l.
    rewrite insert_id //. }
  iSplitR; first done.

  rewrite {4}(insert_id_delete _ _ _ Hx) (insert_id_delete _ _ _ Hvx).
  rewrite -(insert_delete_insert m').
  iApply interp_env_insert.
  1-3:rewrite dom_delete_L; set_solver.
  iFrame.
  iApply big_sepS_union_persistent. iFrame.
  rewrite big_sepS_singleton. eauto.
Qed.

Lemma log_typed_helems Γ Γ' e :
  log_typed Γ e (THashSet 1) Γ' -∗
  log_typed Γ (htbl_elems e) (TIntArray 1) Γ'.
Proof.
  iIntros "#X". iIntros (m vs) "!>". simpl.
  iApply (triple_bind (CtxCall1 _)). iApply "X".
  iIntros (v (s,m')). simpl. iClear "X".

  iApply triple_extract_pure_pre.
  iIntros ((?&?)).

  iApply (triple_use_pure_pre (exists g, s=SHashSet g)).
  { iIntros "(X&_)".
    destruct s; try done. eauto. }
  iIntros ((g&->)).

  rewrite /interp_hashset.
  rewrite -!assoc.
  iApply triple_frame_wand_r.

  iApply triple_end.
  iApply triple_elems.
  iIntros (? xs). iApply (triple_resolve (SArray xs, m')).
  iApply triple_val'.
  iIntros "[% ((->&%Hdedup)&?)] (#?&#?&?)".
  iSplitR; first done. iFrame "#∗". iSplitR; first done.
  iApply big_sepL_intro. iModIntro.
  iIntros (k y Hk).
  apply elem_of_list_lookup_2 in Hk. apply Hdedup in Hk.
  iDestruct (big_sepS_elem_of with "[$]") as "?". done. done.
Qed.

End proof.
