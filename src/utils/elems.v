From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map gen_heap.
From iris.algebra Require Import gmap agree frac_auth gset.

From intdet.utils Require Import more_cmras more_iris more_maps_and_sets.

Section elems.

Context `{Countable A}.
Context `{interpGS Σ, inG Σ (authUR (gmapR nat (gsetUR A)))}.

Definition elems γ P (R:relation A) (vs:list A) : iProp Σ :=
  ∃ (M:gmap nat (gset A)),
    own γ (● M) ∗
    ⌜map_Forall (fun i g => exists v, vs !! i = Some v /\ P v /\ set_Forall (fun x => P x /\ R x v) g) M⌝.

Definition elem_int γ i v := own γ (◯ {[i:={[v]}]}).

Lemma elems_alloc P R vs :
  ⊢ |==> ∃ γ, elems γ P R vs.
Proof.
  iMod (own_alloc (● ∅)) as "[%ge Hge]". apply auth_auth_valid. done.
  iFrame. done.
Qed.

Local Lemma gmap_update_insert `{Countable K, Countable V} (M:gmap K (gset V)) i X :
  (M, ε) ~l~> (<[i:=X ∪ M !!! i]>M, {[i:=X]}).
Proof.
  apply local_update_discrete.
  intros mz Hv E. split.
  { intros j. rewrite lookup_insert_case. case_decide.
    { apply Some_valid. constructor. }
    { apply Hv. } }
  { intros j. rewrite lookup_opM !lookup_insert_case.
    specialize (E j). rewrite lookup_opM lookup_empty left_id in E.
    case_decide; subst.
    { rewrite lookup_total_alt E.
      destruct mz; simpl in *.
      { destruct (c !! j) eqn:R; rewrite R.
        done. simpl. rewrite !right_id //. }
      rewrite !right_id //. }
    { rewrite lookup_empty left_id //. } }
Qed.

Lemma elems_insert `{PreOrder _ R} {P} v v' γ vs i :
  vs !! i = Some v' ->
  P v ->
  (¬ P v' \/ R v' v) ->
  elems γ P R vs ==∗ elems γ P R (<[i:=v]> vs) ∗ elem_int γ i v.
Proof.
  iIntros (?? C) "[% (?&%He)]".
  iMod (own_update with "[$]") as "(?&?)".
  apply auth_update_alloc. apply gmap_update_insert. iFrame.
  iPureIntro.
  apply map_Forall_insert_2.
  { exists v. split_and!; try done.
    { rewrite list_lookup_insert //. by eapply lookup_lt_Some. }
    { apply set_Forall_union.
      { apply set_Forall_singleton. done. }
      rewrite lookup_total_alt.
      destruct (M !! i) eqn:E; last done.
      apply He in E. destruct E as (?&?&?&?).
      eapply set_Forall_impl. done. intros ? (?&?).
      split. done. transitivity x. done. naive_solver. } }
  { eapply map_Forall_impl. done. simpl.
    intros j ? (?&?&?&?).
    destruct_decide (decide (i=j)); subst.
    { exists v. split_and !; try done.
      { rewrite list_lookup_insert //. by eapply lookup_lt_Some. }
      eapply set_Forall_impl. done. intros ? (?&?).
      split. done. transitivity x0. done. naive_solver. }
    { eexists. split; last done. rewrite list_lookup_insert_ne //. } }
Qed.

Lemma use_elem_int γ P R i (vs:list A) v :
  elem_int γ i v -∗
  elems γ P R vs -∗
  ⌜∃ v', vs !! i = Some v' /\ R v v' /\ P v'⌝.
Proof.
  iIntros "Hf [% (Ha&%Hm)]".
  iDestruct (own_valid_2 with "Ha Hf") as "%Hv".
  iPureIntro.

  apply auth_both_valid_discrete in Hv.
  destruct Hv as (Hv&_).
  rewrite lookup_included in Hv. specialize (Hv i).
  rewrite lookup_insert in Hv.
  destruct (Some_included_is_Some _ _ Hv) as (g&Hg).
  rewrite Hg in Hv.
  apply Hm in Hg. destruct Hg as (?&?&?&X).
  eexists. split_and !; try done.
  apply X.
  rewrite Some_included_total in Hv.
  set_solver.
Qed.

End elems.
