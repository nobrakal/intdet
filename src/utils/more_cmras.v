From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import gen_heap.
From iris.algebra Require Import gmap auth gset excl_auth.
From iris.base_logic.lib Require Import invariants.
From stdpp Require Import gmap gmultiset.

From intdet.utils Require Import more_maps_and_sets.

Section gset.
Context `{Countable K}.
Context `{inG Σ (authUR (gsetUR K))}.

Lemma elem_of_gset  γ (S:gset K) l :
  own γ (●S) -∗ own γ (◯ {[l]}) -∗ ⌜l ∈ S⌝.
Proof.
  iIntros.
  iDestruct (own_valid_2 γ with "[$][$]") as "%Hv".
  apply auth_both_valid_discrete in Hv.
  destruct Hv as (Hv,?).
  apply gset_included in Hv.
  iPureIntro. set_solver.
Qed.

Lemma auth_gset_update γ (S S':gset K) :
  S ⊆ S' ->
  own γ (● S) ==∗ own γ (● S').
Proof.
  iIntros.
  iApply (own_update with "[$]").
  eapply auth_update_auth . apply gset_local_update. set_solver.
Qed.

Lemma extract_witness_gset γ (S:gset K) :
  own γ (● S) ==∗ own γ (● S) ∗ own γ (◯ S).
Proof.
  iIntros.
  iApply own_op. iApply (own_update with "[$]").
  apply auth_update_alloc . apply gset_local_update. set_solver.
Qed.

Lemma gset_conclude γ S1 S2 :
  S1 ⊆ S2 ->
  own γ (◯ S2) -∗ own γ (◯ S1).
Proof.
  intros ?.
  replace S2 with (S1 ∪ S2) by set_solver.
  rewrite -gset_op. iIntros "(?&?)". by iFrame.
Qed.

Lemma extract_witness_gset_elem l γ (S:gset K) :
  l ∈ S ->
  own γ (● S) ==∗ own γ (● S) ∗ own γ (◯ {[l]}).
Proof.
  iIntros. iMod (extract_witness_gset with "[$]") as "(?&?)".
  iFrame. iModIntro. iApply (gset_conclude with "[$]"). set_solver.
Qed.

End gset.

Section gmap.

Context `{Countable K} {A:cmra}.

Lemma insert_op_l k v (m1 m2:gmap K A) :
  k ∉ dom m2 ->
  <[k:=v]> (m1 ⋅ m2) = <[k:=v]> m1 ⋅ m2.
Proof.
  intros. rewrite !gmap_op.
  apply insert_merge_l.
  rewrite not_elem_of_dom_1 //.
Qed.

Lemma valid_insert k v (m:gmap K A) :
  ✓ m ->
  ✓ v ->
  ✓ (<[k:=v]> m).
Proof.
  intros X1 X2. intros i. rewrite lookup_insert_case.
  case_decide; naive_solver.
Qed.

Lemma gmap_valid_singleton (k:K) (v:A) :
  ✓ v ->
  ✓ ({[k:=v]} : gmap K A).
Proof.
  intros ? i. rewrite lookup_insert_case. case_decide; done.
Qed.

Lemma delete_op (m1 m2:gmap K A) (i:K) :
  delete i (m1 ⋅ m2) = delete i m1 ⋅ delete i m2.
Proof.
  rewrite gmap_op delete_merge //.
Qed.

Lemma gmap_valid_delete i (m:gmap K A) :
  ✓ m ->
  ✓ (delete i m).
Proof.
  intros X j. destruct_decide (decide (i=j)); subst.
  { rewrite lookup_delete //. }
  { rewrite lookup_delete_ne //. }
Qed.

End gmap.
