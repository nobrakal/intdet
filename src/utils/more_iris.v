From iris.prelude Require Import prelude.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gset.

Section big_sepS.

Lemma big_sepS_union_persistent `{Countable A} {PROP:bi} `{BiAffine PROP} (P:A -> PROP) (S1 S2:gset A) :
  (forall x, Persistent (P x)) ->
  ([∗ set] x ∈ (S1 ∪ S2), P x)%I ≡ (([∗ set] x ∈ S1, P x) ∗ ([∗ set] x ∈ S2, P x))%I .
Proof.
  intros.
  iSplit.
  { iIntros "#H".
    iSplitL; iIntros; rewrite !big_sepS_forall; iIntros; iApply "H";
      iPureIntro; set_solver. }
  { rewrite !big_sepS_forall.
    iIntros "(H1&H2)". iIntros (? Ht). apply elem_of_union in Ht.
    destruct Ht; [ iApply "H1" | iApply "H2"]; eauto. }
Qed.

End big_sepS.
