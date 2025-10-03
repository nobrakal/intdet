From stdpp Require Import binders.

From iris.proofmode Require Import proofmode.
From iris.bi Require Import monpred.

From intdet.lang Require Import utils.
From intdet.musketeer Require Import dwp lockstep.

Section utils.

Context `{intdetGS Σ}.

(* TODO move to iris, add index as param of Φ *)
Lemma monPred_at_big_sepL2 {I : biIndex} {PROP : bi} {A B : Type} xs ys i (Φ : A → B →  monPred I PROP) :
  ([∗ list] x;y ∈ xs;ys, Φ x y) i ⊣⊢ ([∗ list] x;y ∈ xs;ys, Φ x y i).
Proof.
  iInduction xs as [|] "IH" forall (ys).
  { iSplit.
    { iIntros. destruct ys; first done. simpl.
      rewrite monPred_at_pure //. }
    { iIntros "X".
      iDestruct (big_sepL2_nil_inv_l with "X") as "->".
      simpl. rewrite monPred_at_emp //. } }
  { iSplit.
    { iIntros "X". destruct ys; simpl.
      { rewrite monPred_at_pure //. }
      { rewrite monPred_at_sep.
        iDestruct "X" as "(?&?)". iFrame. by iApply "IH". } }
    { iIntros "X".
      iDestruct (big_sepL2_cons_inv_l with "X") as "[% [% (->&?&?)]]".
      simpl. rewrite monPred_at_sep. iFrame.
      by iApply "IH". } }
Qed.

Lemma monPred_at_big_sepM2 {I : biIndex} {PROP : bi} {A B C: Type} `{Countable A} xs ys i (Φ : A → B → C -> monPred I PROP) :
  ([∗ map] k ↦ x;y ∈ xs;ys, Φ k x y) i ⊣⊢ ([∗ map] k ↦ x;y ∈ xs;ys, Φ k x y i).
Proof.
  rewrite /big_sepM2 seal_eq /big_op.big_sepM2_def. simpl.
  rewrite monPred_at_and monPred_at_pure monPred_at_big_sepM //.
Qed.

Lemma big_sepM2_binsert {A B} (i:binders.binder) x1 x2 (m1:gmap string A) (m2:gmap string B) (Φ: _ -> _ -> vProp Σ) :
  Φ x1 x2 ∗ ([∗ map] y1;y2 ∈ m1;m2, Φ y1 y2) -∗
  [∗ map] y1;y2 ∈ binsert i x1 m1;binsert i x2 m2, Φ y1 y2.
Proof.
  iIntros "(?&E)". destruct i; first done.
  iDestruct (big_sepM2_lookup_iff with "[$]") as "%X".
  destruct (m1 !! s) as [e1|] eqn:E1.
  { assert (is_Some (m2 !! s)) as (e2&?) by naive_solver.
    rewrite -(insert_delete m1 s e1) // -(insert_delete m2 s e2) //.
    rewrite big_sepM2_insert. 2,3:rewrite lookup_delete //. simpl.
    rewrite !insert_insert.
    rewrite big_sepM2_insert. 2,3:rewrite lookup_delete //. simpl.
    iDestruct "E" as "(?&?)". iFrame. }
  { assert (m2 !! s = None).
    { destruct (m2 !! s) eqn:Hs; last done. exfalso.
      assert (is_Some (m1 !! s)) as (?&?); naive_solver. }
    iApply big_sepM2_insert. 1,2:done. iFrame. }
Qed.

Lemma big_sepM2_binserts_rev {A B} xs1 xs2 bs xs1' xs2' (m1:gmap string A) (m2:gmap string B) (Φ: _ -> _ -> vProp Σ) :
  length xs1 = length xs1' ->
  length xs2 = length xs2' ->
  xs1 = zip bs xs1' ->
  xs2 = zip bs xs2' ->
  ([∗ list] y1;y2 ∈ xs1';xs2', Φ y1 y2) -∗
  ([∗ map] y1;y2 ∈ m1;m2, Φ y1 y2) -∗
  [∗ map] y1;y2 ∈ binserts (rev xs1) m1;binserts (rev xs2) m2, Φ y1 y2.
Proof.
  iIntros (X1 X2 Heq1 Heq2) "E1".
  iInduction xs1 as [|] "IH" forall (xs2 bs xs1' xs2' m1 m2 X1 X2 Heq1 Heq2); iIntros "E2".
  { destruct xs1'; simpl in *; try congruence.
    iDestruct (big_sepL2_nil_inv_l with "[$]") as "->".
    destruct xs2; simpl in *; try congruence. done. }
  { destruct xs1'; simpl in *; try congruence.
    iDestruct (big_sepL2_cons_inv_l with "[$]") as "[% [% (->&E1&X1)]]".
    destruct xs2; simpl in *; try congruence. destruct bs; simpl in *; try congruence.
    inversion Heq1. subst. inversion Heq2. subst.
    rewrite !binserts_app.
    iApply ("IH" with "[%][%][%//][%//] X1"). 1,2:lia.
    simpl. iApply big_sepM2_binsert. iFrame. }
Qed.

End utils.
