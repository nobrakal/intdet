From stdpp Require Import binders.

From iris.proofmode Require Import proofmode.
From iris Require Import gmap saved_prop invariants.
From iris.bi Require Import monpred.

From intdet.utils Require Import restrict more_maps_and_sets.
From intdet.lang Require Import syntax utils substitution2 notations.
From intdet.musketeer Require Import dwp lockstep.
From intdet.types Require Import utils.
From intdet.types.affine Require Import typing shape.

(* Ensures that the functions do not strangely evolve *)
Fixpoint similar τ1 τ2 : Prop :=
  match τ1,τ2 with
  | TUnit, TUnit | TInt, TInt | TBool, TBool | THashSet _, THashSet _ => True
  | TProd x1 x2, TProd y1 y2 => similar x1 y1 /\ similar x2 y2
  | TArrow x1 x2, TArrow y1 y2 => x1=y1 /\ x2=y2
  | TRef _,TRef _ | TEmpty, TEmpty | TIntArray _, TIntArray _ => True
  | TPRead q1, TPRead q2 | TPWrite q1, TPWrite q2
  | TPRead q1, TPWrite q2 | TPWrite q1, TPRead q2 => True
  | _,_ => False
  end.

Definition senv `{Countable K} {A B} (f:A -> B -> Prop) (m1 : gmap K A) (m2 : gmap K B) :=
  map_relation f  (fun _ => True) (fun _ => True) m1 m2.

Definition similar_env (m1 m2: gmap string typ) := senv similar m1 m2.

Definition similar_shape_env (m1 m2: gmap string shape) := senv similar_shape m1 m2.

Lemma similar_shape_env_refl m : ✓ m -> similar_shape_env m m.
Proof.
  intros X.
  intros k. destruct (m !! k) eqn:Hk; last done.
  (specialize (X k)). rewrite Hk Some_valid in X.
  by apply similar_shape_refl.
Qed.

Definition senv_singleton_l `{Countable K} {A B} (f:A -> B -> Prop) (x:K) y :
  senv f {[x:=y]} ∅.
Proof.
  intros ?. rewrite lookup_insert_case lookup_empty.
  by case_decide.
Qed.

Lemma similar_env_empty_r `{Countable K} {A B} (f:A -> B -> Prop) (m:gmap K A) :
  senv f m ∅.
Proof.
  intros i. rewrite lookup_empty.
  by destruct (m !! i).
Qed.

Lemma similar_shape_sym s1 s2 :
  similar_shape s1 s2 ->
  similar_shape s2 s1.
Proof.
  revert s2. induction s1; intros []; naive_solver.
Qed.

Lemma similar_shape_env_sym m1 m2 :
  similar_shape_env m1 m2 -> similar_shape_env m2 m1.
Proof.
  intros X i. specialize (X i).
  destruct (m1 !! i), (m2 !! i); try done.
  by apply similar_shape_sym.
Qed.

Lemma senv_delete_l `{Countable K} {A B} (f:A -> B -> Prop) (m1 : gmap K A) (m2 : gmap K B) i :
  senv f m1 m2 ->
  senv f (delete i m1) m2.
Proof.
  intros X j. specialize (X j). destruct_decide (decide (i=j)); subst.
  { rewrite lookup_delete //. by destruct (m2 !! j). }
  { rewrite lookup_delete_ne //. }
Qed.

Lemma senv_delete_r `{Countable K} {A B} (f:A -> B -> Prop) (m1 : gmap K A) (m2 : gmap K B) i :
  senv f m1 m2 ->
  senv f m1 (delete i m2).
Proof.
  intros X j. specialize (X j). destruct_decide (decide (i=j)); subst.
  { rewrite lookup_delete //. by destruct (m1 !! j). }
  { rewrite lookup_delete_ne //. }
Qed.

Lemma upd_typ_preserves_similar t0 t1 t2 :
  upd_typ t2 t1 ->
  similar t1 t0 ->
  similar t2 t0.
Proof.
  intros X. revert t0; induction X; try done; intros t0.
  all:destruct t0; try done; naive_solver.
Qed.

Lemma similar_env_insert x t1 t2 m1 m2 :
  similar t1 t2 ->
  similar_env m1 m2 ->
  similar_env (<[x:=t1]>m1) (<[x:=t2]>m2).
Proof.
  intros ? X i.
  specialize (X i).
  rewrite !lookup_insert_case.
  case_decide; subst; done.
Qed.

Lemma similar_refl t :
  ✓ t ->
  similar t t.
Proof.
  induction t; try done; intros (?&?); naive_solver.
Qed.

Lemma similar_env_refl m :
  ✓ m ->
  similar_env m m.
Proof.
  intros X i. specialize (X i).
  destruct (m !! i) eqn:E; last done.
  rewrite E Some_valid in X. by apply similar_refl.
Qed.

Lemma upd_typ_env_preserves_similar Γ Γ' Γ0 :
  upd_typ_env Γ' Γ ->
  similar_env Γ Γ0 ->
  similar_env Γ' Γ0.
Proof.
  intros X1 X2. intros i.
  specialize (X1 i). specialize (X2 i).
  destruct (Γ !! i), (Γ' !! i); try done.
  destruct (Γ0 !! i); try done. simpl in *.
  by eapply upd_typ_preserves_similar.
Qed.

Lemma similar_preserves_valid x y :
  similar x y ->
  ✓ x ->
  ✓ y.
Proof.
  revert y; induction x; intros []; try done.
  all:intros (X1&X2) (Y1&Y2); split; naive_solver.
Qed.

Fixpoint nomix t1 t2 :=
  match t1,t2 with
  | TProd t11 t12, TProd t21 t22 => nomix t11 t21 /\ nomix t12 t22
  | TPWrite _, TPRead _ | TPRead _, TPWrite _ => False
  | _,_ => True end.

Lemma similar_preserves_valid_compose x x' y y' :
  similar x x' ->
  similar y y' ->
  nomix x' y' ->
  ✓ (x ⋅ y) ->
  ✓ (x' ⋅ y').
Proof.
  revert x' y y'; induction x; intros []; try done.
  all:intros [] [] X; try done.
  { intros (X1&X2) (Y1&Y2) (?&?). split; naive_solver. }
  { intros (->&->) _. rewrite !typ_op_unfold. simpl.
    destruct X. subst.
    case_decide as E; last done. destruct E. subst.
    done. }
Qed.

Definition nomix_env (Γ1 Γ2:gmap string typ) :=
  map_relation nomix (fun _ => True) (fun _ => True) Γ1 Γ2.

Lemma valid_op_similar_env_l Γ1 Γ1' Γ2 :
  similar_env Γ1 Γ1' ->
  nomix_env Γ1' Γ2 ->
  dom Γ1' ⊆ dom Γ1 ->
  ✓ (Γ1 ⋅ Γ2) ->
  ✓ (Γ1' ⋅ Γ2).
Proof.
  intros X2 X4 X1 X3. intros i. specialize (X3 i). specialize (X4 i).
  rewrite lookup_op. rewrite lookup_op in X3,X4.
  destruct_decide (decide (i ∈ dom Γ1')).
  { assert (is_Some (Γ1 !! i )) as (x1&E1).
    { eapply elem_of_dom. set_solver. }
    rewrite E1 in X3.
    assert (is_Some (Γ1' !! i )) as (x1'&E1').
    { eapply elem_of_dom. set_solver. }
    rewrite E1'.
    specialize (X2 i). rewrite E1 E1' in X2. simpl in *.
    destruct (Γ2 !! i) eqn:E2.
    { rewrite E2 -Some_op Some_valid in X3.
      rewrite E2 -Some_op Some_valid. eapply similar_preserves_valid_compose; try done. apply similar_refl. eauto using cmra_valid_op_r. rewrite E1' // in X4. }
    { rewrite E2 right_id Some_valid in X3. rewrite E2 right_id Some_valid.
      eauto using similar_preserves_valid. } }
  { rewrite not_elem_of_dom_1 // left_id. eauto using cmra_valid_op_r. }
Qed.

Lemma valid_op_similar_env Γ1 Γ1' Γ2 Γ2' :
  similar_env Γ1 Γ1' ->
  similar_env Γ2 Γ2' ->
  dom Γ1' ⊆ dom Γ1 ->
  dom Γ2' ⊆ dom Γ2 ->
  nomix_env Γ1' Γ2' ->
  ✓ Γ1' -> ✓ Γ2' ->
  ✓ (Γ1 ⋅ Γ2) ->
  ✓ (Γ1' ⋅ Γ2').
Proof.
  intros X1 X2 X3 X4 X5 I1 I2 X.
  intros i.
  specialize (X1 i). specialize (X2 i). specialize (X i).
  rewrite lookup_op. rewrite lookup_op in X.
  destruct_decide (decide (i ∈ dom Γ1')).
  { assert (is_Some (Γ1 !! i )) as (x1&E1).
    { eapply elem_of_dom. set_solver. }
    rewrite E1 in X, X1.
    assert (is_Some (Γ1' !! i )) as (x1'&E1').
    { eapply elem_of_dom. set_solver. }
    rewrite E1'. rewrite E1' in X1.
    destruct_decide (decide (i ∈ dom Γ2')).
    { assert (is_Some (Γ2' !! i)) as (x2'&Hx2').
      { apply elem_of_dom. set_solver. }
      rewrite Hx2' -Some_op Some_valid.
      assert (is_Some (Γ2 !! i)) as (x2&Hx2).
      { apply elem_of_dom. set_solver. }
      rewrite Hx2 Hx2' in X2.
      rewrite Hx2 -Some_op Some_valid in X. simpl in *.
      specialize (X5 i). rewrite Hx2' E1' in X5.
      eauto using similar_preserves_valid_compose. }
    { rewrite not_elem_of_dom_1 // right_id Some_valid. simpl in *.
      specialize (I1 i). rewrite E1' // in I1. } }
  { rewrite not_elem_of_dom_1 // left_id.
    specialize (I2 i). done. }
Qed.

Global Instance similar_trans : Transitive similar.
Proof.
  intros t1. induction t1; intros t2 t3; simpl; try done.
  4,5:destruct t2,t3; try done; simpl; intros (?&?) (?&?); naive_solver.
  all:try by destruct t2,t3.
Qed.

Global Instance similar_shape_trans : Transitive  similar_shape.
Proof.
  intros s1. induction s1; intros s2 s3; simpl; try done.
  3:destruct s2,s3; try done; simpl; intros (?&?) (?&?); naive_solver.
  all:destruct s2,s3; naive_solver.
Qed.

Lemma senv_trans `{Countable K} {A} (f:relation A) `{Transitive _ f} (m1 m2 m3:gmap K A) :
  dom m3 ⊆ dom m2 ->
  senv f m1 m2 ->
  senv f m2 m3 ->
  senv f m1 m3.
Proof.
  intros X1 X2 X3 i.
  specialize (X2 i). specialize (X3 i).
  destruct (m1 !! i); last by destruct (m3 !! i).
  destruct_decide (decide (i ∈ dom m3)).
  { assert (is_Some (m3 !! i)) as (?&X). by eapply elem_of_dom.
    rewrite X in X2,X3. rewrite X.
    assert (is_Some (m2 !! i)) as (?&X'). eapply elem_of_dom. set_solver.
    rewrite X' in X2,X3. simpl in *.
    by etrans. }
  { rewrite not_elem_of_dom_1 //. }
Qed.

Lemma senv_add_delete_l `{Countable K} {A B} x (f:A -> B -> Prop) (m1 : gmap K A) (m2 : gmap K B)  :
  senv f (delete x m1) (delete x m2) ->
  senv f m1 (delete x m2).
Proof.
  intros X i. specialize (X i).
  destruct_decide (decide (i=x)); subst.
  { rewrite lookup_delete. by destruct (m1 !! x). }
  { rewrite lookup_delete_ne //. rewrite !lookup_delete_ne // in X. }
Qed.

Lemma similar_op_one x1 x1' x2 :
  similar x1 x1' ->
  ✓ (x1 ⋅ x2) ->
  similar (x1 ⋅ x2) x1'.
Proof.
  revert x1' x2. induction x1; intros []; try done.
  all:intros []; try done.
  { intros (?&?) (?&?); split; naive_solver. }
  { intros (->&->). rewrite typ_op_unfold. simpl.
    case_decide as X; last done. destruct X. subst. done. }
Qed.

Lemma similar_op_both t1 t2 t :
  ✓ (t1 ⋅ t) ->  ✓ (t2 ⋅ t) ->
  similar t1 t2 ->
  similar (t1 ⋅ t) (t2 ⋅ t).
Proof.
  revert t2 t. induction t1; intros t2 t ??; simpl; try done.
  4:{ destruct t2; try done. destruct t; try done.
      simpl in *. destruct H, H0. naive_solver. }
  all:try by destruct t2,t.
  { destruct t2; try done. destruct t; try done.
    rewrite !typ_op_unfold in H, H0. simpl in *.
    case_decide as X; last done. destruct X. subst.
    case_decide as X; last done. destruct X. subst.
    intros. rewrite typ_op_unfold. simpl. rewrite decide_True //. }
Qed.

Lemma similar_comm t1 t2 :
  similar t1 t2 ->
  similar t2 t1.
Proof.
  revert t2; induction t1; intros []; try done; intros (?&?); split; naive_solver.
Qed.

Lemma similar_op_l t t' :
  ✓ (t ⋅ t') ->
  similar (t ⋅ t') t'.
Proof.
  revert t'; induction t; intros []; try done.
  { intros (?&?); split; naive_solver. }
  { rewrite typ_op_unfold. simpl. case_decide as X; last done.
    destruct X. subst. done. }
Qed.

Lemma similar_env_op_l m1 m2 m :
  ✓ (m1 ⋅ m) ->
  ✓ (m2 ⋅ m) ->
  similar_env m1 m2 ->
  similar_env (m1 ⋅ m) (m2 ⋅ m).
Proof.
  intros Xl Xr X. intros i. rewrite !lookup_op.
  specialize (X i). specialize (Xl i). specialize (Xr i).
  rewrite !lookup_op in Xl,Xr.
  destruct (m !! i) eqn:E; rewrite !E; rewrite !E in Xl, Xr.
  2:rewrite !right_id //.
  destruct (m1 !! i) eqn:E1; rewrite E1; rewrite E1 in Xl.
  { destruct (m2 !! i) eqn:E2; rewrite E2; rewrite E2 in Xr.
    { rewrite -!Some_op. simpl in *.
      rewrite -Some_op Some_valid in Xl.
      eauto using similar_op_both. }
    { rewrite -Some_op Some_valid in Xl. rewrite -Some_op. simpl.
      eauto using similar_op_l. } }
  { rewrite left_id.
     destruct (m2 !! i) eqn:E2; rewrite E2.
    { rewrite -!Some_op. simpl in *.
      rewrite E2 -Some_op Some_valid in Xr.
      eauto using similar_comm, similar_op_l. }
    { rewrite left_id in Xl. rewrite left_id. simpl in *.
      eauto using similar_refl. } }
Qed.


Lemma similar_op x1 x1' x2 x2' :
  similar x1 x1' ->
  similar x2 x2' ->
  ✓ (x1 ⋅ x2) ->
  ✓ (x1' ⋅ x2') ->
  similar (x1 ⋅ x2) (x1' ⋅ x2').
Proof.
  intros. apply similar_op_one; try done.
  apply similar_comm. apply similar_op_one. by apply similar_comm.
  done.
Qed.

Lemma similar_env_op m1 m2 m1' m2' :
  dom m1' ⊆ dom m1 ->
  dom m2' ⊆ dom m2 ->
  ✓ (m1 ⋅ m2) ->
  ✓ (m1' ⋅ m2') ->
  similar_env m1 m1' ->
  similar_env m2 m2' ->
  similar_env (m1 ⋅ m2) (m1' ⋅ m2').
Proof.
  intros El Er Tl Tr Xl Xr. intros i. rewrite !lookup_op.
  specialize (Xl i). specialize (Xr i).
  specialize (Tl i). specialize (Tr i). rewrite !lookup_op in Tl,Tr.
  destruct_decide (decide (i ∈ dom m1')).
  { assert (i ∈ dom m1) by set_solver.
    assert (is_Some (m1 !! i)) as (x1&Hx1) by by eapply elem_of_dom.
    assert (is_Some (m1' !! i)) as (x1'&Hx1') by by eapply elem_of_dom.
    rewrite Hx1 Hx1'. rewrite Hx1 Hx1' in Xl.
    destruct_decide (decide (i ∈ dom m2')).
    { assert (i ∈ dom m2) by set_solver.
      assert (is_Some (m2 !! i)) as (x2&Hx2) by by eapply elem_of_dom.
      assert (is_Some (m2' !! i)) as (x2'&Hx2') by by eapply elem_of_dom.
      rewrite Hx2 Hx2'. rewrite Hx2 Hx2' in Xr. simpl in *.
      rewrite Hx1 Hx2 -Some_op Some_valid in Tl. rewrite Hx1' Hx2' -Some_op Some_valid in Tr.
      eauto using similar_op. }
    { apply not_elem_of_dom in H1. rewrite H1 right_id.
      destruct (m2 !! i) eqn:Hx2; rewrite Hx2.
      { rewrite -Some_op. simpl in *.
        rewrite Hx1 Hx2 -Some_op Some_valid in Tl.
        eauto using similar_op_one. }
      { rewrite right_id. done. } } }
  { apply not_elem_of_dom in H. rewrite H left_id.
    destruct_decide (decide (i ∈ dom m2')).
    2:{ apply not_elem_of_dom in H0. rewrite H0.
        remember (m1 !! i ⋅ m2 !! i) as  x. rewrite -Heqx. by destruct x. }
    assert (is_Some (m2 !! i)) as (x2&Hx2) by (eapply elem_of_dom; set_solver).
    assert (is_Some (m2' !! i)) as (x2'&Hx2') by by eapply elem_of_dom.
    rewrite Hx2 Hx2'. rewrite Hx2 Hx2' in Xr. simpl in *.
    destruct_decide (decide (i ∈ dom m1)).
    { assert (is_Some (m1 !! i)) as (x1&Hx1) by by eapply elem_of_dom.
      rewrite Hx1 -Some_op. simpl in *.
      rewrite Hx1 Hx2 -Some_op Some_valid in Tl.
      rewrite comm_L. apply similar_op_one; try done. rewrite comm_L //. }
    { apply not_elem_of_dom in H1. rewrite H1 left_id //. } }
Qed.

Fixpoint nomix_shape s1 s2 :=
  match s1,s2 with
  | SProd t11 t12, SProd t21 t22 => nomix_shape t11 t21 /\ nomix_shape t12 t22
  | SPRead _, SPWrite _ | SPWrite _, SPRead _ => False
  | SPRead x, SPRead y => x=y
  | SArray xs, SArray xs' => xs=xs'
  | SRef _ _, SRef _ _ => False
  | _,_ => True end.

Lemma nomix_shape_sym s1 s2 :
  nomix_shape s1 s2 -> nomix_shape s2 s1.
Proof.
  revert s2; induction s1; intros []; naive_solver.
Qed.

Definition nomix_shape_env (Γ1 Γ2:gmap string shape) :=
  map_relation nomix_shape (fun _ => True) (fun _ => True) Γ1 Γ2.

Lemma similar_shape_op s1 s2 s1' s2' :
  ✓ (s1 ⋅ s2) ->
  nomix_shape s1 s2 ->
  nomix_shape s1' s2' ->
  similar_shape s1 s1' ->
  similar_shape s2 s2' ->
  similar_shape (s1 ⋅ s2) (s1' ⋅ s2').
Proof.
  revert s1' s2 s2'. induction s1; intros [] s2 s2'; try done; simpl.
  all:rewrite ?shape_op_unfold.
  all:destruct s2,s2'; try done; simpl.
  { intros (?&?) (?&?) (?&?) (?&?) (?&?). naive_solver. }
  all:case_decide; try done.
  { intros _ _ _ -> ->. rewrite decide_True //. }
  { intros _ -> -> _ _. rewrite decide_True //. }
  { intros _ -> -> _ _. rewrite decide_True //. }
Qed.

Lemma shape_valid_unfold s : ✓ s = shape_valid s.
Proof. done. Qed.

Lemma similar_shape_op_one x1 x1' x2 :
  nomix_shape x1 x2 ->
  ✓ (x1 ⋅ x2) ->
  similar_shape x1 x1' ->
  similar_shape (x1 ⋅ x2) x1'.
Proof.
  rewrite shape_op_unfold shape_valid_unfold.
  revert x1' x2. induction x1; intros []; try done; simpl.
  { by intros []. }
  { intros []; naive_solver. }
  { intros []; try done.
    by case_decide. }
  { intros []; try done. by case_decide. }
  { intros []; try done. intros ->. by case_decide. }
  1,2,3:by intros [].
  { intros [] _; try done. by case_decide. }
Qed.

Lemma similar_shape_env_op m1 m2 m1' m2' :
  dom m1' ⊆ dom m1 ->
  dom m2' ⊆ dom m2 ->
  nomix_shape_env m1 m2 ->
  nomix_shape_env m1' m2' ->
  similar_shape_env m1 m1' ->
  ✓ (m1 ⋅ m2) ->
  similar_shape_env m2 m2' ->
  similar_shape_env (m1 ⋅ m2) (m1' ⋅ m2').
Proof.
  intros El Er T1 T2 Xl R1 Xr. intros i. rewrite !lookup_op.
  specialize (Xl i). specialize (Xr i).
  specialize (T1 i). specialize (T2 i).
  specialize (R1 i).
  destruct_decide (decide (i ∈ dom m1')).
  { assert (i ∈ dom m1) by set_solver.
    assert (is_Some (m1 !! i)) as (x1&Hx1) by by eapply elem_of_dom.
    assert (is_Some (m1' !! i)) as (x1'&Hx1') by by eapply elem_of_dom.
    rewrite Hx1 Hx1'. rewrite Hx1 Hx1' in Xl.
    rewrite Hx1 in T1. rewrite Hx1' in T2.
    destruct_decide (decide (i ∈ dom m2')).
    { assert (i ∈ dom m2) by set_solver.
      assert (is_Some (m2 !! i)) as (x2&Hx2) by by eapply elem_of_dom.
      assert (is_Some (m2' !! i)) as (x2'&Hx2') by by eapply elem_of_dom.
      rewrite Hx2 Hx2'. rewrite Hx2 Hx2' in Xr. simpl in *.
      rewrite Hx2 in T1. rewrite Hx2' in T2.
      rewrite lookup_op Hx1 Hx2 in R1.
      eauto using similar_shape_op. }
    { apply not_elem_of_dom in H1. rewrite H1 right_id.
      destruct (m2 !! i) eqn:Hx2; rewrite Hx2.
      { rewrite -Some_op. simpl in *.
        rewrite H1 in Xr. rewrite lookup_op Hx1 Hx2 -Some_op Some_valid in R1.
        by eapply similar_shape_op_one. }
      { rewrite right_id. done. } } }
  { apply not_elem_of_dom in H. rewrite H left_id.
    destruct_decide (decide (i ∈ dom m2')).
    2:{ apply not_elem_of_dom in H0. rewrite H0.
        remember (m1 !! i ⋅ m2 !! i) as  x. rewrite -Heqx. by destruct x. }
    assert (is_Some (m2 !! i)) as (x2&Hx2) by (eapply elem_of_dom; set_solver).
    assert (is_Some (m2' !! i)) as (x2'&Hx2') by by eapply elem_of_dom.
    rewrite Hx2 Hx2'. rewrite Hx2 Hx2' in Xr. simpl in *.
    destruct_decide (decide (i ∈ dom m1)).
    { assert (is_Some (m1 !! i)) as (x1&Hx1) by by eapply elem_of_dom.
      rewrite Hx1 -Some_op.
      rewrite Hx1 Hx2 in T1,R1. simpl in *.
      rewrite comm_L. apply similar_shape_op_one; try done.
      by apply nomix_shape_sym.
      rewrite lookup_op Hx1 Hx2 -Some_op Some_valid in R1.
      rewrite comm_L //. }
    { apply not_elem_of_dom in H1. rewrite H1 left_id //. } }
Qed.


Lemma similar_shape_preserves_valid_compose x x' y y' :
  similar_shape x x' ->
  similar_shape y y' ->
  nomix_shape x' y' ->
  ✓ (x ⋅ y) ->
  similar_shape x' y'.
Proof.
  revert x' y y'; induction x; intros []; try done.
  all:intros [] []; try done.
  { intros (?&?) (X1&X2) (Y1&Y2) (?&?). split; naive_solver. }
  { simpl. intros -> -> _. rewrite shape_op_unfold. simpl.
    by case_decide. }
Qed.

Lemma valid_op_similar_shape_env m1 m2 m1' m2' :
  similar_shape_env m1 m1' ->
  similar_shape_env m2 m2' ->
  dom m1' ⊆ dom m1 ->
  dom m2' ⊆ dom m2 ->
  nomix_shape_env m1' m2' ->
  ✓ (m1 ⋅ m2) ->
  similar_shape_env m1' m2'.
Proof.
  intros X1 X2 X3 X4 X5 X.
  intros i.
  specialize (X1 i). specialize (X2 i). specialize (X i).
  rewrite lookup_op in X.
  destruct_decide (decide (i ∈ dom m1')).
  { assert (is_Some (m1 !! i )) as (x1&E1).
    { eapply elem_of_dom. set_solver. }
    rewrite E1 in X, X1.
    assert (is_Some (m1' !! i )) as (x1'&E1').
    { eapply elem_of_dom. set_solver. }
    rewrite E1'. rewrite E1' in X1.
    destruct_decide (decide (i ∈ dom m2')).
    { assert (is_Some (m2' !! i)) as (x2'&Hx2').
      { apply elem_of_dom. set_solver. }
      rewrite Hx2'. simpl.
      assert (is_Some (m2 !! i)) as (x2&Hx2).
      { apply elem_of_dom. set_solver. }
      rewrite Hx2 Hx2' in X2.
      rewrite Hx2 -Some_op Some_valid in X. simpl in *.
      specialize (X5 i). rewrite Hx2' E1' in X5.
      eauto using similar_shape_preserves_valid_compose. }
    { rewrite not_elem_of_dom_1 //. } }
  { rewrite not_elem_of_dom_1 //. by destruct (m2' !! i). }
Qed.

Lemma valid_op_similar_shape s1 s2 :
  ✓ (s1 ⋅ s2) ->
  similar_shape s1 s2.
Proof.
  revert s2. induction s1; intros []; try done; rewrite shape_op_unfold; simpl.
  { intros (?&?). naive_solver. }
  all:by case_decide.
Qed.
