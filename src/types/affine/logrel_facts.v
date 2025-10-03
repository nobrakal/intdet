From stdpp Require Import binders.

From iris.proofmode Require Import proofmode.
From iris Require Import gmap saved_prop invariants.
From iris.bi Require Import monpred.

From intdet.utils Require Import restrict more_cmras more_maps_and_sets.
From intdet.lang Require Import syntax utils substitution2 notations.
From intdet.musketeer Require Import dwp lockstep.
From intdet.types Require Import utils.
From intdet.types.affine Require Import typing logrel op_related.

Section proof.

Context `{intdetGS Σ, typeG Σ}.

Lemma interp_op_l x1 x2 s v :
  interp (x1 ⋅ x2) s v -∗
  ⌜s = s ⋅ s⌝.
Proof.
  iIntros "X".
  iInduction x1 as [] "IH" forall (x2 s v).
  all:destruct x2; try done.
  all:destruct s; try done.
  { simpl. iDestruct "X" as "[% [% (->&?&?)]]".
    rewrite shape_op_unfold. simpl.
    iDestruct ("IH" with "[$]") as "%E1".
    iDestruct ("IH1" with "[$]") as "%E2".
    iPureIntro. by f_equal. }
  all:rewrite typ_op_unfold; simpl; try by case_decide.
  { case_decide as X; last done. destruct X. subst.
    iPureIntro. rewrite shape_op_unfold. simpl. rewrite decide_True //. }
  { iPureIntro. rewrite shape_op_unfold.
    simpl. rewrite decide_True //. }
  { iPureIntro. rewrite shape_op_unfold. simpl.
    f_equal. lia. }
  { iPureIntro. rewrite shape_op_unfold. simpl. f_equal. set_solver. }
  {  iPureIntro. rewrite shape_op_unfold. simpl. rewrite decide_True //. }
Qed.

Lemma interp_insert_val_inv Γ ms i v vs :
  i ∉ dom vs ->
  interp_env Γ ms (<[i:=v]>vs) -∗
  ∃ t m Γ' ms',
    ⌜Γ = <[i:=t]> Γ' /\ i ∉ dom Γ' /\ ms = <[i:=m]>ms' /\ i ∉ dom ms'⌝ ∗
    interp t m v ∗ interp_env Γ' ms' vs.
Proof.
  iIntros (?) "(%&X)".
  iDestruct (big_sepM2_dom with "X") as "%Hd".
  rewrite dom_map_zip dom_insert_L in Hd.
  assert (is_Some (Γ !! i)) as (?&X1).
  { apply elem_of_dom. set_solver. }
  assert (is_Some (ms !! i)) as (?&X2).
  { apply elem_of_dom. set_solver. }
  iExists _,_,(delete i _),(delete i _).
  iSplitR.
  { iPureIntro. split_and !.
    rewrite insert_delete_insert insert_id //.
    rewrite dom_delete; set_solver.
    rewrite insert_delete_insert insert_id //.
    rewrite dom_delete; set_solver. }
  rewrite -{1}(insert_id _ _ _ X1) -(insert_delete_insert Γ) -{1}(insert_id _ _ _ X2) -(insert_delete_insert ms).
  rewrite map_zip_insert big_sepM2_insert.
  2:{ apply not_elem_of_dom. rewrite dom_map_zip !dom_delete; set_solver. }
  2:{ by eapply not_elem_of_dom. }
  iDestruct "X" as "(?&?)". iFrame. iPureIntro.
  rewrite !dom_delete_L. set_solver.
Qed.

Lemma interp_sepM2_op_inv_l Γ1 Γ2 ms vs :
  interp_env (Γ1 ⋅ Γ2) ms vs ⊢
  ⌜exists m1 m2, ms = m1 ⋅ m2 ∧ dom m1 = dom Γ1 /\ dom m2 = dom Γ2 /\ (dom Γ1 = dom Γ2 -> m1=ms /\ m2=ms)⌝.
Proof.
  iIntros "X". iInduction vs as [|] "IH" using map_ind forall (Γ1 Γ2 ms).
  { iDestruct "X" as "(%Hd&X)".
    iDestruct (big_sepM2_empty_l with "X") as "%X".
    apply map_zip_empty_inv in X; last done. destruct X as (?&->).
    iPureIntro.
    rewrite dom_empty_L dom_op in Hd.
    assert (dom Γ1 = ∅ /\ dom Γ2 = ∅) as (->&->) by set_solver.
    exists ∅,∅. rewrite dom_empty_L //. }
  { iDestruct (interp_insert_val_inv with "X") as "(%&%&%&%&((%X1&%X2&%X3&%X4)&?&X))".
    by eapply not_elem_of_dom.

    generalize X1. intros X1'. apply (@f_equal _ _ (fun x => delete i x)) in X1'.
    rewrite delete_op delete_insert in X1'; last by eapply not_elem_of_dom.
    rewrite -X1'.

    generalize X3. intros X3'. apply (@f_equal _ _ (fun x => delete i x)) in X3'.
    rewrite delete_insert in X3'; last by eapply not_elem_of_dom.
    rewrite -X3'.

    iDestruct ("IH" with "[$]") as "[%m1 [%m2 (%&%&%&%Hrec)]]".
    iClear "IH X". clear X1' X3'.

    apply (@f_equal _ _ (fun x => x !! i)) in X1.
    rewrite lookup_op lookup_insert in X1.
    subst. rewrite delete_insert in H2; last by eapply not_elem_of_dom.

    rewrite !dom_delete_L in H3,H4.

    destruct (Γ1 !! i) as [x1 | ] eqn:Hx1; rewrite Hx1 in X1.
    { assert (i ∈ dom Γ1) as HΓi1 by by eapply elem_of_dom.
      destruct (Γ2 !! i) as [x2 | ] eqn:Hx2; rewrite Hx2 in X1.
      { rewrite -Some_op in X1. inversion X1. subst.
        iDestruct (interp_op_l with "[$]") as "%HX". subst.
        iExists (<[i:=m0]>m1),(<[i:=m0]>m2). iPureIntro.
        assert (i ∈ dom Γ2) as HΓi2 by by eapply elem_of_dom.
        rewrite dom_op in X4.
        split_and !.
        { rewrite -insert_op -HX //. }
        { rewrite dom_insert_L H3 -union_difference_L //.
          set_solver. }
        { rewrite dom_insert_L H4 -union_difference_L //.
          set_solver. }
        { intros.
          destruct Hrec as (R1&R2). rewrite !dom_delete_L. set_solver.
          rewrite delete_insert in R1,R2.
          2:{ apply not_elem_of_dom. rewrite dom_op. set_solver. }
          split. rewrite -R1 //. rewrite -R2 //. } }
      { rewrite right_id in X1. inversion X1. subst.
        iExists (<[i:=_]>m1),m2. iPureIntro.
        apply not_elem_of_dom in Hx2.
        split_and !.
        { rewrite gmap_op. erewrite insert_merge_l; first done.
          rewrite not_elem_of_dom_1 //.
          apply not_elem_of_dom in Hx2. set_solver. }
        { rewrite dom_insert_L H3 -union_difference_L //.
          set_solver. }
        { set_solver. }
        { intros E. exfalso. congruence. } } }
    { rewrite left_id in X1.
      apply not_elem_of_dom in Hx1. apply elem_of_dom_2 in X1.
      iExists m1,(<[i:=_]>m2). iPureIntro.
      split_and !.
      { subst. rewrite gmap_op. erewrite insert_merge_r; first done.
        rewrite not_elem_of_dom_1 //. set_solver. }
      { set_solver. }
      { rewrite dom_insert_L H4 -union_difference_L //.
        set_solver. }
      { intros E. exfalso. congruence. } } }
Qed.

Lemma interp_env_insert i x1 x2 x3 m1 m2 m3 :
  i ∉ dom m1 -> i ∉ dom m2 -> i ∉ dom m3 ->
  interp_env (<[i:=x1]>m1) (<[i:=x2]>m2) (<[i:=x3]>m3) ⊣⊢
  interp x1 x2 x3 ∗ interp_env m1 m2 m3.
Proof.
  iIntros. rewrite /interp_env !dom_insert_L map_zip_insert.
  iSplit.
  { iIntros "(%Hd&X)". rewrite big_sepM2_insert.
    iDestruct "X" as "(?&?)". iFrame. iPureIntro. set_solver.
    all:apply not_elem_of_dom. rewrite dom_map_zip. all:set_solver. }
  { iIntros "(?&(%&?))". iSplitR.
    { iPureIntro. set_solver. }
    rewrite big_sepM2_insert. iFrame.
    all:apply not_elem_of_dom. rewrite dom_map_zip. all:set_solver. }
Qed.

Lemma gmap_valid_bdelete (A:cmra) i (m:gmap _ A) :
  ✓ m ->
  ✓ (bdelete i m).
Proof.
  intros ?. destruct i; [ done | by apply gmap_valid_delete ].
Qed.

Lemma interp_valid τ s v:
  interp τ s v ⊢ ⌜✓ τ⌝.
Proof.
  iIntros "X". iInduction τ as [] "IH" forall (s v).
  all:destruct s; try done.
  simpl. iDestruct "X" as "(%&%&->&X1&X2)".
  iDestruct ("IH" with "X1") as "%".
  iDestruct ("IH1" with "X2") as "%".
  iPureIntro. done.
Qed.

Lemma interp_env_split_1 Γ1 Γ2 m1 m2 vs :
  dom m1 = dom Γ1 ->
  dom m2 = dom Γ2 ->
  interp_env (Γ1 ⋅ Γ2) (m1 ⋅ m2) vs ⊢
  interp_env Γ1 m1 (restrict (dom Γ1) vs) ∗ interp_env Γ2 m2 (restrict (dom Γ2) vs).
Proof.
  iIntros (R2 R3) "X".
  iInduction vs as [] "IH" using map_ind forall (Γ1 Γ2 m1 m2 R2 R3).
  { iDestruct "X" as "(%Hd&X)".
    iDestruct (big_sepM2_empty_l with "X") as "%X".
    apply map_zip_empty_inv in X; last done. destruct X as (X&->).
    apply (@f_equal _ _ dom) in X.
    rewrite dom_empty_L dom_op in X.
    assert (dom Γ1 = ∅ /\ dom Γ2 = ∅) as (X1&X2) by set_solver.
    apply dom_empty_inv_L in X1,X2. subst.
    assert (dom m1 = ∅ /\ dom m2 = ∅) as (X1&X2) by set_solver.
    apply dom_empty_inv_L in X1,X2. subst.
    rewrite restrict_empty.
    iSplit; rewrite /interp_env map_zip_empty big_sepM2_empty //. }
  { apply not_elem_of_dom in H1.
    iDestruct (interp_insert_val_inv with "X") as "(%&%&%&%&((%X1&%X2&%X3&%X4)&U&X))".
    done.

    generalize X1. intros X1'. apply (@f_equal _ _ (fun x => delete i x)) in X1'.
    rewrite delete_op delete_insert in X1'; last by eapply not_elem_of_dom.
    rewrite -X1'.

    generalize X3. intros X3'. apply (@f_equal _ _ (fun x => delete i x)) in X3'.
    rewrite delete_insert in X3'; last by eapply not_elem_of_dom.
    rewrite -X3'.

    rewrite delete_op.
    iDestruct ("IH" with "[%][%] X") as "(?&?)".
    1,2:rewrite !dom_delete_L; set_solver.

    iClear "IH". clear X1' X3'.

    apply (@f_equal _ _ (fun x => x !! i)) in X1.
    apply (@f_equal _ _ (fun x => x !! i)) in X3.
    rewrite !lookup_op !lookup_insert in X1,X3.
    rewrite !dom_delete_L !restrict_difference_not_in; only 2,3:set_solver.
    iDestruct (interp_valid with "U") as "%Hv".
    destruct_decide (decide (i ∈ dom Γ1)) as Hd1.
    { assert (is_Some (Γ1 !! i)) as (x1&Hx1). by eapply elem_of_dom.
      assert (is_Some (m1 !! i)) as (y1&Hy1).
      { apply elem_of_dom. set_solver. }
      rewrite {3}(insert_id_delete _ _ _ Hx1) {2}(insert_id_delete _ _ _ Hy1).
      rewrite restrict_insert // decide_True //.
      rewrite interp_env_insert; only 2,3:(rewrite dom_delete_L; set_solver); only 2:(rewrite dom_restrict; set_solver).
      destruct_decide (decide (i ∈ dom Γ2)) as Hd2.
      { assert (is_Some (Γ2 !! i)) as (x2&Hx2). by eapply elem_of_dom.
        rewrite Hx1 Hx2 -Some_op in X1. inversion X1. subst.
        assert (is_Some (m2 !! i)) as (y2&Hy2).
        { apply elem_of_dom. set_solver. }
        rewrite Hy1 Hy2 -Some_op in X3. inversion X3. subst.
        iDestruct (interp_shape_valid with "U") as "%".
        apply valid_op_similar_shape in H2.
        rewrite interp_op //.
        iDestruct "U" as "(?&?)".
        rewrite restrict_insert // decide_True //.
        rewrite {3}(insert_id_delete _ _ _ Hx2) {2}(insert_id_delete _ _ _ Hy2).
        rewrite interp_env_insert; only 2,3:(rewrite dom_delete_L; set_solver); only 2:(rewrite dom_restrict; set_solver).
        iFrame. }
      { assert (Γ2 !! i = None) as Hx2 by by eapply not_elem_of_dom.
        assert (m2 !! i = None) as Hy2 by (eapply not_elem_of_dom; set_solver).
        rewrite Hx1 Hx2 right_id in X1. inversion X1. subst.
        rewrite Hy1 Hy2 right_id in X3. inversion X3. subst.
        rewrite restrict_insert //. rewrite decide_False //.
        rewrite (delete_notin Γ2); last by eapply not_elem_of_dom.
        rewrite (delete_notin m2); last (eapply not_elem_of_dom; set_solver).
        iFrame. } }
    { assert (Γ1 !! i = None) as Hx1 by by eapply not_elem_of_dom.
      assert (m1 !! i = None) as Hy1 by (eapply not_elem_of_dom; set_solver).
      assert (i ∈ dom Γ2) as Hd2.
      { apply elem_of_dom. destruct (Γ2 !! i) eqn:X; try done.
        rewrite Hx1 X left_id in X1. congruence. }
      assert (is_Some (Γ2 !! i)) as (x2&Hx2). by eapply elem_of_dom.
      assert (is_Some (m2 !! i)) as (y2&Hy2).
      { apply elem_of_dom. set_solver. }
      rewrite Hx1 Hx2 left_id in X1. inversion X1. subst.
      rewrite Hy1 Hy2 left_id in X3. inversion X3. subst.
      rewrite {3}(insert_id_delete _ _ _ Hx2) {2}(insert_id_delete _ _ _ Hy2).
      rewrite restrict_insert //. rewrite decide_False //.
      rewrite restrict_insert //. rewrite decide_True //.
      rewrite interp_env_insert; only 2,3:(rewrite dom_delete_L; set_solver); only 2:(rewrite dom_restrict; set_solver).
      rewrite (delete_notin Γ1); last by eapply not_elem_of_dom.
      rewrite (delete_notin m1); last (eapply not_elem_of_dom; set_solver).
      iFrame. } }
Qed.

Lemma interp_env_dom_12 Γ m vs :
  interp_env Γ m vs -∗ ⌜dom Γ = dom m⌝.
Proof.
  iIntros "(%&?)". done.
Qed.

Lemma interp_env_dom_13 Γ m vs :
  interp_env Γ m vs -∗ ⌜dom Γ = dom vs⌝.
Proof.
  iIntros "(%&?)".
  iDestruct (big_sepM2_dom with "[$]") as "%Hd".
  iPureIntro. rewrite dom_map_zip in Hd.
  set_solver.
Qed.


Lemma interp_env_split_2 Γ1 Γ2 m1 m2 vs :
  ✓ (Γ1 ⋅ Γ2) ->
  similar_shape_env m1 m2 ->
  dom vs = dom (Γ1 ⋅ Γ2) ->
  interp_env Γ1 m1 (restrict (dom Γ1) vs) ∗
  interp_env Γ2 m2 (restrict (dom Γ2) vs) ⊢
  interp_env (Γ1 ⋅ Γ2) (m1 ⋅ m2) vs.
Proof.
  iIntros (R1 R2 R3) "(X1&X2)".
  iInduction Γ1 as [] "IH" using map_ind forall (Γ2 m1 m2 vs R1 R2 R3).
  { iDestruct( interp_env_dom_12 with "X1") as "%Hd".
    rewrite dom_empty_L in Hd. symmetry in Hd. apply dom_empty_inv_L in Hd. subst.
    rewrite !left_id_L. iClear "X1".
    rewrite dom_op dom_empty_L in R3.
    rewrite restrict_id //. set_solver. }
  rewrite dom_op dom_insert_L in R3.
  assert (i ∉ dom m) by by eapply not_elem_of_dom.
  iDestruct (interp_env_dom_12 with "X1") as "%Hd".
  rewrite dom_insert_L in Hd.
  assert (i ∈ dom m1) as Hd1 by set_solver.
  assert (is_Some (m1 !! i)) as (y1&Hy1) by by eapply elem_of_dom.
  rewrite (insert_id_delete _ _ _ Hy1).
  rewrite dom_insert_L.
  iDestruct (interp_env_dom_13 with "X1") as "%Hd'".
  rewrite dom_insert_L dom_restrict in Hd'.
  assert (i ∈ dom vs) as Hd2 by set_solver.
  assert (is_Some (vs !! i)) as (z&Hz) by by eapply elem_of_dom.
  rewrite (insert_id_delete _ _ _ Hz).
  rewrite restrict_insert; last (rewrite dom_delete_L; set_solver).
  rewrite decide_True; last set_solver.
  rewrite interp_env_insert //.
  2:rewrite dom_delete_L; set_solver.
  2:rewrite dom_restrict; set_solver.
  iDestruct "X1" as "(?&X1)".

  iDestruct (interp_env_dom_12 with "X2") as "%Hd''".
  rewrite -(restrict_difference_not_in _ {[i]}).
  replace (({[i]} ∪ dom m) ∖ {[i]}) with (dom m) by set_solver.
  2:rewrite dom_delete_L; set_solver.

  destruct_decide (decide (i ∈ dom Γ2)).
  { assert (is_Some (Γ2 !! i)) as (x2&Hx2) by by eapply elem_of_dom.
    assert (i ∈ dom m2) as Hd3 by set_solver.
    assert (is_Some (m2 !! i)) as (y2&Hy2) by by eapply elem_of_dom.
    rewrite (insert_id_delete _ _ _ Hx2) (insert_id_delete _ _ _ Hy2).
    rewrite -!insert_op.
    rewrite dom_insert_L dom_delete_L.
    rewrite restrict_insert; last (rewrite dom_delete_L; set_solver).
    rewrite decide_True; last set_solver.
    rewrite interp_env_insert.
    2,3:rewrite dom_delete_L; set_solver.
    2:rewrite dom_restrict; set_solver.
    iDestruct "X2" as "(?&X2)".
    rewrite interp_env_insert.
    2,3:rewrite dom_op !dom_delete_L; set_solver.
    2:rewrite dom_delete_L; set_solver.

    rewrite interp_op.
    2:{ specialize (R1 i). rewrite lookup_op lookup_insert Hx2 // in R1. }
    2:{ specialize (R2 i). rewrite Hy1 Hy2 // in R2. }

    iFrame.

    iApply ("IH" with "[%][%][%][$] [X2]").
    { eapply (gmap_valid_delete i) in R1.
      rewrite delete_op delete_insert // in R1. }
    { eapply senv_delete_l. eapply senv_delete_r. done. }
    { rewrite dom_op !dom_delete_L; set_solver. }
    { rewrite dom_delete_L.
      rewrite -(restrict_difference_not_in _ {[i]}).
      replace (({[i]} ∪ dom Γ2 ∖ {[i]}) ∖ {[i]}) with (dom Γ2 ∖ {[i]}) by set_solver.
      done. rewrite dom_delete_L; set_solver. } }
  { assert (Γ2 !! i = None) by by eapply not_elem_of_dom.
    assert (i ∉ dom m2) by rewrite -Hd'' //.
    assert (m2 !! i = None) as Hy2 by by eapply not_elem_of_dom.
    rewrite restrict_insert; last (rewrite dom_delete_L; set_solver).
    rewrite decide_False //.
    rewrite -!insert_op_l //.
    rewrite interp_env_insert.
    2:rewrite dom_op; set_solver.
    2:rewrite dom_op dom_delete_L; set_solver.
    2:rewrite dom_delete_L; set_solver.
    iFrame.
    iApply ("IH" with "[%][%][%][$][$]").
    { eapply (gmap_valid_delete i) in R1.
      rewrite delete_op delete_insert // delete_notin // in R1. }
    { by apply senv_delete_l. }
    { rewrite dom_delete_L dom_op; set_solver. } }
Qed.

Lemma map_zip_binsert {A B} x a b (m1:gmap _ A) (m2:gmap _ B) :
  binsert x (a,b) (map_zip m1 m2) = map_zip (binsert x a m1) (binsert x b m2).
Proof.
  destruct x; first done.
  simpl. rewrite /map_zip. by apply insert_merge.
Qed.

Lemma binsert_interp_env x v1 v2 v3 Γ m vs :
  interp v1 v2 v3 ∗ interp_env Γ m vs -∗
  interp_env (binsert x v1 Γ) (binsert x v2 m) (binsert x v3 vs).
Proof.
  iIntros "(?&(%&?))".
  iSplitR. iPureIntro. rewrite !dom_binsert; set_solver.
  rewrite -map_zip_binsert. iApply big_sepM2_binsert. by iFrame.
Qed.


Lemma interp_env_bdelete x m1 m2 m3 :
  interp_env m1 m2 m3 -∗
  interp_env (bdelete x m1) (bdelete x m2) (bdelete x m3).
Proof.
  iIntros "X".
  destruct x as [|x]; first done; simpl.
  iDestruct (interp_env_dom_12 with "[$]") as "%".
  iDestruct (interp_env_dom_13 with "[$]") as "%".
  destruct_decide (decide (x ∈ dom m1)).
  { assert (is_Some (m1 !! x)) as (?&X1) by (eapply elem_of_dom; set_solver).
    assert (is_Some (m2 !! x)) as (?&X2) by (eapply elem_of_dom; set_solver).
    assert (is_Some (m3 !! x)) as (?&X3) by (eapply elem_of_dom; set_solver).
    rewrite {1}(insert_id_delete _ _ _ X1) {1}(insert_id_delete _ _ _ X2) {1}(insert_id_delete _ _ _ X3).
    rewrite interp_env_insert.
    2-4:rewrite dom_delete_L; set_solver.
    iDestruct "X" as "(?&?)". iFrame. }
  { rewrite !delete_notin //; apply not_elem_of_dom; set_solver. }
Qed.

Lemma interp_env_valid m1 m2 m3 :
  interp_env m1 m2 m3 ⊢ ⌜✓ m1⌝.
Proof.
  iIntros "X". iIntros (i).
  destruct_decide (decide (i ∈ dom m1)) as Hi.
  { iDestruct (interp_env_dom_13 with "X") as "%".
    assert (is_Some (m3 !! i)) as (?&X). eapply elem_of_dom. set_solver.
    rewrite {1}(insert_id_delete _ _ _ X).
    iDestruct (interp_insert_val_inv with "X") as "(%&%&%&%&(%&%&%&%)&?&_)".
    { rewrite dom_delete_L; set_solver. }
    subst. rewrite lookup_insert Some_valid.
    by iApply interp_valid. }
  { rewrite not_elem_of_dom_1 //. }
Qed.

Lemma interp_env_shape_valid m1 m2 m3 :
  interp_env m1 m2 m3 ⊢ ⌜✓ m2⌝.
Proof.
  iIntros "X". iIntros (i).
  iDestruct (interp_env_dom_12 with "X") as "%".
  destruct_decide (decide (i ∈ dom m1)) as Hi.
  { iDestruct (interp_env_dom_13 with "X") as "%".
    assert (is_Some (m3 !! i)) as (?&X). eapply elem_of_dom. set_solver.
    rewrite {1}(insert_id_delete _ _ _ X).
    iDestruct (interp_insert_val_inv with "X") as "(%&%&%&%&(%&%&%&%)&?&_)".
    { rewrite dom_delete_L; set_solver. }
    subst. rewrite lookup_insert Some_valid.
    by iApply interp_shape_valid. }
  { rewrite not_elem_of_dom_1 //. set_solver. }
Qed.

Lemma interp_env_binsert arg τ Γ s m v vs:
  interp τ s v -∗
  interp_env Γ m vs -∗
  interp_env (binsert arg τ Γ) (binsert arg s m) (binsert arg v vs).
Proof.
  iIntros "X1 (%&X2)".
  rewrite /interp_env.
  iSplitR.
  { iPureIntro. rewrite !dom_binsert //. set_solver. }
  rewrite -map_zip_binsert //. iApply big_sepM2_binsert.
  iFrame.
Qed.


Lemma interp_dup_intuitionistically t s v :
  t = t ⋅ t ->
  interp t s v -∗ □ interp t s v.
Proof.
  iIntros (Ht) "X".
  iInduction t as [] "IH" forall (s v); try done.
  all:destruct s; try done; simpl.
  { iDestruct "X" as "->". done. }
  { iDestruct "X" as "[% ->]". by iExists _. }
  { iDestruct "X" as "[% ->]". by iExists _. }
  { iDestruct "X" as "[% [% (->&?&?)]]".
    rewrite typ_op_unfold in Ht. simpl in Ht. inversion Ht.
    iDestruct ("IH" with "[%] [$]") as "#?".
    { rewrite -H2 //. }
    iDestruct ("IH1" with "[%] [$]") as "#?".
    { rewrite -H3 //. }
    by iFrame "#". }
  { iDestruct "X" as "#?". done. }
  { rewrite typ_op_unfold in Ht. simpl in Ht. inversion Ht.
    exfalso. eapply (Qp.not_add_le_l q q). rewrite -H2 //. }
  { rewrite typ_op_unfold in Ht. simpl in Ht. inversion Ht.
    exfalso. eapply (Qp.not_add_le_l q q). rewrite -H2 //. }
  { rewrite typ_op_unfold in Ht. simpl in Ht. inversion Ht.
    exfalso. eapply (Qp.not_add_le_l q q). rewrite -H2 //. }
  { rewrite typ_op_unfold in Ht. simpl in Ht. inversion Ht.
    exfalso. eapply (Qp.not_add_le_l q q). rewrite -H2 //. }
Qed.

Lemma interp_env_dup_intuitionistically Γ m' vs :
  Γ = Γ ⋅ Γ ->
  interp_env Γ m' vs -∗ □ interp_env Γ m' vs.
Proof.
  iIntros (HΓ) "X".
  iInduction vs as [] "IH" using map_ind forall (Γ m' HΓ).
  { iDestruct "X" as "(%Hd&X)".
    iDestruct (big_sepM2_empty_l with "X") as "%X".
    apply map_zip_empty_inv in X; last done. destruct X as (X&->).
    apply (@f_equal _ _ dom) in X.
    rewrite dom_empty_L in X.
    apply dom_empty_inv_L in X. subst. iModIntro.
    iSplit; first done. rewrite /interp_env map_zip_empty big_sepM2_empty //. }
  { apply not_elem_of_dom in H1.
    iDestruct (interp_insert_val_inv with "X") as "(%&%&%&%&((%X1&%X2&%X3&%X4)&U&X))".
    done.

    rewrite X1 X3.

    iDestruct ("IH" with "[%] X") as "#?".
    { generalize X1. intros X1'. apply (@f_equal _ _ (fun x => delete i x)) in X1'.
      rewrite delete_insert in X1'; last by eapply not_elem_of_dom.
      rewrite -X1' -delete_op -HΓ //. }

    iClear "IH X".

    apply (@f_equal _ _ (fun x => x !! i)) in X1.
    apply (@f_equal _ _ (fun x => x !! i)) in X3.
    rewrite !lookup_insert in X1,X3.
    iDestruct (interp_dup_intuitionistically with "U") as "#?".
    { apply (@f_equal _ _ (fun x => x !! i)) in HΓ.
      rewrite lookup_op X1 -Some_op in HΓ. naive_solver. }
    iModIntro. iApply interp_env_insert. 1-3:done. iFrame "#". }
Qed.

Lemma big_sepM2_singleton_inv_l `{Countable K} {A B} (Φ : K → A → B → vProp Σ)
  (i : K) (x1 : A) m2 :
  ([∗ map] k↦y1;y2 ∈ {[i := x1]};m2, Φ k y1 y2) -∗
  ∃ x2, ⌜ m2 = {[i := x2]} ⌝ ∗ Φ i x1 x2.
Proof.
  iIntros "X".
  iDestruct (big_sepM2_delete_l _ _ _ i with "X") as "[% (%&?&?)]".
  rewrite lookup_insert //.
  rewrite delete_singleton.
  iDestruct (big_sepM2_empty_r with "[$]") as "%".
  iExists _. iFrame. iPureIntro. apply map_eq.
  intros j. destruct_decide (decide (i=j)).
  { subst. rewrite lookup_insert //. }
  { rewrite lookup_insert_ne // lookup_empty.
    rewrite -(lookup_delete_ne m2 i j) // H3 //. }
Qed.

Lemma interp_env_singleton x τ s v :
  interp_env {[x := τ]} {[x := s]} {[x := v]} ⊣⊢
  interp τ s v.
Proof.
  rewrite /interp_env map_zip_singleton !dom_singleton_L big_sepM2_singleton.
  simpl. iSplit.
  { iIntros "(_&?)". done. }
  { iIntros. by iFrame. }
Qed.

End proof.
