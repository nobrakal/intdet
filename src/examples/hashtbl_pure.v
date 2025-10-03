From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export cancelable_invariants.
From iris.algebra Require Import gmap gmultiset agree frac_auth gset.

From intdet.lang Require Import syntax syntax_instances notations head_semantics.
From intdet.utils Require Import more_maps_and_sets.

(******************************************************************************)
(* Some matching theory *)

Definition stable `{Countable M, Countable W} (pm:M -> W -> W -> Prop) (pw:W -> M -> M -> Prop) (X:gmap M W) :=
  forall m w m' w',
  X !! m = Some w ->
  X !! m' = Some w' ->
  ¬ (pm m w' w /\ pw w' m m'). (* no instability *)

Definition injective `{Countable K} {V} (m:gmap K V) :=
  forall k1 k2 v, m !! k1 = Some v -> m !! k2 = Some v -> k1 = k2.

Lemma injective_delete `{Countable K} {V} v (M:gmap K V)  :
  injective M ->
  injective (delete v M).
Proof.
  intros Hp. intros ???.
  rewrite !lookup_delete_Some.
  naive_solver.
Qed.

Definition men_optimal `{Countable M, Countable W} (pm:M -> W -> W -> Prop) (pw:W -> M -> M -> Prop) P (X:gmap M W) (D:gset M) :=
  forall (X':gmap M W),
  dom X' = D ->
  P X' ->
  injective X' ->
  stable pm pw X' ->
  forall m w w', X !! m = Some w -> X' !! m = Some w' -> ¬ pm m w' w.

Lemma stable_delete `{Countable M, Countable W} (pm:M -> W -> W -> Prop) (pw:W -> M -> M -> Prop) m (X:gmap M W) :
  stable pm pw X ->
  stable pm pw (delete m X).
Proof.
  intros Hs. intros m1 m2 w1 w2.
  rewrite !lookup_delete_Some.
  intros (_&?) (_&?). by eapply Hs.
Qed.

Lemma men_optimal_delete `{Countable M, Countable W} (pm:M -> W -> W -> Prop) (pw:W -> M -> M -> Prop) m P (X:gmap M W) D :
  men_optimal pm pw P X D ->
  men_optimal pm pw P (delete m X) D.
Proof.
  intros Hopt.
  intros M' ????. intros ???. rewrite lookup_delete_Some.
  intros (?&?) ?. by eapply Hopt.
Qed.

(******************************************************************************)
(* Some parameters. *)

Record params :=
  mkp {
      cap: nat;
      hash: val -> nat;
      cmp: val -> val -> bool;
      dummy: loc;
      cmp_total : TotalOrder cmp
    }.

#[global] Existing Instance cmp_total.

Lemma anti_symm_cmp p x y:
  p.(cmp) x y /\ p.(cmp) y x ->
  x = y.
Proof.
  intros (?&?).
  eapply (@anti_symm _ eq p.(cmp)). apply _. all: done.
Qed.

(******************************************************************************)
(* probe & rank *)

Definition probe p k i :=
  (hash p k + i) `mod` cap p.

Definition rank p k v : nat :=
  Z.to_nat ((Z.of_nat v - Z.of_nat (hash p k)) `mod` cap p).

Lemma rank_probe p v i :
  rank p v (probe p v i) = i `mod` cap p.
Proof.
  intros.
  rewrite /rank /probe.
  rewrite Zminus_mod.
  rewrite Znat.Nat2Z.inj_mod.
  rewrite Zmod_mod.
  rewrite -Zminus_mod.
  rewrite -Nat2Z.inj_sub. 2:lia.
  replace (hash p v + i - hash p v) with i by lia.

  rewrite -(Nat2Z.id (i `mod` cap p)).
  rewrite Znat.Nat2Z.inj_mod //.
Qed.

Lemma probe_diff p v i :
  hash p v <= i ->
  probe p v (i - hash p v) = i `mod` cap p.
Proof.
  intros.
  rewrite /probe. f_equal. lia.
Qed.

Local Lemma probe_rank0 p v i :
  cap p ≠ 0 ->
  hash p v <= i ->
  probe p v (rank p v i) = i `mod` cap p.
Proof.
  intros.
  rewrite /probe /rank.
  rewrite (Nat.Div0.add_mod (hash p v)) //.
  rewrite Znat.Z2Nat.inj_mod. 2,3:lia.
  rewrite !Nat2Z.id.
  rewrite Nat.Div0.mod_mod.
  rewrite -(Nat.Div0.add_mod (hash p v) (Z.to_nat (i - hash p v)) (cap p)).
  rewrite Z2Nat.inj_sub. 2:lia.
  rewrite !Nat2Z.id. f_equal. lia.
Qed.

Lemma rank_add_mod p x i :
  cap p ≠ 0 ->
  rank p x i = rank p x (i `mod` cap p).
Proof.
  intros. rewrite /rank.
  rewrite (Zminus_mod (i `mod` cap p)%nat).
  rewrite Nat2Z.inj_mod. rewrite Z.mod_mod. 2:lia.
  rewrite -Zminus_mod //.
Qed.

Lemma probe_add_mod p x i :
  cap p ≠ 0 ->
  probe p x i = probe p x (i `mod` cap p).
Proof.
  intros. rewrite /probe.
  rewrite Nat.Div0.add_mod_idemp_r //.
Qed.

Lemma probe_rank p v i :
  cap p ≠ 0 ->
  probe p v (rank p v i) = i `mod` cap p.
Proof.
  intros.
  assert (rank p v i = (rank p v (i + hash p v * cap p))) as Hrankbuf.
  { symmetry. rewrite rank_add_mod // Nat.Div0.mod_add -rank_add_mod //. }
  rewrite Hrankbuf.
  rewrite probe_rank0 //; last nia.
  rewrite Nat.Div0.mod_add //.
Qed.

Lemma rank_hash_add p x i :
  rank p x (hash p x + i) = i `mod` cap p.
Proof.
  rewrite /rank.
  rewrite -Zminus_mod_idemp_l.
  rewrite -Znat.Nat2Z.inj_mod.
  fold (probe p x i).
  fold (rank p x (probe p x i)).
  rewrite rank_probe //.
Qed.

Lemma rank_lt_cap p v i :
  cap p ≠ 0 ->
  hash p v <= i ->
  rank p v i < cap p.
Proof.
  intros. rewrite /rank. rewrite Z2Nat.inj_mod. 2,3:lia.
  rewrite !Nat2Z.id. apply Nat.mod_upper_bound. done.
Qed.

(******************************************************************************)
(* The invariant *)

Definition before_pred P (p:params) (vs:list val) (i:nat) v :=
  ∀ j, j < i -> ∃ v', vs !! (probe p v j) = Some v' /\ P v'.

(* [before_full p vs i v] asserts that for any index [j < i]
   vs !! j contains other elements than v and the dummy,
   and that the ordering is preserved *)
Definition before_full (p:params) (vs:list val) (i:nat) (v:val) :=
  before_pred (fun v' => v' ≠ VLoc p.(dummy) /\ p.(cmp) v' v /\ v' ≠ v) p vs i v.

Definition hashset_inv_elem (p:params) (M:gmap val nat) (vs:list val) (v:val) (i:nat) :=
  v ≠ p.(dummy) /\ vs !! i = Some v /\ exists j, i = probe p v j /\ j < p.(cap) /\ before_full p vs j v.

Definition hashset_inv_model (p:params) (M:gmap val nat) (vs:list val) :=
  map_Forall (hashset_inv_elem p M vs) M.

(* [tie p M vs] asserts that each element in [vs] is either dummy or not dummy and in the map. *)
Definition tie p (M:gmap val nat) (vs:list val) :=
  ∀ i v, vs !! i = Some v -> v ≠ VLoc p.(dummy) -> M !! v = Some i.

Definition pkey (p:params) (k:val) (w w':nat) :=
  (rank p k w < rank p k w')%Z.

Definition pval (p:params) (w:nat) (k k':val) :=
  p.(cmp) k k' /\ k ≠ k'.

Definition all_are_probe p (M:gmap val nat) :=
  map_Forall (fun v i => i < cap p /\ exists j, j < cap p /\ i = probe p v j) M.

Lemma tie_in_dom i v p M vs :
  tie p M vs ->
  vs !! i = Some v ->
  v ≠ VLoc p.(dummy) ->
  v ∈ dom M.
Proof.
  intros X Y ?.
  apply X in Y.
  eapply elem_of_dom_2. by eapply Y.
Qed.

Lemma tie_add1 p vs i M v0 x :
  length vs = cap p ->
  vs !! i = Some v0 ->
  x ≠ VLoc p.(dummy) ->
  x ∉ dom M ->
  tie p M vs ->
  tie p (<[x:=i]> M) (<[i:=x]> vs) .
Proof.
  intros ? Hvsi Hx Hdx Htie.
  intros j v Hj Hv. destruct_decide (decide (i =j)); try subst j.
  { rewrite list_lookup_insert in Hj.
    2:{ apply lookup_lt_is_Some; eauto. }
    injection Hj. intros ->. rewrite lookup_insert //. }
  rewrite list_lookup_insert_ne // in Hj.
  apply Htie in Hj. apply Hj in Hv.
  rewrite lookup_insert_ne //.
  intros ->. apply Hdx. now apply elem_of_dom.
Qed.

Lemma nodup_tie v i j p M vs :
  tie p M vs ->
  vs !! i = Some v ->
  vs !! j = Some v ->
  v ≠ VLoc p.(dummy) ->
  i = j.
Proof.
  intros Htie Hi Hj Hv.
  pose proof (Htie _ _ Hi Hv).
  pose proof (Htie _ _ Hj Hv).
  naive_solver.
Qed.

Lemma tie_add2 p vs i M v0 x :
  vs !! i = Some v0 ->
  x ≠ VLoc p.(dummy) ->
  x ∉ dom M ->
  hashset_inv_model p M vs ->
  tie p M vs ->
  tie p (<[x:=i]> (delete v0 M)) (<[i:=x]> vs) .
Proof.
  intros  Hvsi Hx Hdx Hmod Htie.
  intros j v Hj Hv. destruct_decide (decide (i=j)); try subst j.
  { rewrite list_lookup_insert in Hj.
    2:{ apply lookup_lt_is_Some; eauto. }
    injection Hj. intros ->.
    rewrite lookup_insert. naive_solver. }
  rewrite list_lookup_insert_ne // in Hj.
  pose proof (Htie _ _ Hj Hv) as X.
  rewrite lookup_insert_ne //.
  2:{ intros ->. apply Hdx. now apply elem_of_dom. }
  rewrite lookup_delete_ne //. intros ->.
  apply Hmod in X. destruct X as (_&?&?).
  (* I have two occurrences of v at two different offsets !! *)
  eauto using nodup_tie.
Qed.

Lemma model_add1 p vs i i' M x :
  p.(cap) ≠ 0 ->
  p.(cap) = length vs ->
  vs !! i = Some (VLoc p.(dummy)) ->
  i = probe p x i' ->
  i' < cap p ->
  x ≠ (VLoc p.(dummy)) ->
  before_full p vs i' x ->
  hashset_inv_model p M vs ->
  hashset_inv_model p (<[x:=i]> M) (<[i:=x]> vs).
Proof.
  intros ?? Hvs ?? Hx Hfull Hmodel.
  intros v j Hv. rewrite /hashset_inv_elem.
  destruct_decide (decide (x=v)) as Hxv; try subst v.
  { rewrite lookup_insert in Hv. injection Hv. intros <-.
    subst. rewrite list_lookup_insert.
    2:{ apply lookup_lt_is_Some; eauto. }
    split_and ! ; eauto. eexists. do 2 (split; first done).
    intros z Hz.
    apply Hfull in Hz. destruct Hz as (y&?&?&?&?).
    exists y. rewrite list_lookup_insert_ne //.
    intros Hz. rewrite Hz in Hvs. naive_solver. }
  { rewrite lookup_insert_ne // in Hv.
    destruct (Hmodel _ _ Hv) as (Hv1&Hv2&(j'&?&?&Hv3)).
    split; first done.
    assert (i ≠ j).
    { (* v0 = v *)
      subst. intros E. rewrite -E in Hv2.
      rewrite Hvs in Hv2. naive_solver. }
    split.
    { rewrite list_lookup_insert_ne //. }
    { exists j'. do 2 (split; first done). intros z Hz.
      destruct (Hv3 _ Hz) as (v',(?&?&?)).
      destruct_decide (decide ( i = probe p v z)) as Eq; rewrite ?Eq.
      { eexists. rewrite list_lookup_insert.
        2:{ eauto using lookup_lt_Some. }
        split. done. split. done.
        rewrite Eq in Hvs. naive_solver. }
      exists v'. rewrite list_lookup_insert_ne //. } }
Qed.

Lemma model_add2 p vs i i' M x v0 :
  p.(cap) ≠ 0 ->
  p.(cap) = length vs ->
  vs !! i = Some v0 ->
  i = probe p x i' ->
  i' < cap p ->
  cmp p x v0 /\ x ≠ v0 ->
  x ≠ (VLoc p.(dummy)) ->
  before_full p vs i' x ->
  hashset_inv_model p M vs ->
  hashset_inv_model p (<[x:=i]> (delete v0 M)) (<[i:=x]> vs).
Proof.
  intros ? Hcap Hvs ?? (?&Hv') Hx Hfull Hmodel.
  intros v j Hv. rewrite /hashset_inv_elem.
  destruct_decide (decide (x=v)) as Hxv; try subst v.
  { rewrite lookup_insert in Hv. injection Hv. intros <-.
    subst. rewrite list_lookup_insert.
    2:{ apply lookup_lt_is_Some; eauto. }
    split_and ! ; eauto. eexists. do 2 (split; first done).
    intros z Hz.
    apply Hfull in Hz. destruct Hz as (y&?&?&?&?).
    exists y. rewrite list_lookup_insert_ne //.
    intros Hz. rewrite Hz in Hvs.
    assert (y = v0) by naive_solver. subst.
    apply Hv'. eauto using anti_symm_cmp. }
  { rewrite lookup_insert_ne // in Hv.
    apply lookup_delete_Some in Hv. destruct Hv as (?&Hv).
    destruct (Hmodel _ _ Hv) as (Hv1&Hv2&(j'&?&?&Hv3)).
    split; first done.
    assert (i ≠ j).
    { (* v0 = v *)
      subst. intros E. rewrite -E in Hv2.
      rewrite Hvs in Hv2. naive_solver. }
    split.
    { rewrite list_lookup_insert_ne //. }
    { exists j'. do 2 (split; first done). intros z Hz.
      destruct (Hv3 _ Hz) as (v',(?&?&?&?)).
      destruct_decide (decide ( i = probe p v z)) as Eq; rewrite ?Eq.
      { eexists. rewrite list_lookup_insert.
        2:{ eauto using lookup_lt_Some. }
        split. done. split. done.
        rewrite Eq in Hvs. assert (v0 = v') as -> by naive_solver.
        split. by etrans. done. }
      exists v'. rewrite list_lookup_insert_ne //. } }
Qed.

Lemma deduce_all_are_probe p M vs :
  length vs = cap p ->
  hashset_inv_model p M vs ->
  all_are_probe p M.
Proof.
  intros ? Hmod.
  intros v i Hv.
  apply Hmod in Hv. destruct Hv as (?&Hi&?&?&?&?).
  apply lookup_lt_Some in Hi. split. lia. eauto.
Qed.

Lemma all_are_probe_delete p v M :
  all_are_probe p M ->
  all_are_probe p (delete v M).
Proof.
  apply map_Forall_delete.
Qed.

Lemma all_are_probe_insert p v i M :
  cap p ≠ 0 ->
  i < cap p ->
  all_are_probe p M ->
  all_are_probe p (<[v:=probe p v i]> M).
Proof.
  intros. apply map_Forall_insert_2; last done.
  split. by apply Nat.mod_upper_bound.
  eauto.
Qed.

Definition opt p := men_optimal (pkey p) (pval p) (all_are_probe p).

Lemma model_injective p M vs :
  hashset_inv_model p M vs ->
  injective M.
Proof.
  intros Hmodel. intros k1 k2 v Hk1 Hk2.
  apply Hmodel in Hk1, Hk2.
  destruct Hk1 as (_&?&_).
  destruct Hk2 as (_&?&_).
  naive_solver.
Qed.

Lemma opt_add1 p M v vs i D v0 :
  p.(cap) ≠ 0 ->
  p.(cap) = length vs ->
  i < cap p ->
  vs !! (probe p v i) = Some v0 ->
  (v0 = VLoc p.(dummy) \/ v0 ≠ VLoc p.(dummy) /\ cmp p v v0) ->
  dom M ⊆ D ->
  before_full p vs i v ->
  (forall x j, j ≠ probe p v i -> vs !! j = Some x -> x ≠ VLoc (dummy p) -> M !! x = Some j) -> (* little specialized Htie to avoid duplication and a add2 *)
  all_are_probe p M ->
  opt p M D ->
  opt p (<[v:=probe p v i]> M) D.
Proof.
  intros ??? ? T U Hfull Htie Hare0 Hopt.
  intros M'. intros Hd Hare Hinj Hs.
  intros v' i1 i2.

  rewrite lookup_insert_case. case_decide; try subst v'.
  { inversion 1. subst.
    intros HM'. unfold pkey.
    intros Hrank. rewrite rank_probe in Hrank.
    rewrite Nat.mod_small // in Hrank.
    destruct (Hfull (rank p v i2)) as (x&Hx&Hdx&?&Hxv). lia.

    assert (i2 < cap p).
    { apply Hare in HM'. naive_solver. }

    rewrite probe_rank // Nat.mod_small // in Hx.
    assert (i2 ≠ probe p v i) as W.
    { destruct T as [ | (?&?)]. naive_solver. intros ->.
      assert (x = v0) by naive_solver. subst.
      eauto using anti_symm_cmp. }

    pose proof (Htie _ _ W Hx Hdx) as X.

    (* Where is x in M'? *)
    assert (is_Some (M' !! x)) as (j&Hj).
    { apply elem_of_dom. apply elem_of_dom_2 in X. set_solver. }
    pose proof (Hs _ _ _ _ Hj HM') as Hstbl.
    unfold pkey,pval in Hstbl.
    apply Hstbl. split_and !. 2,3:done.
    destruct_decide (decide (rank p x i2 = rank p x j)) as Eq.
    { exfalso. apply Hxv. (* x = v *)

      (* from [rank p x i2 = rank p x j] we are going
         to derive that [M' !! v = M' !! x] and conclude
         with the fact that M' is a partial function.
       *)
      destruct (Hare _ _ Hj) as (?&j2&?&Hj2). subst.
      rewrite rank_probe Nat.mod_small // in Eq.
      destruct (Hare _ _ HM') as (?&_).

      destruct (Hare0 _ _ X) as (?&j'&?&Hi2).
      rewrite Hi2 in Eq.
      rewrite rank_probe Nat.mod_small // in Eq.
      rewrite -Eq -Hi2 in Hj.

      by eapply Hinj. }
    destruct_decide (decide ((rank p x i2 < rank p x j))).
    { lia. }
    exfalso.
    assert (¬ (¬ (rank p x j < rank p x i2)))%Z as B by lia.
    apply B. clear B. by eapply (Hopt M'). }
  { intros ??. by eapply (Hopt M'). }
Qed.

Lemma opt_add2 p M D v vs i v0 :
  p.(cap) ≠ 0 ->
  p.(cap) = length vs ->
  i < cap p ->
  dom M ⊆ D ->
  vs !! (probe p v i) = Some v0 ->
  v0 ≠ VLoc p.(dummy) ->
  cmp p v v0 /\ v ≠ v0 ->
  before_full p vs i v ->
  tie p M vs ->
  all_are_probe p M ->
  opt p M D ->
  opt p (<[v:=probe p v i]> (delete v0 M)) D.
Proof.
  intros ??? U Hv0 Hdv0 (?&?) Hfull Htie Hare0 Hopt.

  eapply opt_add1; try done.
  { naive_solver. }
  { rewrite dom_delete_L. set_solver. }
  { intros ??? Hj ?. rewrite lookup_delete_ne //. by eapply Htie.
    intros <-. apply Htie in Hj, Hv0. naive_solver. }
  { eauto using all_are_probe_delete. }
  { by eapply men_optimal_delete. }
Qed.

Lemma opt_add p M D x :
  x ∉ dom M ->
  opt p M D ->
  opt p M ({[x]} ∪ D).
Proof.
  intros ? Hopt.

  destruct_decide (decide (x ∈ D)).
  { replace ({[x]} ∪ D) with D by set_solver. done. }

  intros X' Hd ??? ??? Hw ?.
  eapply (Hopt (delete x X')).
  { rewrite dom_delete_L. set_solver. }
  { eauto using all_are_probe_delete. }
  { eauto using injective_delete. }
  { eauto using stable_delete. }
  { done. }
  { rewrite lookup_delete_ne //. intros ->.
    eapply elem_of_dom_2 in Hw. set_solver. }
Qed.

(******************************************************************************)

Lemma inv_gives_stable p M vs :
  cap p ≠ 0 ->
  tie p M vs ->
  hashset_inv_model p M vs ->
  stable (pkey p) (pval p) M.
Proof.
  intros ? Htie Hmod.
  intros m w m' w' Hm Hm' (X1&(X2&X3)). apply X3. clear X3.
  unfold pkey in *.
  apply Hmod in Hm. destruct Hm as (?&?&j&?&?&Hfull).
  apply Hmod in Hm'. destruct Hm' as (?&?&j'&?&?&Hfull').
  subst w.
  rewrite rank_probe in X1. rewrite Nat.mod_small // in X1.
  edestruct (Hfull (rank p m w')) as (x&Hx&?&?&?).
  lia.
  subst.
  rewrite probe_rank // in Hx.
  rewrite Nat.mod_small in Hx. 2:by apply Nat.mod_upper_bound.
  assert (x=m') by naive_solver. subst.
  eauto using anti_symm_cmp.
Qed.

Lemma stable_optimal_inj p P M M' :
  dom M = dom M' ->
  P M /\ injective M /\ stable (pkey p) (pval p) M /\ men_optimal (pkey p) (pval p) P M (dom M)  ->
  P M' /\ injective M' /\ stable (pkey p) (pval p) M' /\ men_optimal (pkey p) (pval p) P M' (dom M') ->
  forall v i i',
  M !! v = Some i -> M' !! v = Some i' ->
  rank p v i = rank p v i'.
Proof.
  intros Hd (X1&X2&X3&X4) (Y1&Y2&Y3&Y4).
  intros v i i' Hi Hi'.
  assert (¬ pkey p v i' i).
  { by eapply X4. }
  assert (¬ pkey p v i i').
  { eapply Y4. 5,6:done. all:done. }
  unfold pkey in *. lia.
Qed.

Lemma rank_suffices p M1 M2 vs1 vs2 :
  cap p ≠ 0 ->
  length vs1 = cap p -> length vs2 = cap p ->
  dom M1 = dom M2 ->
  hashset_inv_model p M1 vs1 ->
  hashset_inv_model p M2 vs2 ->
  (forall v i i', M1 !! v = Some i -> M2 !! v = Some i' -> rank p v i = rank p v i') ->
  M1 = M2.
Proof.
  intros Hp Hl1 Hl2 Hdom Hmod1 Hmod2 X.
  apply map_eq. intros v.
  destruct_decide (decide (v ∈ dom M1)).
  { assert (is_Some (M1 !! v)) as (i1&Hi1).
    { by apply elem_of_dom. }
    assert (is_Some (M2 !! v)) as (i2&Hi2).
    { apply elem_of_dom. set_solver. }

    rewrite Hi1 Hi2. f_equal.
    edestruct (Hmod1 v i1) as (_&Hiv1&j1&?&?&_). done.
    edestruct (Hmod2 v i2) as (_&Hiv2&j2&?&?&_). done.
    apply lookup_lt_Some in Hiv1, Hiv2.
    rewrite -(Nat.mod_small _ _ Hiv1) -(Nat.mod_small _ _ Hiv2).
    rewrite Hl1 Hl2.
    rewrite -(probe_rank p v i1) // -(probe_rank p v i2) //.
    f_equal. eauto. }
  { rewrite !not_elem_of_dom_1 //. set_solver. }
Qed.

Record hashtbl_invariant p g M vs :=
  { hi1 : length vs = p.(cap);
    hi2 : tie p M vs;
    hi3 : hashset_inv_model p M vs;
    hi4 : opt p M (dom M ∪ g)
  }.

Lemma model_unique p M1 M2 vs1 vs2 :
  cap p ≠ 0 ->
  dom M1 = dom M2 ->
  hashtbl_invariant p ∅ M1 vs1 ->
  hashtbl_invariant p ∅ M2 vs2 ->
  M1 = M2.
Proof.
  intros Hp Hdom [Hl1 Htie1 Hmod1 Hopt1] [Hl2 Htie2 Hmod2 Hopt2].
  rewrite !right_id_L in Hopt1,Hopt2.
  eapply (rank_suffices p M1 M2 vs1 vs2); try done.
  intros.
  eapply stable_optimal_inj; first done.
  { split_and !; last done.
    all:eauto using model_injective, inv_gives_stable, deduce_all_are_probe. }
  { split_and !; last done.
    all:eauto using model_injective, inv_gives_stable, deduce_all_are_probe. }
  all:done.
Qed.

Lemma support_unique p M vs1 vs2 :
  cap p ≠ 0 ->
  hashtbl_invariant p ∅ M vs1 ->
  hashtbl_invariant p ∅ M vs2 ->
  vs1 = vs2.
Proof.
  intros Hp [Hl1 Htie1 Hmod1 Hopt1] [Hl2 Htie2 Hmod2 Hopt2].
  rewrite !right_id_L in Hopt1,Hopt2.

  apply list_eq. intros i.
  destruct_decide (decide (i < cap p)).
  { assert (is_Some (vs1 !! i)) as (v1&Hv1).
    { apply lookup_lt_is_Some_2. lia. }
    assert (is_Some (vs2 !! i)) as (v2&Hv2).
    { apply lookup_lt_is_Some_2. lia. }
    rewrite Hv1 Hv2.
    destruct_decide (decide (v1=VLoc (dummy p))) as X1.
    { subst.
      destruct_decide (decide (v2=VLoc (dummy p))) as X2.
      { naive_solver. }
      { exfalso. specialize (Htie2 _ _ Hv2 X2).
        apply Hmod1 in Htie2. destruct Htie2 as (_&?&_).
        naive_solver. } }
    { destruct_decide (decide (v2=VLoc (dummy p))) as X2.
      { exfalso. specialize (Htie1 _ _ Hv1 X1).
        apply Hmod2 in Htie1. destruct Htie1 as (_&?&_).
        naive_solver. }
      { specialize (Htie1 _ _ Hv1 X1).
        specialize (Htie2 _ _ Hv2 X2).
        apply Hmod2 in Htie1. destruct Htie1 as (_&?&_).
        naive_solver. } } }
  { rewrite !lookup_ge_None_2 //; lia. }
Qed.

Definition deterministic_support p g vs :=
  exists M, dom M = g /\ hashtbl_invariant p ∅ M vs.

Lemma use_deterministic_support p g vs1 vs2 :
  cap p ≠ 0 ->
  deterministic_support p g vs1 ->
  deterministic_support p g vs2 ->
  vs1 = vs2.
Proof.
  intros ? (M1&?&HM1) (M2&?&HM2). subst g.
  assert (M1 = M2) as -> by eauto using model_unique.
  eauto using support_unique.
Qed.

Lemma hashtbl_invariant_init p :
  hashtbl_invariant p ∅ ∅ (replicate (cap p) (VLoc (dummy p))).
Proof.
  constructor.
  { rewrite replicate_length //. }
  { intros ?? X1 X2. exfalso. apply lookup_replicate_1 in X1. naive_solver. }
  { intros ??. naive_solver. }
  { intros ??. simpl. naive_solver. }
Qed.

Definition NoDup_except `{EqDecision A} (x:A) (xs:list A) :=
  NoDup (base.filter (fun y => y ≠ x) xs).

(* A correctness lemma *)
Lemma nodup_ok p M vs :
  tie p M vs -> NoDup_except (VLoc p.(dummy)) vs.
Proof.
  intros Htie. apply NoDup_alt.
  intros i j x Hi Hj.
  destruct_decide (decide (i=j)) as Hij; eauto.
  exfalso.
  assert (exists i' j', i' ≠ j' /\ x ≠ VLoc p.(dummy) /\ vs !! i' = Some x /\ vs !! j'= Some x) as (i',(j',(Hij'&Hx&Hi'&Hj'))).
  2:eauto using nodup_tie.
  clear Htie. revert i Hi j Hj Hij. induction vs; intros.
  { rewrite filter_nil in Hi.  rewrite lookup_nil in Hi. congruence. }
  { rewrite filter_cons in Hi,Hj. case_decide.
    { destruct i,j; simpl in *. congruence.
      { apply elem_of_list_lookup_2 in Hj. apply elem_of_list_filter in Hj. destruct Hj as (?&Hj).
        apply elem_of_list_lookup_1 in Hj. destruct Hj as (j'&?). exists 0,(S j'). naive_solver. }
      { apply elem_of_list_lookup_2 in Hi. apply elem_of_list_filter in Hi. destruct Hi as (?&Hi).
        apply elem_of_list_lookup_1 in Hi. destruct Hi as (i'&?). exists (S i'),0. naive_solver. }
      destruct (IHvs i Hi j Hj) as (i',(j',(?&?&?&?))). naive_solver.
      exists (S i'), (S j'). naive_solver. }
    { destruct (IHvs i Hi j Hj) as (i',(j',(?&?&?&?))). naive_solver.
      exists (S i'), (S j'). naive_solver. } }
Qed.

Lemma hashset_model_ok p M vs :
  tie p M vs ->
  hashset_inv_model p M vs ->
  (dom M ⊆ list_to_set vs ⊆ dom M ∪ {[VLoc p.(dummy)]}).
Proof.
  intros Htie HM. split; intros v; rewrite elem_of_list_to_set elem_of_list_lookup; intros Hv.
  { apply elem_of_dom in Hv. destruct Hv as (?,Hv).
    destruct (HM _ _ Hv). naive_solver. }
  { destruct Hv as (i,Hi).
    apply Htie in Hi.
    destruct_decide (decide (v=VLoc (dummy p))). set_solver.
    rewrite elem_of_union elem_of_dom. eauto. }
Qed.

Record correct_result (dumm:val) (cap:nat) (g:gset val) (vs:list val):=
  mkcr
    { cr_nodup  : NoDup_except dumm vs;
      cr_length : length vs = cap;
      cr_elem   : g ⊆ list_to_set vs ⊆ g ∪ {[dumm]};
      cr_notin  : dumm ∉ g
    }.

Lemma hashset_gives_correct_result p M g vs :
  hashtbl_invariant p g M vs ->
  correct_result (dummy p) (cap p) (dom M) vs.
Proof.
  intros [? ? Hmod ?].
  constructor; eauto using nodup_ok,hashset_model_ok.
  intros X. apply elem_of_dom in X. destruct X as (?&X).
  apply Hmod in X. destruct X as (X&_). congruence.
Qed.

Definition deduped (xs:list val) (X:gset val) :=
  NoDup xs /\ (∀ x, x ∈ xs <-> x ∈ X).

Lemma list_to_set_subseteq (xs ys: list val) :
  list_to_set xs ⊆ (list_to_set ys : gset val) ->
  xs ⊆ ys.
Proof.
  intros Hincl x Hx. specialize (Hincl x).
  rewrite !elem_of_list_to_set in Hincl. eauto.
Qed.

From intdet.examples Require Import filter_compact.

Lemma correct_result_dedup e s xs g :
  correct_result e s g xs ->
  deduped (filter_pure e xs) g.
Proof.
  intros []. constructor; eauto. intros x.
  destruct cr_elem0 as (E1&E2).
  rewrite /filter_pure elem_of_list_filter.
  set_solver.
Qed.
