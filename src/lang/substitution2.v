From Coq Require Import Wellfounded ssreflect.
From stdpp Require Import base strings gmap ssreflect.

From intdet.utils Require Import more_maps_and_sets.
From intdet.lang Require Import utils syntax.

(******************************************************************************)
(* [msubsts] is an environment-based substitution *)

Fixpoint msubsts (vs:gmap string val) (e:expr) : expr :=
  match e with
  | Val _ => e
  | Code x xs e' => Code x xs (msubsts (bdeletes [x;xs] vs) e')
  | Var y =>
      match vs !! y with
      | Some v => Val v
      | None => e end
  | Call e ts =>
      Call (msubsts vs e) (msubsts vs ts)
  | CallPrim p e1 e2 =>
      CallPrim p (msubsts vs e1) (msubsts vs e2)
  | If e1 e2 e3 =>
      If (msubsts vs e1) (msubsts vs e2) (msubsts vs e3)
  | Let y e1 e2 =>
      Let y (msubsts vs e1) (msubsts (bdelete y vs) e2)
  | Assert e =>
      Assert (msubsts vs e)
  | Alloc e =>
      Alloc (msubsts vs e)
  | Fst e =>
      Fst (msubsts vs e)
  | Snd e =>
      Snd (msubsts vs e)
  | Length e =>
      Length (msubsts vs e)
  | Pair e1 e2 =>
      Pair (msubsts vs e1) (msubsts vs e2)
  | Load e1 e2  =>
      Load (msubsts vs e1) (msubsts vs e2)
  | Store e1 e2 e3 =>
      Store (msubsts vs e1) (msubsts vs e2) (msubsts vs e3)
  | Par e1 e2 =>
      Par (msubsts vs e1) (msubsts vs e2)
  | RunPar e1 e2 =>
      RunPar (msubsts vs e1) (msubsts vs e2)
  | CAS e1 e2 e3 e4 =>
      CAS (msubsts vs e1) (msubsts vs e2) (msubsts vs e3) (msubsts vs e4)
  end.

Lemma msubsts_val vs (v:val) :
  msubsts vs v = v.
Proof. done. Qed.

Lemma msubsts_empty e :
  msubsts ∅ e = e.
Proof.
  induction e as [e IH] using (well_founded_induction (wf_inverse_image _ nat _ expr_size PeanoNat.Nat.lt_wf_0)).
  destruct e; simpl; try done.
  all:try (f_equal; apply IH; simpl; lia).
  { f_equal. rewrite !bdelete_empty. naive_solver by lia. }
  { f_equal. naive_solver by lia. rewrite bdelete_empty. naive_solver by lia. }
Qed.

Lemma elem_of_binders_set x xs :
  binders.BNamed x ∈ xs <-> x ∈ binders_set xs.
Proof.
  induction xs; simpl. set_solver.
  rewrite binders_set_cons elem_of_cons.
  rewrite IHxs. destruct a; set_solver.
Qed.

Lemma subst_msubsts x v e :
  subst x v e = msubsts {[x:=v]} e.
Proof.
  induction e as [e IH] using (well_founded_induction (wf_inverse_image _ nat _ expr_size PeanoNat.Nat.lt_wf_0)).
  destruct e; first done.
  { cbn [subst msubsts]. case_decide as X; rewrite elem_of_binders_set in X; f_equal.
    { rewrite -(bdeletes_already_in x); last set_solver.
      rewrite bdelete_bdeletes. cbn [bdelete].
      rewrite delete_singleton bdeletes_empty msubsts_empty //. }
    { rewrite bdeletes_disj.
      { apply IH. simpl. lia. }
      { rewrite binders_set_cons. set_solver. } } }
  all:simpl.
  { rewrite lookup_insert_case. case_decide; done. }
  all: try rewrite !IH; try (simpl; lia); try done.
  { f_equal. case_decide; subst; try done.
    { simpl. rewrite delete_singleton msubsts_empty //. }
    { rewrite bdelete_singleton_ne //. } }
Qed.

Lemma msubsts_union m1 m2 e :
  msubsts (m1 ∪ m2) e = msubsts m2 (msubsts m1 e).
Proof.
  revert m1 m2.
  induction e; first done; intros m1 m2.
  { cbn [msubsts]. f_equal. rewrite bdeletes_union IHe //. }
  all: simpl; try rewrite ?IHe ?IHe1 ?IHe2 ?IHe3 ?IHe4 //.
  { rewrite lookup_union.
    destruct (m1!! s) eqn:E.
    { rewrite union_Some_l. destruct (m2!!s); simpl; rewrite ?E //. }
    { rewrite left_id //. } }
  { f_equal. rewrite bdelete_union IHe2 //. }
Qed.

Lemma msubsts_insert s v m e :
  msubsts (<[s:=v]> m) e = msubsts m (subst s v e).
Proof.
  rewrite insert_union_singleton_l msubsts_union subst_msubsts //.
Qed.

Lemma insert_msubsts s v m e :
 subst s v (msubsts (delete s m) e) = msubsts (<[s:=v]>m) e.
Proof.
  rewrite -insert_delete_insert insert_union_singleton_l subst_msubsts -msubsts_union.
  f_equal. apply map_union_comm. apply map_disjoint_dom_2.
  rewrite dom_delete_L dom_singleton_L. set_solver.
Qed.

Lemma binsert_msubsts s v m e :
 subst' s v (msubsts (bdelete s m) e) = msubsts (binsert s v m) e.
Proof.
  destruct s; first done. simpl. apply insert_msubsts.
Qed.

Lemma msubsts_insert_notin s v m e :
  s ∉ dom m ->
  msubsts (<[s:=v]> m) e = subst s v (msubsts m e).
Proof.
  intros.
  rewrite insert_union_singleton_l map_union_comm.
  2:{ apply map_disjoint_singleton_l_2. by apply not_elem_of_dom. }
  rewrite !msubsts_union subst_msubsts //.
Qed.

Lemma msubsts_binsert x v m e :
  msubsts (binsert x v m) e = msubsts m (subst' x v e).
Proof.
  destruct x; first done. simpl. rewrite msubsts_insert //.
Qed.

Lemma subst_msubsts_bdelete x y m e :
  binder_set x ## dom m ->
  subst' x y (msubsts m e) =
  msubsts (binsert x y m) e.
Proof.
  intros. destruct x; first done. simpl.
  rewrite msubsts_insert -msubsts_insert_notin; last set_solver.
  rewrite msubsts_insert //.
Qed.

Lemma substs_msubsts_bdeletes xs ys m e :
  length xs = length ys ->
  binders_set xs ## dom m ->
  substs' (zip xs ys) (msubsts m e) =
  msubsts (extend xs ys m) e.
Proof.
  revert ys e; induction xs using rev_ind; intros ys e Hl Hdisj.
  { destruct ys; done. }
  destruct (last ys) eqn:Hlast; last first.
  { rewrite app_length in Hl. apply last_None in Hlast. subst.
    simpl in *. lia. }
  { apply last_Some in Hlast. destruct Hlast as (ys'&->).
    rewrite !app_length in Hl. simpl in Hl.
    rewrite zip_app; last lia. simpl.
    rewrite substs'_app. simpl.
    rewrite /extend rev_zip.
    2:{ rewrite !app_length. simpl. lia. }
    rewrite !rev_app_distr zip_app; last by (simpl; lia).
    simpl. rewrite -rev_zip; last lia.
    rewrite binders_set_app in Hdisj.
    destruct x; simpl.
    { rewrite IHxs //.
      lia. set_solver. }
    rewrite msubsts_insert -msubsts_insert_notin.
    2:{ rewrite /binders_set in Hdisj. simpl in *. set_solver. }
    rewrite -IHxs; only 2:lia; last set_solver.
    rewrite msubsts_insert //. }
Qed.

Lemma dom_bdelete {A} b (m:gmap string A) :
  dom (bdelete b m) = dom m ∖ binder_set b.
Proof.
  destruct b; simpl; set_solver.
Qed.

Lemma dom_bdeletes {A} bs (m:gmap string A) :
  dom (bdeletes bs m) = dom m ∖ ⋃ (binder_set <$> bs).
Proof.
  induction bs. set_solver.
  simpl. rewrite dom_bdelete. rewrite IHbs. set_solver.
Qed.

Local Ltac goih IH := apply IH; [ simpl; lia | ].

Lemma msubsts_not_in_fv m e :
  dom m ## fv e ->
  msubsts m e = e.
Proof.
  revert m.
  induction e as [e IH] using (well_founded_induction (wf_inverse_image _ nat _ expr_size PeanoNat.Nat.lt_wf_0)).
  intros ? X.
  destruct e; first done.
  { cbn [msubsts]. f_equal. goih IH.
    rewrite dom_bdeletes //. set_solver. }
  { simpl. rewrite not_elem_of_dom_1 //. set_solver. }
  all:simpl; f_equal; goih IH; rewrite ?dom_bdelete; set_solver.
Qed.
