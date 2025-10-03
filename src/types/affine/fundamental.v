From stdpp Require Import binders.

From iris.proofmode Require Import proofmode.
From iris Require Import gmap saved_prop invariants.
From iris.bi Require Import monpred.

From intdet.utils Require Import restrict more_cmras more_maps_and_sets.
From intdet.lang Require Import syntax utils substitution2 notations.
From intdet.musketeer Require Import dwp lockstep.
From intdet.types Require Import utils.
From intdet.types.affine Require Import typing logrel op_related logrel_facts syntactical.
From intdet.examples Require Import tactics_triple.

Section fundamental.

Context `{intdetGS Σ, typeG Σ}.

Lemma log_typed_var (x:string) τ :
  ⊢ log_typed {[x:=τ]} x τ ∅.
Proof.
  iModIntro. iIntros (m vs). simpl.

  iApply (triple_use_pure_pre (exists s v, m = {[x:=s]} /\ vs = {[x:=v]})).
  { iIntros "(%Hd&X)". rewrite dom_insert_L dom_empty_L right_id_L in Hd.
    apply dom_singleton_inv_L in Hd. destruct Hd as (?&?). subst.
    rewrite map_zip_singleton.
    iDestruct (big_sepM2_singleton_inv_l with "X") as "[%x2 (->&?)]".
    eauto. }
  iIntros ((s&v&->&->)).

  rewrite lookup_singleton. iApply triple_val.
  iExists (s,∅). rewrite /interp_env. monPred.unseal.
  rewrite !monPred_at_big_sepM2 //.
  rewrite !map_zip_singleton !big_sepM2_singleton. simpl.
  iSplitL; iIntros "(_&?)"; iFrame; simpl.
  all:rewrite map_zip_empty dom_empty_L restrict_empty' big_sepM2_empty right_id.
  all:iPureIntro; split_and !; try done.
  all:apply senv_singleton_l.
Qed.

Lemma log_typed_unit :
  ⊢ log_typed ∅ VUnit TUnit ∅.
Proof.
  iIntros (? ?) "!>". simpl.
  iApply (triple_use_pure_pre (m = ∅ /\ vs = ∅)).
  { iIntros "(%Hd&?)".
    rewrite dom_empty_L in Hd. apply dom_empty_inv_L in Hd. subst.
    rewrite map_zip_empty.
    iDestruct (big_sepM2_empty_r with "[$]") as "->". done. }
  iIntros ((->&->)).
  iApply (triple_resolve (SNone,∅)).
  iApply triple_val'.
  iIntros "?". iFrame. done.
Qed.

Lemma log_typed_bool b :
  ⊢ log_typed ∅ (VBool b) TBool ∅.
Proof.
  iIntros (? ?) "!>". simpl.
  iApply (triple_use_pure_pre (m = ∅ /\ vs = ∅)).
  { iIntros "(%Hd&?)".
    rewrite dom_empty_L in Hd. apply dom_empty_inv_L in Hd. subst.
    rewrite map_zip_empty.
    iDestruct (big_sepM2_empty_r with "[$]") as "->". done. }
  iIntros ((->&->)).
  iApply (triple_resolve (SNone,∅)).
  iApply triple_val'.
  iIntros "?". iFrame. iSplit; first done.
  by iExists _.
Qed.

Lemma log_typed_int i :
  ⊢ log_typed ∅ (VInt i) TInt ∅.
Proof.
  iIntros (? ?) "!>". simpl.
  iApply (triple_use_pure_pre (m = ∅ /\ vs = ∅)).
  { iIntros "(%Hd&?)".
    rewrite dom_empty_L in Hd. apply dom_empty_inv_L in Hd. subst.
    rewrite map_zip_empty.
    iDestruct (big_sepM2_empty_r with "[$]") as "->". done. }
  iIntros ((->&->)).
  iApply (triple_resolve (SNone,∅)).
  iApply triple_val'.
  iIntros "?". iFrame. iSplit; first done.
  by iExists _.
Qed.

Lemma log_typed_assert Γ Γ' e :
  log_typed Γ e TBool Γ' -∗
  log_typed Γ (Assert e) TUnit Γ'.
Proof.
  iIntros "#X". iIntros (m vs) "!>". simpl.
  iApply (triple_bind CtxAssert). iApply "X".
  iIntros (v (s,m')). simpl.

  iApply (triple_use_pure_pre (s = SNone /\ exists (b:bool), v = b)).
  { iIntros "(_&R&?)".
    destruct s; try done.
    iDestruct "R" as "[% ->]". eauto. }
  iIntros ((->&(b&->))). simpl.
  iApply (triple_resolve (SNone,m')).
  iApply triple_conseq_pre.
  { iApply bi.emp_sep_1. }
  rewrite comm.
  iApply triple_frame_wand.
  iApply triple_conseq. 3:iApply triple_assert.
  { by iIntros. }
  { iIntros (? _) "(->&->) (?&?&?)". iFrame.
    rewrite /interp_unit //. }
Qed.

Local Lemma map_subseteq_exists `{Countable K} {V:cmra} (m1 m2:gmap K V) :
  m1 ⊆ m2 ->
  exists m0, m2 = m0 ⋅ m1 /\ dom m1 ## dom m0.
Proof.
  intros Hincl.
  exists (restrict (dom m2 ∖ dom m1) m2).
  split.
  { apply map_eq. intros i. rewrite lookup_op.
    rewrite lookup_restrict.
    case_decide.
    { rewrite (not_elem_of_dom_1 m1); last set_solver. rewrite right_id_L //. }
    { rewrite left_id_L. specialize (Hincl i).
      destruct (m1 !! i) eqn:E1, (m2 !! i) eqn:E2; simpl in *; try done.
      naive_solver.
      apply elem_of_dom_2 in E2. apply not_elem_of_dom in E1. set_solver. } }
  { rewrite dom_restrict. set_solver. }
Qed.

Lemma senv_op_l_disj `{Countable K} {A:cmra} f (Γ1 Γ2 Γ3:gmap K A) :
  dom Γ1 ## dom Γ3 ->
  senv f Γ2 Γ3 ->
  senv f (Γ1 ⋅ Γ2) Γ3.
Proof.
  intros X1 X2. intros i. rewrite lookup_op.
  specialize (X2 i).
  destruct (Γ1 !! i) eqn:E1.
  { apply elem_of_dom_2 in E1.
    rewrite (not_elem_of_dom_1 Γ3). 2:set_solver.
    by destruct (Some c ⋅ Γ2 !! i). }
  { rewrite left_id_L //. }
Qed.

Lemma senv_op_r_disj `{Countable K} {A:cmra} f (Γ1 Γ2 Γ3:gmap K A) :
  dom Γ2 ## dom Γ3 ->
  senv f Γ1 (Γ2 ⋅ Γ3) ->
  senv f Γ1 Γ3.
Proof.
  intros X1 X2. intros i.
  specialize (X2 i).
  rewrite lookup_op in X2.
  destruct (Γ3 !! i) eqn:E1.
  { apply elem_of_dom_2 in E1.
    rewrite (not_elem_of_dom_1 Γ2) in X2. 2:set_solver.
    rewrite left_id in X2. done. }
  { by destruct (Γ1 !! i). }
Qed.

Lemma log_typed_weak Γ1 Γ1' Γ2 Γ2' e t :
  dom Γ2' ⊆ dom Γ1' ->
  fv e ⊆ dom Γ1' ->
  Γ1' ⊆ Γ1 ->
  Γ2 ⊆ Γ2' ->
  log_typed Γ1' e t Γ2' -∗
  log_typed Γ1 e t Γ2.
Proof.
  iIntros (HX ? Hincl1 Hincl2) "#X !>".
  iIntros (m vs).
  apply map_subseteq_exists in Hincl1.
  destruct Hincl1 as (Γ0&->&?).

  iApply triple_use_pure_pre.
  iApply interp_sepM2_op_inv_l.
  iIntros ((m1&m2&->&?&?&_)).

  iApply triple_conseq_pre.
  iApply interp_env_split_1. 1,2:done.

  rewrite {3}(restrict_split (dom Γ1') vs) map_union_comm.
  2:{ apply map_disjoint_dom. rewrite !dom_restrict. set_solver. }
  rewrite !msubsts_union.
  rewrite (msubsts_not_in_fv _ e).
  2:{ rewrite dom_restrict. set_solver. }

  (* XXX Should not be m'*)


  iApply triple_end.
  iApply triple_conseq_pre. 2:iApply "X".
  { iIntros "(_&?)". iFrame. }

  iIntros (? (s,m')).
  iApply triple_extract_pure_pre.
  iIntros ((?&?)).

  apply map_subseteq_exists in Hincl2.
  destruct Hincl2 as (Γ0'&->&?).
  iApply triple_use_pure_pre.
  { iIntros "(_&?)". by iApply interp_sepM2_op_inv_l. }
  iIntros ((m1'&m2'&->&?&?&_)).

  iApply (triple_resolve (s,m2')).
  iApply triple_val'.

  iIntros "(?&?)". iFrame.
  rewrite restrict_restrict.
  iDestruct (interp_env_dom_13 with "[$]") as "%Hd2".
  rewrite dom_restrict in Hd2.
  replace (dom (Γ0' ⋅ Γ2) ∩ dom Γ1') with (dom (Γ0' ⋅ Γ2)) by set_solver.

  iDestruct (interp_env_split_1 with "[$]") as "(_&?)". 1,2:done.
  rewrite restrict_restrict. rewrite dom_op.
  replace (dom Γ2 ∩ (dom Γ0' ∪ dom Γ2)) with (dom Γ2) by set_solver.
  iFrame.
  iPureIntro.
  rewrite dom_op in HX.
  split.
  { apply senv_op_l_disj; try done. set_solver.
    eapply senv_op_r_disj; try done. }
  { apply senv_op_l_disj; try done. set_solver.
    eapply senv_op_r_disj; try done. set_solver. }
Qed.

Lemma log_typed_if Γ e1 e2 e3 Γ' Γ'' t :
  fv e2 ∪ fv e3 ⊆ dom Γ' ->
  log_typed Γ e1 TBool Γ' -∗
  log_typed Γ' e2 t Γ'' -∗
  log_typed Γ' e3 t Γ'' -∗
  log_typed Γ (If e1 e2 e3) t Γ''.
Proof.
  iIntros (?) "#X1 #X2 #X3".
  iIntros "!>" (m vs). simpl.
  iApply (triple_bind (CtxIf _ _)).
  iApply "X1". iClear "X1".
  iIntros (v (s,m')).
  iApply (triple_use_pure_pre (s = SNone /\ dom m' = dom Γ' /\ exists (b:bool), v = b)).
  { iIntros "(_&R&?)".
    iDestruct (interp_env_dom_12 with "[$]") as "%".
    destruct s; try done.
    iDestruct "R" as "[% ->]". eauto. }
  iIntros ((->&?&(b&->))).
  iApply triple_extract_pure_pre. iIntros ((?&?)).
  simpl.

  rewrite {2 3}(restrict_split (dom Γ') vs) map_union_comm.
  2:{ apply map_disjoint_dom. rewrite !dom_restrict. set_solver. }
  rewrite !msubsts_union.
  rewrite (msubsts_not_in_fv _ e2).
  2:{ rewrite dom_restrict. set_solver. }
  rewrite (msubsts_not_in_fv _ e3).
  2:{ rewrite dom_restrict. set_solver. }

  triple_if.
  iApply triple_conseq_post.
  2:{ destruct b.
      { iApply triple_conseq_pre. 2:iApply "X2".
        iIntros "(?&?)". iFrame. }
      { iApply triple_conseq_pre. 2:iApply "X3".
        iIntros "(?&?)". iFrame. } }

  iIntros (? (?,?)) "((%&%)&?&?)".
  rewrite restrict_restrict.
  iDestruct (interp_env_dom_12 with "[$]") as "%".
  iDestruct (interp_env_dom_13 with "[$]") as "%Hd".
  rewrite dom_restrict in Hd.
  replace (dom Γ'' ∩ dom Γ') with (dom Γ'') by set_solver. iFrame.
  iPureIntro. split.
  { eapply senv_trans. apply _. 2,3:done. set_solver. }
  { eapply senv_trans. apply _. 2,3:done. set_solver. }
Qed.

Lemma get_result_call_prim p t1 t2 t3 v1 s1 v2 s2 :
  prim_typed p t1 t2 t3 ->
  interp t1 s1 v1 -∗
  interp t2 s2 v2 -∗
  ∃ v, ⌜eval_call_prim p v1 v2 = Some v⌝ ∗ interp t3 SNone v.
Proof.
  destruct p; only 1:intros (->&->); only 2-4:intros (->&->&->); simpl.
  { iIntros "_ _". eauto. }
  { iIntros "X1 X2". destruct s1; try done. destruct s2; try done.
    iDestruct "X1" as "[% ->]".
    iDestruct "X2" as "[% ->]".
    destruct b; eauto. }
  { iIntros "X1 X2". destruct s1; try done. destruct s2; try done.
    iDestruct "X1" as "[% ->]".
    iDestruct "X2" as "[% ->]".
    destruct i; eauto. }
  { iIntros "X1 X2". destruct s1; try done. destruct s2; try done.
    iDestruct "X1" as "[% ->]".
    iDestruct "X2" as "[% ->]".
    destruct i; eauto. }
Qed.

Lemma log_typed_call_prim p Γ e1 t1 Γ' e2 t2 Γ'' t3 :
  fv e2 ⊆ dom Γ' ->
  prim_typed p t2 t1 t3 ->
  log_typed Γ e1 t1 Γ' -∗
  log_typed Γ' e2 t2 Γ'' -∗
  log_typed Γ (CallPrim p e2 e1) t3 Γ''.
Proof.
  iIntros (? Hp) "#X1 #X2".
  iIntros "!>" (m vs). simpl.

  iApply (triple_bind (CtxCallPrim1 _ _)).
  iApply "X1". iClear "X1".
  iIntros (v1 (s1,m')). simpl.

  iApply triple_extract_pure_pre. iIntros ((?&?)).

  iApply (triple_use_pure_pre (dom Γ' = dom m')).
  { iIntros "(_&?)".
    iApply (interp_env_dom_12 with "[$]"). }
  iIntros.

  rewrite {2}(restrict_split (dom Γ') vs) map_union_comm.
  2:{ apply map_disjoint_dom. rewrite !dom_restrict. set_solver. }
  rewrite !msubsts_union.
  rewrite (msubsts_not_in_fv _ e2).
  2:{ rewrite dom_restrict. set_solver. }

  iApply (triple_bind (CtxCallPrim2 _ _)).
  { iApply triple_frame_wand.
    iApply triple_conseq_post. 2:iApply "X2".
    iIntros (? (?,?)) "((%&%)&?&?) ?".
    iDestruct (interp_env_dom_12 with "[$]") as "%".
    iDestruct (interp_env_dom_13 with "[$]") as "%Hd".
    rewrite !dom_restrict in Hd.
    rewrite restrict_restrict.

    replace (dom Γ'' ∩ dom Γ') with (dom Γ'') by set_solver.
    Unshelve.
    2:exact (fun v '(s,g) => ⌜similar_env Γ' Γ'' /\ similar_shape_env m' g /\ dom Γ'' ⊆ dom Γ'⌝ ∗ interp t2 s v ∗ interp_env Γ'' g (restrict (dom Γ'') vs) ∗ interp t1 s1 v1)%I. iFrame. iPureIntro. set_solver. }
  iIntros (? (s',m'')). simpl.

  iApply triple_extract_pure_pre. iIntros ((?&?&?)). iClear "X2".

  iApply (triple_conseq_pre (∃ v', ⌜eval_call_prim p v v1 = Some v'⌝ ∗ interp t3 SNone v' ∗ interp_env Γ'' m'' (restrict (dom Γ'') vs)))%I.
  { iIntros "(X1&?&X2)".
    iDestruct (get_result_call_prim with "X1 X2") as "(%&%&?)". done.
    by iFrame. }

  iApply triple_extrude_existential.
  { monPred.unseal. iIntros (?) "(%E1&_)". iModIntro.
    iIntros (?) "(%E2&_)". iPureIntro. naive_solver. }
  iIntros (x).
  iApply triple_extract_pure_pre. iIntros (?).

  iApply (triple_resolve (SNone,m'')).
  iApply triple_conseq_post. 2:by iApply triple_call_prim'.
  iIntros (? []) "(->&?&?)".

  iDestruct (interp_env_dom_12 with "[$]") as "%".
  iDestruct (interp_env_dom_13 with "[$]") as "%Hd".
  rewrite dom_restrict in Hd.

  iFrame. iPureIntro.
  split.
  { eapply senv_trans. apply _. 2,3:done. set_solver. }
  { eapply senv_trans. apply _. 2,3:done. set_solver. }
Qed.

Lemma subst_msubsts' x v e :
  subst' x v e = msubsts (bmap [x] [v]) e.
Proof.
  rewrite /bmap /extend. simpl.
  destruct x; simpl.
  { rewrite msubsts_empty //. }
  { rewrite subst_msubsts //. }
Qed.

Lemma upd_typ_env_same_dom m1 m2 :
  upd_typ_env m1 m2 -> dom m1 = dom m2.
Proof.
  intros X. apply leibniz_equiv. intros i.
  specialize (X i).
  do 2 rewrite elem_of_dom.
  by destruct (m1 !! i), (m2 !! i).
Qed.

Lemma upd_typ_env_cons_l_inv i t Γ1 Γ2:
  i ∉ dom Γ1 ->
  upd_typ_env (<[i:=t]> Γ1) Γ2 ->
  exists Γ2' t', Γ2 = <[i:=t']>Γ2' /\ i ∉ dom Γ2' /\ upd_typ t t' /\ upd_typ_env Γ1 (delete i Γ2).
Proof.
  intros X1 X2.
  pose proof (upd_typ_env_same_dom _ _ X2) as Hd. rewrite dom_insert_L in Hd.
  assert (is_Some (Γ2 !! i)) as (x&Hx). eapply elem_of_dom. set_solver.
  exists (delete i Γ2), x. split_and !.
  { rewrite insert_delete_insert insert_id //. }
  { rewrite dom_delete_L. set_solver. }
  { specialize (X2 i). rewrite lookup_insert Hx in X2. done. }
  { intros j. specialize (X2 j).
    destruct_decide (decide (i=j)); subst.
    { rewrite lookup_delete not_elem_of_dom_1 //. }
    { rewrite lookup_insert_ne // in X2. rewrite lookup_delete_ne //. } }
Qed.

Lemma upd_typ_strong_env_insert i t s t' s' Γ m Γ' m' :
  upd_typ_strong t s t' s' ->
  upd_typ_strong_env Γ m Γ' m' ->
  upd_typ_strong_env (<[i:=t]> Γ) (<[i:=s]> m) (<[i:=t']> Γ') (<[i:=s']> m').
Proof.
  intros ? [X1 X2 X3 X4].
  constructor.
  1-3:rewrite dom_insert_L; set_solver.
  intros j ????. rewrite ! lookup_insert_case.
  case_decide. naive_solver. eauto.
Qed.

Lemma upd_typ_to_strong Γ1 Γ2 m1 vs :
  upd_typ_env Γ1 Γ2 ->
  interp_env Γ1 m1 vs -∗
  ⌜exists m2, upd_typ_strong_env Γ1 m1 Γ2 m2⌝.
Proof.
  iIntros (R) "X".
  iInduction vs as [] "IH" using map_ind forall (Γ1 Γ2 m1 R).
  { iDestruct "X" as "(%Hd&X)".
    iDestruct (big_sepM2_empty_l with "X") as "%X".
    apply map_zip_empty_inv in X; last done. destruct X as (->&->).
    apply upd_typ_env_same_dom in R. rewrite dom_empty_L in R. symmetry in R.
    apply dom_empty_inv_L in R. subst. iPureIntro. exists ∅.
    constructor; done. }
  { apply not_elem_of_dom in H1.
    iDestruct (interp_insert_val_inv with "X") as "(%&%&%&%&((%X1&%X2&%X3&%X4)&U&X))".
    done.
    subst.
    apply upd_typ_env_cons_l_inv in R; last done.
    destruct R as (?&?&->&?&?&?).
    iDestruct ("IH" with "[%//][$]") as "[%m2 %X]".
    rewrite delete_insert in X; last by eapply not_elem_of_dom.
    iDestruct (upd_typ_to_strong with "U") as "(%&%)". done.
    iPureIntro. exists (<[i:=s2]>m2). eauto using upd_typ_strong_env_insert. }
Qed.

Lemma upd_typ_strong_env_cons_l_inv i t Γ1 Γ2 s m1 m2:
  i ∉ dom Γ1 -> i ∉ dom m1 ->
  upd_typ_strong_env (<[i:=t]> Γ1) (<[i:=s]>m1) Γ2 m2 ->
  exists Γ2' t' m2' s', Γ2 = <[i:=t']>Γ2' /\ i ∉ dom Γ2' /\ m2 = <[i:=s']>m2' /\ i ∉ dom m2' /\ upd_typ_strong t s t' s' /\ upd_typ_strong_env Γ1 m1 Γ2' m2'.
Proof.
  intros X1 X2 [X3 X4 X5 X6].
  rewrite !dom_insert_L in X3,X4,X5.
  assert (is_Some (Γ2 !! i)) as (t'&Ht'). eapply elem_of_dom. set_solver.
  assert (is_Some (m2 !! i)) as (s'&Hs'). eapply elem_of_dom. set_solver.
  exists (delete i Γ2), t', (delete i m2), s'. split_and !.
  1,3: rewrite insert_delete_insert insert_id //.
  1,2:rewrite dom_delete_L; set_solver.
  { eapply X6; try done. all:rewrite lookup_insert //. }
  { constructor. set_solver. 1,2:rewrite dom_delete_L; set_solver.
    intros. apply lookup_delete_Some in H3,H4.
    eapply (X6 i0).
    1,2:rewrite lookup_insert_ne //; intros ->; apply elem_of_dom_2 in H1,H2; set_solver.
    1,2:naive_solver. }
Qed.

Lemma interp_env_upd_typ Γ1 Γ2 m1 m2 vs :
  upd_typ_strong_env Γ1 m1 Γ2 m2 ->
  interp_env Γ1 m1 vs ={⊤}=∗ interp_env Γ2 m2 vs.
Proof.
  iIntros (R) "X".
  iInduction vs as [] "IH" using map_ind forall (Γ1 Γ2 m1 m2 R).
  { iDestruct "X" as "(%Hd&X)".
    iDestruct (big_sepM2_empty_l with "X") as "%X".
    apply map_zip_empty_inv in X; last done. destruct X as (->&->).
    destruct R as [_ X1 X2 _].
    rewrite dom_empty_L in X1,X2. symmetry in X1,X2.
    apply dom_empty_inv_L in X1,X2. subst.
    iModIntro. iSplit; done. }
  { apply not_elem_of_dom in H1.
    iDestruct (interp_insert_val_inv with "X") as "(%&%&%&%&((%X1&%X2&%X3&%X4)&U&X))".
    done.
    subst.
    apply upd_typ_strong_env_cons_l_inv in R; try done.
    destruct R as (?&?&?&?&->&?&->&?&?&?).
    iMod ("IH" with "[% //][$]") as "?".
    iMod (interp_upd_typ with "U") as "?". done.
    iModIntro. rewrite interp_env_insert //.
    iFrame. }
Qed.

Lemma upd_typ_strong_preserves_similar_shape t s t' s' s0 :
  upd_typ_strong t s t' s' ->
  similar_shape s' s0 ->
  similar_shape s s0.
Proof.
  intros Hstrong.
  revert s0; induction Hstrong; subst; try done; intros ? X.
  { destruct s0; try done. inversion X. naive_solver. }
Qed.

Lemma upd_typ_strong_preserves_similar_shape_env Γ m Γ' m' m0 :
  upd_typ_strong_env Γ m Γ' m' ->
  similar_shape_env m' m0 ->
  similar_shape_env m m0.
Proof.
  intros [? ? ? X1] X2. intros i.
  specialize (X1 i). specialize (X2 i).
  destruct (m !! i) eqn:Hm', (m0 !! i); try done. simpl in *.
  apply elem_of_dom_2 in Hm'.
  assert (is_Some (m' !! i)) as (?&X).
  { apply elem_of_dom. set_solver. }
  rewrite X in X2.
  assert (is_Some (Γ !! i)) as (?&R1).
  { apply elem_of_dom. set_solver. }
  assert (is_Some (Γ' !! i)) as (?&R2).
  { apply elem_of_dom. set_solver. }
  specialize (X1 _ _ _ _ R1 (eq_refl _) R2 X). simpl in *.
  eauto using upd_typ_strong_preserves_similar_shape.
Qed.


Lemma log_typed_conseq Γ1 Γ1' e τ Γ2 :
  upd_typ_env Γ1 Γ1' ->
  log_typed Γ1' e τ Γ2 -∗
  log_typed Γ1 e τ Γ2.
Proof.
  iIntros (X1) "#X !>". iIntros (m vs).

  iApply triple_use_pure_pre.
  { iApply upd_typ_to_strong. done. }
  iIntros ((m2&Hstrong)).

  iApply triple_conseq_pre.
  { iIntros. iApply (interp_env_upd_typ with "[$]"). done. }
  iApply triple_fupd_pre.

  iApply triple_conseq_post; last iApply "X".
  iIntros (? (?&?)) "((%&%)&?&?)". iFrame.
  iPureIntro. split. by eapply upd_typ_env_preserves_similar. by eapply upd_typ_strong_preserves_similar_shape_env.
Qed.

Local Lemma binsert_alt {A} x (v:A) m :
  bmap [x] [v] ∪ bdelete x m = binsert x v m.
Proof.
  apply map_eq. intros y.
  rewrite !lookup_union /bmap /extend. simpl.
  destruct x; simpl.
  { rewrite lookup_empty left_id //. }
  destruct_decide (decide (s=y)); subst.
  { rewrite !lookup_insert lookup_delete right_id //. }
  { rewrite !lookup_insert_ne // lookup_delete_ne // lookup_empty left_id //. }
Qed.

Lemma valid_binsert {V:cmra} k v (m:gmap _ V) :
  ✓ m ->
  ✓ v ->
  ✓ (binsert k v m).
Proof.
  intros X1 X2. destruct k; first done. by eapply valid_insert.
Qed.

Lemma senv_bdelete {A B} x (f:A -> B -> Prop) (m1:gmap _ A) (m2:gmap _ B):
  senv f m1 m2 ->
  senv f (bdelete x m1) (bdelete x m2).
Proof.
  destruct x; first done.
  intros X i. specialize (X i).
  destruct_decide (decide (i=s)); subst.
  { rewrite !lookup_delete //. }
  { rewrite !lookup_delete_ne //. }
Qed.

Lemma senv_add_bdelete_l {A B} x (f:A -> B -> Prop) (m1:gmap _ A) (m2:gmap _ B) :
  senv f (bdelete x m1) (bdelete x m2) ->
  senv f m1 (bdelete x m2).
Proof. destruct x; try done. apply senv_add_delete_l. Qed.

Lemma restrict_binsert {V} g x v (m:gmap _ V) :
  binder_set x ## dom m ->
  restrict g (binsert x v m) = if (decide (binder_set x ⊆ g)) then binsert x v (restrict g m) else restrict g m.
Proof.
  intros. destruct x; simpl.
  { rewrite decide_True //. }
  { rewrite restrict_insert; last set_solver.
    case_decide. rewrite decide_True //; set_solver.
    rewrite decide_False //; set_solver. }
Qed.

Lemma bdelete_restrict {V} x g (m:gmap _ V):
  bdelete x (restrict g m) = restrict (g ∖ binder_set x) m.
Proof.
  destruct x; simpl.
  { rewrite difference_empty_L //. }
  apply delete_restrict.
Qed.

Lemma log_typed_let Γ Γ1 Γ2 x e1 e2 τ τ' :
  fv e2 ⊆ binder_set x ∪ dom Γ1 ->
  log_typed Γ e1 τ' Γ1 -∗
  log_typed (binsert x τ' Γ1) e2 τ Γ2 -∗
  log_typed Γ (Let x e1 e2) τ (bdelete x Γ2).
Proof.
  iIntros (?) "#E1 #E2 !>". iIntros (m vs). simpl.

  iApply (triple_bind (CtxLet _ _) with "[E1]").
  { iApply "E1". }

  iClear "E1". iIntros (v (s,m')). simpl.

  iApply triple_let_val.

  iApply (triple_use_pure_pre (similar_env Γ Γ1 /\ similar_shape_env m m' /\ ✓τ' /\ dom Γ1 = dom vs ∩ dom Γ1 /\ dom m' = dom Γ1)).
  { iIntros "(%&?&X)".
    iDestruct (interp_valid with "[$]") as "%".
    iDestruct (interp_env_dom_12 with "X") as "%".
    iDestruct (interp_env_dom_13 with "X") as "%Hd'".
    iPureIntro. rewrite dom_restrict in Hd'. naive_solver. }
  iIntros "(%&%&%&%)".

  rewrite {2}(restrict_split (dom Γ1) vs).
  rewrite bdelete_union map_union_comm.
  2:{ apply map_disjoint_dom. rewrite !dom_bdelete !dom_restrict. set_solver. }
  rewrite msubsts_union.
  rewrite (msubsts_not_in_fv _ e2).
  2:{ rewrite dom_bdelete dom_restrict. set_solver. }

  rewrite subst_msubsts' -msubsts_union map_union_comm.
  2:{ apply map_disjoint_dom. rewrite dom_bmap // dom_bdelete. set_solver. }
  rewrite binsert_alt.

  iApply (triple_shift (fun '(s,m) => (s,bdelete x m))).
  iApply triple_conseq; last iApply "E2".
  { iIntros "(_&?&?)". iApply binsert_interp_env. iFrame. }
  { intros ? (s''&m'').
    iIntros "((%R2&%R3)&?&X)". iFrame.
    iDestruct (interp_env_dom_12 with "X") as "%".
    iDestruct (interp_env_dom_13 with "X") as "%Hd".
    rewrite dom_restrict dom_binsert dom_restrict in Hd.
    iSplitR.
    { iPureIntro. split.
      { apply (senv_bdelete x) in R2.
        rewrite bdelete_binsert in R2.
        eapply senv_trans; last done. apply _.
        { rewrite !dom_bdelete. set_solver. }
        apply senv_add_bdelete_l.
        by eapply senv_bdelete. }
      { apply (senv_bdelete x) in R3.
        rewrite bdelete_binsert in R3.
        eapply senv_trans. apply _. shelve. done.
        by eapply senv_add_bdelete_l. Unshelve. rewrite dom_bdelete. set_solver. } }
    { iDestruct (interp_env_bdelete x with "X") as "?".
      replace (bdelete x (restrict (dom Γ2) (binsert x v (restrict (dom Γ1) vs)))) with (restrict (dom (bdelete x Γ2)) vs). done.
      rewrite bdelete_restrict binsert_bdelete.
      rewrite restrict_binsert.
      2:{ rewrite dom_bdelete. set_solver. }
      destruct x.
      { rewrite decide_True; last set_solver. simpl. rewrite restrict_restrict.
        f_equal. set_solver. }
      rewrite decide_False; last set_solver. simpl.
      rewrite delete_restrict restrict_restrict dom_delete_L.
      f_equal. set_solver. } }
Qed.

Lemma map_zip_extend {V1 V2} xs ys zs (m1:gmap _ V1) (m2:gmap _ V2) :
  length xs = length ys -> length xs = length zs ->
  map_zip (extend xs ys m1) (extend xs zs m2) = extend xs (zip ys zs) (map_zip m1 m2).
Proof.
  revert ys zs m1 m2. induction xs; intros [] [] m1 m2; simpl; try lia.
  { done. }
  { intros. rewrite !extend_cons IHxs. 2,3:lia.
    f_equal. rewrite map_zip_binsert //. }
Qed.

Lemma big_sepM2_extend {A B} (Φ : A → B → vProp Σ) m1 m2 xs ys zs :
  length xs = length ys ->
  ([∗ map] y1;y2 ∈ m1;m2, Φ y1 y2) -∗
  ([∗ list] y1;y2 ∈ ys;zs, Φ y1 y2) -∗
  [∗ map] y1;y2 ∈ (extend xs ys m1);(extend xs zs m2), Φ y1 y2.
Proof.
  iIntros (E1) "X1 X2".
  iDestruct (big_sepL2_length with "X2") as "%E2".
  iInduction xs as [] "IH" forall (ys zs m1 m2 E1 E2).
  { destruct ys,zs; simpl in *; try done. }
  destruct ys; simpl in E1; try done.
  destruct zs; simpl in E2; try done.
  rewrite big_sepL2_cons. iDestruct "X2" as "(?&X2)".
  rewrite !extend_cons. iApply ("IH" with "[%][%][-X2]"). 1,2:lia.
  { iApply big_sepM2_binsert. iFrame. }
  { iFrame. }
Qed.

Lemma log_typed_abs Γ f arg code τs τ :
  Γ = Γ ⋅ Γ -> (* persistence of the context *)
  log_typed (extend [f;arg] [TArrow τs τ;τs] Γ) code τ ∅ -∗ (* empty return because the modifs of the env are visible only at call time *)
  log_typed Γ (Code f arg code) (TArrow τs τ) ∅.
Proof.
  iIntros (?) "#E !>".
  iIntros (m vs). cbn [msubsts].

  iMod (saved_pred_alloc (interp_env Γ m vs) DfracDiscarded) as "[%γ #Hsaved]".
  by constructor.

  iApply triple_code.
  iApply triple_conseq_pre.
  { iApply interp_env_dup_intuitionistically. done. }

  iApply triple_val.
  iExists (SArrow γ, ∅); simpl.
  iSplitL; iIntros "Hi".
  all:iApply monPred_at_sep; rewrite !monPred_at_pure.
  all:iSplitR; first (iPureIntro; split; apply similar_env_empty_r).
  all:iApply monPred_at_sep; iSplitL; last (iClear "E"; rewrite /interp_env; monPred.unseal; rewrite map_zip_empty !dom_empty_L restrict_empty' big_sepM2_empty monPred_at_emp //).
simpl.
  all:unfold interp_arrow; iApply monPred_at_sep; rewrite monPred_at_pure; iSplitR; first done; rewrite monPred_at_exist.
  all:iExists _; iApply monPred_at_sep; rewrite monPred_at_embed; simpl; iFrame "#∗".
  all:iApply monPred_at_sep; rewrite !monPred_at_intuitionistically; simpl; iDestruct "Hi" as "#Hi"; do 2 iFrame "#∗".
  iClear "Hi".

  iLöb as "IH".
  iModIntro. iIntros.

  iApply (triple_conseq_pre (▷ (interp_env Γ m vs ∗ interp τs s v))).
  { iIntros "(?&?)". iFrame. }

  iApply triple_call. done. iModIntro.
  rewrite (substs_msubsts_bdeletes [_;_] [_;_]). 2:done.
  2:{ rewrite (dom_bdeletes [_;_]) binders_set_cons. set_solver. }

  iApply (triple_give_back with "IH").
  iApply (triple_give_back_embed with "Hsaved").

  iApply (triple_shift (fun '(x,_) => x)).
  iApply triple_conseq. 3:iExact "E".
  2:{ simpl. intros ? (?,?). iIntros "(?&?&?)". iFrame. }

  iIntros "(#X1&#X2&X&X4)".
  iDestruct (interp_env_dup_intuitionistically with "X") as "#X'".
  done.
  iClear "X".

  rewrite (binserts_bdeletes_same (f::_) (_::_)); last (simpl; lia).

  iApply (interp_env_binsert with "[$]").
  iApply (interp_env_binsert with "[] [$]").
  Unshelve. 2:exact (SArrow γ). simpl. iFrame "# ∗". iModIntro. done.
Qed.

Lemma log_typed_app Γ Γ' Γ'' e1 e2 τs τ :
  fv e1 ⊆ dom Γ' ->
  log_typed Γ e2 τs Γ' -∗
  log_typed Γ' e1 (TArrow τs τ) Γ'' -∗
  log_typed Γ (Call e1 e2) τ Γ''.
Proof.
  iIntros (?) "#X1 #X2 !>". iIntros. cbn [msubsts].

  iApply (triple_bind (CtxCall1 _) with "X1").
  iClear "X1". iIntros (v (s,m')).
  rewrite assoc.

  rewrite {2}(restrict_split (dom Γ') vs).
  rewrite map_union_comm.
  2:{ apply map_disjoint_dom. rewrite !dom_restrict. set_solver. }
  rewrite msubsts_union.
  rewrite (msubsts_not_in_fv _ e1).
  2:{ rewrite dom_restrict. set_solver. }

  iApply (triple_bind (CtxCall2 _)).
  { iApply triple_use_pure_pre.
    { iIntros "(?&?)". iApply (interp_env_dom_12 with "[$]"). }
    iIntros.

    iApply triple_frame_wand.
    iApply (triple_conseq_post with "X2").
    iIntros (? (?,?)). iIntros "((%&%)&?&?) ((%&%)&?)".
    rewrite restrict_restrict.
    iDestruct (interp_env_dom_12 with "[$]") as "%".
    iDestruct (interp_env_dom_13 with "[$]") as "%Hd".
    rewrite dom_restrict in Hd.
    replace (dom Γ'' ∩ dom Γ') with (dom Γ'') by set_solver.
    assert (similar_env Γ Γ'').
    { eapply senv_trans. apply _. 2,3:done. set_solver. }
    assert (similar_shape_env m g).
    { eapply senv_trans. apply _. 2,3:done. set_solver. }
    Unshelve.
    2:exact (fun v0 '(s0,g) => ⌜similar_env Γ Γ'' /\ similar_shape_env m g⌝ ∗ interp (TArrow τs τ) s0 v0 ∗ interp_env Γ'' g (restrict (dom Γ'') vs) ∗ interp τs s v )%I.
    by iFrame. }
  iIntros (? (?,?)). simpl. iClear "X2".

  iApply (triple_use_pure_pre (similar_env Γ Γ'' ∧ similar_shape_env m g /\ exists γ, s0=SArrow γ)).
  { iIntros "((%&%)&?&_)". destruct s0; try done. eauto. }
  iIntros ((?&?&γ&->)).

  iApply triple_conseq_pre.
  { iIntros "(_&?&?&?)". iStopProof. reflexivity. }


  (* breaking abstraction here, RIP *)
  rewrite /interp_arrow triple_eq.
  iIntros (C ks F Q1 Q2) "HP HPOST". monPred.unseal.
  iDestruct "HP" as "((_&[%P #(HP&X)])&?&?)".
  rewrite monPred_at_intuitionistically.
  iDestruct "X" as "(#HPtrue&#Htriple)".

  iSpecialize ("Htriple" $! v s). rewrite triple_eq. simpl.
  iSpecialize ("Htriple" $! C ks (interp_env Γ'' g (restrict (dom Γ'') vs) false ∗ F)%I Q1 Q2).
  iSpecialize ("Htriple" with "[$]").

  iApply dwpk_conseq_r; last first.
  { iApply "Htriple". iIntros.
    iSpecialize ("HPOST" $! v1 (x,g)). simpl.
    iApply dwpk_conseq_r.
    2:{ iApply "HPOST". by iFrame. }
    { iIntros (?) "(?&?&?)". by iFrame. } }
  { iIntros (?) "(((_&[%P' (HP'&X&_)])&?&?)&?)". iFrame.
    rewrite monPred_at_intuitionistically. simpl.
    iDestruct "X" as "#X".
    iDestruct (saved_pred_agree _ _ _ _ _ false with "HP HP'") as "Equiv".
    iModIntro. iRewrite "Equiv". done. }
Qed.

Lemma interp_nomix t1 s1 t2 s2 v :
  interp t1 s1 v -∗ interp t2 s2 v -∗ ⌜nomix t1 t2⌝.
Proof.
  iIntros "X1 X2".
  iInduction t1 as [] "IH" forall (s1 t2 s2 v).
  all:destruct t2; try done.
  { destruct s1; try done. destruct s2; try done. simpl.
    iDestruct "X1" as "(%&%&->&?&?)".
    iDestruct "X2" as "(%&%&%Eq&?&?)". inversion Eq. subst.
    iDestruct ("IH" with "[$][$]") as "%".
    iDestruct ("IH1" with "[$][$]") as "%".
    done. }
  { destruct s1; try done. destruct s2; try done. simpl.
    iDestruct "X1" as "(%&->&?)". iDestruct "X2" as "(%&%E&?)".
    inversion E. subst. iApply (is_priority_confront with "[$][$]"). }
  { destruct s1; try done. destruct s2; try done. simpl.
    iDestruct "X1" as "(%&->&?)". iDestruct "X2" as "(%&%E&?)".
    inversion E. subst.  iApply (is_priority_confront with "[$][$]"). }
Qed.

Lemma interp_env_nomix Γ1 m1 Γ2 m2 vs :
  interp_env Γ1 m1 (restrict (dom Γ1) vs) -∗
  interp_env Γ2 m2 (restrict (dom Γ2) vs) -∗
  ⌜nomix_env Γ1 Γ2⌝.
Proof.
  iIntros "X1 X2". iIntros (i).
  destruct (Γ1 !! i) eqn:E1 ; destruct (Γ2 !! i) eqn:E2; try done.
  rewrite -{1}(insert_id _ _ _ E1) -{1}(insert_id _ _ _ E2).
  iDestruct (interp_env_dom_12 with "X1") as "%Hd11".
  iDestruct (interp_env_dom_13 with "X1") as "%Hd12".
  iDestruct (interp_env_dom_12 with "X2") as "%Hd21".
  iDestruct (interp_env_dom_13 with "X2") as "%Hd22".
  rewrite !dom_insert_L in Hd11, Hd12, Hd21, Hd22.
  assert (is_Some (m1 !! i)) as (x1&Hx1). eapply elem_of_dom. set_solver.
  assert (is_Some (m2 !! i)) as (x2&Hx2). eapply elem_of_dom. set_solver.
  assert (is_Some (restrict (dom Γ1) vs !! i)) as (v&Hv). eapply elem_of_dom. set_solver.
  assert (restrict (dom Γ2) vs !! i = Some v) as Hv'.
  { rewrite !dom_restrict in Hd12 Hd22. rewrite lookup_restrict.
    rewrite decide_True; last set_solver.
    rewrite lookup_restrict in Hv. rewrite decide_True in Hv; set_solver. }
  rewrite -(insert_delete_insert Γ1) -(insert_delete_insert Γ2).
  rewrite (insert_id_delete _ _ _ Hx1) (insert_id_delete _ _ _ Hx2).
  rewrite (insert_id_delete _ _ _ Hv) (insert_id_delete _ _ _ Hv').
  rewrite !interp_env_insert. 2-7:rewrite dom_delete_L; set_solver.
  iDestruct "X1" as "(X1&_)". iDestruct "X2" as "(X2&_)".
  iApply (interp_nomix with "X1 X2").
Qed.

Lemma interp_nomix_shape t1 s1 t2 s2 v :
  interp t1 s1 v -∗ interp t2 s2 v -∗ ⌜nomix_shape s1 s2⌝.
Proof.
  iIntros "X1 X2".
  iInduction t1 as [] "IH" forall (s1 t2 s2 v).
  all:destruct s1; try done; simpl.
  { iDestruct "X1" as "(%&%&->&?&?)".
    destruct s2; try done. destruct t2; try done; simpl.
    iDestruct "X2" as "(%&%&%Eq&?&?)". inversion Eq. subst.
    iDestruct ("IH" with "[$][$]") as "%".
    iDestruct ("IH1" with "[$][$]") as "%". eauto. }
  { iDestruct "X1" as "[% (->&?&?)]".
    destruct s2; try done. destruct t2; try done; simpl.
    iDestruct "X2" as "[% (%E&?&?)]". inversion E. subst.
    iDestruct (pointsto_confront with "[$][$]") as "%".
    by vm_compute. congruence. }
  { iDestruct "X1" as "[% (->&?)]".
    destruct s2; try done.
    { destruct t2; try done; simpl.
      iDestruct "X2" as "[% (%E&?)]". inversion E. subst.
      iDestruct (is_priority_is_agree with "[$][$]") as "%". done. }
    { destruct t2; try done; simpl.
      iDestruct "X2" as "[% (%E&?)]". inversion E. subst.
      iApply (is_priority_confront with "[$][$]"). } }
  { destruct s2; try done.
    destruct t2; try done; simpl.
    iDestruct "X1" as "[% (->&?)]".
    iDestruct "X2" as "[% (%E&?)]". inversion E. subst.
    iApply (is_priority_confront with "[$][$]"). }
  { destruct s2; try done. destruct t2; try done. simpl.
    iDestruct "X1" as "(%&->&X1&_)".
    iDestruct "X2" as "(%&%E&X2&_)". inversion E. subst.
    iApply (pointsto_agree with "X1 X2"). }
Qed.

Lemma interp_env_nomix_shape Γ1 m1 Γ2 m2 vs :
  interp_env Γ1 m1 (restrict (dom Γ1) vs) -∗
  interp_env Γ2 m2 (restrict (dom Γ2) vs) -∗
  ⌜nomix_shape_env m1 m2⌝.
Proof.
  iIntros "X1 X2". iIntros (i).
  destruct (m1 !! i) eqn:E1 ; destruct (m2 !! i) eqn:E2; try done.
  rewrite -{1}(insert_id _ _ _ E1) -{1}(insert_id _ _ _ E2).
  iDestruct (interp_env_dom_12 with "X1") as "%Hd11".
  iDestruct (interp_env_dom_13 with "X1") as "%Hd12".
  iDestruct (interp_env_dom_12 with "X2") as "%Hd21".
  iDestruct (interp_env_dom_13 with "X2") as "%Hd22".
  rewrite !dom_insert_L in Hd11, Hd12, Hd21, Hd22.
  assert (is_Some (Γ1 !! i)) as (x1&Hx1). eapply elem_of_dom. set_solver.
  assert (is_Some (Γ2 !! i)) as (x2&Hx2). eapply elem_of_dom. set_solver.
  assert (is_Some (restrict (dom Γ1) vs !! i)) as (v&Hv). eapply elem_of_dom. set_solver.
  assert (restrict (dom Γ2) vs !! i = Some v) as Hv'.
  { rewrite !dom_restrict in Hd12 Hd22. rewrite lookup_restrict.
    rewrite decide_True; last set_solver.
    rewrite lookup_restrict in Hv. rewrite decide_True in Hv; set_solver. }
  rewrite -{1}(insert_delete_insert m1) -{1}(insert_delete_insert m2).
  rewrite {1}(insert_id_delete _ _ _ Hx1) {1}(insert_id_delete _ _ _ Hx2).
  rewrite (insert_id_delete _ _ _ Hv) (insert_id_delete _ _ _ Hv').
  rewrite !interp_env_insert. 2-7:rewrite dom_delete_L; set_solver.
  iDestruct "X1" as "(X1&_)". iDestruct "X2" as "(X2&_)". simpl.
  iApply (interp_nomix_shape with "X1 X2").
Qed.

Lemma log_typed_par Γ Γ1 Γ2 Γ1' Γ2' e1 e2 τ1 τ2 :
  Γ = Γ1 ⋅ Γ2 ->
  fv e1 ⊆ dom Γ1 -> fv e2 ⊆ dom Γ2 -> (* should be given by the syntactical typing judgment *)
  log_typed Γ1 e1 τ1 Γ1' -∗
  log_typed Γ2 e2 τ2 Γ2' -∗
  log_typed Γ (Par e1 e2) (TProd τ1 τ2) (Γ1' ⋅ Γ2').
Proof.
  iIntros (-> X1 X2) "#E1 #E2". iIntros (m vs) "!>". simpl.

  iApply (triple_use_pure_pre (exists m1 m2, m = m1 ⋅ m2 ∧ dom m1 = dom Γ1 /\ dom m2 = dom Γ2)).
  { iIntros "X". iDestruct (interp_sepM2_op_inv_l with "X") as "(%&%&%&%&%&_)".
    eauto 10. }
  iIntros ((m1&m2&->&?&?)).

  iApply (triple_use_pure_pre (✓ (Γ1 ⋅ Γ2) /\ ✓ (m1 ⋅ m2))).
  { iIntros.
    iDestruct (interp_env_valid with "[$]") as "%".
    iDestruct (interp_env_shape_valid with "[$]") as "%". done. }
  iIntros ((?&?)).

  iApply triple_conseq_pre.
  { by apply interp_env_split_1. }

  iApply (triple_use_pure_pre (nomix_shape_env m1 m2)).
  { iIntros "(X1&X2)". iApply (interp_env_nomix_shape with "X1 X2"). }
  iIntros.

  iSpecialize ("E1" $! m1). iSpecialize ("E2" $! m2).

  iApply (triple_shift (fun '((x,y) : (shape * gmap string shape) * (shape * gmap string shape )) => (SProd x.1 y.1, x.2 ⋅ y.2 ))).

  rewrite {3}(restrict_split (dom Γ1) vs).
  rewrite (map_union_comm (restrict (dom Γ1) _)).
  2:{ apply map_disjoint_dom. rewrite !dom_restrict. set_solver. }
  rewrite {6}(restrict_split (dom Γ2) vs).
  rewrite (map_union_comm (restrict (dom Γ2) _)).
  2:{ apply map_disjoint_dom. rewrite !dom_restrict. set_solver. }

  rewrite !msubsts_union.
  rewrite (msubsts_not_in_fv _ e1).
  2:{ rewrite dom_restrict. set_solver. }
  rewrite (msubsts_not_in_fv _ e2).
  2:{ rewrite dom_restrict. set_solver. }

  iApply triple_conseq_post.
  2:iApply (triple_par with "E1 E2").
  iIntros (? ((?&m1'),(?&m2'))) "[% [% (->&((%R2&%R3)&?&X1)&((%R4&%R5)&?&X2))]]".

  iDestruct (interp_env_dom_12 with "X1") as "%".
  iDestruct (interp_env_dom_12 with "X2") as "%".
  iDestruct (interp_env_dom_13 with "X1") as "%T1".
  iDestruct (interp_env_dom_13 with "X2") as "%T2".

  rewrite !restrict_restrict !dom_restrict in T1,T2.

  assert (dom Γ1' ⊆ dom Γ1) by set_solver.
  assert (dom Γ2' ⊆ dom Γ2) by set_solver.

  iDestruct (interp_env_valid with "X1") as "%Hv1".
  iDestruct (interp_env_valid with "X2") as "%Hv2".
  rewrite !restrict_restrict.
  replace (dom Γ1' ∩ dom Γ1) with (dom Γ1') by set_solver.
  replace (dom Γ2' ∩ dom Γ2) with (dom Γ2') by set_solver.

  iDestruct (interp_env_nomix with "X1 X2") as "%".
  iDestruct (interp_env_nomix_shape with "X1 X2") as "%".

  assert (✓ (Γ1' ⋅ Γ2')) by eauto using valid_op_similar_env.

  simpl. iFrame. iSplitR.
  { iPureIntro. split. eauto using similar_env_op.
    eapply similar_shape_env_op; try done.
    1,2:set_solver. }
  iSplitR; first done.
  iApply interp_env_split_2.
  { eauto using valid_op_similar_env. }
  { eapply valid_op_similar_shape_env; try done; set_solver. }
  { rewrite dom_restrict !dom_op. set_solver. }
  { rewrite !restrict_restrict.
    replace (dom Γ1' ∩ dom (Γ1' ⋅ Γ2')) with (dom Γ1').
    2:{ rewrite dom_op. set_solver. }
    replace (dom Γ2' ∩ dom (Γ1' ⋅ Γ2')) with (dom Γ2').
    2:{ rewrite dom_op. set_solver. }
    iFrame. }
Qed.

Lemma log_typed_alloc Γ Γ' e τ :
  log_typed Γ e τ Γ' -∗
  log_typed Γ (ref e) (TRef τ) Γ'.
Proof.
  iIntros "#X". iIntros (m vs) "!>". simpl.
  iApply (triple_bind (CtxCall1 _)). iApply "X".
  iIntros (v (s,m')). simpl.
  iApply (triple_resolve (SRef v s,m')).
  iApply (triple_conseq_pre ((⌜similar_env Γ Γ' ∧ similar_shape_env m m'⌝ ∗ interp τ s v ∗ interp_env Γ' m' (restrict (dom Γ') vs)) ∗ True)%I).
  { rewrite right_id //. }
  iApply triple_frame_wand.
  iApply triple_conseq_post.
  2:iApply triple_ref. simpl.
  iIntros (? _) "[% (->&?&?)] (?&?&?)".
  by iFrame.
Qed.

(* ANF here *)
Lemma log_typed_load (x:string) τ :
  ⊢ log_typed {[x:=TRef τ]} (Load x 0) τ {[x:=TRef TEmpty]}.
Proof.
  iIntros (m vs) "!>". simpl.

  iApply (triple_use_pure_pre (exists (v v':val) s, m = {[x:=(SRef v' s)]} /\ vs = {[x:=v]})).
  { iIntros "(%Hd&X)". rewrite dom_insert_L dom_empty_L right_id_L in Hd.
    apply dom_singleton_inv_L in Hd. destruct Hd as (?&?). subst.
    rewrite map_zip_singleton.
    iDestruct (big_sepM2_singleton_inv_l with "X") as "[%x2 (->&?)]".
    simpl. destruct x0; try done. eauto 10. }
  iIntros ((v&v'&s&->&->)).

  rewrite lookup_insert.
  rewrite interp_env_singleton. simpl.

  unfold interp_ref.

  iApply (triple_use_pure_pre (exists (l:loc), v = l)).
  { iIntros "[% (->&_)]". eauto. }
  iIntros "[% ->]".

  iApply (triple_conseq_pre (interp τ s v' ∗ pointsto l (DfracOwn 1) [v'])).
  { iIntros "[% (%Eq&?&?)]". inversion Eq. subst. iFrame. }

  iApply triple_frame_wand.
  iApply (triple_resolve (s,{[x:=SRef v' SNone]})).
  iApply triple_end.
  iApply triple_load. simpl.
  iIntros (??). iApply triple_val'.

  Unshelve. 2:apply _.

  iIntros "((%X&_&%E)&?) ?". inversion X. subst. simpl in E.
  inversion E. subst. clear E X.
  iDestruct (interp_shape_valid with "[$]") as "%".
  iFrame.
  iSplitR.
  { iPureIntro. split.
    { intros i; rewrite !lookup_insert_case. case_decide; done. }
    { intros i; rewrite !lookup_insert_case. case_decide; done. } }
  { rewrite restrict_singleton.
    rewrite dom_singleton_L decide_True; last set_solver.
    iApply interp_env_singleton. simpl. iExists _. by iFrame. }
Qed.

Lemma similar_shape_insert_ref_l m x v s v' s' m' :
  similar_shape_env m (<[x:=SRef v s]> m') ->
  similar_shape_env m (<[x:=SRef v' s']> m').
Proof.
  intros X i. specialize (X i).
  destruct (m !! i).
  2:{ by destruct (<[x:=SRef v' s']> m' !! i). }
  rewrite lookup_insert_case. rewrite lookup_insert_case in X.
  case_decide; subst; last done.
  simpl in *. by destruct s0.
Qed.

Lemma log_typed_store Γ Γ' e (x:string) τ :
  dom Γ' ⊆ dom Γ -> (* I should be able to remove that *)
  Γ' !! x = Some (TRef TEmpty) ->
  log_typed Γ e τ Γ' -∗
  log_typed Γ (Store x 0 e) TUnit (insert x (TRef τ) Γ').
Proof.
  iIntros (? Hx) "#X".
  iIntros (m vs) "!>". simpl.

  iApply (triple_use_pure_pre (dom Γ = dom vs)).
  { iApply interp_env_dom_13. }

  iIntros "%".
  assert (x ∈ dom Γ') by by eapply elem_of_dom.
  assert (is_Some (vs !! x)) as (v&Hv). apply elem_of_dom. set_solver.
  rewrite Hv.

  iApply (triple_bind (CtxStore1 _ _)).
  { iApply "X". }
  iIntros (w (s',m')).

  iApply (triple_use_pure_pre (exists (l:loc) (v':val) s, m' !! x = Some (SRef v' s) /\ v =l)).
  { iIntros "(%&_&X)".
    iDestruct (interp_env_dom_12 with "X") as "%Hd1".
    iDestruct (interp_env_dom_13 with "X") as "%Hd2".
    assert (is_Some (m' !! x)) as (?&Hx'). eapply elem_of_dom. set_solver.
    assert (restrict (dom Γ') vs !! x = Some v) as Hx''.
    { rewrite lookup_restrict. rewrite decide_True //. }
    rewrite {1}(insert_id_delete _ _ _ Hx) (insert_id_delete _ _ _ Hx') (insert_id_delete _ _ _ Hx'').
    rewrite interp_env_insert //.
    2-4:rewrite dom_delete_L; set_solver.
    iDestruct "X" as "(X&?)". simpl.
    destruct x0; try done. subst. iDestruct "X" as "(%&->&_)".
    iPureIntro. eexists _,_,_. rewrite !lookup_insert. eauto. }
  iIntros "(%&%&%&%Hmx&->)".

  assert (restrict (dom Γ') vs !! x = Some (VLoc l)) as Hvx.
    { rewrite lookup_restrict. rewrite decide_True //. }

  rewrite {5}(insert_id_delete _ _ _ Hx) (insert_id_delete _ _ _ Hmx) (insert_id_delete _ _ _ Hvx).

  rewrite interp_env_insert.
  2-4:rewrite dom_delete_L; set_solver.
  simpl.

  iClear "X".
  iApply (triple_conseq_pre (((⌜similar_env Γ Γ' /\ similar_shape_env m (<[x:=SRef v' s]> (delete x m'))⌝ ∗ interp τ s' w ∗  interp_env (delete x Γ') (delete x m') (delete x (restrict (dom Γ') vs))) ∗ interp_ref v' s (fun s => match s with SNone => fun _ => True | _ => fun _ => False end%I) l))).
  { iIntros "(?&?&?&?)". iFrame. }

  iApply triple_frame_wand.

  iApply (triple_conseq_pre (pointsto l (DfracOwn 1) [v'])).
  { iIntros "[% (%Eq&?&?)]". inversion Eq. subst. iFrame. }

  iApply (triple_resolve (SNone, <[x:=SRef w s']>m')).
  iApply triple_end.
  iApply triple_store.
  iIntros (??). iApply triple_val'.
  iIntros "((%Eq&->&_)&?) ((%&%)&?&?)". inversion Eq. subst.

  iSplitR.
  { iPureIntro.
    assert (is_Some (Γ !! x)) as (x0&Hx0).
    { apply elem_of_dom. set_solver. }
    rewrite -(insert_id _ _ _ Hx0) -(insert_id _ _ _ Hmx).
    split.
    { apply similar_env_insert; last done.
      specialize (H4 x). rewrite Hx0 Hx in H4.
      by destruct x0. }
    { rewrite insert_insert. rewrite insert_delete_insert in H5.
      by eapply similar_shape_insert_ref_l. } }
  iSplitR; first done.
  rewrite dom_insert_L.
  rewrite -(insert_delete_insert Γ') -(insert_delete_insert m').
  rewrite (insert_id_delete x (VLoc l) (restrict ({[x]} ∪ dom Γ') vs)).
  2:{ rewrite lookup_restrict. rewrite decide_True; last set_solver. done. }
  rewrite interp_env_insert. iFrame.
  iSplitR; first done.
  2-4:rewrite dom_delete_L; set_solver.
  rewrite !delete_restrict.
  replace (({[x]} ∪ dom Γ') ∖ {[x]}) with (dom Γ' ∖ {[x]}) by set_solver.
  iFrame.
Qed.

Lemma nomix_shape_env_sym m1 m2 :
  nomix_shape_env m1 m2 → nomix_shape_env m2 m1.
Proof.
  intros X i. specialize (X i).
  destruct (m1 !! i), (m2 !! i); try done.
  by apply nomix_shape_sym.
Qed.

Lemma similar_shape_env_sym m1 m2 :
  similar_shape_env m1 m2 → similar_shape_env m2 m1.
Proof.
  intros X i. specialize (X i).
  destruct (m1 !! i), (m2 !! i); try done.
  by apply similar_shape_sym.
Qed.

Lemma log_typed_frame Γ1 Γ2 e τ Γ2' :
  fv e ⊆ dom Γ2 ->
  log_typed Γ2 e τ Γ2' -∗
  log_typed (Γ1 ⋅ Γ2) e τ (Γ1 ⋅ Γ2').
Proof.
  iIntros (Hfv) "#X".
  iIntros (m vs) "!>".

  iApply (triple_use_pure_pre (exists m1 m2, m = m1 ⋅ m2 ∧ dom m1 = dom Γ1 /\ dom m2 = dom Γ2)) .
  { iIntros "X". iDestruct (interp_sepM2_op_inv_l with "X") as "(%&%&%&%&%&_)".
    eauto 10. }
  iIntros ((m1&m2&->&?&?)).

  iApply (triple_use_pure_pre (✓(Γ1 ⋅ Γ2) /\ ✓(m1 ⋅ m2))) .
  { iIntros.
    iDestruct (interp_env_valid with "[$]") as "%".
    iDestruct (interp_env_shape_valid with "[$]") as "%".
    eauto. }
  iIntros ((?&?)).

  iApply triple_conseq_pre.
  { by apply interp_env_split_1. }

  iApply (triple_use_pure_pre (dom Γ1 = dom Γ1 ∩ dom vs /\ dom Γ2 = dom Γ2 ∩ dom vs /\ nomix_shape_env m1 m2)).
  { iIntros "(X1&X2)".
    iDestruct (interp_env_dom_13 with "X1") as "%E1".
    iDestruct (interp_env_dom_13 with "X2") as "%E2".
    iDestruct (interp_env_nomix_shape with "X1 X2") as "%".
    rewrite !dom_restrict in E1,E2. iPureIntro. set_solver. }
  iIntros "(%&%&%)".

  rewrite {3}(restrict_split (dom Γ2) vs).
  rewrite map_union_comm.
  2:{ apply map_disjoint_dom. rewrite !dom_restrict. set_solver. }
  rewrite msubsts_union. rewrite (msubsts_not_in_fv (restrict (dom vs ∖ dom Γ2) vs)).
  2:{ rewrite dom_restrict. set_solver. }

  iApply triple_frame_wand.
  iApply (triple_shift (fun '(x1,x2) => (x1,m1 ⋅ x2))).
  iApply triple_conseq_post. 2:iApply "X".
  iIntros (? (s,m')) "((%X2&%)&?&T1) T2".
  iDestruct (interp_env_valid with "T2") as "%".
  iFrame.

  iDestruct (interp_env_shape_valid with "T2") as "%".

  iDestruct (interp_env_dom_12 with "T1") as "%".
  iDestruct (interp_env_dom_13 with "T1") as "%HT1".
  iDestruct (interp_env_dom_13 with "T2") as "%HT2".

  rewrite dom_restrict in HT2.
  rewrite !dom_restrict in HT1.

  rewrite !restrict_restrict.
  replace (dom Γ2' ∩ dom Γ2) with (dom Γ2') by set_solver.

  iDestruct (interp_env_nomix with "T1 T2") as "%".
  iDestruct (interp_env_nomix_shape with "T1 T2") as "%".

  assert (✓ (Γ1 ⋅ Γ2')).
  { rewrite comm_L. eapply valid_op_similar_env_l.
    4:rewrite comm_L //. 1,2:done. set_solver. }

  iSplitR.
  { iPureIntro.
    rewrite !(comm_L _ Γ1). split.
    { eapply similar_env_op_l; try done.
      all:rewrite comm_L //. }
    { eapply similar_shape_env_op; try done. set_solver.
      by apply nomix_shape_env_sym.
      by apply similar_shape_env_refl. } }
  { iApply interp_env_split_2. done.
    { eapply valid_op_similar_shape_env; try done. by apply similar_shape_env_refl.
      set_solver. by apply nomix_shape_env_sym. }
    { rewrite dom_op dom_restrict. set_solver. }
    rewrite !restrict_restrict dom_op.
    replace (dom Γ1 ∩ (dom Γ1 ∪ dom Γ2')) with (dom Γ1) by set_solver.
    replace (dom Γ2' ∩ (dom Γ1 ∪ dom Γ2')) with (dom Γ2') by set_solver.
    iFrame. }
Qed.

Lemma similar_shape_env_swprio_l x n n' m m':
  similar_shape_env m (<[x:=SPWrite n]> m') ->
  similar_shape_env m (<[x:=SPWrite n']> m').
Proof.
  intros X i. specialize (X i).
  destruct (m !! i).
  2:{ by destruct (<[x:=SPWrite n']> m' !! i). }
  rewrite lookup_insert_case. rewrite lookup_insert_case in X.
  case_decide; subst; last done.
  simpl in *. by destruct s.
Qed.

Lemma log_typed_pwrite Γ (x:string) e q Γ' :
  dom Γ' ⊆ dom Γ ->
  Γ' !! x = Some (TPWrite q) ->
  log_typed Γ e TInt Γ' -∗
  log_typed Γ (pwrite (Var x) e)%E TUnit Γ'.
Proof.
  iIntros (Hd Hx) "#X".
  iIntros (m vs) "!>". cbn [msubsts].
  simpl.

  iApply (triple_use_pure_pre (dom Γ = dom vs)).
  { iApply interp_env_dom_13. }
  iIntros "%D1".
  assert (x ∈ dom Γ') by by eapply elem_of_dom.
  assert (is_Some (vs !! x)) as (v&Hv). apply elem_of_dom. set_solver.
  rewrite Hv.

  iApply (triple_bind (CtxCall1 _)).
  iApply "X".
  iIntros (? (s,m')).
  iApply (triple_use_pure_pre (exists n, s=SNone /\ v0=VInt n)).
  { iIntros "(?&X&?)". destruct s; try done.
    iDestruct "X" as "[% ->]". eauto. }
  iIntros ((i&->&->)). iClear "X".

  iApply triple_extract_pure_pre.
  iIntros ((?&?)).

  iApply triple_conseq_pre. iIntros "(_&?)". iStopProof. reflexivity.

  assert (restrict (dom Γ') vs !! x = Some v) as Hvx.
  { rewrite lookup_restrict. rewrite decide_True //. }

  iApply (triple_use_pure_pre (exists q', m' !! x = Some (SPWrite q'))).
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
  iIntros "(%n&%Hmx)".

  rewrite {1}(insert_id_delete _ _ _ Hx) (insert_id_delete _ _ _ Hmx) (insert_id_delete _ _ _ Hvx).

  rewrite interp_env_insert.
  2-4:rewrite dom_delete_L; set_solver.
  simpl. rewrite /interp_pref_write.


  iApply (triple_resolve (SNone,<[x:=SPWrite (Z.max n i)]>m')).

  iApply triple_frame_wand_r.
  iApply (triple_elim_exist (fun l => v=VLoc l)).
  { naive_solver. }
  { iIntros (?) "(?&?)". iFrame. }
  iIntros (l).
  iApply triple_extract_pure_pre. iIntros (->).

  iApply triple_conseq_post. 2:iApply triple_pwrite.

  iIntros (? []) "(->&?) ?".
  iSplitR. iPureIntro. split. done.
  { eapply similar_shape_env_swprio_l. rewrite insert_id //. }
  iSplitR. done.

  rewrite {3}(insert_id_delete _ _ _ Hx) {2}(insert_id_delete _ _ _ Hmx).
  rewrite insert_insert.

  iApply interp_env_insert.
  1-3:rewrite dom_delete_L; set_solver.
  by iFrame.
Qed.

Lemma log_typed_pread (x:string) q :
  ⊢ log_typed {[x:=TPRead q]} (pread (Var x))%E TInt {[x:=TPRead q]}.
Proof.
  iIntros (m vs) "!>". cbn [msubsts].
  simpl.

  iApply (triple_use_pure_pre (exists (l:loc) z, m = {[x:=SPRead z]} /\ vs = {[x:=VLoc l]})).
  { iIntros "(%Hd&X)". rewrite dom_insert_L dom_empty_L right_id_L in Hd.
    apply dom_singleton_inv_L in Hd. destruct Hd as (?&?). subst.
    rewrite map_zip_singleton.
    iDestruct (big_sepM2_singleton_inv_l with "X") as "[%x2 (->&X)]".
    simpl. destruct x0; try done.
    iDestruct "X" as "(%&->&?)".
    eauto 10. }
  iIntros ((l&z&->&->)).

  rewrite lookup_singleton.
  rewrite interp_env_singleton. simpl.

  iApply (triple_resolve (SNone,{[x := SPRead z]})).
  iApply triple_conseq. 3:iApply triple_pread.
  { iIntros "(%&%E&?)". inversion E. subst. done. }
  Unshelve. 2:apply _.
  iIntros (? []) "(->&?)".
  iSplitR.
  { iPureIntro. split. apply similar_env_refl. apply gmap_valid_singleton. done.
    apply similar_shape_env_refl.
    { intros ?. rewrite lookup_insert_case. by case_decide. } }
  iSplitR. by iExists _.
  rewrite restrict_singleton dom_singleton_L.
  rewrite decide_True; last set_solver.
  rewrite interp_env_singleton. by iFrame.
Qed.

Lemma log_typed_palloc Γ e Γ' :
  log_typed Γ e TInt Γ' -∗
  log_typed Γ (palloc e)%E (TPWrite 1)  Γ'.
Proof.
  iIntros "#X". iIntros (m vs) "!>". simpl.
  iApply (triple_bind (CtxCall1 _)). iApply "X".
  iIntros (v (s,m')). simpl.

  iApply (triple_use_pure_pre (exists n, s=SNone /\ v=VInt n)).
  { iIntros "(_&X&_)".
    destruct s; try done.
    iDestruct "X" as "[% ->]". eauto. }
  iIntros "(%&->&->)".

  iApply (triple_resolve (SPWrite n,m')).
  rewrite -(right_id _ _ (⌜similar_env Γ Γ' /\ _⌝ ∗ _)%I).
  iApply triple_frame_wand.
  iApply triple_conseq.
  3:iApply triple_palloc.
  { by iIntros. }
  { iIntros (? []) "[% (->&?)] (?&?&?&?)". by iFrame. }
Qed.

End fundamental.
