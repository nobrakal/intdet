From stdpp Require Import binders.

From iris.proofmode Require Import proofmode.
From iris Require Import gmap saved_prop invariants.
From iris.bi Require Import monpred.

From intdet.utils Require Import restrict more_cmras more_maps_and_sets more_iris.
From intdet.lang Require Import syntax utils substitution2 notations.
From intdet.musketeer Require Import dwp lockstep.
From intdet.types Require Import utils.
From intdet.types.affine Require Import typing logrel op_related logrel_facts syntactical.

From intdet.examples Require Import tactics_triple fill.

Section fundamental.

Context `{intdetGS Σ, typeG Σ}.

Lemma log_typed_length (x:string) q :
  ⊢ log_typed {[x:=TIntArray q]} (Length x) TInt {[x:=TIntArray q]}.
Proof.
  iIntros (m vs) "!>". simpl.

  iApply (triple_use_pure_pre (exists (v:val) l, m = {[x:=SArray l]} /\ vs = {[x:=v]})).
  { iIntros "(%Hd&X)". rewrite dom_insert_L dom_empty_L right_id_L in Hd.
    apply dom_singleton_inv_L in Hd. destruct Hd as (?&?). subst.
    rewrite map_zip_singleton.
    iDestruct (big_sepM2_singleton_inv_l with "X") as "[%x2 (->&?)]".
    simpl. destruct x0; try done. eauto 10. }
  iIntros ((v&xs&->&->)).
  rewrite lookup_singleton.
  rewrite interp_env_singleton. simpl.
  rewrite /interp_array.

  iApply triple_extrude_existential.
  { iIntros (?). rewrite monPred_at_sep monPred_at_pure.
    iIntros "(->&_) !>". iIntros (?).
    rewrite monPred_at_sep monPred_at_pure.
    iIntros "(%E&_)". inversion E. eauto. }

  iIntros (l). iApply triple_extract_pure_pre. iIntros "->".
  rewrite comm. iApply triple_frame_wand.
  unshelve iApply (triple_resolve (SNone,{[x:=SArray xs]})). apply _.
  iApply triple_conseq_post. 2:iApply triple_length.
  iIntros (? []). iIntros "(->&?) ?".
  iSplitR.
  { iPureIntro. split.
    { intros i; rewrite !lookup_insert_case. case_decide; done. }
    { intros i; rewrite !lookup_insert_case. case_decide; done. } }
  iSplitR. by iExists _.
  rewrite dom_singleton_L. rewrite restrict_id.
  2:rewrite dom_singleton_L; set_solver.
  rewrite interp_env_singleton. iExists _. eauto.
Qed.

Lemma log_typed_intarr_load (x:string) q Γ Γ' e :
  dom Γ' ⊆ dom Γ ->
  Γ' !! x = Some (TIntArray q) ->
  log_typed Γ e TInt Γ' -∗
  log_typed Γ (Load x e) TInt Γ'.
Proof.
  iIntros (? Hx) "#X".
  iIntros (m vs) "!>". simpl.

  iApply (triple_use_pure_pre (dom Γ = dom vs)).
  { iApply interp_env_dom_13. }

  iIntros "%".
  assert (x ∈ dom Γ') by by eapply elem_of_dom.
  assert (is_Some (vs !! x)) as (v&Hv). apply elem_of_dom. set_solver.
  rewrite Hv.

  iApply (triple_bind (CtxLoad1 _)).
  iApply "X". iClear "X".
  iIntros (v0 (s,m')).

  iApply triple_extract_pure_pre. iIntros ((?&?)).

  iApply (triple_use_pure_pre (exists (n:Z), s=SNone /\ v0=n)).
  { iIntros "(X&_)". destruct s; try done.
    iDestruct "X" as "(%&->)". eauto. }
  iIntros "(%n&->&->)". simpl.

  assert (restrict (dom Γ') vs !! x = Some v) as Hvx.
  { rewrite lookup_restrict. rewrite decide_True //. }

  iApply (triple_use_pure_pre (exists xs, m' !! x = Some (SArray xs))).
  { iIntros "(_&X)".
    iDestruct (interp_env_dom_12 with "X") as "%Hd1".
    iDestruct (interp_env_dom_13 with "X") as "%Hd2".
    assert (is_Some (m' !! x)) as (?&Hx'). eapply elem_of_dom. set_solver.
    rewrite {1}(insert_id_delete _ _ _ Hx) (insert_id_delete _ _ _ Hx') (insert_id_delete _ _ _ Hvx).
    rewrite interp_env_insert //.
    2-4:rewrite dom_delete_L; set_solver.
    iDestruct "X" as "(X&?)". simpl.
    destruct x0; try done. subst. iDestruct "X" as "(%&->&_)".
    iPureIntro. eexists _. rewrite !lookup_insert. eauto. }
  iIntros ((xs&Hmxs)).

  rewrite {1}(insert_id_delete _ _ _ Hx) {1}(insert_id_delete _ _ _ Hmxs) {1}(insert_id_delete _ _ _ Hvx).

  rewrite interp_env_insert.
  2-4:rewrite dom_delete_L; set_solver.
  simpl.

  iApply (triple_conseq_pre (∃ l : loc, ⌜v = (#l)%V⌝ ∗
       ( ([∗ list] v0 ∈ xs, ⌜∃ n0 : Z, v0 = (^n0)%V⌝) ∗
     interp_env (delete x Γ') (delete x m') (delete x (restrict (dom Γ') vs)))  ∗ pointsto l (DfracOwn q) xs )).
  { iIntros "(_&(%&->&?&?)&?)". by iFrame. }

  iApply triple_extrude_existential.
  { iIntros (?). rewrite monPred_at_sep monPred_at_pure.
    iIntros "(->&_) !>". iIntros (?).
    rewrite monPred_at_sep monPred_at_pure.
    iIntros "(%E&_)". inversion E. eauto. }

  iIntros (l). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_frame_wand.

  iApply triple_end.
  iApply triple_load.
  iIntros (? ?).
  iApply (triple_resolve (SNone, m')).
  iApply triple_val'.
  iIntros "((%X&%&%)&?) (#?&?)". inversion X. subst. clear X.
  iSplitR; first done.
  iDestruct (big_sepL_lookup with "[$]") as "(%&->)". done.
  iSplitR; first by iExists _.

  rewrite {3}(insert_id_delete _ _ _ Hx) {2}(insert_id_delete _ _ _ Hmxs) {2}(insert_id_delete _ _ _ Hvx).
  iApply interp_env_insert.
  1-3:rewrite dom_delete_L; set_solver.
  by iFrame "#∗".
Qed.

Lemma triple_alloc' E P (i:Z) :
  ⊢ triple E P (alloc i) (fun v' '(i,l) => ⌜(0 <= i)%Z ∧ v' = (#l)%V⌝ ∗
         pointsto l (DfracOwn 1) (replicate (Z.to_nat i) VUnit) ∗
         meta_token l ∗ P).
Proof.
  iApply (triple_conseq_pre (P ∗ True)).
  { iIntros. by iFrame. }
  iApply triple_frame_wand.
  iApply triple_conseq_post. 2:iApply triple_alloc.
  iIntros (? (?,?)); simpl.
  iIntros "((%Eq&%&%)&?&?&_) ?". inversion Eq. subst. by iFrame.
Qed.

Lemma log_typed_intarr_alloc e1 e2 Γ1 Γ2 Γ3 :
  dom Γ3 ⊆ dom Γ2 -> (* I can derive this within the proof but I'm lazy *)
  fv e2 ⊆ dom Γ2 ->
  log_typed Γ1 e1 TInt Γ2 -∗
  log_typed Γ2 e2 TInt Γ3 -∗
  log_typed Γ1 (alloc_fill e2 e1) (TIntArray 1) Γ3.
Proof.
  iIntros (??) "#X1 #X2". iIntros (m vs) "!>". simpl.
  iApply (triple_bind (CtxCall1 _)).
  iApply "X1". iClear "X1".
  iIntros ( ? (?,?)).
  iApply triple_extract_pure_pre. iIntros ((?&?)).

  iApply (triple_use_pure_pre (exists i, s=SNone /\ v=VInt i)).
  { iIntros "(X&?)". destruct s; try done.
    iDestruct "X" as "(%&->)". eauto. }
  iIntros ((i&->&->)).
  iApply triple_conseq_pre.
  { iIntros "(_&?)". iStopProof. reflexivity. }

  iApply triple_use_pure_pre. iApply interp_env_dom_12.
  iIntros.

  rewrite {2}(restrict_split (dom Γ2) vs) map_union_comm.
  2:{ apply map_disjoint_dom. rewrite !dom_restrict. set_solver. }
  rewrite !msubsts_union.
  rewrite (msubsts_not_in_fv _ e2).
  2:{ rewrite dom_restrict. set_solver. }
  simpl.

  iApply (triple_bind (CtxCall2 _)).
  { iApply (triple_bind (CtxCall1 _)).
    iApply "X2". iClear "X2".
    iIntros (? (?,?)). simpl.
    iApply (triple_use_pure_pre (exists i, s=SNone /\ v=VInt i)).
    { iIntros "(_&X&?)". destruct s; try done.
      iDestruct "X" as "(%&->)". eauto. }
    iIntros ((j&->&->)).
    iApply triple_call'. done. iModIntro. simpl.
    Unshelve.
    2:exact (fun v '(j,g0) => (⌜v=(λ:"x",let: "l" := alloc ^j in fill "l" "x";; "l")%V⌝ ∗ ⌜similar_env Γ2 Γ3 ∧ similar_shape_env g g0⌝ ∗ interp_int ^j ∗
                            interp_env Γ3 g0 (restrict (dom Γ3) (restrict (dom Γ2) vs))))%I.

    iApply triple_code.
    iApply (triple_resolve (j,g0)).
    iApply triple_val'.
    iIntros "(?&?)". by iFrame. }

  iIntros (v (j,m')). iClear "X2".
  iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_extract_pure_pre. iIntros ((?&?)).
  iApply (triple_conseq_pre ((interp_env Γ3 m' (restrict (dom Γ3) (restrict (dom Γ2) vs))) ∗ True))%I.
  { iIntros "(?&?)". by iFrame. }
  iApply triple_frame_wand.
  iApply triple_call'. done. iModIntro. simpl.

  iApply (triple_bind (CtxLet _ _)).
  { iApply triple_alloc. }
  iIntros (v (j',l)).
  iApply triple_extract_pure_pre.
  iIntros ((Eq&_&->)). inversion Eq. subst j'. iApply triple_let_val. simpl.

  iApply (triple_bind (CtxLet _ _)).
  iApply triple_conseq_pre.
  2:iApply triple_fill. iIntros "(?&?)". iFrame.

  iIntros (? []).
  iApply triple_extract_pure_pre. iIntros "->".
  rewrite replicate_length.
  iApply triple_let_val. simpl.

  iApply (triple_resolve (SArray _,m')). iApply triple_val'.
  iIntros "? ?". iFrame.

  rewrite restrict_restrict.
  replace (dom Γ3 ∩ dom Γ2) with (dom Γ3) by set_solver.
  iDestruct (interp_env_dom_12 with "[$]") as "%".

  iFrame.
  iSplitR.

  assert (similar_shape_env m m').
  { eapply senv_trans. apply _. 2,3:done. set_solver. }

  iPureIntro.
  { split. eapply senv_trans. apply _. done. done. done. done. }
  iSplitR; first done.
  iApply big_opN.big_sepL_replicate.
  iModIntro. eauto.
Qed.

Lemma similar_shape_insert_array_r m x xs xs' m' :
  similar_shape_env m (<[x:=SArray xs]> m') ->
  similar_shape_env m (<[x:=SArray xs']> m').
Proof.
  intros X i. specialize (X i).
  destruct (m !! i).
  2:{ by destruct (<[x:=SArray xs']> m' !! i). }
  rewrite lookup_insert_case. rewrite lookup_insert_case in X.
  case_decide; subst; last done.
  simpl in *. destruct s; try done.
Qed.

Lemma log_typed_intarr_store (x:string) e1 e2 Γ1 Γ2 Γ3 :
  x ∈ dom Γ1 ->
  dom Γ3 ⊆ dom Γ2 -> (* Again, I'm lazy *)
  fv e2 ⊆ dom Γ2 ->
  Γ3 !! x = Some (TIntArray 1) ->
  log_typed Γ1 e1 TInt Γ2 -∗
  log_typed Γ2 e2 TInt Γ3 -∗
  log_typed Γ1 (Store x e2 e1) TUnit Γ3.
Proof.
  iIntros (??? E3) "#X1 #X2". iIntros (m vs) "!>".
  simpl.

  iApply triple_use_pure_pre.
  iApply interp_env_dom_13.
  iIntros.

  assert (is_Some (vs !! x)) as (v&Hv).
  { apply elem_of_dom. apply elem_of_dom_2 in E3. set_solver. }
  rewrite Hv.

  iApply (triple_bind (CtxStore1 _ _)).
  iApply "X1". iClear "X1". iIntros (v' (s,m')).
  iApply triple_extract_pure_pre. iIntros ((?&?)).
  iApply (triple_use_pure_pre (exists i, s=SNone /\ v'=i)).
  { iIntros "(X&_)". destruct s; try done.
    iDestruct "X" as "(%&->)". eauto. }
  iIntros ((i&->&->)).

  iApply (triple_use_pure_pre (exists i', i=VInt i')).
  { iIntros "([% ->]&_)". eauto. }
  iIntros ((i'&->)).

  iApply triple_conseq_pre.
  { iIntros "(_&?)". iStopProof. reflexivity. }

  rewrite {2}(restrict_split (dom Γ2) vs) map_union_comm.
  2:{ apply map_disjoint_dom. rewrite !dom_restrict. set_solver. }
  rewrite !msubsts_union.
  rewrite (msubsts_not_in_fv _ e2).
  2:{ rewrite dom_restrict. set_solver. }
  simpl.

  iApply triple_use_pure_pre.
  iApply interp_env_dom_12. iIntros.

  iApply (triple_bind (CtxStore2 _ _)).
  iApply "X2". iClear "X2".

  iIntros (v' (s,m'')).
  iApply triple_extract_pure_pre. iIntros ((?&?)).
  iApply (triple_use_pure_pre (exists i, s=SNone /\ v'=i)).
  { iIntros "(X&_)". destruct s; try done.
    iDestruct "X" as "(%&->)". eauto. }
  iIntros ((j&->&->)).

  iApply (triple_use_pure_pre (exists j', j=VInt j')).
  { iIntros "([% ->]&_)". eauto. }
  iIntros ((j'&->)).

  iApply triple_conseq_pre.
  { iIntros "(_&?)". iStopProof. reflexivity. }

  rewrite restrict_restrict.
  replace (dom Γ3 ∩ dom Γ2) with (dom Γ3) by set_solver. simpl.

  iApply triple_use_pure_pre.
  iApply interp_env_dom_12.
  iIntros.

  assert (x ∈ dom Γ3) by by eapply elem_of_dom.

  assert (is_Some (m'' !! x)) as (s&Hx'). eapply elem_of_dom. set_solver.
  assert (restrict (dom Γ3) vs !! x = Some v) as Hx''.
  { rewrite lookup_restrict. rewrite decide_True //. }
  rewrite {1}(insert_id_delete _ _ _ E3) (insert_id_delete _ _ _ Hx') (insert_id_delete _ _ _ Hx'').
  rewrite interp_env_insert. simpl.
  2-4:rewrite dom_delete_L; set_solver.

  iApply (triple_use_pure_pre (exists l vs, s=SArray vs /\ v=VLoc l)).
  { iIntros "(X&_)". destruct s; eauto.
    iDestruct "X" as "(%&->&_)". eauto. }

  iIntros ( (l&xs&->&->)).
  rewrite comm.
  iApply triple_frame_wand.
  iApply (triple_conseq_pre (pointsto l (DfracOwn 1) xs ∗ ([∗ list] v ∈ xs, ⌜∃ n : Z, v = (^n)%V⌝))).
  { iIntros "(%&%Eq&?&?)". inversion Eq. subst. eauto. }
  rewrite comm. iApply triple_frame_wand.

  iApply triple_end. iApply triple_store.
  iIntros (v k). iApply triple_extract_pure_pre.
  iIntros ((Eq&->&?)). subst.
  iApply (triple_resolve (SNone, <[x:=SArray (<[Z.to_nat k:=VInt _]> xs)]>m'')).
  iApply triple_val'.
  iIntros "X1 X2 X3".
  iSplitR.
  { iPureIntro. split.
    { eapply senv_trans; try done. apply _. }
    { eapply similar_shape_insert_array_r. rewrite insert_id //.
      eapply senv_trans. 3,4:done. apply _. set_solver. } }
  iSplitR; first done.

  rewrite {3}(insert_id_delete _ _ _ E3) -(insert_delete_insert m'' x (SArray (<[Z.to_nat k:=VInt _]> xs))).
  rewrite interp_env_insert.
  2-4:rewrite dom_delete_L; set_solver.
  iFrame.

  iSplitR; first done.
  assert (is_Some (xs !! Z.to_nat k)) as (?&?).
  { apply lookup_lt_is_Some_2. lia. }
  iDestruct (big_sepL_insert_acc with "[$]") as "(_&X)". done.
  iApply "X". eauto.
Qed.

End fundamental.
