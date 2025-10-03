From stdpp Require Import binders.

From iris.proofmode Require Import proofmode.
From iris Require Import gmap saved_prop invariants.
From iris.bi Require Import monpred.
From iris.algebra Require Import cmra gmap.

From intdet.utils Require Import restrict more_cmras more_maps_and_sets more_iris big_opN.
From intdet.lang Require Import syntax utils substitution2 notations.
From intdet.musketeer Require Import dwp lockstep.
From intdet.types Require Import utils.
From intdet.types.affine Require Import typing logrel op_related logrel_facts fundamental_hashtbl syntactical.

From intdet.examples Require Import parfor.

Section proof.

Context `{intdetGS Σ, typeG Σ}.

Lemma interp_env_iterated_op_inv_l Γ n ms vs :
  interp_env (iter_sep n Γ) ms vs ⊢
  ⌜ms = iter_sep n ms⌝.
Proof.
  iIntros "X".
  iInduction n as [] "IH" forall (vs).
  { simpl. iDestruct (interp_env_dom_12 with "X") as "%X".
    iPureIntro. symmetry in X. apply dom_empty_inv_L in X. done. }
  { simpl.
    iDestruct (interp_sepM2_op_inv_l with "X") as "(%m1&%m2&->&%&%&%X)".
    rewrite interp_env_split_1 //.
    iDestruct "X" as "(_&X)".
    destruct n.
    { simpl. rewrite right_id_L //. }
    destruct X as (X1&X2). rewrite dom_iter_sep //.
    rewrite -X1 X2 -X1.
    iDestruct ("IH" with "X") as "<-".
    iPureIntro. rewrite {3}X1 -X2 //. }
Qed.

Lemma interp_env_iter_split_1 n Γ ms vs :
  interp_env (iter_sep n Γ) (iter_sep n ms) vs ⊢
  [∗ nat] _ ∈ [0; n], interp_env Γ ms vs.
Proof.
  iIntros "X".
  iInduction n as [] "IH".
  { rewrite big_sepN_0 //. }
  { destruct_decide (decide (n=0)).
    { simpl. subst. simpl. rewrite !right_id_L. iClear "IH".
      rewrite big_sepN_S; last lia. iFrame.
      rewrite big_sepN_0 //. }
    iDestruct (interp_env_dom_12 with "X") as "%E1".
    iDestruct (interp_env_dom_13 with "X") as "%E2".
    rewrite !dom_iter_sep // in E1,E2. simpl.
    iDestruct (interp_env_split_1 with "X") as "(?&?)".
    done. rewrite !dom_iter_sep //.
    rewrite dom_iter_sep //.
    rewrite restrict_id. 2:set_solver.
    iApply big_sepN_snoc. lia. iFrame. iApply "IH". done. }
Qed.

(* Not foldr because fold_op cons does not work ?? *)
Fixpoint fold_op {A:ucmra} (xs:list A) :=
  match xs with
  | [] => ε
  | x::xs => x ⋅ fold_op xs end.

Lemma interp_env_empty :
  ⊢ interp_env ∅ ∅ ∅.
Proof.
  rewrite /interp_env.
  iSplitR; first done.
  rewrite map_zip_empty big_sepM2_empty //.
Qed.

Lemma fold_op_cons {A:ucmra} (x:A) xs :
  fold_op (x::xs) = x ⋅ fold_op xs.
Proof. reflexivity. Qed.

Lemma similar_shape_op_l_same s s1 s2 :
  similar_shape s s1 ->
  similar_shape s s2 ->
  nomix_shape s1 s2 ->
  similar_shape s (s1 ⋅ s2).
Proof.
  revert s1 s2. induction s; intros [] []; try done; simpl.
  { naive_solver. }
  all:rewrite shape_op_unfold; simpl.
  { intros -> ->. rewrite decide_True //. }
  { intros _ _ ->. rewrite decide_True //. }
  { intros _ _ ->. rewrite decide_True //.  }
  { intros _ _ ->. rewrite decide_True //. }
Qed.

Lemma similar_shape_env_op_same m x y :
  similar_shape_env m x ->
  similar_shape_env m y ->
  nomix_shape_env x y ->
  similar_shape_env m (x ⋅ y).
Proof.
  intros X1 X2 X3.
  intros k. rewrite lookup_op.
  specialize (X1 k). specialize (X2 k). specialize (X3 k).
  destruct (m !! k) eqn:Hm.
  2:{ destruct (x !! k ⋅ y !! k) eqn:X; rewrite X //. }

  destruct (x !! k) eqn:Hx; rewrite Hx.
  { destruct (y !! k) eqn:Hy; rewrite Hy.
    { simpl in *. eauto using similar_shape_op_l_same. }
    { rewrite right_id. done. } }
  { rewrite left_id. done. }
Qed.

Lemma nomix_shape_valid s1 s2 :
  ✓ (s1 ⋅ s2) -> nomix_shape s1 s2.
Proof.
  revert s2; induction s1; intros []; try done.
  all:rewrite shape_op_unfold; simpl.
  { inversion 1. naive_solver. }
  all:by case_decide.
Qed.

Lemma similar_shape_env_fold_op m xs :
  ✓ (fold_op xs) ->
  Forall (similar_shape_env m) xs ->
  similar_shape_env m (fold_op xs).
Proof.
  intros Hv Hxs.
  induction xs.
  { intros. simpl. intros ?. rewrite lookup_empty. by destruct (m !! i). }
  simpl. inversion Hxs. subst.
  apply similar_shape_env_op_same. done.
  { simpl in *. apply IHxs. eauto using cmra_valid_op_r. done. }
  { intros k. specialize (Hv k). simpl in *. rewrite lookup_op in Hv.
    destruct (a !! k) eqn:Ha; rewrite Ha;
      destruct (fold_op xs !! k) eqn:Hxsk; rewrite Hxsk //.
    simpl. rewrite Ha Hxsk -Some_op Some_valid in Hv.
    eauto using nomix_shape_valid. }
Qed.

Lemma similar_shape_env_trans m1 m2 m3 :
  dom m1 = dom m2 ->
  similar_shape_env m1 m2 ->
  similar_shape_env m2 m3 ->
  similar_shape_env m1 m3.
Proof.
  intros ? X1 X2 k.
  specialize (X1 k). specialize (X2 k).
  destruct (m1 !! k) eqn:E1.
  2:by destruct (m3 !! k).
  destruct (m3 !! k); last done.
  apply elem_of_dom_2 in E1.
  assert (is_Some (m2 !!k )) as (?&X). by (apply elem_of_dom; set_solver).
  rewrite X in X1 X2. simpl in *. eauto using similar_shape_trans.
Qed.

Local Lemma interp_env_join_fold Γ xs vs n m0 :
  ✓ (iter_sep n Γ) ->
  dom vs = dom Γ ->
  n ≠ 0 ->
  n = length xs ->
  dom m0 = dom Γ ->
  Forall (similar_shape_env m0) xs ->
  ([∗ list] m ∈ xs, interp_env Γ m vs) -∗
  interp_env (iter_sep n Γ) (fold_op xs) vs.
Proof.
  iIntros (??? -> ? Hfor) "H".
  iInduction xs as [] "IH".
  { exfalso. simpl in *. congruence. }
  { rewrite fold_op_cons. simpl.
    iDestruct "H" as "(?&?)".
    inversion Hfor. subst.

    iDestruct (interp_env_dom_13 with "[$]") as "%".
    destruct_decide (decide (length xs = 0)).
    { destruct xs; simpl in *; last done.
      rewrite !right_id_L //. }

    iDestruct ("IH" with "[%][%//][%//][$]") as "?".
    { simpl in *. eauto using cmra_valid_op_r. }

    iDestruct (interp_env_dom_12 Γ with "[$]") as "%".
    iDestruct (interp_env_shape_valid with "[$]") as "%".
    iApply interp_env_split_2.
    { done. }
    { eapply similar_shape_env_fold_op. done.
      eapply Forall_impl. done. intros.
      eapply similar_shape_env_trans. 2:by apply similar_shape_env_sym.
      set_solver. done. }
    { rewrite dom_op. destruct xs.
      { simpl. rewrite dom_empty_L right_id_L //. }
      { rewrite dom_iter_sep. set_solver. done. } }

    rewrite dom_iter_sep //.
    rewrite restrict_id; last set_solver.
    iFrame. }
Qed.

Lemma restrict_binsert {V} X x (v:V) m :
  binder_set x ## dom m ->
  restrict X (binsert x v m) = if (decide (binder_set x ## X)) then restrict X m else binsert x v (restrict X m).
Proof.
  intros.
  destruct x.
  { rewrite decide_True //. }
  simpl. rewrite restrict_insert. 2:set_solver.
  case_decide.
  { rewrite decide_False //; set_solver. }
  { rewrite decide_True //; set_solver. }
Qed.

Lemma log_typed_parfor Γ Γf arg body (x1 x2:string) :
  Γ !! x1 = Some TInt ->
  Γ !! x2 = Some TInt ->
  binder_set arg ## dom Γ ->
  fractional Γ Γf -> (* pre and post the same because parfor might be id. *)
  □ (∀ n, log_typed (binsert arg TInt (Γf n)) body TUnit (Γf n)) -∗
  log_typed Γ (parfor x1 x2 (Code BAnon arg body)) TUnit Γ.
Proof.
  iIntros (Hx1 Hx2 ? Hf).
  iIntros "#Hf !>". iIntros (m vs). simpl.
  iApply (triple_use_pure_pre (dom Γ = dom m /\ dom Γ = dom vs)).
  { iIntros.
    iDestruct (interp_env_dom_12 with "[$]") as "%".
    iDestruct (interp_env_dom_13 with "[$]") as "%".
    eauto. }
  iIntros ((?&?)).

  iApply (triple_use_pure_pre (exists (i1:Z), vs !! x1 = Some (VInt i1))).
  { iIntros "X".
    assert (x1 ∈ dom Γ) by by apply (elem_of_dom_2 Γ) in Hx1.
    assert (is_Some (m !! x1)) as (?&Hmx1). eapply elem_of_dom. set_solver.
    assert (is_Some (vs !! x1)) as (?&Hvx1). eapply elem_of_dom. set_solver.
    rewrite {1}(insert_id_delete _ _ _ Hx1) (insert_id_delete _ _ _ Hmx1) (insert_id_delete _ _ _ Hvx1).
    rewrite interp_env_insert. 2-4:rewrite dom_delete_L; set_solver.
    iDestruct "X" as "(X&_)".
    destruct x; try done. iDestruct "X" as "(%&->)".
    rewrite lookup_insert. eauto. }
  iIntros ((i1&->)).

  iApply (triple_use_pure_pre (exists (i2:Z), vs !! x2 = Some (VInt i2))).
  { iIntros "X".
    assert (x2 ∈ dom Γ) by by apply (elem_of_dom_2 Γ) in Hx2.
    assert (is_Some (m !! x2)) as (?&Hmx1). eapply elem_of_dom. set_solver.
    assert (is_Some (vs !! x2)) as (?&Hvx1). eapply elem_of_dom. set_solver.
    rewrite {1}(insert_id_delete _ _ _ Hx2) (insert_id_delete _ _ _ Hmx1) (insert_id_delete _ _ _ Hvx1).
    rewrite interp_env_insert. 2-4:rewrite dom_delete_L; set_solver.
    iDestruct "X" as "(X&_)".
    destruct x; try done. iDestruct "X" as "(%&->)".
    rewrite lookup_insert. eauto. }

  iIntros ((i2&->)).

  remember (Z.to_nat (i2-i1)) as n.

  iApply (triple_bind (CtxCall1 _)).
  iApply triple_code'.

  iIntros (? []).
  iApply triple_extract_pure_pre. iIntros "->".

  destruct_decide (decide (i1 < i2)%Z); last first.
  { iApply (triple_conseq_pre (interp_env Γ m vs ∗ True))%I.
    { iIntros. by iFrame. }
    iApply triple_frame_wand.

    iApply (triple_resolve (SNone, m)).
    iApply triple_end.
    iApply triple_conseq.
    3:iApply (parfor_spec _ _ _ _ (fun _ => True)%I (fun _ _ => True)%I).
    { iIntros. rewrite big_sepZ_0 //. lia. }
    { iIntros (?? ((->&?)&?)). Unshelve.
      3:exact unit. 2:exact (fun v _ => ⌜v=VUnit⌝)%I. done. }
    { rewrite big_sepZ_0 //. lia. }
    iIntros (? _). iApply triple_val'.
    iIntros "-> ?".

    iDestruct (interp_env_valid with "[$]") as "%".
    iDestruct (interp_env_shape_valid with "[$]") as "%".
    rewrite restrict_id. 2:set_solver. iFrame.
    iSplitR; last done. iPureIntro.
    eauto using similar_env_refl, similar_shape_env_refl. }

  assert (n ≠ 0) as Hn by lia.
  specialize (Hf n Hn). rewrite Hf.

  iApply triple_use_pure_pre.
  { iApply interp_env_iterated_op_inv_l. }
  iIntros (Hm). rewrite {1}Hm.

  iApply triple_use_pure_pre.
  { iApply interp_env_valid. }
  iIntros (HΓv).

  iApply triple_conseq_pre. iApply interp_env_iter_split_1.
  assert (([∗ nat] _ ∈ [0; n], interp_env (Γf n) m vs) ⊣⊢ ([∗ Z] _ ∈ [i1;i2], interp_env (Γf n) m vs)) as X.
  { rewrite /big_sepZ. subst. f_equiv. }

  rewrite X.

  assert (dom Γ = dom (Γf n)) as Hdf.
  { apply (@f_equal _ _ dom) in Hf. rewrite dom_iter_sep // in Hf. }

  iApply triple_end.
  { iApply (parfor_spec _ _ _ _ (fun _ => interp_env (Γf n) m vs)).
    iApply big_sepN_intro. iModIntro. iIntros.
    iApply triple_call'. done. iModIntro. simpl.
    iDestruct ("Hf" $! n (binsert arg SNone m)) as "#Hf'". iClear "Hf".
    rewrite binsert_msubsts.
    iApply triple_conseq.
    3:iApply "Hf'".
    { iIntros. iApply binsert_interp_env. iFrame. iExists _. done. }
    { iIntros (? (s,m')) "((%&%Hsim)&X&?)".
      destruct s; try done. iDestruct "X" as "->".
      iSplitR; first done.
      Unshelve. 2:exact (fun _ '(s,m'') => ⌜s=SNone /\ similar_shape_env m m''⌝ ∗ interp_env (Γf n) m'' vs)%I.
      simpl. iSplitR.
      { iPureIntro. split; first done.
        intros k. specialize (Hsim k).
        destruct arg; first done. simpl in *.
        rewrite lookup_insert_case in Hsim. case_decide; last done.
        rewrite not_elem_of_dom_1. 2:set_solver. by destruct (m' !! k). }
      { rewrite restrict_binsert; last set_solver.
        rewrite decide_True; last set_solver.
        rewrite restrict_id //. set_solver. } } }

  iIntros (? xs).
  iApply triple_extract_pure_pre.
  iIntros ((->&?)).

  iApply (triple_resolve (SNone, fold_op (snd <$> xs))).
  iApply triple_val'.
  iIntros "X".

  iAssert (⌜Forall (similar_shape_env m) xs.*2⌝)%I as "%Hfor".
  { rewrite Forall_forall. iIntros (x Hx).
    apply elem_of_list_fmap in Hx.
    destruct Hx as ((?&?)&Hx&Hy).
    iDestruct (big_sepL_elem_of with "[$]") as "X". done.
    simpl. iDestruct "X" as "((_&%)&_)". simpl in *. subst. done. }

  iAssert ([∗ list] m' ∈ xs.*2, interp_env (Γf n) m' vs)%I with "[X]" as "X".
  { clear X Hm Heqn H1 H2 H5 Hfor. iInduction xs as [ | (?,?) ? ] "IH". done.
    simpl. iDestruct "X" as "((_&?)&?)". iFrame. by iApply "IH". }

  rewrite dom_iter_sep // -Hdf restrict_id. 2:set_solver.

  iDestruct (interp_env_join_fold with "[$]") as "?".
  { done. }
  { set_solver. }
  { done. }
  { rewrite fmap_length. lia. }
  2:{ done. }
  { set_solver. }

  iDestruct (interp_env_shape_valid with "[$]") as "%".
  iFrame.

  iSplitR; last done.
  { iPureIntro. split. apply similar_env_refl. done.
    apply similar_shape_env_fold_op. done. done. }
Qed.

End proof.
