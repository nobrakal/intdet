From Coq Require Import Wellfounded.

From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates ghost_map.
From iris.algebra Require Import gset frac.

From intdet.utils Require Import more_maps_and_sets.
From intdet.lang Require Import syntax semantics locations atomic.

Class inInjG Σ :=
  InInjG {
      γinj1 : gname;                    (* the injection *)
      γinj2 : gname;
      iinj : ghost_mapG Σ loc loc;
      γwaiting : gname;                (* the waiting set *)
      iwaiting : inG Σ (authUR (gset_disjR loc));
    }.

#[local] Existing Instance iinj.
#[local] Existing Instance iwaiting.

Section go.

Context `{inInjG Σ}.

Definition img_in (g:gset loc) (α:gmap loc loc) :=
  map_Forall (fun _ v => v ∈ g) α.

Definition interp_inj (g1 g2:gset loc) : iProp Σ :=
  ∃ (α1 α2:gmap loc loc),
    ghost_map_auth γinj1 1%Qp α1 ∗ ghost_map_auth γinj2 1%Qp α2 ∗
    own γwaiting (● (GSet (g1 ∖ dom α1))) ∗
    ⌜dom α1 ⊆ g1 /\ dom α2 ⊆ g2⌝.

Definition waiting l := own γwaiting (◯ (GSet {[l]})).

Definition ininj (ll lr:loc) : iProp Σ :=
  ghost_map_elem γinj1 ll DfracDiscarded lr ∗
  ghost_map_elem γinj2 lr DfracDiscarded ll.

Fixpoint eininj (e1 e2:expr) : iProp Σ :=
  match e1,e2 with
  | Val v1, Val v2 => vininj v1 v2
  | Code f1 args1 body1, Code f2 args2 body2 =>
      ⌜f1=f2 /\ args1=args2⌝ ∗ eininj body1 body2
  | Var x1, Var x2 => ⌜x1=x2⌝
  | Call e1 e2, Call e1' e2' => eininj e1 e1' ∗ eininj e2 e2'
  | CallPrim p e1 e2, CallPrim p' e1' e2' => ⌜p=p'⌝ ∗ eininj e1 e1' ∗ eininj e2 e2'
  | If e1 e2 e3, If e1' e2' e3' | Store e1 e2 e3, Store e1' e2' e3' => eininj e1 e1' ∗ eininj e2 e2' ∗ eininj e3 e3'
  | CAS e1 e2 e3 e4, CAS e1' e2' e3' e4' => eininj e1 e1' ∗ eininj e2 e2' ∗ eininj e3 e3' ∗ eininj e4 e4'
  | Let x e1 e2, Let x' e1' e2' => ⌜x=x'⌝ ∗ eininj e1 e1' ∗ eininj e2 e2'
  | Alloc e, Alloc e' | Assert e, Assert e' | Fst e,Fst e' | Snd e,Snd e' | Length e,Length e' => eininj e e'
  | Pair e1 e2, Pair e1' e2' | Load e1 e2, Load e1' e2' | Par e1 e2, Par e1' e2' | RunPar e1 e2, RunPar e1' e2' => eininj e1 e1' ∗ eininj e2 e2'
  | _,_ => False end
with vininj (v1 v2:val) : iProp Σ :=
  match v1, v2 with
  | VPair v11 v12, VPair v21 v22 => vininj v11 v21 ∗ vininj v12 v22
  | VLoc l1, VLoc l2 => ininj l1 l2
  | VCode f1 args1 body1, VCode f2 args2 body2 =>
      ⌜f1=f2 /\ args1=args2⌝ ∗ eininj body1 body2
  | v1,v2 => ⌜v1 = v2⌝
  end.

Ltac goih IH := eapply IH; simpl; lia.

Global Instance eininj_persist e e' : Persistent (eininj e e').
Proof.
  revert e'.
  induction e as [e IHe] using (well_founded_induction (wf_inverse_image _ nat _ expr_size PeanoNat.Nat.lt_wf_0)).
  assert (∀ y e', expr_size y < expr_size e → Persistent (eininj y e')) as IH.
  naive_solver. clear IHe.
  destruct e; simpl.
  all:destruct e'; try apply _.
  { destruct v,v0; try apply _; simpl.
    { apply bi.sep_persistent.
      goih (IH (Val v1) (Val v0_1)). goih (IH (Val v2) (Val v0_2)). }
    { apply bi.sep_persistent. apply _. goih IH. } }
  all:repeat apply bi.sep_persistent; try apply _.
  all:goih IH.
Qed.

Global Instance vininj_persist v v' : Persistent (vininj v v').
Proof. apply (eininj_persist (Val v) (Val v')). Qed.

Global Instance eininj_timeless e e' : Timeless (eininj e e').
Proof.
  revert e'.
  induction e as [e IHe] using (well_founded_induction (wf_inverse_image _ nat _ expr_size PeanoNat.Nat.lt_wf_0)).
  assert (∀ y e', expr_size y < expr_size e → Timeless (eininj y e')) as IH.
  naive_solver. clear IHe.
  destruct e; simpl.
  all:destruct e'; try apply _.
  { destruct v,v0; try apply _; simpl.
    { apply bi.sep_timeless.
      goih (IH (Val v1) (Val v0_1)). goih (IH (Val v2) (Val v0_2)). }
    { apply bi.sep_timeless. apply _. goih IH. } }
  all:repeat apply bi.sep_timeless; try apply _.
  all:goih IH.
Qed.

Global Instance vininj_timeless v v' : Timeless (vininj v v').
Proof. apply (eininj_timeless (Val v) (Val v')). Qed.

Definition cininj (k1 k2:ctx) : iProp Σ :=
  match k1,k2 with
  | CtxCall1 x1, CtxCall1 x1' => eininj x1 x1'
  | CtxStore1 x x1,CtxStore1 x' x1' => eininj x x' ∗ eininj x1 x1'
  | CtxCall2 x, CtxCall2 x' => vininj x x'
  | CtxStore2 x e, CtxStore2 x' e' => eininj x x' ∗ vininj e e'
  | CtxStore3 x e, CtxStore3 x' e' => vininj x x' ∗ vininj e e'
  | CtxCallPrim1 p x, CtxCallPrim1 p' x' => ⌜p=p'⌝ ∗ eininj x x'
  | CtxCallPrim2 p x, CtxCallPrim2 p' x' => ⌜p=p'⌝ ∗ vininj x x'
  | CtxIf x1 x2, CtxIf x1' x2' => eininj x1 x1' ∗ eininj x2 x2'
  | CtxLet x1 x2, CtxLet x1' x2' => ⌜x1=x1'⌝∗ eininj x2 x2'
  | CtxLoad1 x, CtxLoad1 x' => eininj x x'
  | CtxLoad2 x, CtxLoad2 x' => vininj x x'
  | CtxPair1 x, CtxPair1 x' => eininj x x'
  | CtxPair2 x, CtxPair2 x' => vininj x x'
  | CtxAlloc, CtxAlloc | CtxAssert, CtxAssert | CtxFst,CtxFst | CtxSnd,CtxSnd | CtxLength,CtxLength => True
  | CtxCas1 x1 x2 x3, CtxCas1 x1' x2' x3' => eininj x1 x1' ∗ eininj x2 x2' ∗ eininj x3 x3'
  | CtxCas2 x1 x2 x3, CtxCas2 x1' x2' x3' => eininj x1 x1' ∗ eininj x2 x2' ∗ vininj x3 x3'
  | CtxCas3 x1 x2 x3, CtxCas3 x1' x2' x3' => eininj x1 x1' ∗ vininj x2 x2' ∗ vininj x3 x3'
  | CtxCas4 x1 x2 x3, CtxCas4 x1' x2' x3' => vininj x1 x1' ∗ vininj x2 x2' ∗ vininj x3 x3'
  | _,_ => False end.

Global Instance cininj_persist k k' : Persistent (cininj k k').
Proof.
  destruct k,k'; simpl; try apply _.
  all:rewrite !hoist_bigpsepL2.
  all:apply _.
Qed.

Lemma big_sepL2_wininj_inv_vals (xs:list val) (ys:list expr) :
  ([∗ list] y1;y2 ∈ xs;ys, eininj (Val y1) y2) -∗
  ⌜exists vs, ys = Val <$> vs⌝.
Proof.
  iIntros "X". iInduction xs as [] "IH" forall (ys).
  { iDestruct (big_sepL2_nil_inv_l with "X") as "->". iPureIntro. by exists nil. }
  { iDestruct (big_sepL2_cons_inv_l with "X") as "[% [% (->&?&?)]]".
    iDestruct ("IH" with "[$]") as "[% ->]". destruct x2; try done.
    iPureIntro. by eexists (_::_). }
Qed.

Lemma eininj_fill_item_inv kl el er :
  eininj (fill_item kl el) er -∗
  ∃ kr er', ⌜er=fill_item kr er'⌝ ∗ cininj kl kr ∗ eininj el er'.
Proof.
  iIntros "Hinj".
  destruct kl,er; simpl; try done.
  { iDestruct "Hinj" as "(?&?)".
    iExists (CtxCall1 _),_.  by iFrame. }
  { iDestruct "Hinj" as "(?&?)".
    destruct er2; try done.
    iExists (CtxCall2 _),_. by iFrame. }
  { iDestruct "Hinj" as "(->&?&?)".
    iExists (CtxCallPrim1 _ _), _. by iFrame. }
  { iDestruct "Hinj" as "(->&?&?)". destruct er2; try done.
    iExists (CtxCallPrim2 _ _), _. by iFrame. }
  { iDestruct "Hinj" as "(?&?&?)".
    iExists (CtxIf _ _), _. by iFrame. }
  { iDestruct "Hinj" as "(->&?&?)".
    iExists (CtxLet _ _), _. by iFrame. }
  { iExists CtxAlloc, _. by iFrame. }
  { iExists CtxFst, _. by iFrame. }
  { iExists CtxSnd, _. by iFrame. }
  { iDestruct "Hinj" as "(?&?)".
    iExists (CtxPair1 _), _. simpl. by iFrame. }
  { iDestruct "Hinj" as "(?&?)". destruct er2; try done.
    iExists (CtxPair2 _), _. by iFrame. }
  { iDestruct "Hinj" as "(?&?)".
    iExists (CtxLoad1 _), _. simpl. by iFrame. }
  { iDestruct "Hinj" as "(?&?)". destruct er2; try done.
    iExists (CtxLoad2 _), _. by iFrame. }
  { iDestruct "Hinj" as "(?&?&?)". iExists (CtxStore1 _ _),_. simpl. by iFrame. }
  { iDestruct "Hinj" as "(?&?&?)". destruct er3; try done.
    iExists (CtxStore2 _ _),_. by iFrame. }
  { iDestruct "Hinj" as "(?&?&?)".
    destruct er2; try done. destruct er3; try done.
    iExists (CtxStore3 _ _),_. by iFrame. }
  { iExists CtxAssert,_. by iFrame. }
  { iExists CtxLength,_. by iFrame. }
  { iDestruct "Hinj" as "(?&?&?&?)".
    iExists (CtxCas1 _ _ _), _. by iFrame. }
  { iDestruct "Hinj" as "(?&?&?&?)". destruct er4; try done.
    iExists (CtxCas2 _ _ _), _. by iFrame. }
  { iDestruct "Hinj" as "(?&?&?&?)".
    destruct er3; try done. destruct er4; try done.
    iExists (CtxCas3 _ _ _), _. by iFrame. }
  { iDestruct "Hinj" as "(?&?&?&?)".
    destruct er2; try done. destruct er3; try done. destruct er4; try done.
    iExists (CtxCas4 _ _ _), _. by iFrame. }
Qed.

Definition cininjs kls krs : iProp Σ :=
  [∗ list] kl;kr ∈ kls; krs, cininj kl kr.

Lemma eininj_fill_items_inv kls el er :
  eininj (fill_items kls el) er -∗
  ∃ krs er', ⌜er=fill_items krs er'⌝  ∗ cininjs kls krs ∗ eininj el er'.
Proof.
  iIntros "Hinj".
  iInduction kls as [|] "IH" forall (el er).
  { iExists nil,_. iFrame. rewrite /cininjs big_sepL2_nil //. }
  { simpl.
    iDestruct (eininj_fill_item_inv with "Hinj") as "[% [% (->&?&?)]]".
    iDestruct ("IH" with "[$]") as "[% [% (->&?&?)]]".
    iExists (_::_),_. iSplitR; first done. iFrame. }
Qed.

Lemma eininj_fill_item kl kr el er :
  cininj kl kr -∗ eininj el er -∗
  eininj (fill_item kl el) (fill_item kr er).
Proof.
  iIntros "Hk He".
  destruct kl,kr; try done; simpl.
  all:iFrame.
Qed.

Lemma eininj_fill_items kls krs el er :
  cininjs kls krs -∗ eininj el er -∗
  eininj (fill_items kls el) (fill_items krs er).
Proof.
  iIntros "Hk He".
  iInduction kls as [|] "IH" forall (krs).
  { iDestruct (big_sepL2_nil_inv_l with "Hk") as "->".
    done. }
  { iDestruct (big_sepL2_cons_inv_l with "Hk") as "[% [% (->&?&?)]]".
    simpl. iApply (eininj_fill_item with "[$]").
    iApply ("IH" with "[$][$]"). }
Qed.

Ltac goih IHe x ::=
  iApply (IHe with (String.append x "[$]")); simpl; lia.

Lemma eininj_subst x e e' v v' :
  eininj e e' -∗
  vininj v v' -∗
  eininj (subst x v e) (subst x v' e').
Proof.
  revert e'.
  induction e as [e IHe] using (well_founded_induction (wf_inverse_image _ nat _ expr_size PeanoNat.Nat.lt_wf_0)).
  destruct e; simpl.
  { iIntros (e') "? ?".
    destruct e'; try done. }
  { iIntros (?) "Hinj ?".
    destruct e'; try done. iDestruct "Hinj" as "((->&->)&?)". simpl.
    case_decide; simpl.
    { by iFrame. }
    { iSplit; first done. goih IHe "[$]". } }
  { iIntros (?) "Hinj ?".
    destruct e'; try done. iDestruct "Hinj" as "->". simpl.
    by case_decide. }
  { iIntros (?) "Hinj ?". destruct e'; try done.
    iDestruct "Hinj" as "#(X1&X2)". simpl.
    iSplit. goih IHe "X1". goih IHe "X2". }
  { iIntros (?) "Hinj #?". destruct e'; try done.
    iDestruct "Hinj" as "#(->&X1&X2)". simpl.
    iSplit; first done.
    iSplit. all: iApply IHe; simpl; try lia; by iFrame. }
  { iIntros (?) "Hinj #?". destruct e'; try done.
    iDestruct "Hinj" as "#(X1&X2&X3)". simpl.
    iSplit. goih IHe "X1". iSplit. goih IHe "X2". goih IHe "X3". }
  { iIntros (?) "Hinj #?". destruct e'; try done.
    iDestruct "Hinj" as "#(->&X1&X2)". simpl.
    iSplit; first done.
    iSplit. goih IHe "X1".
    case_decide; try done. goih IHe "X2". }
  { iIntros (?) "Hinj ?". destruct e'; try done.
    iDestruct "Hinj" as "#(X1&X2)". simpl.
    iSplit. goih IHe "X1". goih IHe "X2". }
  { iIntros (?) "Hinj ?". destruct e'; try done.
    goih IHe "[$]". }
  { iIntros (?) "Hinj ?". destruct e'; try done.
    goih IHe "[$]". }
  { iIntros (?) "Hinj ?". destruct e'; try done.
     goih IHe "[$]". }
  { iIntros (?) "Hinj ?". destruct e'; try done.
    iDestruct "Hinj" as "#(X1&X2)". simpl.
    iSplit. goih IHe "X1". goih IHe "X2". }
  { iIntros (?) "Hinj #?". destruct e'; try done.
    iDestruct "Hinj" as "#(X1&X2&X3)". simpl.
    iSplit. goih IHe "X1". iSplit. goih IHe "X2". goih IHe "X3". }
  { iIntros (?) "Hinj ?". destruct e'; try done.
    goih IHe "[$]". }
  { iIntros (?) "Hinj ?". destruct e'; try done.
    goih IHe "[$]". }
  { iIntros (?) "Hinj #?". destruct e'; try done.
    iDestruct "Hinj" as "#(X1&X2)". simpl.
    iSplit. goih IHe "X1". goih IHe "X2". }
  { iIntros (?) "Hinj #?". destruct e'; try done.
    iDestruct "Hinj" as "#(X1&X2)". simpl.
    iSplit. goih IHe "X1". goih IHe "X2". }
  { iIntros (?) "Hinj #?". destruct e'; try done.
    iDestruct "Hinj" as "#(X1&X2&X3&X4)". simpl.
    iSplit. goih IHe "X1". iSplit. goih IHe "X2".
    iSplit. goih IHe "X3". goih IHe "X4". }
Qed.

Lemma eininj_subst' x e e' v v' :
  eininj e e' -∗
  vininj v v' -∗
  eininj (subst' x v e) (subst' x v' e').
Proof.
  iIntros. destruct x; first done. by iApply (eininj_subst with "[$][$]").
Qed.

Lemma eininj_substs' xs e e' vs vs' :
  length xs = length vs ->
  eininj e e' -∗
  ([∗ list] v;v' ∈ vs;vs', vininj v v') -∗
  eininj (substs' (zip xs vs) e) (substs' (zip xs vs') e').
Proof.
  iIntros (Hl) "He HL".
  iInduction vs as [|] "IH" forall (xs vs' Hl).
  { iDestruct (big_sepL2_nil_inv_l with "HL") as "->". simpl.
    destruct xs; done. }
  { iDestruct (big_sepL2_cons_inv_l with "HL") as "[% [% (->&X&?)]]".
    destruct xs; try done. simpl in *.
    iApply (eininj_subst' with "[-X] X").
    iApply ("IH" with "[%] He [$]"). lia. }
Qed.

Ltac goih IH ::=
  iApply IH; [simpl; lia | set_solver].

Lemma eininj_refl e :
  locs e = ∅ ->
  ⊢ eininj e e.
Proof.
  induction e as [e IHe] using (well_founded_induction (wf_inverse_image _ nat _ expr_size PeanoNat.Nat.lt_wf_0)).
  destruct e; simpl.
  { destruct v; simpl. 1-4:naive_solver.
    iIntros. iSplit. goih (IHe v1). goih (IHe v2).
    intros. iSplit; first done. set_solver. }
  1,2:set_solver.
  all:iIntros.
  { iSplit; goih IHe. }
  { iSplit. done. iSplit; goih IHe. }
  { iSplit; last iSplit; goih IHe. }
  { iSplit; first done. iSplit; goih IHe. }
  all:repeat (iSplit; first goih IHe); goih IHe.
Qed.

Lemma vininj_refl v :
  locs v = ∅ ->
  ⊢ vininj v v.
Proof. apply (eininj_refl (Val v)). Qed.

Lemma eininj_noloc e1 e2 :
  locs e1 = ∅ ->
  eininj e1 e2 -∗ ⌜e1=e2⌝.
Proof.
  revert e2. induction e1 as [e IHe] using (well_founded_induction (wf_inverse_image _ nat _ expr_size PeanoNat.Nat.lt_wf_0)).
  iIntros (e2 Hl) "He". destruct e; simpl.
  { destruct e2; try done.
    destruct v; simpl.
    { iDestruct "He" as "%E". inversion E. done. }
    { iDestruct "He" as "%E". inversion E. done. }
    { iDestruct "He" as "%E". inversion E. done. }
    { exfalso. naive_solver. }
    { destruct v0.
      all:try iDestruct "He" as "%"; try naive_solver.
      iDestruct "He" as "(X1&X2)".
      iDestruct (IHe (Val v1) _ (Val _) with "X1") as "%". set_solver.
      iDestruct (IHe (Val v2) _ (Val _) with "X2") as "%". set_solver.
      subst. iPureIntro. naive_solver.
      Unshelve. all:simpl; lia. }
    { destruct v0.
      all:try iDestruct "He" as "%"; try naive_solver.
      iDestruct "He" as "((->&->)&?)".
      iDestruct (IHe with "[$]") as "->". simpl. lia. set_solver. done. } }
  { destruct e2.
    all:try iDestruct "He" as "%"; try naive_solver.
    iDestruct "He" as "((->&->)&?)".
    iDestruct (IHe with "[$]") as "->". simpl. lia. set_solver. done. }
  { destruct e2; try done. iDestruct "He" as "->". eauto. }
  { destruct e2; try done.
    iDestruct "He" as "(X1&X2)".
    iDestruct (IHe with "X1") as "->". simpl. lia. set_solver.
    iDestruct (IHe with "X2") as "->". simpl. lia. set_solver.
    done. }
  { destruct e2; try done.
    iDestruct "He" as "(->&X1&X2)".
    iDestruct (IHe with "X1") as "->". simpl. lia. set_solver.
    iDestruct (IHe with "X2") as "->". simpl. lia. set_solver.
    done. }
  { destruct e2; try done.
    iDestruct "He" as "(X1&X2&X3)".
    iDestruct (IHe with "X1") as "->". simpl. lia. set_solver.
    iDestruct (IHe with "X2") as "->". simpl. lia. set_solver.
    iDestruct (IHe with "X3") as "->". simpl. lia. set_solver.
    done. }
  { destruct e2; try done.
    iDestruct "He" as "(->&X1&X2)".
    iDestruct (IHe with "X1") as "->". simpl. lia. set_solver.
    iDestruct (IHe with "X2") as "->". simpl. lia. set_solver.
    done. }
  { destruct e2; try done.
    iDestruct "He" as "(X1&X2)".
    iDestruct (IHe with "X1") as "->". simpl. lia. set_solver.
    iDestruct (IHe with "X2") as "->". simpl. lia. set_solver.
    done. }
  { destruct e2; try done.
    iDestruct (IHe with "He") as "->". simpl. lia. set_solver.
    done. }
  { destruct e2; try done.
    iDestruct (IHe with "He") as "->". simpl. lia. set_solver.
    done. }
  { destruct e2; try done.
    iDestruct (IHe with "He") as "->". simpl. lia. set_solver.
    done. }
  { destruct e2; try done.
    iDestruct "He" as "(X1&X2)".
    iDestruct (IHe with "X1") as "->". simpl. lia. set_solver.
    iDestruct (IHe with "X2") as "->". simpl. lia. set_solver.
    done. }
  { destruct e2; try done.
    iDestruct "He" as "(X1&X2&X3)".
    iDestruct (IHe with "X1") as "->". simpl. lia. set_solver.
    iDestruct (IHe with "X2") as "->". simpl. lia. set_solver.
    iDestruct (IHe with "X3") as "->". simpl. lia. set_solver.
    done. }
  { destruct e2; try done.
    iDestruct (IHe with "He") as "->". simpl. lia. set_solver.
    done. }
  { destruct e2; try done.
    iDestruct (IHe with "He") as "->". simpl. lia. set_solver.
    done. }
  { destruct e2; try done.
    iDestruct "He" as "(X1&X2)".
    iDestruct (IHe with "X1") as "->". simpl. lia. set_solver.
    iDestruct (IHe with "X2") as "->". simpl. lia. set_solver.
    done. }
  { destruct e2; try done.
    iDestruct "He" as "(X1&X2)".
    iDestruct (IHe with "X1") as "->". simpl. lia. set_solver.
    iDestruct (IHe with "X2") as "->". simpl. lia. set_solver.
    done. }
  { destruct e2; try done.
    iDestruct "He" as "(X1&X2&X3&X4)".
    iDestruct (IHe with "X1") as "->". simpl. lia. set_solver.
    iDestruct (IHe with "X2") as "->". simpl. lia. set_solver.
    iDestruct (IHe with "X3") as "->". simpl. lia. set_solver.
    iDestruct (IHe with "X4") as "->". simpl. lia. set_solver.
    done. }
Qed.

Lemma vininj_noloc v1 v2 :
  locs v1 = ∅ ->
  vininj v1 v2 -∗ ⌜v1 = v2⌝.
Proof.
  iIntros.
  iDestruct (eininj_noloc (Val _) (Val _) with "[$]") as "%X". done.
  inversion X. eauto.
Qed.

Lemma ininj_partial_func l l1 l2 :
  ininj l l1 -∗ ininj l l2 -∗ ⌜l1=l2⌝.
Proof.
  iIntros "(E1&_) (E2&_)".
  iDestruct (ghost_map_elem_valid_2 with "E1 E2") as "(_&%)".
  done.
Qed.

Lemma ininj_is_inj l l1 l2 :
  ininj l1 l -∗ ininj l2 l -∗ ⌜l1=l2⌝.
Proof.
  iIntros "(_&E1) (_&E2)".
  iDestruct (ghost_map_elem_valid_2 with "E1 E2") as "(_&%)".
  eauto.
Qed.

Lemma img_in_mono g1 g2 σ :
  img_in g1 σ ->
  g1 ⊆ g2 ->
  img_in g2 σ.
Proof.
  intros. eapply map_Forall_impl. done.
  set_solver.
Qed.

Lemma ininj_insert_waiting l g1 g2 :
  l ∉ g1 ->
  interp_inj g1 g2 ==∗
  interp_inj ({[l]} ∪ g1) g2 ∗ waiting l.
Proof.
  iIntros (?) "[%α [% (X1&X2&?&(%&%))]]".
  iMod (own_update with "[$]") as "[? ?]".
  { apply auth_update_alloc.
    apply gset_disj_alloc_empty_local_update with (Z := {[l]}).
    apply disjoint_singleton_l. set_solver. }
  replace ({[l]} ∪ g1 ∖ dom α) with (({[l]} ∪ g1) ∖ dom α).
  2:{ rewrite difference_union_distr_l_L.
      assert (({[l]} ∖ dom α) = {[l]}) as ->. set_solver. done. }
  iFrame. iPureIntro. set_solver.
Qed.

Lemma ininj_insert_inj l l' g1 g2 :
  l' ∉ g2 ->
  waiting l -∗
  interp_inj g1 g2 ==∗
  interp_inj g1 ({[l']} ∪ g2) ∗ ininj l l'.
Proof.
  iIntros (?) "Hw [%α1 [%α2 (X1&X2&Hwait&(%&%))]]".

  iDestruct (own_valid_2 with "Hwait Hw") as "%Hv".
  apply auth_both_valid_discrete in Hv. destruct Hv as (Hv&_).
  apply gset_disj_included in Hv.

  iMod (own_update_2 with "Hwait Hw") as "?".
  { apply auth_update_dealloc.
    apply gset_disj_dealloc_local_update. }

  iMod (ghost_map_insert l l' with "X1") as "(?&X1)".
  { apply not_elem_of_dom. set_solver. }

  iMod (ghost_map_insert l' l with "X2") as "(?&X2)".
  { apply not_elem_of_dom. set_solver. }

  iMod (ghost_map_elem_persist with "X1") as "?".
  iMod (ghost_map_elem_persist with "X2") as "?".
  replace (g1 ∖ dom α1 ∖ {[l]}) with (g1 ∖ ({[l]} ∪ dom α1)) by set_solver.
  iFrame. rewrite dom_insert_L. iFrame.
  iPureIntro.
  split_and !.
  { set_solver. }
  { rewrite dom_insert_L. set_solver. }
Qed.

Lemma eininj_partial_func e x1 x2 :
  eininj e x1 -∗ eininj e x2 -∗
  ⌜x1 = x2⌝.
Proof.
  revert e x1 x2.
  apply (expr_rec_strong
    (fun e => ∀ x1 x2, eininj e x1 -∗ eininj e x2 -∗ ⌜x1 = x2⌝)
    (fun v => ∀ x1 x2, vininj v x1 -∗ vininj v x2 -∗ ⌜x1 = x2⌝)).
  { iIntros (v IH x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct (IH with "X1 X2") as "->". done. }
  { iIntros (?? e IH x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "((->&->)&X1)".
    iDestruct "X2" as "((->&->)&X2)".
    iDestruct (IH with "X1 X2") as "->". done. }
  { iIntros (? x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "->". iDestruct "X2" as "->". done. }
  { iIntros (e1 IH1 e2 IH2 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(?&?)". iDestruct "X2" as "(?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->". done. }
  { iIntros (p e1 IH1 e2 IH2 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(->&?&?)".
    iDestruct "X2" as "(->&?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->". done. }
  { iIntros (e1 IH1 e2 IH2 e3 IH3 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(?&?&?)".
    iDestruct "X2" as "(?&?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->".
    iDestruct (IH3 with "[$][$]") as "->". done. }
  { iIntros (?? IH1 ? IH2 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(->&?&?)".
    iDestruct "X2" as "(->&?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->". done. }
  { iIntros (? IH1 ? IH2 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(?&?)".
    iDestruct "X2" as "(?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->". done. }
  { iIntros (? IH x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct (IH with "[$][$]") as "->". done. }
  { iIntros (? IH x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct (IH with "[$][$]") as "->". done. }
  { iIntros (? IH x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct (IH with "[$][$]") as "->". done. }
  { iIntros (? IH1 ? IH2 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(?&?)".
    iDestruct "X2" as "(?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->". done. }
  { iIntros (e1 IH1 e2 IH2 e3 IH3 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(?&?&?)".
    iDestruct "X2" as "(?&?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->".
    iDestruct (IH3 with "[$][$]") as "->". done. }
  { iIntros (? IH x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct (IH with "[$][$]") as "->". done. }
  { iIntros (? IH x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct (IH with "[$][$]") as "->". done. }
  { iIntros (? IH1 ? IH2 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(?&?)".
    iDestruct "X2" as "(?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->". done. }
  { iIntros (? IH1 ? IH2 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(?&?)".
    iDestruct "X2" as "(?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->". done. }
  { iIntros (e1 IH1 e2 IH2 e3 IH3 e4 IH4 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(?&?&?&?)".
    iDestruct "X2" as "(?&?&?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->".
    iDestruct (IH3 with "[$][$]") as "->".
    iDestruct (IH4 with "[$][$]") as "->". done. }
  { iIntros (x1 x2) "<- <-". done. }
  { iIntros (? x1 x2) "X1 X2".
    destruct x1; try (iDestruct "X1" as "%"; congruence).
    destruct x2; try (iDestruct "X2" as "%"; congruence).
    iDestruct "X1" as "->". iDestruct "X2" as "->". done. }
  { iIntros (? x1 x2) "X1 X2".
    destruct x1; try (iDestruct "X1" as "%"; congruence).
    destruct x2; try (iDestruct "X2" as "%"; congruence).
    iDestruct "X1" as "->". iDestruct "X2" as "->". done. }
  { iIntros (? x1 x2) "X1 X2".
    destruct x1; try (iDestruct "X1" as "%"; congruence).
    destruct x2; try (iDestruct "X2" as "%"; congruence). simpl.
    iDestruct (ininj_partial_func with "[$][$]") as "->". done. }
  { iIntros (v1 IH1 v2 IH2 x1 x2) "X1 X2".
    destruct x1; try (iDestruct "X1" as "%"; congruence).
    destruct x2; try (iDestruct "X2" as "%"; congruence). simpl.
    iDestruct "X1" as "(?&?)".
    iDestruct "X2" as "(?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->". done. }
  { iIntros (??? IH x1 x2) "X1 X2".
    destruct x1; try (iDestruct "X1" as "%"; congruence).
    destruct x2; try (iDestruct "X2" as "%"; congruence). simpl.
    iDestruct "X1" as "((->&->)&?)".
    iDestruct "X2" as "((->&->)&?)".
    iDestruct (IH with "[$][$]") as "->". done. }
Qed.

Lemma eininj_inj e x1 x2 :
  eininj x1 e -∗ eininj x2 e -∗
  ⌜x1 = x2⌝.
Proof.
  revert e x1 x2.
  apply (expr_rec_strong
    (fun e => ∀ x1 x2, eininj x1 e -∗ eininj x2 e -∗ ⌜x1 = x2⌝)
    (fun v => ∀ x1 x2, vininj x1 v -∗ vininj x2 v -∗ ⌜x1 = x2⌝)).
  { iIntros (v IH x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct (IH with "X1 X2") as "->". done. }
  { iIntros (?? e IH x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "((->&->)&X1)".
    iDestruct "X2" as "((->&->)&X2)".
    iDestruct (IH with "X1 X2") as "->". done. }
  { iIntros (? x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "->". iDestruct "X2" as "->". done. }
  { iIntros (e1 IH1 e2 IH2 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(?&?)". iDestruct "X2" as "(?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->". done. }
  { iIntros (p e1 IH1 e2 IH2 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(->&?&?)".
    iDestruct "X2" as "(->&?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->". done. }
  { iIntros (e1 IH1 e2 IH2 e3 IH3 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(?&?&?)".
    iDestruct "X2" as "(?&?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->".
    iDestruct (IH3 with "[$][$]") as "->". done. }
  { iIntros (?? IH1 ? IH2 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(->&?&?)".
    iDestruct "X2" as "(->&?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->". done. }
  { iIntros (? IH1 ? IH2 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(?&?)".
    iDestruct "X2" as "(?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->". done. }
  { iIntros (? IH x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct (IH with "[$][$]") as "->". done. }
  { iIntros (? IH x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct (IH with "[$][$]") as "->". done. }
  { iIntros (? IH x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct (IH with "[$][$]") as "->". done. }
  { iIntros (? IH1 ? IH2 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(?&?)".
    iDestruct "X2" as "(?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->". done. }
  { iIntros (e1 IH1 e2 IH2 e3 IH3 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(?&?&?)".
    iDestruct "X2" as "(?&?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->".
    iDestruct (IH3 with "[$][$]") as "->". done. }
  { iIntros (? IH x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct (IH with "[$][$]") as "->". done. }
  { iIntros (? IH x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct (IH with "[$][$]") as "->". done. }
  { iIntros (? IH1 ? IH2 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(?&?)".
    iDestruct "X2" as "(?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->". done. }
  { iIntros (? IH1 ? IH2 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(?&?)".
    iDestruct "X2" as "(?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->". done. }
  { iIntros (e1 IH1 e2 IH2 e3 IH3 e4 IH4 x1 x2) "X1 X2".
    destruct x1; try done. destruct x2; try done. simpl.
    iDestruct "X1" as "(?&?&?&?)".
    iDestruct "X2" as "(?&?&?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->".
    iDestruct (IH3 with "[$][$]") as "->".
    iDestruct (IH4 with "[$][$]") as "->". done. }
  { iIntros (x1 x2) "X1 X2".
    destruct x1; try (iDestruct "X1" as "%"; congruence).
    destruct x2; try (iDestruct "X2" as "%"; congruence).
    done. }
  { iIntros (? x1 x2) "X1 X2".
    destruct x1; try (iDestruct "X1" as "%"; congruence).
    destruct x2; try (iDestruct "X2" as "%"; congruence).
    iDestruct "X1" as "->". iDestruct "X2" as "->". done. }
  { iIntros (? x1 x2) "X1 X2".
    destruct x1; try (iDestruct "X1" as "%"; congruence).
    destruct x2; try (iDestruct "X2" as "%"; congruence).
    iDestruct "X1" as "->". iDestruct "X2" as "->". done. }
  { iIntros (? x1 x2) "X1 X2".
    destruct x1; try (iDestruct "X1" as "%"; congruence).
    destruct x2; try (iDestruct "X2" as "%"; congruence). simpl.
    iDestruct (ininj_is_inj with "[$][$]") as "->". done. }
  { iIntros (v1 IH1 v2 IH2 x1 x2) "X1 X2".
    destruct x1; try (iDestruct "X1" as "%"; congruence).
    destruct x2; try (iDestruct "X2" as "%"; congruence). simpl.
    iDestruct "X1" as "(?&?)".
    iDestruct "X2" as "(?&?)".
    iDestruct (IH1 with "[$][$]") as "->".
    iDestruct (IH2 with "[$][$]") as "->". done. }
  { iIntros (??? IH x1 x2) "X1 X2".
    destruct x1; try (iDestruct "X1" as "%"; congruence).
    destruct x2; try (iDestruct "X2" as "%"; congruence). simpl.
    iDestruct "X1" as "((->&->)&?)".
    iDestruct "X2" as "((->&->)&?)".
    iDestruct (IH with "[$][$]") as "->". done. }
Qed.

Lemma vininj_partial_func v x1 x2 :
  vininj v x1 -∗ vininj v x2 -∗
  ⌜x1 = x2⌝.
Proof.
  iIntros "X1 X2".
  iDestruct (eininj_partial_func (Val _) (Val _) (Val _) with "X1 X2") as "%".
  naive_solver.
Qed.

Lemma vininj_inj v x1 x2 :
  vininj x1 v -∗ vininj x2 v -∗
  ⌜x1 = x2⌝.
Proof.
  iIntros "X1 X2".
  iDestruct (eininj_inj (Val _) (Val _) (Val _) with "X1 X2") as "%".
  naive_solver.
Qed.

Lemma vininj_preserves_eq v1 v2 v1' v2' g1 g2 :
  vininj v1 v1' -∗ vininj v2 v2' -∗ interp_inj g1 g2 -∗
  ⌜v1 = v2 <-> v1' = v2'⌝.
Proof.
  iIntros "X1 X2 ?".
  destruct_decide (decide (v1=v2)).
  { subst. iDestruct (vininj_partial_func with "X1 X2") as "->". done. }
  { destruct_decide (decide (v1'=v2')); last done.
    subst. iExFalso.
    iDestruct (vininj_inj with "X1 X2") as "%". done. }
Qed.

Lemma ininj_preserve_call_prim g1 g2 p v1 v2 v1' v2' v:
  eval_call_prim p v1 v2 = Some v ->
  vininj v1 v1' ∗
  vininj v2 v2' -∗
  interp_inj g1 g2 -∗
  ⌜eval_call_prim p v1' v2' = Some v⌝.
Proof.
  iIntros (Hv) "(E1&E2) Hi".
  destruct p; simpl in *.
  { inversion Hv. subst.
    iDestruct (vininj_preserves_eq with "E1 E2 Hi") as "%E".
    iPureIntro. f_equal. do 2 case_bool_decide; naive_solver. }
  { destruct v1; try done.
    destruct v2; try done.
    iDestruct "E1" as "<-". iDestruct "E2" as "<-". done. }
  { destruct v1; try done.
    destruct v2; try done.
    iDestruct "E1" as "<-". iDestruct "E2" as "<-". done. }
  { destruct v1; try done.
    destruct v2; try done.
    iDestruct "E1" as "<-". iDestruct "E2" as "<-". done. }
Qed.

Lemma eininj_atomic e e' :
  Atomic e ∨ is_val e ->
  eininj e e' -∗
  ⌜ Atomic e' ∨ is_val e' ⌝.
Proof.
  iIntros (Ha) "Hi". destruct e,e'; simpl in *; try done.
  { eauto. }
  all:rewrite right_id in Ha; rewrite right_id; inversion Ha; subst.
  { iDestruct "Hi" as "(->&?&?)".
    destruct e'1; try done. destruct e'2; try done.
    eauto using Atomic. }
  { iDestruct "Hi" as "(X1&X2)".
    destruct e'1; try done. destruct e'2; try done.
    destruct v; try (iDestruct "X1" as "%"; congruence).
    destruct v0; try (iDestruct "X2" as "%"; congruence).
    eauto using Atomic. }
  { iDestruct "Hi" as "(X1&X2&X3)".
    destruct e'1; try done. destruct e'2; try done. destruct e'3; try done.
    destruct v0; try (iDestruct "X1" as "%"; congruence).
    destruct v1; try (iDestruct "X2" as "%"; congruence).
    eauto using Atomic. }
  { simpl.
    destruct e'; try done.
    destruct v; try (iDestruct "Hi" as "%"; congruence).
    eauto using Atomic. }
  { iDestruct "Hi" as "(X1&X2&X3&X4)".
    destruct e'1; try done. destruct e'2; try done.
    destruct e'3; try done. destruct e'4; try done.
    destruct v; try (iDestruct "X1" as "%"; congruence).
    destruct v0; try (iDestruct "X2" as "%"; congruence).
    eauto using Atomic. }
Qed.

Lemma eininj_val e e' :
  is_val e ->
  eininj e e' -∗
  ⌜ is_val e' ⌝.
Proof.
  iIntros (Ha) "Hi". destruct e,e'; simpl in *; done.
Qed.

Lemma eininj_not_val e e' :
  ¬ is_val e ->
  eininj e e' -∗
  ⌜ ¬ is_val e' ⌝.
Proof.
  iIntros (Ha) "Hi". destruct e,e'; simpl in *; done.
Qed.

End go.

Module Initialization.

Definition inInjΣ : gFunctors :=
  #[  ghost_mapΣ loc loc;
      GFunctor (authUR (gset_disjR loc)) ].

Class inInjpreG (Σ:gFunctors) :=
  { pi4 : ghost_mapG Σ loc loc;
    pi5 : inG Σ (authUR (gset_disjR loc))}.

#[local] Existing Instance pi4.
#[local] Existing Instance pi5.

Global Instance subG_inInjGpre Σ :
  subG inInjΣ Σ → inInjpreG Σ.
Proof. solve_inG. Qed.

Global Instance inInjGpre_inInjΣ : inInjpreG inInjΣ.
Proof. eauto with typeclass_instances. Qed.

Lemma ininj_alloc `{inInjpreG Σ} :
  ⊢ |==> ∃ (H:inInjG Σ), interp_inj ∅ ∅.
Proof.
  iStartProof.
  iMod (@ghost_map_alloc_empty _ loc loc _ _ _) as "[%γinj1 ?]".
  iMod (@ghost_map_alloc_empty _ loc loc _ _ _) as "[%γinj2 ?]".
  iMod (own_alloc (● (GSet ∅))) as "[%γsep Ht]".
  { by apply auth_auth_valid. }
  iModIntro. iExists (InInjG _ _ _ _ _ _). iFrame.
  rewrite !dom_empty_L difference_empty_L. iFrame.
  iPureIntro. split_and !.
  { set_solver. }
  { intros ??. set_solver. }
Qed.

End Initialization.
