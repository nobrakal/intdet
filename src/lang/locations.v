From Coq Require Import Wellfounded.
From stdpp Require Import base ssreflect sets gmap.
From intdet.lang Require Import semantics.
From intdet.utils Require Import more_maps_and_sets.

(******************************************************************************)
(* Locations *)
(* We define a typeclass for [locs], a function returning a set of locations. *)
Class Location A := locs : A -> gset loc.
Global Instance location_list  `{Location A} : Location (list A) :=
  fun xs => ⋃ (locs <$> xs).
Global Instance location_loc : Location loc := gset_singleton.

Fixpoint locs_expr (e:expr) : gset loc :=
  match e with
  | Val v => locs_val v
  | Var _ => ∅
  | Length e1 | Fst e1 | Snd e1 | Alloc e1 | Assert e1 | Code _ _ e1 => locs_expr e1
  | Store e1 e2 e3 | If e1 e2 e3  => locs_expr e1 ∪ locs_expr e2 ∪ locs_expr e3
  | Pair e1 e2 | Load e1 e2 | CallPrim _ e1 e2 | Let _ e1 e2
  | Par e1 e2 | RunPar e1 e2 => locs_expr e1 ∪ locs_expr e2
  | Call e1 e2 => locs_expr e1 ∪ locs_expr e2
  | CAS e1 e2 e3 e4 => locs_expr e1 ∪ locs_expr e2 ∪ locs_expr e3 ∪ locs_expr e4
  end
with locs_val (v:val) :=
  match v with
  | VUnit | VInt _ | VBool _ => ∅
  | VLoc l => {[l]}
  | VPair v1 v2 => locs_val v1 ∪ locs_val v2
  | VCode _ _ e => locs_expr e end.
Global Instance location_expr : Location expr := locs_expr.
Global Instance location_val : Location val := locs_val.
Definition locs_ctx (k:ctx) : gset loc :=
  match k with
  | CtxCall1 e => locs e
  | CtxCall2 x => locs x
  | CtxCallPrim1 _ x0 => locs x0
  | CtxCallPrim2 _ x0 => locs x0
  | CtxIf x x0 => locs x ∪ locs x0
  | CtxLet _ x0 => locs x0
  | CtxAssert | CtxAlloc | CtxFst | CtxSnd | CtxLength => ∅
  | CtxPair1 x => locs x
  | CtxPair2 x => locs x
  | CtxLoad1 x => locs x
  | CtxLoad2 x => locs x
  | CtxStore1 x x0 => locs x ∪ locs x0
  | CtxStore2 x x0 => locs x ∪ locs x0
  | CtxStore3 x x0 => locs x ∪ locs x0
  | CtxCas1 x x0 x1 => locs x ∪ locs x0 ∪ locs x1
  | CtxCas2 x x0 x1 => locs x ∪ locs x0 ∪ locs x1
  | CtxCas3 x x0 x1 => locs x ∪ locs x0 ∪ locs x1
  | CtxCas4 x x0 x1 => locs x ∪ locs x0 ∪ locs x1
  end.
Global Instance location_ctx : Location ctx := locs_ctx.
Local Lemma union_list_locs_particular l :
  ⋃ (locs_expr <$> (Val <$> l)) = locs l.
Proof. induction l; set_solver. Qed.
Lemma locs_fill_item K e :
  locs (fill_item K e) = locs K ∪ locs e.
Proof.
  destruct K; try set_solver; simpl.
  all: unfold locs,location_expr,location_ctx; simpl.
Qed.

(* ------------------------------------------------------------------------ *)
(* Facts of substitution. *)
Local Ltac ih_for H x v e :=
  assert (locs (subst x v e) ⊆ locs v ∪ locs e) by (apply H; simpl; lia).
(* No equality, as we don't know if x occurs in v. *)
Lemma locs_subst x v e :
  locs (subst x v e) ⊆ locs v ∪ locs e.
Proof.
  induction e; simpl.
  2,3,7: case_decide; set_solver.
  all:set_solver.
Qed.

Lemma location_list_val vs :
  ⋃ (location_expr <$> (Val <$> vs)) = location_list vs.
Proof. induction vs; set_solver. Qed.

Lemma locs_subst' x v e :
  locs (subst' x v e) ⊆ locs v ∪ locs e.
Proof. destruct x. set_solver. apply locs_subst. Qed.

Lemma locs_substs' xs e :
  locs (substs' xs e) ⊆ locs xs.*2 ∪ locs e.
Proof.
  revert e. induction xs as [|(?,?)]; intros; simpl.
  { set_solver. }
  { etrans. apply locs_subst'. set_solver. }
Qed.

(******************************************************************************)

Lemma head_step_grow_store e σ e' σ' :
  head_step e σ e' σ' ->
  dom σ ⊆ dom σ'.
Proof.
  inversion 1; subst; try done.
  1,2:rewrite dom_insert_L; set_solver.
  case_bool_decide; last done.
  rewrite dom_insert_L; set_solver.
Qed.

Lemma step_grow_store e σ e' σ' :
  step e σ e' σ' ->
  dom σ ⊆ dom σ'.
Proof.
  induction 1; try done.
  eauto using head_step_grow_store.
Qed.

Lemma eval_call_prim_no_loc p v1 v2 v :
  eval_call_prim p v1 v2 = Some v ->
  locs v = ∅.
Proof.
  destruct p,v1,v2,v; simpl; try done.
Qed.
