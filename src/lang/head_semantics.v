From Coq.ssr Require Import ssreflect.
From stdpp Require Import strings binders gmap gmultiset sets ssreflect.

From intdet.lang Require Export syntax syntax_instances.

Notation store := (gmap loc (list val)).
Implicit Type σ : store.

(******************************************************************************)
(* semantics of primitives *)

Definition exec_int_op op :=
  match op with
  | IntAdd => Z.add
  | IntMul => Z.mul
  | IntSub => Z.sub
  | IntDiv => Z.div
  | IntMod => Z.modulo
  | IntMin => Z.min
  | IntMax => Z.max end.

Definition exec_int_cmp op :=
  match op with
  | IntLt => Z.ltb
  | IntLe => Z.leb
  | IntGt => Z.gtb
  | IntGe => Z.geb end.

Definition exec_bool_bin_op op :=
  match op with
  | BoolAnd => andb
  | BoolOr => orb end.

Definition eval_call_prim p (v1 v2:val) :=
  match p,v1,v2 with
  | PrimBoolOp op, VBool b1, VBool b2 => Some (VBool (exec_bool_bin_op op b1 b2))
  | PrimIntOp op, VInt m, VInt n => Some (VInt (exec_int_op op m n))
  | PrimIntCmp op, VInt m, VInt n => Some (VBool (exec_int_cmp op m n))
  | PrimEq, v1, v2 => Some (VBool (bool_decide (v1 = v2)))
  | _,_,_ => None end.

(******************************************************************************)
(* head semantics *)

(* The val option indicates if a value was loaded, and which value.
 *)
Inductive head_step : expr -> store -> expr -> store -> Prop :=
| HeadIf : forall σ (b:bool) e1 e2,
  head_step
    (If b e1 e2) σ
    (if b then e1 else e2) σ
| HeadLet : forall σ (v:val) x e,
  head_step
    (Let x v e) σ
    (subst' x v e) σ
| HeadCode : forall σ self arg code,
  head_step (Code self arg code) σ (VCode self arg code) σ
| HeadCall : forall σ v self arg code,
  head_step
    (Call (VCode self arg code) (Val v)) σ
      (substs' (zip [self;arg] [VCode self arg code;v]) code) σ
| HeadCallPrim : forall σ v1 v2 v p,
  eval_call_prim p v1 v2 = Some v ->
  head_step
    (CallPrim p v1 v2) σ
    v σ
| HeadAlloc : forall σ σ' (n:Z) (l:loc),
  (0 <= n)%Z ->
  l ∉ dom σ ->
  σ' = <[l:= (replicate (Z.to_nat n) VUnit)]> σ ->
  head_step
    (Alloc n) σ
    (Val l) σ'
| HeadLoad : forall σ (l:loc) (vs:list val) (v:val) (i:Z),
  σ !! l = Some vs ->
  (0 <= i < Z.of_nat (length vs))%Z ->
  vs !! (Z.to_nat i) = Some v ->
  head_step
    (Load l i) σ
    v σ
| HeadStore : forall σ σ' (l:loc) vs (i:Z) (v:val),
  σ !! l = Some vs ->
  (0 <= i < Z.of_nat (length vs))%Z ->
  σ' = <[l := <[Z.to_nat i := v]> vs]> σ ->
  head_step
    (Store l i v) σ
    VUnit σ'
| HeadCAS : forall σ σ' (l:loc) vs i (v v0 v':val),
  σ !! l = Some vs ->
  (0 <= i < Z.of_nat (length vs))%Z ->
  vs !! (Z.to_nat i) = Some v0 ->
  σ' = (if bool_decide (v0 = v)
        then (insert l (<[Z.to_nat i := v']> vs) σ) else σ) ->
  head_step
    (CAS l i v v') σ
    (Val (bool_decide (v0 = v))) σ'
| HeadAssert : forall σ,
  head_step (Assert true) σ VUnit σ
| HeadPair : forall (v1 v2:val) σ,
  head_step (Pair v1 v2) σ (VPair v1 v2) σ
| HeadFst : forall (v1 v2:val) σ,
  head_step (Fst (VPair v1 v2)) σ v1 σ
| HeadSnd : forall (v1 v2:val) σ,
  head_step (Snd (VPair v1 v2)) σ v2 σ
| HeadLength : forall (l:loc) (vs:list val) σ,
  σ !! l = Some vs ->
  head_step (Length l) σ (VInt (Z.of_nat (length vs))) σ
| HeadFork : forall σ e1 e2,
  head_step (Par e1 e2) σ (RunPar e1 e2) σ
| HeadJoin : forall σ (v1 v2:val),
  head_step (RunPar v1 v2) σ (VPair v1 v2) σ
.

Local Lemma middle_list {X:Type} (l:list X) x l1 l2 :
  l = l1 ++ x::l2 ->
  l !! length l1 = Some x.
Proof.
  intros ->.
  rewrite list_lookup_middle; easy.
Qed.

Lemma must_be_val vs xs e ys :
  Val <$> vs = (Val <$> xs) ++ e :: ys ->
  is_val e.
Proof.
  intros E.
  apply middle_list in E.
  rewrite list_lookup_fmap in E.
  destruct (vs !! length (Val <$> xs)); naive_solver.
Qed.

Lemma head_step_no_ctx K e σ e' σ' :
  ¬ is_val e ->
  ¬ head_step (fill_item K e) σ e' σ'.
Proof.
  intros ? Hstep. inversion Hstep; subst.
  all:destruct K; try naive_solver.
  all:inversion H0; eauto using must_be_val.
Qed.

Lemma head_step_no_val e σ e' σ' :
  head_step e σ e' σ' ->
  ¬ is_val e.
Proof. inversion 1; eauto. Qed.

#[export] Hint Constructors head_step : head_step.
