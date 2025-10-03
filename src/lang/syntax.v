From Coq Require Import Wellfounded.
From stdpp Require Import strings binders gmap gmultiset.

(* ------------------------------------------------------------------------ *)
(* Syntax of IntDet *)

(******************************************************************************)
(* Locations. *)

Inductive loc := to_loc : Z -> loc.
Definition of_loc : loc -> Z := fun '(to_loc x) => x.

(* We inherit various instances from Z. *)
#[export] Instance loc_eq_dec : EqDecision loc.
Proof. solve_decision. Qed.
#[export] Instance loc_countable : Countable loc.
Proof. apply inj_countable' with of_loc to_loc. now intros []. Qed.
#[export] Instance loc_infinite : Infinite loc.
Proof. apply inj_infinite with to_loc (fun x => Some (of_loc x)). easy. Qed.
#[export] Instance loc_inhabited : Inhabited loc := populate (to_loc inhabitant).

(******************************************************************************)
(* Primitives, expressions *)

Inductive int_op := IntAdd | IntMul | IntSub | IntDiv | IntMod | IntMin | IntMax.
Inductive int_cmp := IntLt | IntLe | IntGt | IntGe.
Inductive bool_op := BoolAnd | BoolOr.

Inductive prim :=
| PrimEq : prim
| PrimBoolOp : bool_op -> prim
| PrimIntOp : int_op -> prim
| PrimIntCmp : int_cmp -> prim.

Inductive expr :=
(* Values *)
| Val : val -> expr
| Code : binder -> binder -> expr -> expr
| Var : string -> expr
| Call : expr -> expr -> expr
| CallPrim : prim -> expr -> expr -> expr
| If : expr -> expr -> expr -> expr
| Let : binder -> expr -> expr -> expr
(* Prod *)
| Pair : expr -> expr -> expr
| Fst : expr -> expr
| Snd : expr -> expr
(* Memory *)
| Alloc : expr -> expr
| Load : expr -> expr -> expr
| Store : expr -> expr -> expr -> expr
| Length : expr -> expr
(* Assertion *)
| Assert : expr -> expr
(* Parallelism *)
| Par : expr -> expr -> expr
| RunPar : expr -> expr -> expr
| CAS : expr -> expr -> expr -> expr -> expr
with val :=
| VUnit : val
| VBool : bool -> val
| VInt : Z -> val
| VLoc : loc -> val
| VPair : val -> val -> val
| VCode : binder -> binder -> expr -> val.

Scheme expr_rec_strong := Induction for expr Sort Prop
with val_rec_strong := Induction for val Sort Prop.

Coercion VLoc : loc >-> val.
Coercion VBool : bool >-> val.
Coercion VInt : Z >-> val.

Coercion Val : val >-> expr.
Coercion Var : string >-> expr.

(* ------------------------------------------------------------------------ *)
(* [to_val], [is_val], and [is_loc] *)

Definition to_val e :=
  match e with
  | Val v => Some v
  | _ => None end.

Definition is_val e :=
  match e with
  | Val v => true
  | _ => false end.

Lemma is_val_true e :
  is_val e <-> exists v, e = Val v.
Proof. split; destruct e; naive_solver. Qed.
Lemma is_val_false e :
  ¬ is_val e <-> to_val e = None.
Proof. destruct e; naive_solver. Qed.

Definition is_loc v :=
  match v with
  | VLoc _ => true
  | _ => false end.

Lemma is_loc_inv v :
  is_loc v -> exists l, v = VLoc l.
Proof. destruct v; naive_solver. Qed.

Fixpoint expr_size (e : expr):= 1 +
  match e with
  | Var _ => 0
  | Val v => val_size v
  | Call e1 xs => expr_size e1 + expr_size xs
  | Length e1 | Alloc e1 | Assert e1 | Fst e1 | Snd e1 => expr_size e1
  | Code _ _ e1 => S (expr_size e1) (* for mcs *)
  | Load e1 e2 | CallPrim _ e1 e2 | Let _ e1 e2 | RunPar e1 e2 => expr_size e1 + expr_size e2
  | Pair e1 e2 | Par e1 e2 => 1 + expr_size e1 + expr_size e2
  | Store e1 e2 e3 | If e1 e2 e3 => expr_size e1 + expr_size e2 + expr_size e3
  | CAS e1 e2 e3 e4 => expr_size e1 + expr_size e2 + expr_size e3 + expr_size e4
  end
with val_size (v:val) :=
  match v with
  | VCode _ _ e => expr_size e
  | VPair v1 v2 => S (val_size v1 + val_size v2)
  | _ => 0 end
.

Lemma expr_size_non_zero e :
  expr_size e ≠ 0.
Proof. destruct e; simpl; lia. Qed.

(******************************************************************************)
(* Substitution. *)

Fixpoint subst (x:string) (v:val) (e:expr) : expr :=
  match e with
  | Val _ => e
  | Code y ys e' =>
      if (decide ((BNamed x) ∈ [y;ys])) then e else Code y ys (subst x v e')
  | Var y =>
      if (decide (x=y)) then v else e
  | Call e ts =>
      Call (subst x v e) (subst x v ts)
  | CallPrim p e1 e2 =>
      CallPrim p (subst x v e1) (subst x v e2)
  | If e1 e2 e3 =>
      If (subst x v e1) (subst x v e2) (subst x v e3)
  | Let y e1 e2 =>
      Let y (subst x v e1)
        (if (decide (y = BNamed x)) then e2 else subst x v e2)
  | Alloc e1 =>
      Alloc (subst x v e1)
  | Length e1 =>
      Length (subst x v e1)
  | Load e1 e2 =>
      Load (subst x v e1) (subst x v e2)
  | Store e1 e2 e3 =>
      Store (subst x v e1) (subst x v e2) (subst x v e3)
  | Assert e1 =>
      Assert (subst x v e1)
  | Fst e1 =>
      Fst (subst x v e1)
  | Snd e1 =>
      Snd (subst x v e1)
  | Pair e1 e2 =>
      Pair (subst x v e1) (subst x v e2)
  | Par e1 e2 =>
      Par (subst x v e1) (subst x v e2)
  | RunPar e1 e2 =>
      RunPar (subst x v e1) (subst x v e2)
  | CAS e1 e2 e3 e4 =>
      CAS (subst x v e1) (subst x v e2) (subst x v e3) (subst x v e4)
  end.

(* Substitution by a binder. *)
Definition subst' (x:binder) (v:val) (e:expr) :=
  match x with
  | BAnon => e
  | BNamed x => subst x v e end.

(* Iterated substitution. *)
Definition substs (xlvs : list (string * val)) (i : expr) : expr :=
  foldr (fun '(x, lv) => subst x lv) i xlvs.

Definition substs' (xlvs : list (binder * val)) (i : expr) : expr :=
  foldr (fun '(x, lv) => subst' x lv) i xlvs.

Lemma substs'_app xs ys e :
  substs' (xs ++ ys) e = substs' xs (substs' ys e).
Proof. apply foldr_app. Qed.

(* ------------------------------------------------------------------------ *)
(* Contexts. *)

(* Contexts are syntactically non-recursive. *)
Inductive ctx :=
| CtxCall1 : expr -> ctx (* call e ◻ *)
| CtxCall2 : val -> ctx (* call ◻ v *)
| CtxCallPrim1 : prim -> expr -> ctx (* call_prim p e ◻ *)
| CtxCallPrim2 : prim -> val -> ctx (* call_prim p ◻ v *)
| CtxIf : expr -> expr -> ctx (* if ◻ then e1 else e2 *)
| CtxLet : binder -> expr -> ctx (* let x = ◻ in e2 *)
| CtxAlloc : ctx (* alloc ◻ *)
| CtxFst : ctx (* alloc ◻ *)
| CtxSnd : ctx (* alloc ◻ *)
| CtxPair1 : expr -> ctx (* Pair e ◻ *)
| CtxPair2 : val -> ctx (* Pair ◻ v *)
| CtxLoad1 : expr -> ctx (* load e ◻ *)
| CtxLoad2 : val -> ctx (* load ◻ v *)
| CtxStore1 : expr -> expr -> ctx (* store e1 e2 ◻ *)
| CtxStore2 : expr -> val -> ctx (* store e1 ◻ v3 *)
| CtxStore3 : val -> val -> ctx (* store ◻ v2 v3 *)
| CtxAssert : ctx
| CtxLength : ctx
| CtxCas1 : expr -> expr -> expr -> ctx (* cas e1 e2 e3 ◻ *)
| CtxCas2 : expr -> expr -> val -> ctx (* cas e1 e2 ◻ v4  *)
| CtxCas3 : expr -> val -> val -> ctx (* cas e1 ◻ v3 v4  *)
| CtxCas4 : val -> val -> val -> ctx (* cas ◻ v2 v3 v4 *)
.

Definition fill_item (k:ctx) (e:expr) : expr :=
  match k with
  | CtxCall1 e' => Call e' e
  | CtxCall2 v => Call e v
  | CtxCallPrim1 p e1 => CallPrim p e1 e
  | CtxCallPrim2 p v => CallPrim p e v
  | CtxAssert => Assert e
  | CtxIf e2 e3 => If e e2 e3
  | CtxLet x e2 => Let x e e2
  | CtxAlloc => Alloc e
  | CtxFst => Fst e
  | CtxSnd => Snd e
  | CtxLength => Length e
  | CtxPair1 e1 => Pair e1 e
  | CtxPair2 v => Pair e v
  | CtxLoad1 e2 => Load e2 e
  | CtxLoad2 v => Load e (Val v)
  | CtxStore1 e1 e2 => Store e1 e2 e
  | CtxStore2 e1 v3 => Store e1 e (Val v3)
  | CtxStore3 v2 v3 => Store e (Val v2) (Val v3)
  | CtxCas1 e1 e2 e3 => CAS e1 e2 e3 e
  | CtxCas2 e1 e2 v4 => CAS e1 e2 e v4
  | CtxCas3 e1 v3 v4 => CAS e1 e v3 v4
  | CtxCas4 v2 v3 v4 => CAS e v2 v3 v4 end.

Lemma to_val_fill_item K e:
  to_val (fill_item K e) = None.
Proof. by destruct K. Qed.

Lemma ctx_list_length xs xs' e e' ys ys' :
  ¬ is_val e ->
  ¬ is_val e' ->
  (Val <$> xs) ++ e :: ys = (Val <$> xs') ++ e' :: ys' ->
  length xs = length xs'.
Proof.
  revert xs' e e' ys ys'.
  induction xs; intros.
  all: destruct xs'; naive_solver.
Qed.

(* [fill_item] is injective for non-values. *)
Lemma fill_item_inj K1 K2 e1 e2 :
  ¬ is_val e1 ->
  ¬ is_val e2 ->
  fill_item K1 e1 = fill_item K2 e2 ->
  K1=K2 /\ e1 = e2.
Proof.
  intros ? ? E.
  assert (Inj eq eq Val) as Hinj.
  { intros ? ? Heq'. injection Heq'. easy. }
  destruct K1,K2; inversion E; subst; simpl in *; try naive_solver.
Qed.

Definition fill_items (ks:list ctx) (e:expr) := List.fold_right fill_item e ks.

Lemma fill_items_app ks1 ks2 e :
  fill_items (ks1 ++ ks2) e = fill_items ks1 (fill_items ks2 e).
Proof. revert ks2. induction ks1; intros; simpl; first done. by rewrite IHks1. Qed.

(* ------------------------------------------------------------------------ *)

(* elim_ctx_sure tries to find a context, destruct it, and solve the goal. *)
Ltac elim_ctx_sure :=
  match goal with
  | K : ctx |- _ => destruct K; naive_solver end.
(* elim_ctx tries elim_ctx_sure *)
Ltac elim_ctx := try (exfalso; elim_ctx_sure).

(* ------------------------------------------------------------------------ *)

Definition binder_set (b:binder) : gset string :=
  match b with
  | BAnon => ∅
  | BNamed s => {[s]} end.

Fixpoint fv (e:expr) : gset string :=
  match e with
  | Val _ => ∅
  | Code x xs e => fv e ∖ (binder_set x ∪ binder_set xs)
  | Var x => {[x]}
  | Call x x0 => fv x ∪ fv x0
  | CallPrim x x0 x1 => fv x0 ∪ fv x1
  | If x x0 x1 => fv x ∪ fv x0 ∪ fv x1
  | Let x x0 x1 => fv x0 ∪ (fv x1 ∖ binder_set x)
  | Alloc x | Fst x | Snd x => fv x
  | Pair x x1 | Load x x1 => fv x ∪ fv x1
  | Store x x0 x1 => fv x ∪ fv x0 ∪ fv x1
  | Assert x => fv x
  | Length x => fv x
  | Par x x0 => fv x ∪ fv x0
  | RunPar x x0 => fv x ∪ fv x0
  | CAS x x0 x1 x2 => fv x ∪ fv x0 ∪ fv x1 ∪ fv x2
  end.
