From stdpp Require Import gmap binders.
From iris.prelude Require Import options.

From intdet.lang Require Import syntax utils notations.
From intdet.examples Require Export reference.

Inductive strongness := Weak | Strong.

Inductive typ :=
  | TUnit : typ
  | TInt : typ
  | TBool : typ
  | TProd : typ -> typ -> typ
(*  | TSum : typ -> typ -> typ *)
  (* What about strongness polymorphism? *)
  | TArrow : strongness -> typ -> typ -> typ
(*  | TRec (τ : {bind 1 of typ})
  | TVar (x : var)
  | TForall (τ : {bind 1 of typ})
  | TExist (τ : {bind 1 of typ}) *)
  | TRef : typ -> typ.

Definition prim_typed p (τ1 τ2 τ:typ) :=
  match p with
  | PrimEq => τ1=τ2 /\ τ=TBool
  | PrimBoolOp _ => τ1=TBool /\ τ2=TBool /\ τ=TBool
  | PrimIntOp _ => τ1=TInt /\ τ2=TInt /\ τ=TInt
  | PrimIntCmp _ => τ1=TInt /\ τ2=TInt /\ τ=TBool
  end.

Inductive typed : strongness -> gmap string typ -> expr -> typ -> Prop :=
| TYVar : forall m Γ (x:string) τ,
  Γ !! x = Some τ ->
  typed m Γ x τ
| TYUnit : forall m Γ,
  typed m Γ VUnit TUnit
| TYBool : forall m Γ b,
  typed m Γ (VBool b) TBool
| TYInt : forall m Γ i,
  typed m Γ (VInt i) TInt
| TYLet : forall m Γ x e1 e2 τ τ',
  typed m Γ e1 τ' ->
  typed m (binsert x τ' Γ) e2 τ ->
  typed m Γ (Let x e1 e2) τ
| TYIf : forall m Γ e1 e2 e3 τ,
  typed m Γ e1 TBool ->
  typed m Γ e2 τ ->
  typed m Γ e3 τ ->
  typed m Γ (If e1 e2 e3) τ
| TYCallPrim : forall m Γ e1 e2 p τ1 τ2 τ,
  prim_typed p τ1 τ2 τ ->
  typed m Γ e1 τ1 ->
  typed m Γ e2 τ2 ->
  typed m Γ (CallPrim p e1 e2) τ
| TYAbs : forall Γ m m' self arg code τ τ',
  (m = Strong -> m' = Strong) ->
  typed m' (extend [self; arg] [TArrow m' τ τ'; τ] Γ) code τ' ->
  typed m Γ (Code self arg code) (TArrow m' τ τ')
| TYCall : forall m m' Γ e es τs τ,
  (m = Strong -> m' = Strong) ->
  (m = Weak -> m' = Strong -> τ = TUnit) ->
  typed m Γ e (TArrow m' τs τ) ->
  typed m Γ es τs ->
  typed m Γ (Call e es) τ
| TYRef : forall Γ e τ,
  typed Weak Γ e τ ->
  typed Weak Γ (ref e) (TRef τ)
| TYLoad : forall Γ e τ,
  typed Strong Γ e (TRef τ) ->
  typed Strong Γ (Load e 0) τ
| TYCAS : forall Γ e1 e2 e3 τ,
  typed Strong Γ e1 (TRef τ) ->
  typed Strong Γ e2 τ ->
  typed Strong Γ e3 τ ->
  typed Strong Γ (CAS e1 0 e2 e3) TBool
| TYPar : forall Γ e1 e2 τ1 τ2,
  typed Weak Γ e1 τ1 -> (* XXX can I tolerate strong? *)
  typed Weak Γ e2 τ2 ->
  typed Weak Γ (Par e1 e2) (TProd τ1 τ2)
| TYPair : forall m Γ e1 e2 τ1 τ2,
  typed m Γ e1 τ1 ->
  typed m Γ e2 τ2 ->
  typed m Γ (Pair e1 e2) (TProd τ1 τ2)
.
