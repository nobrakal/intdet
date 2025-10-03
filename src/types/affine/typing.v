From stdpp Require Import gmap binders ssreflect.
From iris.prelude Require Import options.
From iris.algebra Require Import cmra.

From intdet.lang Require Import syntax utils.
From intdet.examples Require Import hashtbl_pure hashtbl.

Inductive typ :=
| TInvalid : typ
| TUnit : typ
| TInt : typ
| TBool : typ
| TProd : typ -> typ -> typ
| TArrow : typ -> typ -> typ
| TRef : typ -> typ
| TEmpty : typ
| TPRead : Qp -> typ
| TPWrite : Qp -> typ
| THashSet : Qp -> typ
| TIntArray : Qp -> typ
.

Lemma typ_eq_dec : forall (x y:typ), {x = y} + {x ≠ y}.
Proof.
  decide equality. all:try apply Qp.eq_dec.
Qed.

Global Instance eq_dec_typ : EqDecision typ := typ_eq_dec.

Fixpoint typ_op (τ1 τ2:typ) : typ :=
  match τ1,τ2 with
  | TUnit, TUnit => TUnit
  | TInt, TInt => TInt
  | TBool, TBool => TBool
  | TEmpty, TEmpty => TEmpty
  | TProd t11 t12, TProd t21 t22 => TProd (typ_op t11 t21) (typ_op t12 t22)
  | TPRead q1, TPRead q2 => TPRead (q1 + q2)%Qp
  | TPWrite q1, TPWrite q2 => TPWrite (q1 + q2)%Qp
  | TArrow x1 x2, TArrow y1 y2 => if (decide (x1=y1 /\ x2=y2)) then τ1 else TInvalid
  | THashSet q1, THashSet q2 => THashSet (q1 + q2)%Qp
  | TIntArray q1, TIntArray q2 => TIntArray (q1 + q2)%Qp
  | _,_ => TInvalid end.

Lemma typ_op_assoc t1 t2 t3 :
  typ_op t1 (typ_op t2 t3) = typ_op (typ_op t1 t2) t3.
Proof.
  revert t2 t3; induction t1; intros [] []; try done; simpl.
  all:try by case_decide.
  { rewrite IHt1_1 IHt1_2 //. }
  { case_decide as X.
    { destruct X; subst. case_decide as X; last done.
      destruct X. subst. simpl. rewrite decide_True //. }
    { case_decide as X'; last done. simpl.
      rewrite decide_False //. naive_solver. } }
  1,2:f_equal; rewrite assoc_L //.
  1,2:rewrite assoc_L //.
Qed.

Lemma typ_op_comm t1 t2 :
  typ_op t1 t2 = typ_op t2 t1.
Proof.
  revert t2; induction t1; intros []; try done; simpl.
  { rewrite IHt1_1 IHt1_2 //. }
  { case_decide as X.
    { destruct X. subst. rewrite decide_True //. }
    { rewrite decide_False //. naive_solver. } }
  1,2:f_equal; rewrite comm_L //.
  1,2:rewrite comm_L //.
Qed.

Fixpoint typ_valid t : Prop :=
  match t with
  | TInvalid => False
  | TProd t1 t2 => typ_valid t1 /\ typ_valid t2
  | _ => True end.

Lemma typ_valid_op_inv x y :
  typ_valid (typ_op x y) -> typ_valid x.
Proof.
  revert y; induction x; intros []; try done; simpl.
  { naive_solver. }
(*  all: intros; etrans; last done; apply Qp.le_add_l. *)
Qed.

Inductive upd_typ : typ -> typ -> Prop :=
| URefl : forall τ,
  upd_typ τ τ
| UProd : forall τ1 τ2 τ1' τ2',
  upd_typ τ1 τ1' ->
  upd_typ τ2 τ2' ->
  upd_typ (TProd τ1 τ2) (TProd τ1' τ2')
| URefEmpty : forall τ,
  upd_typ (TRef τ) (TRef TEmpty)
| UPRtoW :
  upd_typ (TPRead 1) (TPWrite 1)
| UPWtoR :
  upd_typ (TPWrite 1) (TPRead 1).

Definition upd_typ_env (m1 m2:gmap string typ) :=
  map_relation upd_typ (fun _ => False) (fun _ => False) m1 m2.

Section cmra.

Local Instance typ_op_instance : Op typ := typ_op.
Local Instance typ_pcore_instance : PCore typ := λ m, None.
Local Instance typ_valid_instance : Valid typ := typ_valid.
Local Instance typ_validN_instance : ValidN typ := fun _ => typ_valid.

Canonical Structure typO : ofe := leibnizO typ.

Lemma typ_cmra_mixin : CmraMixin typ.
Proof.
  apply discrete_cmra_mixin; first apply _.
  constructor; try apply _; try done.
  { intros ???. apply typ_op_assoc. }
  { intros ??. apply typ_op_comm. }
  { intros ??. apply typ_valid_op_inv. }
Qed.

Canonical Structure typR : cmra := Cmra typ typ_cmra_mixin.

Global Instance typ_cmra_discrete : CmraDiscrete typR.
Proof. constructor; first apply _. naive_solver. Qed.

End cmra.

Lemma typ_op_unfold t1 t2 :
  t1 ⋅ t2 = typ_op t1 t2.
Proof. reflexivity. Qed.
