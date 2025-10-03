From iris.proofmode Require Import proofmode.
From iris Require Import gmap saved_prop.
From iris.bi Require Import monpred.

From intdet.lang Require Import syntax syntax_instances.

Inductive shape :=
| SInvalid : shape
| SNone : shape
| SRef : val -> shape -> shape
| SProd : shape -> shape -> shape
| SArrow : gname -> shape
| SPRead : Z -> shape
| SPWrite : Z -> shape
| SHashSet : gset val -> shape
(* design choice here: a hash-set can store only ground value
   not linked with any shape. *)
| SArray : list val -> shape
.

Global Instance shape_inhabited : Inhabited shape := populate SNone.

Fixpoint shape_op (s1 s2:shape) : shape :=
  match s1,s2 with
  | SProd s11 s12, SProd s21 s22 => SProd (shape_op s11 s21) (shape_op s12 s22)
  | SPWrite i, SPWrite j => SPWrite (Z.max i j)
  | SPRead i, SPRead j => if decide (i=j) then SPRead i else SInvalid
  | SArrow g1, SArrow g2 => if decide (g1=g2) then s1 else SInvalid
  | SHashSet g1, SHashSet g2 => SHashSet (g1 ∪ g2)
  | SArray vs1, SArray vs2 =>
      if decide (vs1 = vs2) then SArray vs1 else SInvalid
  | SNone, SNone => SNone
  | _,_ => SInvalid end.

Lemma shape_op_comm s1 s2 :
  shape_op s1 s2 = shape_op s2 s1.
Proof.
  revert s2; induction s1; intros []; try done; simpl.
  { rewrite IHs1_1 IHs1_2 //. }
  1,2,5:case_decide; subst; [rewrite decide_True // | rewrite decide_False //].
  { f_equal. lia. }
  { f_equal. set_solver. }
Qed.

Lemma shape_op_assoc s1 s2 s3 :
  shape_op s1 (shape_op s2 s3) = shape_op (shape_op s1 s2) s3.
Proof.
  revert s2 s3; induction s1; intros [] []; simpl; try done.
  all:try by case_decide.
  { rewrite IHs1_1 IHs1_2 //. }
  { case_decide. subst.
    { case_decide; simpl; last done. subst. rewrite decide_True //. }
    { case_decide; simpl. subst. rewrite decide_False //. done. } }
  { case_decide. subst.
    { case_decide; simpl; last done. subst. rewrite decide_True //. }
    { case_decide; simpl. subst. rewrite decide_False //. done. } }
  { f_equal. lia. }
  { f_equal. set_solver. }
  { case_decide. subst.
    { case_decide; simpl; last done. subst. rewrite decide_True //. }
    { case_decide; simpl. subst. rewrite decide_False //. done. } }
Qed.

Fixpoint shape_valid s :=
  match s with
  | SInvalid => False
  | SRef _ x => shape_valid x
  | SProd x x0 => shape_valid x /\ shape_valid x0
  | _ => True
  end.

Lemma shape_valid_op_inv (x y:shape) :
  shape_valid (shape_op x y) → shape_valid x.
Proof.
  revert y. induction x; intros y; try done; simpl.
  destruct y; try done. intros (?&?). eauto.
Qed.

Section cmra.

Local Instance shape_op_instance : Op shape := shape_op.
Local Instance shape_pcore_instance : PCore shape := λ m, None.
Local Instance shape_valid_instance : Valid shape := shape_valid.
Local Instance shape_validN_instance : ValidN shape := λ _, shape_valid.

Canonical Structure shapeO : ofe := leibnizO shape.

Lemma shape_cmra_mixin : CmraMixin shape.
Proof.
  apply discrete_cmra_mixin; try apply _.
  constructor; try done.
  { by intros ??? ->. }
  { by intros ?? -> ?. }
  { intros ???. apply shape_op_assoc. }
  { intros ??. apply shape_op_comm. }
  { apply shape_valid_op_inv. }
Qed.

Canonical Structure shapeR : cmra := Cmra shape shape_cmra_mixin.

Global Instance shape_cmra_discrete : CmraDiscrete shapeR.
Proof. constructor. apply _. naive_solver. Qed.

End cmra.

(* ensures that the gname of arrows do not change *)
Fixpoint similar_shape s1 s2 : Prop :=
  match s1,s2 with
  | SProd s11 s12, SProd s21 s22 => similar_shape s11 s21 /\ similar_shape s12 s22
  | SNone, SNone | SRef _ _, SRef _ _ | SArray _, SArray _   | SHashSet _, SHashSet _ => True
  | SPRead _, SPRead _ | SPWrite _, SPWrite _ | SPWrite _, SPRead _ | SPRead _, SPWrite _ => True
  | SArrow g1, SArrow g2 => g1=g2
  | _,_ => False end.

Lemma shape_op_unfold s1 s2 :
  s1 ⋅ s2 = shape_op s1 s2.
Proof. done. Qed.

Lemma shape_op_none_inv s1 s2 :
  s1 ⋅ s2 = SNone ->
  s1 = SNone /\ s2 = SNone.
Proof.
  destruct s1,s2; try done.
  all: rewrite shape_op_unfold; simpl; by case_decide.
Qed.

Lemma shape_op_arrow_inv s1 s2 γ :
  s1 ⋅ s2 = SArrow γ ->
  s1 = SArrow γ /\ s2 = SArrow γ.
Proof.
  destruct s1,s2; try done; eauto.
  all:rewrite shape_op_unfold; simpl.
  { case_decide; last done. inversion 1. subst. done. }
  all:by case_decide.
Qed.

Lemma shape_op_srprio_inv s1 s2 n :
  s1 ⋅ s2 = SPRead n ->
  s1 = SPRead n /\ s2 = SPRead n.
Proof.
  destruct s1,s2; try done.
  all:rewrite shape_op_unfold; simpl.
  all:case_decide; subst; last done; naive_solver.
Qed.

Lemma shape_op_hashset_inv s1 s2 g :
  s1 ⋅ s2 = SHashSet g ->
  exists g1 g2, s1 = SHashSet g1 /\ s2 = SHashSet g2 /\ g=g1 ∪ g2.
Proof.
  destruct s1,s2; try done.
  all:rewrite shape_op_unfold; simpl.
  1,2,4:by case_decide.
  inversion 1. subst.
  eauto.
Qed.

Lemma shape_op_array_inv s1 s2 vs :
  s1 ⋅ s2 = SArray vs ->
  s1 = SArray vs /\ s2 = SArray vs.
  destruct s1,s2; try done.
  all:rewrite shape_op_unfold; simpl.
  1,2:by case_decide.
  case_decide; last done. inversion 1. subst.
  eauto.
Qed.

Lemma shape_op_prod_inv x1 x2 s1 s2 :
  x1 ⋅ x2 = SProd s1 s2 ->
  exists x11 x12 x21 x22, x1 = SProd x11 x12 /\ x2 = SProd x21 x22 /\ s1 = shape_op x11 x21 /\ s2 = shape_op x12 x22.
Proof.
  destruct x1,x2; try done; rewrite shape_op_unfold; simpl.
  2,3:by case_decide.
  { inversion 1. subst. eauto 10. }
  { by case_decide. }
Qed.

Lemma shape_op_swprio_inv s1 s2 n :
  s1 ⋅ s2 = SPWrite n ->
  exists n1 n2, s1 = SPWrite n1 /\ s2 = SPWrite n2 /\ n = Z.max n1 n2.
Proof.
  destruct s1,s2; try done; rewrite shape_op_unfold; simpl.
  1,2,4:by case_decide.
  { inversion 1. subst. eauto. }
Qed.

Lemma similar_shape_refl s : ✓ s -> similar_shape s s.
Proof. induction s; try done. intros (?&?). naive_solver. Qed.
