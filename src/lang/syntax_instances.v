From stdpp Require Import base countable strings list binders gmap.
From intdet Require Import syntax.

(******************************************************************************)
(* Various typeclass instances for the language. *)

Global Instance val_inhabited : Inhabited val := populate VUnit.
Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

Global Instance bool_op_eq_dec : EqDecision bool_op.
Proof. solve_decision. Qed.
Global Instance bool_op_countable : Countable bool_op.
Proof.
  refine (inj_countable'
    (fun op => match op with BoolAnd => 0 | BoolOr => 1 end)
    (fun n => match n with 0 => BoolAnd | _ => BoolOr end) _).
  intros []; reflexivity.
Qed.

Global Instance int_op_eq_dec : EqDecision int_op.
Proof. solve_decision. Qed.
Global Instance int_op_countable : Countable int_op.
Proof.
  refine (inj_countable'
    (fun op => match op with IntAdd => 0 | IntSub => 1 | IntMul => 2 | IntDiv => 3 | IntMod => 4 | IntMin => 5 | IntMax => 6 end)
    (fun n => match n with 0 => IntAdd | 1 => IntSub | 2 => IntMul | 3 => IntDiv | 4 => IntMod | 5 => IntMin | _ => IntMax end) _).
  intros []; reflexivity.
Qed.

Global Instance int_cmp_eq_dec : EqDecision int_cmp.
Proof. solve_decision. Qed.
Global Instance int_cmp_countable : Countable int_cmp.
Proof.
  refine (inj_countable'
    (fun op => match op with IntLt => 0 | IntLe => 1 | IntGt => 2 | IntGe => 3 end)
    (fun n => match n with 0 => IntLt | 1 => IntLe | 2 => IntGt | _ => IntGe end) _).
  intros []; reflexivity.
Qed.

Global Instance prim_eq_dec : EqDecision prim.
Proof. solve_decision. Qed.
Global Instance prim_countable : Countable prim.
Proof.
  refine
    (inj_countable'
       (λ op,
         match op with
         | PrimIntCmp x => inl (inl x)
         | PrimBoolOp x => inl (inr x)
         | PrimIntOp x => inr (inl x)
         | PrimEq => inr (inr tt) end)
       (λ x,
         match x with
         | inl (inl x) => PrimIntCmp x
         | inl (inr x) => PrimBoolOp x
         | inr (inl x) => PrimIntOp x
         | _ => PrimEq end) _).
  intros [ | ? | ? | ? ]; reflexivity.
Qed.

Lemma eq_val : forall (x y : val), {x = y} + {x ≠ y}
with eq_expr : forall (x y : expr), {x = y} + {x ≠ y}.
Proof.
  { decide equality.
    { apply bool_eq_dec. }
    { apply Z.eq_dec. }
    { apply loc_eq_dec. }
    1,2:apply binder_dec_eq. }
  { decide equality.
    1,2,5:apply binder_dec_eq.
    { apply string_eq_dec. }
    { apply prim_eq_dec. } }
Defined.

Global Instance val_eq_dec : EqDecision val := eq_val.
Global Instance expr_eq_dec : EqDecision expr := eq_expr.


(* Intermediate to help for countable of expr *)
Inductive lit :=
| Lloc : loc -> lit
| Lbool : bool -> lit
| Lint : Z -> lit
| Lunit : lit
| Lprim : prim -> lit
| Lbinder : binder -> lit.

Global Instance lit_eq_dec : EqDecision lit.
Proof.
  intros ??. unfold Decision. decide equality.
  apply loc_eq_dec. apply bool_eq_dec. apply Z.eq_dec.
  apply prim_eq_dec. apply binder_dec_eq.
Qed.

Global Instance lit_countable : Countable lit.
Proof.
  refine (inj_countable'
            (fun op => match op with
                    | Lloc l => inl (inl (inl l))
                    | Lbool b => inl (inl (inr b))
                    | Lint n => inl (inr (inl n))
                    | Lunit => inl (inr (inr tt))
                    | Lprim p => inr (inl (inl p))
                    | Lbinder b => inr (inr (inl b)) end)
            (λ n, match n with
                  | inl (inl (inl l)) => Lloc l
                  | inl (inl (inr b)) => Lbool b
                  | inl (inr (inl n)) => Lint n
                  | inr (inl (inl p)) => Lprim p
                  | inr (inr (inl b)) => Lbinder b
                  | _ => Lunit
                  end) _).
  Unshelve. 4,5:exact unit. all:try apply _. intros []; eauto.
Qed.

Local Fixpoint ence (e:expr) :=
  match e with
  | Val v => GenNode 0 [encv v]
  | Call e es =>
      GenNode 1 [ence e; ence es]
  | CallPrim p e1 e2 => GenNode 3 [GenLeaf (Lprim p); ence e1; ence e2]
  | Var x => GenNode 4 [GenLeaf (Lbinder (BNamed x))]
  | Let x e1 e2 => GenNode 5 [GenLeaf (Lbinder x); ence e1; ence e2]
  | If e1 e2 e3 => GenNode 6 [ence e1; ence e2; ence e3]
  | Alloc e1 => GenNode 7 [ence e1]
  | Load e1 e2 => GenNode 8 [ence e1; ence e2]
  | Store e1 e2 e3 => GenNode 9 [ence e1; ence e2; ence e3]
  | Length e => GenNode 10 [ence e]
  | Par e1 e2 => GenNode 11 [ence e1; ence e2]
  | RunPar e1 e2 => GenNode 111 [ence e1; ence e2]
  | CAS e1 e2 e3 e4 => GenNode 12 [ence e1; ence e2; ence e3; ence e4]
  | Pair e1 e2 => GenNode 13 [ence e1; ence e2]
  | Fst e1 => GenNode 14 [ence e1]
  | Snd e1 => GenNode 15 [ence e1]
  | Code x1 x2 e => GenNode 16 [GenLeaf (Lbinder x1); GenLeaf (Lbinder x2); ence e]
  | Assert e => GenNode 17 [ence e]
  end
with encv (v:val) :=
  match v with
  | VLoc l => GenLeaf (Lloc l)
  | VBool b => GenLeaf (Lbool b)
  | VInt n => GenLeaf (Lint n)
  | VUnit => GenLeaf (Lunit)
  | VPair v1 v2 => GenNode 18 [encv v1; encv v2]
  | VCode x1 x2 e => GenNode 19 [GenLeaf (Lbinder x1); GenLeaf (Lbinder x2); ence e]
  end.

Local Fixpoint dece (gt:gen_tree lit) : expr :=
  match gt with
  | GenNode 0 [v] => Val (decv v)
  | GenNode 1 [e;ts] => Call (dece e) (dece ts)
  | GenNode 3 [GenLeaf (Lprim p); e1; e2] => CallPrim p (dece e1) (dece e2)
  | GenNode 4 [GenLeaf (Lbinder (BNamed x))] => Var x
  | GenNode 5 [GenLeaf (Lbinder x); e1; e2] => Let x (dece e1) (dece e2)
  | GenNode 6 [e1; e2; e3] => If (dece e1) (dece e2) (dece e3)
  | GenNode 7 [e1] => Alloc (dece e1)
  | GenNode 8 [e1; e2] => Load (dece e1) (dece e2)
  | GenNode 9 [e1; e2; e3] => Store (dece e1) (dece e2) (dece e3)
  | GenNode 10 [e] => Length (dece e)
  | GenNode 11 [e1; e2] => Par (dece e1) (dece e2)
  | GenNode 111 [e1; e2] => RunPar (dece e1) (dece e2)
  | GenNode 12 [e1; e2; e3; e4] => CAS (dece e1) (dece e2) (dece e3) (dece e4)
  | GenNode 13 [e1; e2] => Pair (dece e1) (dece e2)
  | GenNode 14 [e1] => Fst (dece e1)
  | GenNode 15 [e1] => Snd (dece e1)
  | GenNode 16 [GenLeaf (Lbinder x1); GenLeaf (Lbinder x2); e] => Code x1 x2 (dece e)
  | GenNode 17 [e] => Assert (dece e)
  | _ => Val VUnit end
with decv (v:gen_tree lit) :=
  match v with
  | GenLeaf (Lloc l) => VLoc l
  | GenLeaf (Lbool b) => VBool b
  | GenLeaf (Lint n) => VInt n
  | GenLeaf (Lunit) => VUnit
  | GenNode 18 [v1; v2] => VPair (decv v1) (decv v2)
  | GenNode 19 [GenLeaf (Lbinder x1); GenLeaf (Lbinder x2); e] => VCode x1 x2 (dece e)
  | _ => VUnit end.

Global Instance expr_countable : Countable expr.
Proof.
  refine (inj_countable' ence dece _).
  refine (fix go (e:expr) {struct e} := _ with gov (v:val) {struct v} := _ for go).
  - destruct e; simpl; f_equal; try done.
    exact (gov v).
  - destruct v; simpl.
    1-4: easy. all:f_equal; easy.
Qed.
Global Instance val_countable : Countable val.
Proof.
  refine (inj_countable Val to_val  _).
  intros []; eauto.
Qed.
