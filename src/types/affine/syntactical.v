From stdpp Require Import gmap binders ssreflect.
From iris.algebra Require Import gmap.

From intdet.lang Require Import syntax utils substitution2 notations.
From intdet.examples Require Import hashtbl_pure hashtbl reference parfor fill priority.

From intdet.types.affine Require Import logrel.
From intdet.types.affine Require Export typing.

Definition prim_typed p (ρ1 ρ2 ρ:typ) :=
  match p with
  | PrimEq => ρ1=ρ2 /\ ρ=TBool
  | PrimBoolOp _ => ρ1=TBool /\ ρ2=TBool /\ ρ=TBool
  | PrimIntOp _ => ρ1=TInt /\ ρ2=TInt /\ ρ=TInt
  | PrimIntCmp _ => ρ1=TInt /\ ρ2=TInt /\ ρ=TBool
  end.

Fixpoint iter_sep {A:ucmra} n (Γ:A) :=
  match n with
  | 0 => ε
  | S n => Γ ⋅ iter_sep n Γ end.

Definition fractional {A:ucmra} (Γ:A) K :=
  forall n, n ≠ 0 -> Γ = iter_sep n (K n).

Definition alloc_fill : val :=
  λ: "n" "x",
    let: "l" := Alloc "n" in
    fill "l" "x";;
    "l".

Inductive typed : gmap string typ -> expr -> typ -> gmap string typ -> Prop :=
| TYVar : forall (x:string) t,
  typed {[x:=t]} x t ∅
| TYUnit :
  typed ∅ VUnit TUnit ∅
| TYBool : forall (b:bool),
  typed ∅ (VBool b) TBool ∅
| TYInt : forall (i:Z),
  typed ∅ (VInt i) TInt ∅
| TYAssert : forall Γ e Γ',
  typed Γ e TBool Γ' ->
  typed Γ (Assert e) TUnit Γ'
| TYLet : forall Γ1 e1 t1 Γ1' e2 t2 Γ2 x,
  typed Γ1 e1 t1 Γ1' ->
  typed (binsert x t1 Γ1') e2 t2 Γ2 ->
  typed Γ1 (Let x e1 e2) t2 (bdelete x Γ2)
| TYAbs : forall Γ f arg code t t',
  Γ = Γ ⋅ Γ ->
  typed (extend [f;arg] [TArrow t t'; t] Γ) code t' ∅ ->
  typed Γ (Code f arg code) (TArrow t t') ∅
| TYApp : forall Γ e2 Γ' e1 t t' Γ'',
  typed Γ e2 t Γ' ->
  typed Γ' e1 (TArrow t t') Γ'' ->
  typed Γ (Call e1 e2) t' Γ''
| TYPar : forall Γ1 e1 t1 Γ1' Γ2 e2 t2 Γ2',
  typed Γ1 e1 t1 Γ1' ->
  typed Γ2 e2 t2 Γ2' ->
  typed (Γ1 ⋅ Γ2) (Par e1 e2) (TProd t1 t2) (Γ1' ⋅ Γ2')
| TYCallPrim : forall p Γ e1 t1 Γ' e2 t2 Γ'' t3,
  prim_typed p t2 t1 t3 ->
  typed Γ e1 t1 Γ' ->
  typed Γ' e2 t2 Γ'' ->
  typed Γ (CallPrim p e2 e1) t3 Γ''
| TYIf : forall Γ e1 e2 e3 Γ' Γ'' t,
  typed Γ e1 TBool Γ' ->
  typed Γ' e2 t Γ'' ->
  typed Γ' e3 t Γ'' ->
  typed Γ (If e1 e2 e3) t Γ''
(* Structural *)
| TYFrame : forall Γ0 Γ e t Γ',
  typed Γ e t Γ' ->
  typed (Γ0 ⋅ Γ) e t (Γ0 ⋅ Γ')
| TYWeak : forall Γ1 Γ1' Γ2 Γ2' e t,
  Γ1' ⊆ Γ1 ->
  Γ2 ⊆ Γ2' ->
  typed Γ1' e t Γ2' ->
  typed Γ1 e t Γ2
| TYUpd : forall Γ1 Γ1' e τ Γ2,
  upd_typ_env Γ1 Γ1' ->
  typed Γ1' e τ Γ2 ->
  typed Γ1 e τ Γ2
(* Refs *)
| TYRef : forall Γ Γ' e τ,
  typed Γ e τ Γ' ->
  typed Γ (Call ref e) (TRef τ) Γ'
| TYSet :  forall Γ Γ' e (x:string) τ,
  Γ' !! x = Some (TRef TEmpty) ->
  typed Γ e τ Γ' ->
  typed Γ (Store x 0 e) TUnit (insert x (TRef τ) Γ')
| TYGet : forall (x:string) τ,
  typed {[x:=TRef τ]} (Load x 0) τ {[x:=TRef TEmpty]}
(* Parfor *)
| TYParFor : forall Γ Γf arg body (x1 x2:string),
  Γ !! x1 = Some TInt ->
  Γ !! x2 = Some TInt ->
  binder_set arg ## dom Γ ->
  fractional Γ Γf -> (* pre and post the same because parfor might be id. *)
  (∀ n, typed (binsert arg TInt (Γf n)) body TUnit (Γf n)) ->
  typed Γ (parfor x1 x2 (Code BAnon arg body)) TUnit Γ
(* IntArray *)
| TYIALength : forall (x:string) q,
  typed {[x:=TIntArray q]} (Length x) TInt {[x:=TIntArray q]}
| TYIALoad : forall (x:string) q Γ Γ' e,
  Γ' !! x = Some (TIntArray q) ->
  typed Γ e TInt Γ' ->
  typed Γ (Load x e) TInt Γ'
| TYIAAlloc : forall e1 e2 Γ1 Γ2 Γ3,
  typed Γ1 e1 TInt Γ2 ->
  typed Γ2 e2 TInt Γ3 ->
  typed Γ1 (alloc_fill e2 e1) (TIntArray 1) Γ3
| TYIAStore : forall (x:string) e1 e2 Γ1 Γ2 Γ3,
  Γ3 !! x = Some (TIntArray 1) ->
  typed Γ1 e1 TInt Γ2 ->
  typed Γ2 e2 TInt Γ3 ->
  typed Γ1 (Store x e2 e1) TUnit Γ3
(* Hashset *)
| TYHSAlloc : forall (h c:val)(hash0:val -> nat) (cmp0:val -> val -> bool) Γ e Γ',
  TotalOrder cmp0 ->
  (forall {Σ} `{X:dwp.intdetGS Σ}, ⊢ @hash_spec Σ X hash0 h) ->
  (forall {Σ} `{wpapi.IsWP Σ pt wpx}, ⊢ @cmp_spec Σ wpx cmp0 c) ->
  typed Γ e TInt Γ' ->
  typed Γ (htbl_init h c e)%E (THashSet 1)  Γ'
| TYHSInsert : forall Γ Γ' e (x:string) q,
  Γ' !! x = Some (THashSet q) ->
  typed Γ e TInt Γ' ->
  typed Γ (htbl_add x e) TUnit Γ'
| TYHSElem : forall Γ e Γ',
  typed Γ e (THashSet 1) Γ' ->
  typed Γ (htbl_elems e) (TIntArray 1) Γ'
(* Prods *)
| TYProd : forall Γ1 e1 t1 Γ2 e2 t2 Γ3,
  typed Γ1 e1 t1 Γ2 ->
  typed Γ2 e2 t2 Γ3 ->
  typed Γ1 (Pair e2 e1) (TProd t2 t1) Γ3
(* Priority *)
| TYPAlloc : forall Γ e Γ',
  typed Γ e TInt Γ' ->
  typed Γ (palloc e)%E (TPWrite 1)  Γ'
| TYPWrite : forall Γ Γ' e q x,
  Γ' !! x = Some (TPWrite q) ->
  typed Γ e TInt Γ' ->
  typed Γ (pwrite (Var x) e)%E TUnit Γ'
| TYPRead : forall x q,
  typed {[x:=TPRead q]} (pread (Var x))%E TInt {[x:=TPRead q]}
.

Lemma upd_env_typ_dom Γ Γ' :
  upd_typ_env Γ Γ' ->
  dom Γ = dom Γ'.
Proof.
  intros X. apply set_eq. intros x.
  specialize (X x). rewrite !elem_of_dom.
  destruct (Γ !! x); by destruct (Γ' !! x).
Qed.

Lemma typed_dom_subseteq Γ e t Γ' :
  typed Γ e t Γ' ->
  dom Γ' ⊆ dom Γ.
Proof.
  induction 1; try done.
  { rewrite dom_bdelete. rewrite dom_binsert in IHtyped2. set_solver. }
  { set_solver. }
  { rewrite !dom_op. set_solver. }
  { set_solver. }
  { set_solver. }
  { rewrite !dom_op. set_solver. }
  { apply subseteq_dom in H,H0. set_solver. }
  { apply upd_env_typ_dom in H. set_solver. }
  { rewrite dom_insert_L. apply elem_of_dom_2 in H. set_solver. }
  { rewrite !dom_singleton_L //. }
  { set_solver. }
  { set_solver. }
  { set_solver. }
Qed.

Lemma dom_iter_sep `{Countable K} {V:cmra} n (Γ:gmap K V) :
  n ≠ 0 ->
  dom (iter_sep n Γ) = dom Γ.
Proof.
  induction n. done. simpl.
  rewrite dom_op. intros _. destruct n. simpl.
  { rewrite dom_empty_L right_id_L //. }
  rewrite IHn //. set_solver.
Qed.

Lemma typed_fv Γ e t Γ' :
  typed Γ e t Γ' ->
  fv e ⊆ dom Γ.
Proof.
  induction 1; simpl; try done.
  { rewrite dom_singleton_L //. }
  { rewrite dom_binsert in IHtyped2.
    apply typed_dom_subseteq in H.
    set_solver. }
  { rewrite dom_extend // in IHtyped. set_solver. }
  { apply typed_dom_subseteq in H. set_solver. }
  { rewrite dom_op. set_solver. }
  { apply typed_dom_subseteq in H0. set_solver. }
  { apply typed_dom_subseteq in H. set_solver. }
  { rewrite dom_op. set_solver. }
  { apply subseteq_dom in H. set_solver. }
  { apply upd_env_typ_dom in H. set_solver. }
  { set_solver. }
  { apply elem_of_dom_2 in H. apply typed_dom_subseteq in H0. set_solver. }
  { rewrite dom_singleton_L. set_solver. }
  { rewrite !left_id_L.
    apply (elem_of_dom_2 Γ) in H. apply (elem_of_dom_2 Γ) in H0.
    specialize (H4 1). rewrite dom_binsert // in H4.
    assert (dom Γ = dom (Γf 1)) as Hd.
    { rewrite (H2 1) // dom_iter_sep //. }
    rewrite -Hd in H4. set_solver. }
  { rewrite dom_insert_L //. set_solver. }
  { apply elem_of_dom_2 in H. apply typed_dom_subseteq in H0. set_solver. }
  { apply typed_dom_subseteq in H. set_solver. }
  { apply typed_dom_subseteq in H0,H1. apply elem_of_dom_2 in H. set_solver. }
  { set_solver. }
  { apply elem_of_dom_2 in H. apply typed_dom_subseteq in H0. set_solver. }
  { set_solver. }
  { apply typed_dom_subseteq in H. set_solver. }
  { set_solver. }
  { apply elem_of_dom_2 in H. apply typed_dom_subseteq in H0. set_solver. }
  { rewrite dom_singleton_L. set_solver. }
Qed.
