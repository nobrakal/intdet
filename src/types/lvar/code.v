From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import frac_auth gmultiset.
From iris.bi Require Import monpred.


From intdet.lang Require Import syntax notations.
From intdet.musketeer Require Import wpg dwp atomic_wpg lockstep.
From intdet.types.lvar Require Import typing soundness.

Definition lv_alloc : expr :=
  λ: "v", ref "v".

Definition lv_get : expr :=
  μ: "self" "leq" "l" "x",
    let: "y" := "l".[0] in
    if: "leq" (Pair "y" "x") then VUnit else "self" "leq" "l" "x".

Definition lv_set : expr :=
  μ: "self" "leq" "lub" "l" "x",
    let: "y" := "l".[0] in
    if: "leq" (Pair "x" "y") then VUnit else
    if: CAS "l" 0 "y" ("lub" (Pair "x" "y"))
    then VUnit else "self" "leq" "lub" "l" "x".

Lemma typed_lv_alloc τ :
  typed Weak ∅ lv_alloc (TArrow Weak τ (TRef τ)).
Proof.
  econstructor. done. constructor. constructor. done.
Qed.

Lemma typed_lv_get m τ :
  typed m ∅ lv_get
    (TArrow Strong (TArrow Strong (TProd τ τ) TBool) (TArrow Strong (TRef τ) (TArrow Strong τ TUnit))).
Proof.
  repeat (econstructor; try done).
Qed.

Lemma typed_lv_set m τ :
  typed m ∅ lv_set
    (TArrow Strong (TArrow Strong (TProd τ τ) TBool) (TArrow Strong (TArrow Strong (TProd τ τ) τ) (TArrow Strong (TRef τ) (TArrow Strong τ TUnit)))).
Proof.
  repeat (econstructor; try done).
Qed.
