From iris.proofmode Require Import proofmode.
From iris Require Import gmap saved_prop.
From iris.bi Require Import monpred.

From intdet.musketeer Require Import dwp lockstep.
From intdet.types Require Export persistent_pred.
From intdet.types.lvar Require Export typing.

Canonical Structure valO := leibnizO val.

(** interp : is a unary logical relation. *)
Section logrel.

Context `{intdetGS Σ, savedPropG Σ}.

Notation D := (persistent_predO val (vPropI Σ)).
Notation env := (gmap string D)%type.

Local Arguments ofe_car !_.

Definition interp_unit : D := PersPred (λ w, ⌜w = VUnit⌝)%I.
Definition interp_int : D := PersPred (λ w, ⌜∃ n, w = VInt n⌝)%I.
Definition interp_bool : D := PersPred (λ w, ⌜∃ n, w = VBool n⌝)%I.

Definition interp_prod (interp1 interp2 : D) : D :=
  PersPred (λ w, ∃ w1 w2, ⌜w = VPair w1 w2⌝ ∧ interp1 w1 ∧ interp2 w2)%I.

Definition savedp γ (P:iProp Σ) :=
  saved_prop_own γ DfracDiscarded P.

Inductive shape :=
| SNone : shape
| SLeaf : gname -> shape
| SProd : shape -> shape -> shape
| SArrow : gname -> shape.

Global Instance shape_inhabited : Inhabited shape := populate SNone.

Definition interp_arrow_weak γ (interps:(shape -> D)) (interp2:shape -> D) : D :=
  PersPred (fun (w:val) =>
    ∃ P, embed (savedp γ P) ∗ □ (pick True P) ∗
         pick (□ ∀ v s, triple ⊤ ((pick True (▷ P)) ∗ interps s v) (Call w (Val v)) (fun v s => interp2 s v)) True)%I.

Definition interp_arrow_strong (interps:shape -> D) (interp2:shape -> D) : D :=
  PersPred (fun (w:val) => □ ∀ v s, interps s v -∗ wp ⊤ (Call w (Val v)) (fun v => ∃ s, interp2 s v))%I.

Definition interp_ref (interp:shape -> D) : D :=
  PersPred (fun (v:val) => ∃ l, ⌜v=VLoc l⌝ ∗ lockstep.inv nroot (∃ s w, pointsto l (DfracOwn 1) [w] ∗ interp s w))%I.

Fixpoint interp (τ:typ) (s:shape) : D :=
  match τ,s with
  | TUnit, SNone => interp_unit
  | TInt, SNone => interp_int
  | TBool, SNone => interp_bool
  | TProd τ1 τ2, SProd s1 s2 => interp_prod (interp τ1 s1) (interp τ2 s2)
  | TArrow Weak τs τ, SArrow γ => interp_arrow_weak γ (interp τs) (interp τ)
  | TArrow Strong τs τ, SNone => interp_arrow_strong (interp τs) (interp τ)
  | TRef τ, SNone => interp_ref (interp τ)
  | _,_ => PersPred (fun _ => False)%I
  end.

Definition interp_env (Γ:gmap string typ) (vs:gmap string (val*shape)) : vProp Σ :=
  ([∗ map] k ↦ τ;v ∈ Γ;vs, interp τ v.2 v.1)%I.

End logrel.
