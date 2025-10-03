From stdpp Require Import base ssreflect.
From intdet.lang Require Import syntax semantics invert_step.

(* ------------------------------------------------------------------------ *)
(* Atomic expression reduces to a value in one step. *)

Inductive Atomic : expr -> Prop :=
| ALoad : forall (l:loc) (i:Z),
  Atomic (Load l i)
| AStore : forall (l:loc) (v:val) (i:Z),
  Atomic (Store l i v)
| ACAS : forall (l:loc) (v1 v2:val) (i:Z),
  Atomic (CAS l i v1 v2)
| ACallPrim : forall (p:prim) (v1 v2:val),
  Atomic (CallPrim p v1 v2)
| ALength : forall (l:loc),
  Atomic (Length l)
.

Lemma Atomic_correct e σ e' σ' :
  Atomic e ->
  step e σ e' σ' ->
  exists v, e' = Val v.
Proof.
  inversion_clear 1; intros Hs.
  { apply invert_step_load in Hs. naive_solver. }
  { apply invert_step_store in Hs. naive_solver. }
  { apply invert_step_cas in Hs. naive_solver. }
  { apply invert_step_call_prim in Hs. naive_solver. }
  { apply invert_step_length in Hs. naive_solver. }
Qed.

Lemma Atomic_no_val e :
  Atomic e ->
  to_val e = None.
Proof. by inversion 1. Qed.
