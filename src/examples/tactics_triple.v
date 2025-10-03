From iris.proofmode Require Import proofmode.

From intdet.examples Require Export tactics.

From intdet.lang Require Import notations.
From intdet.musketeer Require Import dwp lockstep.


Section proof.

Context `{intdetGS Σ}.

Lemma triple_code' E P self arg code :
  ⊢ triple E P (Code self arg code) (fun v (_:unit) => ⌜v = VCode self arg code⌝ ∗ P)%I.
Proof.
  iStartProof.
  iApply triple_conseq_post.
  2:{ unshelve iApply triple_code. exact (fun v _ => ⌜v=VCode self arg code⌝ ∗ P)%I.
      iApply triple_val'. iIntros. by iFrame. }
  intros. reflexivity.
Qed.

Lemma triple_call_prim' E P p (v1 v2 v:val) :
  eval_call_prim p v1 v2 = Some v ->
  ⊢ triple (A:=unit) E P (CallPrim p v1 v2) (fun v' _ => ⌜v'=v⌝ ∗ P)%I.
Proof.
  iIntros.
  iApply (triple_conseq_pre (True ∗ P)%I).
  rewrite left_id //. iApply triple_frame.
  iApply triple_conseq_post.
  2:iApply triple_call_prim. iIntros. iPureIntro. naive_solver.
Qed.

Lemma triple_bind_frame K A B E Q' P P' e Q  :
  triple (A:=B) E P e Q' -∗
  (∀ v x, triple (A:=A) E (Q' v x ∗ P') (fill_item K v) Q) -∗
  triple (A:=A) E (P ∗ P') (fill_item K e) Q.
Proof.
  iIntros "X1 X2".
  iApply (triple_bind with "[X1]").
  { rewrite comm. iApply triple_frame_wand.
    iApply triple_conseq_post; last done.
    iIntros. Unshelve. 2:exact (fun v x => Q' v x ∗ P')%I. by iFrame. }
  done.
Qed.

Lemma triple_extract_pure_pre {A} E X P e Q :
  (⌜X⌝ -∗ triple E P e Q) -∗
  triple (A:=A) E (⌜X⌝ ∗ P) e Q.
Proof.
  iIntros "H".
  iApply (triple_use_pure_pre X).
  { iIntros "(?&?)". done. }
  { iIntros. iApply triple_conseq_pre. 2:by iApply "H".
    iIntros "(?&?)". done. }
Qed.

Lemma triple_let_alloc {A} E P x (n:nat) e Q :
  (∀ l, triple E (P ∗ pointsto l (DfracOwn 1) (replicate n VUnit) ∗ meta_token l ∗ pick (gen_heap.meta_token l (↑nm_base)) True) (subst' x (VLoc l) e) Q) -∗
  triple (A:=A) E P (Let x (Alloc n) e) Q.
Proof.
  iIntros "X".
  iApply (triple_conseq_pre (True ∗ P)%I).
  rewrite left_id //.
  iApply (triple_bind_frame (CtxLet _ _)). iApply triple_alloc.
  iIntros (? (i,l)); simpl.
  rewrite -assoc. iApply triple_extract_pure_pre.
  iIntros ((X&?&?)). inversion X. subst.
  iApply triple_let_val.
  iApply triple_conseq_pre. 2:iApply "X".
  iIntros "((?&?&?)&?)".
  replace (Z.to_nat (Z.of_nat n)) with n by lia.
  iFrame.
Qed.

End proof.

Ltac call1 :=
  iApply triple_call'; first done; iModIntro; simpl.
Ltac call2 := iApply triple_code'.
Ltac call3 :=
  iIntros (? []); simpl; iApply triple_extract_pure_pre; iIntros (->).

Ltac triple_if :=
  iApply triple_if;
  let b := fresh "b" in
  let Hb := fresh "Hb" in
  iIntros (b Hb); inversion Hb; subst b; clear Hb.
