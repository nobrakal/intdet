From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export invariants.

From intdet.lang Require Import syntax notations.
From intdet.musketeer Require Import dwp lockstep.

From intdet.examples Require Import tactics_triple.

Definition ref : val :=
  λ: "n",
    let: "x" := Alloc 1 in
    "x".[0] <- "n";; "x".

Section go.

Context `{intdetGS Σ}.

Lemma triple_ref E (v:val) :
  ⊢ triple E True%I (ref (Val v)) (fun w (_:unit) => ∃ l, ⌜w=VLoc l⌝ ∗ pointsto l (DfracOwn 1) [v] ∗ meta_token l).
Proof.
  iStartProof.

  iApply (triple_conseq_pre (▷ True%I)).
  { by iIntros. }
  iApply (triple_call _ _ _ _ _ _ _). done.
  iModIntro.

  iApply (triple_bind (CtxLet _ _)).
  iApply triple_alloc. iIntros (v' (i,l)).
  iApply triple_extract_pure_pre. iIntros ((X&?&->)). inversion X. subst.
  rewrite comm. simpl. iApply triple_let_val. simpl.

  iApply triple_frame_wand.
  iApply (triple_bind (CtxLet _ _)).
  iApply triple_store.

  iIntros (??). simpl. iApply triple_let_val. simpl.
  iApply triple_val'.
  iIntros "((%X'&%)&?) (?&?)". inversion X'. subst.
  by iFrame.
Qed.

End go.
