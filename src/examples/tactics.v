From iris.proofmode Require Import proofmode.
From intdet.lang Require Import syntax.
From intdet.musketeer Require Import wpapi.

Ltac autocall :=
  iApply wp_call; first done; iModIntro; simpl;
  iApply wp_mono; first iApply wp_code; iIntros (?) "->".

Tactic Notation "gocall" int(k) :=
  do k iApply (wp_bind (CtxCall2 _));
  do k autocall;
  iApply wp_call; first done; iModIntro; simpl.

Ltac wp_easy GO :=
  iApply (wp_bind (CtxLet _ _));
  iApply wp_mono; first iApply GO; iIntros (?) "->";
  iApply wp_let_val.

Ltac wp_fst := wp_easy wp_fst.
Ltac wp_snd := wp_easy wp_snd.
