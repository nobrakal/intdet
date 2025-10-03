From iris.proofmode Require Import base proofmode.
From iris.algebra Require Import gmap gmultiset agree frac_auth gset.

From intdet.lang Require Import syntax syntax_instances notations head_semantics.
From intdet.utils Require Import elems big_opN more_maps_and_sets.
From intdet.musketeer Require Import wpg dwp lockstep.

From intdet.examples Require Import tactics_triple counter.

Definition dumas : val :=
  λ: "n",
    let: "r" := rref 0 in
    Par (ratomic_add "r" 1802) (ratomic_add "r" 42);;
    Assert (rget "r" '== "n").

Section proof.
Context `{intdetGS Σ, ccounterG Σ}.

Lemma musketeer_dumas (n:Z) :
  ⊢ triple ⊤ True (dumas n) (fun _ (_:unit) => True).
Proof.
  iApply triple_call'. done. iModIntro. simpl.

  iApply (triple_bind (CtxLet _ _)).
  iApply triple_rref.
  iIntros (v l).
  iApply triple_extract_pure_pre.
  iIntros "->". iApply triple_let_val. simpl.

  replace 1%Qp with (1/2 + 1/2)%Qp by compute_done.
  assert (0 = 0 + 0) as X by lia.
  rewrite {1}X.
  rewrite (vcounter_split l (1/2) (1/2) 0 0).

  iApply (triple_bind (CtxLet _ _)).
  iApply triple_par.
  { iApply triple_ratomic_add. }
  { iApply triple_ratomic_add. }
  iIntros (? ([]&[])). simpl.
  iApply triple_let_val. simpl.

  iApply triple_conseq_pre.
  { iIntros "(%&%&_&(_&?)&_&?)". iStopProof. reflexivity. }
  rewrite !left_id_L. rewrite -vcounter_split.
  replace (1/2 + 1/2)%Qp with 1%Qp by compute_done.
  replace ((0 + 1802%nat + (0 + 42%nat))) with 1844 by lia.

  iApply (triple_bind CtxAssert).
  { iApply (triple_bind (CtxCallPrim2 _ _)).
    iApply triple_rget. iIntros.
    iApply triple_extract_pure_pre. iIntros "->". simpl.
    iApply triple_conseq_pre. 2:iApply triple_call_prim. by iIntros. }
  iIntros.
  iApply triple_conseq.
  3:iApply triple_assert. all:by iIntros.
Qed.

End proof.

From intdet.angelic Require Import run.

Section angelic.

Context `{seqlogGS Σ}.

Lemma angelic_dumas :
  ⊢ run (dumas 1844) (fun _ => True).
Proof.
  iIntros.

  iApply run_call. simpl.

  iApply (run_bind (CtxLet _ _)).
  iApply run_mono. iApply run_rref.

  iIntros (?) "(%&->&Hl)". iApply run_let_val. simpl.
  iApply (run_bind (CtxLet _ _)).
  iApply run_par_seql.

  iApply (run_mono with "[Hl]").
  { iApply (run_ratomic_add with "[$]"). }
  iIntros (?) "(->&Hl)".

  iApply (run_mono with "[Hl]").
  { iApply (run_ratomic_add with "[$]"). }
  iIntros (?) "(->&Hl)".

  iApply run_let_val. simpl.
  iApply (run_bind CtxAssert).
  iApply (run_bind (CtxCallPrim2 _ _)).

  iApply (run_mono with "[-]").
  iApply (run_rget with "[$]").
  iIntros (?) "(->&?)".
  iApply run_mono. iApply run_call_prim. done.
  iIntros (? ->). simpl.
  iApply run_mono. iApply run_assert. done.
  by iIntros.
Qed.

End angelic.
