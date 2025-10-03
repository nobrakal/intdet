From iris.proofmode Require Import proofmode.

From intdet.lang Require Import notations.
From intdet.angelic Require Import run.
From intdet.examples Require Import parfor.

Section proof.

Context `{seqlogGS Σ}.

Fixpoint forspec (o:nat) k (f:val) Q : iProp Σ :=
  match k with
  | 0 => Q
  | S k => run (f o) (fun v => ⌜v=VUnit⌝ ∗ forspec (S o) k f Q)%I end.

Lemma forspec_mono i k f Q Q' :
  forspec i k f Q -∗
  (Q -∗ Q') -∗
  forspec i k f Q'.
Proof.
  iIntros "X1 X2". iInduction k as [] "IH" forall (i Q).
  by iApply "X2".
  simpl. iApply (run_mono with "[$]").
  iIntros (?) "(->&?)". iSplitR; first done.
  iApply ("IH" with "[$][$]").
Qed.

Lemma forspec_split i k1 k2 f Q :
  forspec i (k1 + k2) f Q -∗
  forspec i k1 f (forspec (i+k1) k2 f Q).
Proof.
  iIntros "X".
  iInduction k1 as [] "IH" forall (i).
  { simpl. rewrite right_id_L. by iFrame. }
  { replace (S k1 + k2) with (S (k1 + k2)) by lia. simpl.
    iApply (run_mono with "[$]").
    iIntros (?) "(->&?)". iSplitR; first done.
    iDestruct ("IH" with "[$]") as "?".
    replace (i + S k1) with (S i + k1) by lia.
    by iFrame. }
Qed.

Lemma div_eq_0_inv a b :
  b ≠ 0 ->
  a `div` b = 0 ->
  a < b.
Proof.
  intros ? E.
  rewrite (Nat.div_mod_eq a b).
  rewrite E right_absorb_L left_id_L.
  by apply Nat.mod_upper_bound.
Qed.

Lemma parfor_seq_spec (i j:nat) (f:val) (Q:iProp Σ) :
  forspec i (j - i) f Q -∗
  run (parfor i j f) (fun v => ⌜v=VUnit⌝ ∗ Q).
Proof.
  iIntros "HK".

  remember (j-i) as k.
  iInduction k as [] "IH" using (well_founded_induction PeanoNat.Nat.lt_wf_0) forall (i j Heqk Q) "HK".
  do 2 iApply (run_bind (CtxCall2 _)).
  do 2 (iApply run_call; iApply run_code; iApply run_val).
  iApply run_call. simpl. fold parfor.

  iApply (run_bind (CtxLet _ _)).
  iApply run_mono. iApply run_call_prim. done.
  iIntros (? ->). iApply run_let_val. simpl.

  iApply (run_bind (CtxIf _ _)).
  iApply run_mono. iApply run_call_prim. done.
  iIntros (? ->). simpl.
  iApply run_if.
  destruct (j - i <=? 0%nat)%Z eqn:X.
  { apply Z.leb_le in X. replace k with 0 by lia. iApply run_val. by iFrame. }

  iApply (run_bind (CtxIf _ _)).
  iApply run_mono. iApply run_call_prim. done.
  iIntros (? ->). simpl.

  iApply run_if. case_bool_decide.
  { inversion H0. subst. assert (j = S i) by lia.
    subst. replace (S i - i) with 1 by lia. simpl.
    iApply (run_mono with "[$]"). iIntros (?) "(->&?)". by iFrame. }

  iApply (run_bind (CtxLet _ _)).
  iApply (run_bind (CtxCallPrim1 _ _)).
  iApply run_mono. iApply run_call_prim. done. iIntros (? ->).
  iApply run_mono. iApply run_call_prim. done. iIntros (? ->).
  simpl. iApply run_let_val. simpl.
  iApply (run_bind (CtxLet _ _)).

  apply Z.leb_gt in X.
  replace (i + (j - i) `div` 2%nat)%Z with (Z.of_nat (i + (j - i) `div` 2)).
  2:{ rewrite Nat2Z.inj_add Nat2Z.inj_div Nat2Z.inj_sub //. lia. }
  rewrite -Heqk.
  pose (mid := (i + k /2)).
  replace (VInt (i + k `div` 2)%nat) with (VInt mid).
  2:{ f_equal. }

  iApply run_par_seql.
  assert (k = (mid - i) + (mid -i + k `mod` 2 )) as Hk.
  { pose proof (Nat.div_mod_eq k 2). lia. }

  rewrite {2}Hk.
  iDestruct (forspec_split with "HK") as "HK".

  assert (k ≠ 1).
  { intros ->. apply H0. f_equal. lia. }
  assert (k `div` 2 ≠ 0).
  { intros F. apply div_eq_0_inv in F; last done. lia. }

  iApply (run_mono with "[-]").
  iApply ("IH" with "[%][%] HK"). lia. reflexivity.
  iIntros (?) "(->&HK)".
  iApply (run_mono with "[-]").
  { iApply ("IH" with "[%][%][HK]"). 2:reflexivity.
    { rewrite Heqk. subst mid. lia. }
    { replace (i + (mid - i)) with mid by lia.
      replace (mid - i + k `mod` 2) with (j - mid) by lia. done. } }
  { iIntros (?) "(->&?)". iApply run_let_val. simpl.
    iApply run_val. by iFrame. }
Qed.

End proof.
