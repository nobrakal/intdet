From iris.proofmode Require Import base proofmode.

From intdet.lang Require Import syntax notations.
From intdet.examples Require Import tactics.
From intdet.angelic Require Import run.

From intdet.examples Require Import fill.

Section proof.

Context `{seqlogGS Σ}.


Local Lemma run_fill_aux (l:loc) (x:val) (n:nat) vs :
  pointsto l (DfracOwn 1) (replicate n x ++ vs) -∗
  run (fill_aux l x (n + length vs) n) (fun v => ⌜v=VUnit⌝ ∗ pointsto l (DfracOwn 1) (replicate (n + length vs) x)).
Proof.
  iIntros "Hl".

  remember (length vs) as k.
  iInduction k as [] "IH" forall (n vs Heqk).
  { do 3 iApply (run_bind (CtxCall2 _)).
    do 3 (iApply run_call; iApply run_code; iApply run_val; simpl).
    iApply run_call. simpl.

    iApply (run_bind (CtxIf _ _)).
    iApply run_mono. iApply run_call_prim. done.
    iIntros (? ->). simpl. iApply run_if. rewrite right_id_L.
    destruct ((n <? n))%Z eqn :X.
    { exfalso. apply Z.ltb_lt in X. lia. }
    iApply run_val. symmetry in Heqk.
    apply nil_length_inv in Heqk. subst. rewrite right_id_L //.
    by iFrame. }
  { do 3 iApply (run_bind (CtxCall2 _)).
    do 3 (iApply run_call; iApply run_code; iApply run_val; simpl).
    iApply run_call.
    iApply (run_bind (CtxIf _ _)).
    iApply run_mono. iApply run_call_prim. done.
    iIntros (? ->). simpl. iApply run_if.
    destruct (n <? (n + S k)%nat)%Z eqn:X.
    2:{ exfalso. apply Z.ltb_ge in X. lia. }
    iApply (run_bind (CtxLet _ _)).
    iApply (run_mono with "[Hl]").
    iApply (run_store with "Hl").
    { rewrite app_length replicate_length. lia. }
    iIntros (?) "(->&Hl)". iApply run_let_val. simpl.

    iApply (run_bind (CtxCall1 _)).
    iApply run_mono. iApply run_call_prim. done.
    iIntros (?) "->". simpl.
    fold fill_aux.

    destruct vs; first done.
    rewrite insert_app_r_alt replicate_length; last lia.
    replace (Z.to_nat n - n) with 0 by lia. simpl.
    replace (n + S k) with ((S n) + k) by lia.
    replace ((n + 1%nat))%Z with (Z.of_nat (S n))%Z by lia.
    iApply ("IH" $! _ vs with "[%][Hl]").
    { simpl in *. lia. }
    { iClear "IH".
      replace (S n) with (n+1) by lia.
      rewrite replicate_add. simpl.
      rewrite cons_middle -assoc_L //. } }
Qed.

Lemma run_fill (l:loc) (x:val) vs :
  pointsto l (DfracOwn 1) vs -∗
  run (fill l x) (fun v => ⌜v=VUnit⌝ ∗ pointsto l (DfracOwn 1) (replicate (length vs) x)).
Proof.
  iIntros "Hl".

  iApply (run_bind (CtxCall2 _)).
  iApply run_call.
  iApply run_code; iApply run_val; simpl.
  iApply run_call. simpl.

  iApply (run_bind (CtxLet _ _)).
  iApply (run_mono with "[Hl]").
  by iApply run_length.
  iIntros (?) "(->&Hl)". iApply run_let_val. simpl.

  iApply (run_mono with "[-]").
  { by iApply (run_fill_aux l x 0 vs with "[Hl]"). }
  iIntros (?) "(->&?)". simpl. by iFrame.
Qed.

End proof.
