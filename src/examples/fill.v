From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export invariants.

From intdet.lang Require Import syntax notations.
From intdet.examples Require Import tactics.

Definition fill_aux : val :=
  μ: "f" "l" "x" "len" "n",
    if: "n" '< "len" then
      "l".["n"] <- "x";; "f" "l" "x" "len" ("n" '+ 1) else VUnit.

Definition fill : val :=
  λ: "l" "x",
    let: "len" := Length "l" in
    fill_aux "l" "x" "len" 0.

From intdet.musketeer Require Import wpapi.

Section proof.

Context `{IsWP Σ pointsto wp}.

Local Lemma wp_fill_aux E (l:loc) (x:val) (n:nat) vs :
  pointsto l (DfracOwn 1) (replicate n x ++ vs) -∗
  wp E (fill_aux l x (n + length vs) n) (fun v => ⌜v=VUnit⌝ ∗ pointsto l (DfracOwn 1) (replicate (n + length vs) x)).
Proof.
  iIntros "X".
  iLöb as "IH" forall (n vs).

  gocall 3.

  iApply (wp_bind (CtxIf _ _)).
  iApply wp_mono. iApply wp_call_prim. done.
  iIntros (?) "->". simpl.
  iApply wp_if.
  destruct vs.
  { simpl. rewrite !right_id_L.
    rewrite Z.ltb_irrefl. iApply wp_val. done. by iFrame. }
  simpl.
  assert ((n <? (n + S (length vs))%nat)%Z = true) as ->.
  { apply Z.ltb_lt. lia. }
  iApply (wp_bind (CtxLet _ _)).
  iApply (wp_mono with "[X]").
  { iApply wp_store; last done. rewrite app_length replicate_length. simpl. lia. }
  iIntros (?) "(->&X)". simpl. iApply wp_let_val. simpl.
  iApply (wp_bind (CtxCall1 _)).
  iApply wp_mono. iApply wp_call_prim. done.
  iIntros (?) "->". simpl.
  rewrite insert_app_r_alt. rewrite replicate_length.
  replace (Z.to_nat n - n) with 0 by lia. simpl.
  rewrite cons_middle assoc_L -replicate_cons_app -replicate_S.
  2:{ rewrite replicate_length. lia. }

  iSpecialize ("IH" with "[$]").
  replace (n + S (length vs)) with (S n + length vs) by lia.
  replace (Z.of_nat n + 1%nat)%Z with (Z.of_nat (S n)) by lia.
  iApply "IH".
Qed.

Lemma wp_fill E (l:loc) (x:val) vs :
  pointsto l (DfracOwn 1) vs -∗
  wp E (fill l x) (fun v => ⌜v=VUnit⌝ ∗ pointsto l (DfracOwn 1) (replicate (length vs) x)).
Proof.
  iIntros.

  gocall 1.

  iApply (wp_bind (CtxLet _ _)).
  iApply (wp_mono with "[-]"). by iApply wp_length.
  iIntros (?) "(->&?)". iApply wp_let_val. simpl.
  iDestruct (wp_fill_aux E l x 0 vs) as "X".
  rewrite !left_id_L. by iApply "X".
Qed.

End proof.

From intdet.musketeer Require Import wpg dwp lockstep.

Section vprop.

Context `{intdetGS Σ}.

(* Is there a way to make this proof shorter?
   It share structure with proofs in priority.v *)
Lemma triple_fill E (l:loc) (x:val) vs :
  ⊢ triple E (pointsto l (DfracOwn 1) vs) (fill l x) (fun v (_:unit) => ⌜v=VUnit⌝ ∗ pointsto l (DfracOwn 1) (replicate (length vs) x))%I.
Proof.
  rewrite triple_eq. iIntros (?????) "? HPOST".
  iApply wpg_binds. iApply (wpg_mono with "[-HPOST]").
  { iApply (@wp_fill _ _ _ _ IsWP_wpl with "[$]"). }
  iIntros (?) "(->&?)". iSpecialize ("HPOST" $! VUnit tt with "[-]").
  { monPred.unseal. by iFrame. }
  iApply (wpg_mono with "[$]").
  iIntros (?) "[% (?&HP)]". iFrame.
  iIntros "(X&?)". iApply wpr_binds.
  iApply (wpr_mono with "[X]").
  { iApply (@wp_fill _ _ _ _ IsWP_wpr with "[$]"). }
  iIntros (?) "(->&?)".
  iApply "HP". monPred.unseal. by iFrame.
Qed.

End vprop.
