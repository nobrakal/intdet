From iris.proofmode Require Import proofmode.

From intdet.lang Require Import notations.
From intdet.musketeer Require Import dwp lockstep.

From intdet.examples Require Export tactics_triple.
From intdet.utils Require Import big_opN.

(* The parallel for loop, as in MPL
   https://github.com/MPLLang/mpl/blob/f10dab421626e4da2c289c4fa1ce5520808b45de/basis-library/schedulers/shh/Scheduler.sml
 *)

Definition ignore (e:expr) : expr := (e ;; VUnit).

Definition parfor : val :=
  μ: "self" "i" "j" "f",
    let: "diff" := "j" '- "i" in
    if: "diff" '≤ 0 then VUnit else
      if: "diff" '== 1 then "f" "i" else
      let: "mid" := "i" '+ ("diff" '/ 2) in
    ignore (Par ("self" "i" "mid" "f") ("self" "mid" "j" "f")).

Section proof.

Context `{intdetGS Σ}.

Lemma parfor_spec {A} E (n m:Z) (f:val) P (Q:Z -> A -> vProp Σ) :
  ([∗ Z] i ∈ [n; m], triple E (P i) (f i) (fun v a => ⌜v=VUnit⌝ ∗ Q i a)) -∗
  triple E ([∗ Z] i ∈ [n;m], P i) (parfor n m f) (fun w (vs:list A) => ⌜w=VUnit /\ length vs = Z.to_nat (m - n)⌝  ∗ [∗ list] i ↦ v ∈ vs, Q (n+i)%Z v).
Proof.
  iIntros "HPs".
  iLöb as "IH" forall (n m).

  iApply (triple_bind (CtxCall2 _)).
  iApply (triple_bind (CtxCall2 _)).
  call1. call2. call3. call1. call2. call3.
  call1. simpl. fold parfor.

  iApply (triple_bind (CtxLet _ _)).
  iApply triple_call_prim'. done. simpl.
  iIntros (? []).
  iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_let_val. simpl.

  iApply (triple_bind (CtxIf _ _)).
  iApply triple_call_prim'. done. simpl.
  iIntros (? []). simpl.
  iApply triple_extract_pure_pre. iIntros "->".

  iApply triple_if. iIntros (? X). inversion X. subst. clear X.
  destruct ((m - n <=? 0%nat)%Z) eqn:Hmn.
  { apply Z.leb_le in Hmn.
    iApply (triple_resolve nil).
    iApply triple_val'. iIntros.
    iSplitR; last done.
    iPureIntro. split; first done. simpl. lia. }
  apply Z.leb_gt in Hmn.

  iApply (triple_bind (CtxIf _ _)).
  iApply triple_call_prim'. done. simpl.
  iIntros (? []).
  iApply triple_extract_pure_pre. iIntros "->".

  iApply triple_if.
  iIntros (? X). inversion X. subst. clear X.
  case_bool_decide as E2.
  { inversion E2.
    assert (m = n + 1)%Z as -> by lia.
    rewrite !(big_sepZ_S n _). 2,3:lia.
    iDestruct "HPs" as "(?&_)".
    rewrite big_sepZ_0 // right_id.

    iApply (triple_shift (fun x => [x])).
    iApply (triple_conseq_post with "[$]").
    iIntros (??) "(->&?)". simpl.
    rewrite !right_id //. iFrame.
    iPureIntro. split; first done. lia. }

  iApply (triple_bind (CtxLet _ _)).
  iApply (triple_bind (CtxCallPrim1 _ _)).
  iApply triple_call_prim'. done. simpl.
  iIntros (? []).
  iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_call_prim'. done. simpl.
  iIntros (? []).
  iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_let_val. simpl.

  pose (mid := (n + (m-n) /2) : Z).
  replace (VInt (n + (m - n) `div` 2%nat)) with (VInt mid).
  2:{ f_equal. }
  assert (n < m)%Z by lia.
  assert (n <= mid <= m)%Z.
  { subst mid.
    assert (0 ≤ (m - n) `div` 2)%Z.
    { apply Z_div_pos. lia. lia. }
    split; first lia.
    rewrite (Z.sub_le_mono_r _ _ n).
    replace (n + (m - n) `div` 2 - n)%Z with ((m - n) `div` 2)%Z by lia.
    apply Z.div_le_upper_bound. lia. lia. }

  rewrite !(big_sepZ_add mid n m); only 2,3: eauto.
  iDestruct "HPs" as "(X1&X2)".

  iApply (triple_bind (CtxLet _ _) with "[-]").
  { iApply (triple_par with "[X1][X2]").
    { iApply ("IH" with "X1"). }
    { iApply ("IH" with "X2"). } }

  iIntros (? (vs1&vs2)). iApply triple_let_val. simpl.
  iApply (triple_resolve (vs1 ++ vs2)).
  iApply triple_val'.
  iIntros "(%&%&_&((_&%)&?)&((_&%)&?))".
  iSplitR.
  { iPureIntro. split; first done. rewrite app_length. lia. }
  iApply big_sepL_app. iFrame.
  iApply (big_sepL_mono with "[$]").
  iIntros (???).
  replace (mid + k)%Z with (n + (length vs1 + k)%nat)%Z by lia.
  reflexivity.
Qed.

End proof.
