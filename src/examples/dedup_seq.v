From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export cancelable_invariants.
From iris.algebra Require Import gmap gmultiset agree frac_auth gset.

From intdet.lang Require Import syntax syntax_instances notations head_semantics.
From intdet.utils Require Import elems big_opN more_maps_and_sets.

From intdet.examples Require Import reference fill_seq filter_compact_seq tactics hashtbl_seq hashtbl_pure dedup parfor_seq.

From intdet.angelic Require Import run.


Section proof.

Context `{seqlogGS Σ}.

Local Lemma dedup_aux (i:nat) l q vs p v g :
  length vs ≤ cap p ->
  size g <= i ->
  Forall (hashtbl.can_insert v) vs ->
  pointsto l q vs -∗
  hashset p v g -∗
  forspec i (length vs - i)%nat (λ:"i",let: "x" := #l.["i"] in hashtbl.htbl_add v "x")
    (hashset p v (g ∪ list_to_set (drop i vs)) ∗ pointsto l q vs).
Proof.
  iIntros (X1 X2 X3) " Hl Hh".
  remember (length vs - i) as k.
  iInduction k as [] "IH" forall (i Heqk g X2).
  { simpl. rewrite drop_ge. 2:lia. simpl.
    rewrite right_id_L //. iFrame. }
  iApply run_call. simpl.

  assert (is_Some (vs !! Z.to_nat i)) as (x&Hx).
  { apply lookup_lt_is_Some_2. lia. }

  iApply (run_bind (CtxLet _ _)).
  iApply (run_mono with "[Hl]").
  iApply run_load. 2:done. lia. done.

  rewrite Nat2Z.id in Hx.
  iIntros (?) "(->&?)". iApply run_let_val. simpl.

  iApply (run_mono with "[Hh]").
  iApply (wp_insert with "Hh").
  { lia. }
  { by eapply Forall_lookup_1. }

  iIntros (?) "(->&?)". iSplitR; first done.
  iApply (forspec_mono with "[-]").
  iApply ("IH" with "[%][%][$][$]"). lia.
  { destruct_decide (decide (x ∈ g)).
    { replace ({[x]} ∪ g) with g by set_solver. lia. }
    { rewrite size_union. 2:set_solver. rewrite size_singleton. lia. } }

  apply drop_S in Hx. rewrite Hx. rewrite list_to_set_cons.
  iIntros.
  replace ({[x]} ∪ g ∪ list_to_set (drop (S i) vs)) with (g ∪ ({[x]} ∪ list_to_set (drop (S i) vs))). done. set_solver.
Qed.

Lemma dedup_spec (l:loc) (q:dfrac) (d:val) (vs:list val) (hash0:val -> nat) (cmp0: val -> val -> bool) (c h:val) :
  TotalOrder cmp0 ->
  (∀ v, Forall (hashtbl.can_insert v) vs) ->
  □ cmp_spec cmp0 c -∗
  □ hash_spec hash0 h -∗
  pointsto l q vs -∗
  run (dedup h c l) (fun v => ∃ l' ws, ⌜v=VPair (VLoc l) (VLoc l')⌝ ∗ pointsto l' (DfracOwn 1) ws ∗ pointsto l q vs ∗ ⌜deduped ws (list_to_set vs)⌝)%I.
Proof.

  iIntros (??) "#X1 #X2 Hl".

  iApply (run_bind (CtxCall2 _)).
  iApply run_code. iApply run_val. simpl.
  iApply run_call. simpl.

  iApply run_let_val. simpl.
  iApply (run_bind (CtxLet _ _)).
  iApply (run_mono with "[Hl]").
  by iApply run_length.
  iIntros (?) "(->&Hl)". iApply run_let_val. simpl.

  iApply (run_bind (CtxLet _ _)).
  iApply (run_bind (CtxCall1 _)).
  iApply run_mono. iApply run_call_prim. done.
  iIntros (? ->). simpl.

  iApply run_mono.
  { iApply (hstbl_alloc_spec with "X1 X2"). lia. }

  iIntros (?) "(%p&?&%Hcap)".
  simpl. iApply run_let_val. simpl.

  iApply (run_bind (CtxLet _ _)).
  iApply (run_bind (CtxCall1 _)). iApply run_code. iApply run_val. simpl.
  iClear "X1 X2".

  iApply (run_mono with "[-]").
  { iPoseProof (parfor_seq_spec 0 (length vs) _ (hashset p v (list_to_set vs) ∗ pointsto l q vs)) as "X".
    rewrite right_id. iApply "X". iClear "X".
    iDestruct (dedup_aux 0 with "[$][$]") as "X". lia. done.
    { eauto. }
    rewrite right_id drop_0 left_id_L. done. }
  { iIntros (?) "(->&?&Hl)". iApply run_let_val. simpl.
    iApply (run_bind (CtxLet _ _)).
    iApply (run_mono with "[-Hl]").
    iApply (elems_spec with "[$]").
    iIntros (?) "(%&%&(->&%)&?)". simpl.
    iApply run_let_val. simpl.
    iApply run_mono. iApply run_pair. iIntros (? ->).
    iExists _,_. by iFrame. }
Qed.

End proof.
