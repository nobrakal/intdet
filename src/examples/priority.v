From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import frac_auth numbers csum.

From intdet.lang Require Import syntax notations.
From intdet.musketeer Require Import wpapi.
From intdet.examples Require Export reference.

Definition pwrite : val :=
  μ: "self" "l" "m",
    let: "n" := "l".[0] in
    if: "m" '≤ "n" then VUnit else
      if: CAS "l" 0 "n" "m" then VUnit else "self" "l" "m".

Definition pread : val :=
  λ: "l", "l".[0].

Definition palloc : val :=
  λ: "n", ref "n".

(* The cmra we need *)

Class priorityG Σ :=
  PriorityG { cpriority_inG : inG Σ (frac_authR (csumR max_Z (agreeR Z))) }.
Local Existing Instance cpriority_inG.

Definition priorityΣ : gFunctors :=
  #[GFunctor (frac_authR (csumR max_Z (agreeR Z)))].

Global Instance subG_priorityΣ {Σ} : subG priorityΣ Σ → priorityG Σ.
Proof. solve_inG. Qed.

Section go.

Context `{IsWP Σ pointsto wp}.
Context `{forall l q v, Timeless (pointsto l q v)}.
Context `{priorityG Σ, gen_heap.gen_heapGS loc (list val) Σ}.

Context (N:namespace).
Context (nm:namespace).

Definition own_prio γ (b:bool) i :=
  own γ (●F (if b then Cinl (MaxZ i) else Cinr (to_agree i))).

Definition priority_inner γ l : iProp Σ :=
  ∃ i (b:bool), pointsto l (DfracOwn 1) [VInt i] ∗ own_prio γ b i.

Definition priority_at_least l q i : iProp Σ :=
  ∃ γ, gen_heap.meta l nm γ ∗ inv N (priority_inner γ l) ∗ own γ (◯F{q} (Cinl (MaxZ i))).

Definition priority_is l q i : iProp Σ :=
  ∃ γ, gen_heap.meta l nm γ ∗ inv N (priority_inner γ l) ∗ own γ (◯F{q} (Cinr (to_agree i))).

Lemma priority_confront l q1 i1 q2 i2 :
  priority_at_least l q1 i1 -∗ priority_is l q2 i2 -∗ ⌜False⌝.
Proof.
  iIntros "(%&X1&_&X2)".
  iIntros "(%&X3&_&X4)".
  iDestruct (gen_heap.meta_agree with "X1 X3") as "->".
  iDestruct (own_valid_2 with "X2 X4") as "%Hv".
  iPureIntro. rewrite -frac_auth_frag_op in Hv.
  apply frac_auth_frag_op_valid in Hv. destruct Hv as (_&Hv).
  done.
Qed.

Lemma own_prio_at_least γ b i n q :
  own_prio γ b i -∗
  own γ (◯F{q} (Cinl (MaxZ n))) -∗
  ⌜b=true /\ n <= i /\ (q=1%Qp -> n = i)⌝%Z.
Proof.
  iIntros "Ha Hf".
  iDestruct (own_valid_2 with "Ha Hf") as "%Hx".
  destruct_decide (decide (q=1%Qp)).
  { subst. apply frac_auth_agree in Hx.
    destruct b; inversion Hx. subst. inversion H7. subst. eauto. }
  apply frac_auth_included in Hx.
  iPureIntro.
  apply Some_csum_included in Hx.
  destruct Hx as [Hx | Hx].
  { by destruct b. }
  destruct Hx as [Hx | Hx].
  { destruct Hx as (?&?&X1&X2&X3).
    inversion X1. destruct b; inversion X2. subst.
    apply Some_included_total, max_Z_included in X3. simpl in *.
    naive_solver. }
  { destruct Hx as (?&?&X&_). naive_solver. }
Qed.

Lemma own_prio_is γ b i n q :
  own_prio γ b i -∗
  own γ (◯F{q} (Cinr (to_agree n))) -∗
  ⌜b=false /\ n = i⌝%Z.
Proof.
  iIntros "Ha Hf".
  iDestruct (own_valid_2 with "Ha Hf") as "%Hx".
  apply frac_auth_included in Hx.
  iPureIntro.
  apply Some_csum_included in Hx.
  destruct Hx as [Hx | Hx].
  { by destruct b. }
  destruct Hx as [Hx | Hx].
  { destruct Hx as (?&?&X&_). naive_solver. }
  { destruct Hx as (?&?&X1&X2&X3).
    inversion X1. destruct b; inversion X2. subst.
    apply Some_included_total, to_agree_included in X3.
    eauto. }
Qed.

Lemma prio_at_least_to_is l i :
  priority_at_least l 1 i ={↑N}=∗ priority_is l 1 i.
Proof.
  iIntros "[%γ' (X2&#I&Hf)]".
  iInv "I" as ">[%x' [%b (Hl&Ha)]]".
  iDestruct (own_prio_at_least with "Ha Hf") as "(->&%_&%eq)".
  rewrite eq //.
  iMod (own_update_2 with "Ha Hf") as "(Ha&Hf)".
  { simpl. apply frac_auth_update_1. shelve. }
  iFrame. iModIntro. iSplitL; last by iFrame.
  iModIntro. iExists false. iFrame.
  Unshelve. constructor.
Qed.

Lemma prio_is_to_at_least l i :
  priority_is l 1 i ={↑N}=∗ priority_at_least l 1 i.
Proof.
  iIntros "[%γ' (X2&#I&Hf)]".
  iInv "I" as ">[%x' [%b (Hl&Ha)]]".

  iDestruct (own_prio_is with "Ha Hf") as "(->&->)".
  iMod (own_update_2 with "Ha Hf") as "(Ha&Hf)".
  { simpl. apply frac_auth_update_1. shelve. }
  iFrame. iModIntro. iSplitL; last by iFrame.
  iModIntro. iExists true. iFrame.
  Unshelve. constructor.
Qed.

Lemma max_Z_local_update' (x y y' : max_Z) :
  (max_Z_car y ≤ max_Z_car y')%Z ->
  (max_Z_car y' ≤ max_Z_car x)%Z ->
  (x,y) ~l~> (x,y').
Proof.
  move: x y y' => [x] [y] [y'] /= ??.
  rewrite local_update_discrete => [ [ [ z ] | ] ] //= _ [?].
  split; first done. rewrite max_Z_op. f_equal. lia.
  split; first done. f_equal. lia.
Qed.

Lemma own_prio_at_least_upd_1 x γ i n q :
  (n ≤ x)%Z -> (x <= i)%Z ->
  own_prio γ true i -∗
  own γ (◯F{q} (Cinl (MaxZ n))) ==∗
  own_prio γ true i ∗  own γ (◯F{q} (Cinl (MaxZ x))).
Proof.
  iIntros (??) "Ha Hf".
  iMod (own_update_2 with "Ha Hf") as "(Ha&Hf)"; last by iFrame.
  apply frac_auth_update.
  apply csum_local_update_l.
  apply max_Z_local_update' with (y':=(MaxZ x)); eauto.
Qed.

Lemma own_prio_at_least_upd_2 x γ i n q :
  (i <= x)%Z ->
  own_prio γ true i -∗
  own γ (◯F{q} (Cinl (MaxZ n))) ==∗
  own_prio γ true x ∗ own γ (◯F{q} (Cinl (MaxZ x))).
Proof.
  iIntros (?) "Ha Hf".
  iMod (own_update_2 with "Ha Hf") as "(Ha&Hf)"; last by iFrame.
  apply frac_auth_update.
  apply csum_local_update_l.
  apply max_Z_local_update with (x':=(MaxZ x)); eauto.
Qed.

Lemma pwrite_spec (l:loc) q (n m:Z) :
  priority_at_least l q n -∗
  wp ⊤ (pwrite (Val l) (Val m)) (fun v => ⌜v=VUnit⌝ ∗ priority_at_least l q (n `max` m)).
Proof.
  iIntros "[%γ (Hm1&#I&Hf)]".
  iLöb as "IH" forall (n).

  (* TODO write wp_call2 *)
  iApply (wp_bind (CtxCall2 _)).
  iApply wp_call. done. iModIntro. simpl.
  iApply wp_mono. iApply wp_code. iIntros (? ->).
  iApply wp_call. done. simpl. iModIntro.

  iApply (wp_bind (CtxLet _ _)).

  iInv "I" as ">[%x [%b (Hl&Ha)]]".
  left. constructor.
  iDestruct (own_prio_at_least with "Ha Hf") as "(->&%)".

  iApply (wp_mono with "[Hl]").
  { iApply wp_load; last iFrame. compute_done. reflexivity. }
  iIntros (?) "(->&Hl)".

  (* tricky *)
  iMod (own_prio_at_least_upd_1 (if m <=? x then n `max` m else x)%Z with "Ha Hf") as "(Ha&Hf)".
    1,2:destruct (m <=? x)%Z eqn:?; simpl; lia.

  iModIntro. iFrame. simpl.

  iApply wp_let_val. simpl.

  iApply (wp_bind (CtxIf _ _)).
  iApply wp_mono.
  { by iApply wp_call_prim. }
  iIntros (b ->). simpl.

  iApply wp_if.
  destruct (m <=? x)%Z eqn:?.
  { iApply wp_val. naive_solver. by iFrame "#∗". }

  iApply (wp_bind (CtxIf _ _)).

  iInv "I" as ">[%x' [%b (Hl&Ha)]]".
  left. constructor.

  iApply (wp_mono with "[Hl]").
  { iApply wp_cas; last iFrame. compute_done. reflexivity. }
  simpl. iIntros (?) "(->&Hl)".

  iDestruct (own_prio_at_least with "Ha Hf") as "(->&%Hx')".

  case_bool_decide as X.
  { inversion X. subst.
    iMod (own_prio_at_least_upd_2 m with "Ha Hf") as "(Ha&Hf)". lia.

    iModIntro. iFrame.
    iApply wp_if. iApply wp_val. naive_solver.
    replace (n `max` m)%Z with m by lia. by iFrame "#∗". }
  { iModIntro. iFrame. iApply wp_if.
    iSpecialize ("IH" with "[$] Hf").
    iApply (wp_mono with "IH").
    iIntros (?) "(?&?)".
    replace (n `max` m)%Z with (x `max` m)%Z by lia.
    iFrame. }
Qed.

Lemma pread_spec (l:loc) q (n:Z) :
  priority_is l q n -∗
  wp ⊤ (pread (Val l)) (fun v => ⌜v=VInt n⌝ ∗ priority_is l q n).
Proof.
  iIntros "[%γ (Hm1&#I&Hf)]".

  iApply wp_call. done.
  simpl. iModIntro.

  iInv "I" as ">[%x [%b (Hl&Ha)]]".
  left. constructor.

  iDestruct (own_prio_is with "Ha Hf") as "(->&->)".
  iApply (wp_mono with "[Hl]").
  { iApply wp_load; last iFrame. compute_done. reflexivity. }
  iIntros (?) "(->&?)". by iFrame "#∗".
Qed.

Lemma priority_is_split l q q' i :
  priority_is l (q+q') i -∗ priority_is l q i ∗ priority_is l q' i.
Proof.
  iIntros "[% (#?&#?&(?&?))]". by iFrame "#∗".
Qed.

Lemma priority_is_agree l q q' i j :
  priority_is l q i -∗ priority_is l q' j -∗ ⌜i=j⌝.
Proof.
  iIntros "[% (X1&I&E1)] [% (#X2&_&E2)]".
  iDestruct (gen_heap.meta_agree with "X2 X1") as "->".
  iDestruct (own_valid_2 with "E1 E2") as "%Hv".
  iPureIntro. apply frac_auth_frag_valid in Hv.
  destruct Hv as (_&Hv). simpl in *.
  rewrite -Cinr_op Cinr_valid to_agree_op_valid in Hv.
  done.
Qed.

Lemma priority_is_join l q q' i :
  priority_is l q i -∗ priority_is l q' i -∗ priority_is l (q+q') i.
Proof.
  iIntros "[% (X1&I&E1)] [% (#X2&_&E2)]".
  iDestruct (gen_heap.meta_agree with "X2 X1") as "->".
  iFrame "#". iCombine "E1 E2" as "?". iFrame.
Qed.

Lemma priority_at_least_split l q q' i j :
  priority_at_least l (q+q') (Z.max i j) -∗ priority_at_least l q i ∗ priority_at_least l q' j.
Proof.
  iIntros "[% (#?&#?&?)]". iFrame "#". iApply own_op.
  rewrite -frac_auth_frag_op -Cinl_op max_Z_op //.
Qed.

Lemma priority_at_least_join l q q' i j :
  priority_at_least l q i -∗ priority_at_least l q' j -∗ priority_at_least l (q+q') (Z.max i j).
Proof.
  iIntros "[% (X1&I&E1)] [% (#X2&_&E2)]".
  iDestruct (gen_heap.meta_agree with "X2 X1") as "->".
  iFrame "#". iCombine "E1 E2" as "?". iFrame.
Qed.

End go.

From intdet.musketeer Require Import wpg dwp lockstep.

Section vprop.

Context `{intdetGS Σ, priorityG Σ}.

Definition is_priority_at_least l q i : vProp Σ :=
  MonPred (fun (b:bool) => @priority_at_least _ _  (if b then pointstol else pointstor) _ _ _ _ nroot (if b then nm_left else nm_right) l q i) _.

Definition is_priority_is l q i : vProp Σ :=
  MonPred (fun (b:bool) => @priority_is _ _ (if b then pointstol else pointstor) _ _ _ _ nroot (if b then nm_left else nm_right) l q i) _.

Lemma is_prio_is_to_at_least l i :
  is_priority_is l 1 i ={⊤}=∗ is_priority_at_least l 1 i.
Proof.
  constructor. intros. monPred.unseal. iIntros (_ ? ->) "?".
  iMod fupd_mask_subseteq. shelve.
  iMod (prio_is_to_at_least with "[$]") as "?". by iFrame.
  Unshelve. set_solver. intros. destruct j; apply _.
Qed.

Lemma is_prio_at_least_to_is l i :
  is_priority_at_least l 1 i ={⊤}=∗ is_priority_is l 1 i.
Proof.
  constructor. intros. monPred.unseal. iIntros (_ ? ->) "?".
  iMod fupd_mask_subseteq. shelve.
  iMod (prio_at_least_to_is with "[$]") as "?". by iFrame.
  Unshelve. set_solver. intros. destruct j; apply _.
Qed.

Lemma is_priority_is_agree l q q' i j :
  is_priority_is l q i -∗ is_priority_is l q' j -∗ ⌜i=j⌝.
Proof.
  apply bi.entails_wand'. constructor. intros. rewrite vprop_at_wand monPred_at_pure.
  iApply priority_is_agree.
Qed.

Lemma is_priority_is_split l q q' i :
  is_priority_is l (q+q') i -∗ is_priority_is l q i ∗ is_priority_is l q' i.
Proof.
  apply bi.entails_wand'. constructor. monPred.unseal. intros.
  iApply priority_is_split.
Qed.

Lemma is_priority_is_join l q q' i :
  is_priority_is l q i -∗ is_priority_is l q' i -∗ is_priority_is l (q+q') i.
Proof.
  apply bi.entails_wand'. constructor. intros. rewrite vprop_at_wand.
  iApply priority_is_join.
Qed.

Lemma is_priority_at_least_split l q q' i j :
  is_priority_at_least l (q+q') (Z.max i j) -∗ is_priority_at_least l q i ∗ is_priority_at_least l q' j.
Proof.
  apply bi.entails_wand'. constructor. monPred.unseal. intros.
  iApply priority_at_least_split.
Qed.

Lemma is_priority_at_least_join l q q' i j :
  is_priority_at_least l q i -∗ is_priority_at_least l q' j -∗ is_priority_at_least l (q+q') (Z.max i j).
Proof.
  apply bi.entails_wand'. constructor. intros. rewrite vprop_at_wand.
  iApply priority_at_least_join.
Qed.

Lemma triple_pwrite l q (n m:Z) :
  ⊢ triple ⊤ (is_priority_at_least l q n)%I (pwrite (Val l) (Val m)) (fun v (_:unit) => ⌜v=VUnit⌝ ∗ is_priority_at_least l q (n `max` m))%I.
Proof.
  rewrite triple_eq. rewrite /is_priority_at_least. monPred.unseal.
  iIntros (?????) "X HPOST".
  iApply wpg_binds. iApply (wpg_mono with "[-HPOST]").
  { iApply (@pwrite_spec _ _ _ _ IsWP_wpl with "[$]"). }
  iIntros (?) "(->&?)". iSpecialize ("HPOST" $! VUnit tt with "[-]").
  { by iFrame. }
  iApply (wpg_mono with "[$]").
  iIntros (?) "[% (?&HP)]". iFrame.
  iIntros "(X&?)". iApply wpr_binds.
  iApply (wpr_mono with "[X]").
  { iApply (@pwrite_spec _ _ _ _ IsWP_wpr with "[$]"). }
  iIntros (?) "(->&?)".
  iApply "HP". by iFrame.
Qed.

Lemma triple_pread l q (n:Z):
  ⊢ triple ⊤ (is_priority_is l q n) (pread (Val l)) (fun v (_:unit) => ⌜v=VInt n⌝ ∗ is_priority_is l q n).
Proof.
  rewrite triple_eq. rewrite /is_priority_at_least. monPred.unseal.
  iIntros (?????) "X HPOST".
  iApply wpg_binds. iApply (wpg_mono with "[-HPOST]").
  { iApply (@pread_spec _ _ _ _ IsWP_wpl with "[$]"). }
  iIntros (?) "(->&?)". iSpecialize ("HPOST" $! (VInt n) tt with "[-]").
  { by iFrame. }
  iApply (wpg_mono with "[$]").
  iIntros (?) "[% (?&HP)]". iFrame.
  iIntros "(X&?)". iApply wpr_binds.
  iApply (wpr_mono with "[X]").
  { iApply (@pread_spec _ _ _ _ IsWP_wpr with "[$]"). }
  iIntros (?) "(->&?)".
  iApply "HP". by iFrame.
Qed.

Lemma triple_palloc (n:Z):
  ⊢ triple ⊤ True%I (palloc (Val n)) (fun v (_:unit) => ∃ l, ⌜v=VLoc l⌝ ∗ is_priority_at_least l 1 n).
Proof.
  iStartProof.
  iApply (triple_conseq_pre (▷ True%I)).
  { by iIntros. }
  iApply triple_call. done.
  iModIntro.

  iApply triple_fupd.
  iApply triple_conseq_post.
  2:iApply triple_ref.
  iIntros (? []) "[% (->&?&?)]".
  iStopProof. constructor. intros. monPred.unseal. destruct i.
  { iIntros "(?&?)".
    iMod (@own_alloc _ _ cpriority_inG) as "[% (?&?)]".
    shelve. iFrame. iMod (gen_heap.meta_set with "[$]") as "#?"; last iFrame "#".
    set_solver.
    iSplitR; first done.
    iApply invariants.inv_alloc. by iFrame. }
  { iIntros "(?&?)".
    iMod (@own_alloc _ _ cpriority_inG) as "[% (?&?)]".
    shelve. iFrame. iMod (gen_heap.meta_set with "[$]") as "#?"; last iFrame "#". set_solver.
    iSplitR; first done.
    iApply invariants.inv_alloc. by iFrame. }
  Unshelve. 2,4:exact true.
  all: apply frac_auth_valid; done.
Qed.

Lemma is_priority_confront l q1 i1 q2 i2 :
  is_priority_at_least l q1 i1 -∗ is_priority_is l q2 i2 -∗ ⌜False⌝.
Proof.
  constructor. intros. rewrite !vprop_at_wand monPred_at_pure.
  iIntros. iApply (priority_confront with "[$][$]").
Qed.
End vprop.
