From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import frac_auth numbers csum.

From intdet.lang Require Import syntax notations.
From intdet.musketeer Require Import wpapi.
From intdet.examples Require Export reference.

Definition ratomic_add : val :=
  μ: "self" "l" "m",
    let: "n" := "l".[0] in
    if: CAS "l" 0 "n" ("m" '+ "n") then VUnit else "self" "l" "m".

Definition rget : val :=
  λ: "l", "l".[0].

Definition rref : val :=
  λ: "n", ref "n".

(* The cmra we need *)

Class ccounterG Σ :=
  CCounterG { ccounter_inG :: inG Σ (frac_authR ZR) }.

Definition ccounterΣ : gFunctors :=
  #[GFunctor (frac_authR ZR)].

Global Instance subG_ccounterΣ {Σ} : subG ccounterΣ Σ → ccounterG Σ.
Proof. solve_inG. Qed.

Local Existing Instance ccounter_inG.

Section go.

Context `{IsWP Σ pointsto wp}.
Context `{forall l q v, Timeless (pointsto l q v)}.
Context `{ccounterG Σ, gen_heap.gen_heapGS loc (list val) Σ}.

Context (N:namespace).
Context (nm:namespace).

Definition ccounter_inv (γ : gname) (l : loc) : iProp Σ :=
  ∃ n, own γ (●F n) ∗ pointsto l (DfracOwn 1) [VInt n].

Definition ccounter_ctx (γ : gname) (l : loc) : iProp Σ :=
  inv N (ccounter_inv γ l).

Definition ccounter (l:loc) (q : frac) (n : Z) : iProp Σ :=
  ∃ γ, gen_heap.meta l nm γ ∗ ccounter_ctx γ l ∗ own γ (◯F{q} n).

Lemma ratomic_add_spec (l:loc) q (n m:Z) :
  ccounter l q n -∗
  wp ⊤ (ratomic_add (Val l) (Val m)) (fun v => ⌜v=VUnit⌝ ∗ ccounter l q (n+m)).
Proof.
  iIntros "[%γ (#Hm&#I&Hf)]".
  iLöb as "IH" forall (n).

  (* TODO write wp_call2 *)
  iApply (wp_bind (CtxCall2 _)).
  iApply wp_call. done. iModIntro. simpl.
  iApply wp_mono. iApply wp_code. iIntros (? ->).
  iApply wp_call. done. simpl. iModIntro.

  iApply (wp_bind (CtxLet _ _)).

  iInv "I" as ">[%x (Ha&Hl)]".
  left. constructor.

  iApply (wp_mono with "[Hl]").
  { iApply wp_load; last iFrame. compute_done. reflexivity. }
  iIntros (?) "(->&Hl)".

  iModIntro. iSplitR "Hf".
  { iFrame "#∗". }

  iApply wp_let_val. simpl.
  iApply (wp_bind (CtxIf _ _)).
  iApply (wp_bind (CtxCas1 _ _ _)).
  iApply wp_mono. iApply wp_call_prim. done. iIntros (? ->).
  simpl.

  iInv "I" as ">[%x' (Ha&Hl)]".
  left. constructor.

  iApply (wp_mono with "[Hl]"). iApply (wp_cas with "Hl"); done.
  iIntros (?) "(->&Hl)".
  case_bool_decide as Eq.
  { inversion Eq. subst. simpl.
    iMod (own_update_2 with "Ha Hf") as "(Ha&Hf)".
    { apply frac_auth_update. apply (Z_local_update _ _ (m+x) (n+m)). lia. }
    iModIntro. iSplitR "Hf". iFrame.
    iApply wp_if. iApply wp_val. done. by iFrame "#∗". }
  { iModIntro. iSplitR "Hf". iFrame.
    iApply wp_if. by iApply "IH". }
Qed.

Lemma rget_spec (l:loc) (n:Z) :
  ccounter l 1 n -∗
  wp ⊤ (rget (Val l)) (fun v => ⌜v=n⌝ ∗ ccounter l 1 n).
Proof.
  iIntros "[%γ (#Hm&#I&Hf)]".
  iApply wp_call. done. iModIntro. simpl.

  iInv "I" as ">[%x (Ha&Hl)]".
  left. constructor.

  iDestruct (own_valid_2 with "Ha Hf") as "%Hv".
  apply frac_auth_agree_L in Hv. subst.

  iApply (wp_mono with "[Hl]").
  { iApply (wp_load with "Hl"); last done. done. }
  iIntros (?) "(->&?)".

  iModIntro. iSplitR "Hf". iFrame.
  by iFrame "#∗".
Qed.

Lemma counter_split l (q1 q2:Qp) (n1 n2:Z) :
  ccounter l (q1 + q2) (n1 + n2) ⊣⊢ ccounter l q1 n1 ∗ ccounter l q2 n2.
Proof.
  iSplit.
  { iIntros "(%&#?&#?&(?&?))". iFrame "#∗". }
  { iIntros "((%&#X1&#?&U1)&(%&#X2&_&U2))".
    iDestruct (gen_heap.meta_agree with "X1 X2") as "->".
    iCombine "U1 U2" as "U".
    iFrame "#∗". }
Qed.

End go.

From intdet.musketeer Require Import wpg dwp lockstep.

Section vprop.

Context `{intdetGS Σ, ccounterG Σ}.

Definition vcounter l q i : vProp Σ :=
  MonPred (fun (b:bool) => @ccounter _ _  (if b then pointstol else pointstor) _ _ _ _ nroot (if b then nm_left else nm_right) l q i) _.

Lemma triple_ratomic_add (l:loc) q (n m:Z) :
  ⊢ triple ⊤ (vcounter l q n) (ratomic_add l m) (fun v (_:unit) => ⌜v=VUnit⌝ ∗ vcounter l q (n+m)).
Proof.
  rewrite triple_eq. rewrite /vcounter. monPred.unseal.
  iIntros (?????) "X HPOST".
  iApply wpg_binds. iApply (wpg_mono with "[-HPOST]").
  { iApply (@ratomic_add_spec _ _ _ _ IsWP_wpl with "[$]"). }
  iIntros (?) "(->&?)". iSpecialize ("HPOST" $! VUnit tt with "[-]").
  { by iFrame. }
  iApply (wpg_mono with "[$]").
  iIntros (?) "[% (?&HP)]". iFrame.
  iIntros "(X&?)". iApply wpr_binds.
  iApply (wpr_mono with "[X]").
  { iApply (@ratomic_add_spec _ _ _ _ IsWP_wpr with "[$]"). }
  iIntros (?) "(->&?)".
  iApply "HP". by iFrame.
Qed.

Lemma triple_rget (l:loc) (n:Z) :
  ⊢ triple ⊤ (vcounter l 1 n) (rget l) (fun v (_:unit) => ⌜v=n⌝ ∗ vcounter l 1 n).
Proof.
  rewrite triple_eq. rewrite /vcounter. monPred.unseal.
  iIntros (?????) "X HPOST".
  iApply wpg_binds. iApply (wpg_mono with "[-HPOST]").
  { iApply (@rget_spec _ _ _ _ IsWP_wpl with "[$]"). }
  iIntros (?) "(->&?)". iSpecialize ("HPOST" $! (VInt n) tt with "[-]").
  { by iFrame. }
  iApply (wpg_mono with "[$]").
  iIntros (?) "[% (?&HP)]". iFrame.
  iIntros "(X&?)". iApply wpr_binds.
  iApply (wpr_mono with "[X]").
  { iApply (@rget_spec _ _ _ _ IsWP_wpr with "[$]"). }
  iIntros (?) "(->&?)".
  iApply "HP". by iFrame.
Qed.

Lemma triple_rref (i:Z) :
  ⊢ triple ⊤ True (rref i) (fun v (l:loc) => ⌜v=l⌝ ∗  vcounter l 1 i).
Proof.
  iApply triple_call'. done. iModIntro. simpl.
  iApply triple_end. iApply triple_ref.
  iIntros (? []).

  iApply triple_extrude_existential.
  { monPred.unseal.
    iIntros (?) "(->&_) !>".
    iIntros (?) "(%E&_)". inversion E. done. }
  iIntros (l).
  iApply tactics_triple.triple_extract_pure_pre.
  iIntros "->".

  iApply triple_fupd.
  iApply (triple_resolve l).
  iApply triple_val'. constructor. iIntros (b).
  monPred.unseal.
  iIntros "(X1&X2)". iSplitR; first done.
  destruct b.
  { iMod (own_alloc (●F i ⋅ ◯F i)) as (γ) "[Hγ Hγ']";
      first by apply auth_both_valid_discrete.
    iMod (gen_heap.meta_set with "[$]") as "?". reflexivity.
    iExists γ. iFrame.
    iApply invariants.inv_alloc. iFrame. }
  { iMod (own_alloc (●F i ⋅ ◯F i)) as (γ) "[Hγ Hγ']";
      first by apply auth_both_valid_discrete.
    iMod (gen_heap.meta_set with "[$]") as "?". reflexivity.
    iExists γ. iFrame.
    iApply invariants.inv_alloc. iFrame. }
Qed.

Lemma vcounter_split l (q1 q2:Qp) (n1 n2:Z) :
  vcounter l (q1 + q2) (n1 + n2) ⊣⊢ vcounter l q1 n1 ∗ vcounter l q2 n2.
Proof.
  constructor. monPred.unseal. intros []; simpl; apply counter_split.
Qed.

End vprop.


From intdet.angelic Require Import run.
From intdet.examples Require Import filter_compact_seq.

Section angelic.

Context `{X:seqlogGS Σ}.

Lemma run_rref (i:Z) :
  ⊢ run (rref i) (fun (v:val) => ∃ l, ⌜v=VLoc l⌝ ∗ pointsto l (DfracOwn 1) [VInt i]).
Proof.
  iIntros.
  iApply run_call. simpl.
  iApply ref_spec.
Qed.

Lemma run_ratomic_add (l:loc) (i j:Z) :
  pointsto l (DfracOwn 1) [VInt i] -∗
  run (ratomic_add l j) (fun v => ⌜v=VUnit⌝ ∗ pointsto l (DfracOwn 1) [VInt (i+j)]).
Proof.
  iIntros "?".

  iApply (run_bind (CtxCall2 _)).
  iApply run_call; iApply run_code; iApply run_val.
  iApply run_call. simpl.

  iApply (run_bind (CtxLet _ _)).
  iApply (run_mono with "[-]").
  by iApply (run_load with "[$]").
  iIntros (?) "(->&?)". iApply run_let_val. simpl.

  iApply (run_bind (CtxIf _ _)).
  iApply (run_bind (CtxCas1 _ _ _)).
  iApply run_mono. iApply run_call_prim. done.
  iIntros (? ->).
  iApply (run_mono with "[-]").
  iApply (run_cas with "[$]"). 1,2:done.
  simpl.
  iIntros (?) "(->&?)".
  rewrite bool_decide_eq_true_2 //.
  iApply run_if. iApply run_val. rewrite comm_L.
  by iFrame.
Qed.

Lemma run_rget (l:loc) (i:Z) :
  pointsto l (DfracOwn 1) [VInt i] -∗
  run (rget l) (fun v => ⌜v=VInt i⌝ ∗ pointsto l (DfracOwn 1) [VInt i]).
Proof.
  iIntros.
  iApply run_call. simpl.
  iApply (run_mono with "[-]").
  by iApply (run_load with "[$]").
  iIntros (?) "(->&?)". by iFrame.
Qed.

End angelic.
