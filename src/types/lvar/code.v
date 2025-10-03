From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import frac_auth gmultiset.
From iris.bi Require Import monpred.


From intdet.lang Require Import syntax notations.
From intdet.musketeer Require Import wpg dwp atomic_wpg lockstep.
From intdet.types.lvar Require Import typing soundness.

Definition lv_alloc : expr :=
  λ: "v", ref "v".

Definition lv_get : expr :=
  μ: "self" "leq" "l" "x",
    let: "y" := "l".[0] in
    if: "leq" (Pair "y" "x") then VUnit else "self" "leq" "l" "x".

Definition lv_set : expr :=
  μ: "self" "leq" "lub" "l" "x",
    let: "y" := "l".[0] in
    if: "leq" (Pair "x" "y") then VUnit else
    if: CAS "l" 0 "y" ("lub" (Pair "x" "y"))
    then VUnit else "self" "leq" "lub" "l" "x".


Lemma typed_lv_alloc τ :
  typed Weak ∅ lv_alloc (TArrow Weak τ (TRef τ)).
Proof.
  econstructor. done. constructor. constructor. done.
Qed.

Lemma typed_lv_get m τ :
  typed m ∅ lv_get
    (TArrow Strong (TArrow Strong (TProd τ τ) TBool) (TArrow Strong (TRef τ) (TArrow Strong τ TUnit))).
Proof.
  repeat (econstructor; try done).
Qed.

Lemma typed_lv_set m τ :
  typed m ∅ lv_set
    (TArrow Strong (TArrow Strong (TProd τ τ) TBool) (TArrow Strong (TArrow Strong (TProd τ τ) τ) (TArrow Strong (TRef τ) (TArrow Strong τ TUnit)))).
Proof.
  repeat (econstructor; try done).
Qed.

(*
Class SemiLattice (A:Type) (f:A -> A -> A) :=
  { slat_comm : Comm eq f;
    slat_assoc : Assoc eq f;
    slat_idemp : forall x, f x x = x;
  }.

Definition leq `(SL:SemiLattice A f) : relation A :=
  fun x y => f x y = y.

(* The cmra we need *)

Class lvarG Σ A `{Countable A} :=
  LvarG { clvar_inG : inG Σ (frac_authR (gmultisetUR A)) }.
Local Existing Instance clvar_inG.

Definition lvarΣ A `{Countable A} : gFunctors :=
  #[GFunctor (frac_authR (gmultisetUR A))].

Global Instance subG_lvarΣ {Σ} `{Countable A} : subG (lvarΣ A) Σ → lvarG Σ A.
Proof. solve_inG. Qed.
 *)

(*)
Section go.

Context `{intdetGS Σ}.

Lemma dwp_fupd_r E el P er Ql Qr :
  dwp E el P er Ql (fun v1 v2 => |={E}=> Qr v1 v2) -∗
  dwp E el P er Ql Qr.
Proof.
  iIntros "Hwp".
  iApply (wpg_mono with "[$]"). iIntros (?) "(?&Hwp)". iFrame.
  iIntros. iSpecialize ("Hwp" with "[$][$]").
  iApply (wpg_strong_mono with "[$]").
  iIntros (?) "(?&>?)". by iFrame.
Qed.
*)

(*
Lemma triple_fupd E P e Q :
  triple E P e (fun v => |={E}=> Q v) -∗
  triple E P e Q.
Proof.
  iIntros "Ht". unfold triple.
  iIntros (ks F Q1 Q2) "HP Hf".
  iApply dwp_fupd_r.
  iApply ("Ht" with "[$]").
  iIntros (v) "Hv". rewrite monPred_at_fupd.
  iMod "Hv". iSpecialize ("Hf" with "[$]").
  iApply (wpg_mono with "[$]").
  iIntros (?) "(?&Hwp)". iFrame. iIntros (?) "? (H&X)".
  rewrite monPred_at_fupd. iMod "H".
  iSpecialize ("Hwp" with "[$][$]").
  iApply (wpg_mono with "[$]"). iIntros (?) "(?&?)". by iFrame.
Qed.

Lemma triple_frame_wand P' E P e Q :
  triple E P e (fun v => P' -∗ Q v)-∗
  triple E (P' ∗ P) e Q.
Proof.
  iIntros "HT".
  iApply (triple_conseq (P ∗ P')%I (fun v => (P' -∗ Q v) ∗ P')%I).
  { iIntros "(?&?)". iFrame. }
  { iIntros (?) "(X&?)". by iApply "X". }
  by iApply triple_frame.
Qed.

Lemma triple_alloc_tac E P (Q:val -> vProp Σ) (v:val) :
  (∀ (l:loc), P -∗ pointsto l (DfracOwn 1) v -∗ Q l) ->
  ⊢ triple E P (Ref v) Q.
Proof.
  iIntros (Hpost).
  iApply (triple_conseq (P ∗ True)%I Q).
  { iIntros. by iFrame. }
  { eauto. }
  iApply triple_frame_wand.
  iApply triple_conseq. 3:iApply triple_alloc. done.
  iIntros (?) "[% (->&?)] ?".
  iApply (Hpost with "[$][$]").
Qed.

Local Definition vprop_inv_def N P : vProp Σ :=
  monPred_upclosed (λ i, inv N (P i))%I.
Local Definition vprop_inv_aux : seal (@vprop_inv_def).
Proof. by eexists. Qed.
Definition vprop_inv := vprop_inv_aux.(unseal).
Local Definition vprop_wand_unseal :
  @vprop_inv = _ := vprop_inv_aux.(seal_eq).

Lemma upclose_vprop (P:bool -> iProp Σ) i :
  (∀ j : bool, ⌜i ⊑ j⌝ → P j) ⊣⊢ P i.
Proof.
  iSplit.
  { iIntros "X". iApply ("X" with "[%//]"). }
  { iIntros "X". iIntros (? Eq). inversion Eq. subst. done. }
Qed.

Lemma vprop_at_inv N P i :
  vprop_inv N P i ⊣⊢ inv N (P i).
Proof.
  rewrite vprop_wand_unseal. simpl.
  rewrite upclose_vprop //.
Qed.


Lemma vprop_inv_alloc N E (P:vProp Σ) : ▷ P ={E}=∗ vprop_inv N P.
Proof.
  constructor. iIntros (?) "_".
  rewrite vprop_at_wand monPred_at_later monPred_at_fupd vprop_at_inv.
  iApply inv_alloc.
Qed.

Context (N:namespace).

Definition islvar P l : vProp Σ :=
  vprop_inv N (∃ v, pointsto l (DfracOwn 1) v ∗ P v)%I.

Lemma lv_alloc_spec P (v:val) :
  ⊢ triple ⊤ (P v) (lv_alloc [Val v]) (fun v => ∃ (l:loc), ⌜v=l⌝ ∗ islvar P l).
Proof.
  iStartProof.

  iApply triple_fupd.
  iApply (triple_call _ _ _ _ _ _ [_]). 1,2:reflexivity.
  iApply triple_alloc_tac.
  iIntros (?) "? ?".
  iMod (vprop_inv_alloc with "[-]").
  2:{ iModIntro. iExists _. iSplitR; done. }
  { iModIntro. iExists _. iFrame. }
Qed.

Lemma triple_val E (v:val) :
  ⊢ triple E True v (fun v' => ⌜v'=v⌝).
Proof.
  iIntros (????) "_ HP".
  iSpecialize ("HP" with "[]").
  { rewrite monPred_at_pure //. }
  iApply (wpg_mono with "[$]").
  iIntros (?) "(?&Hwp)". iFrame.
  iIntros (?) "? (_&?)".
  iApply ("Hwp" with "[$]").
  rewrite monPred_at_pure //. by iFrame.
Qed.

Lemma triple_val_tac E (v:val) P :
  ⊢ triple E P v (fun v' => ⌜v'=v⌝ ∗ P).
Proof.
  iStartProof.
  iApply (triple_conseq (P ∗ True)%I _).
  { iIntros. by iFrame. }
  { eauto. }
  iApply triple_frame_wand.
  iApply triple_conseq. 3:iApply triple_val. done.
  iIntros (?) "-> ?". by iFrame.
Qed.

Lemma triple_pre E e P P' Q :
  (⌜P⌝ -∗ triple E P' e Q) -∗
  triple E (⌜P⌝ ∗ P') e Q.
Proof.
  iIntros "Ht". iIntros (????).
  rewrite monPred_at_sep monPred_at_pure.
  iIntros "(%&?) HQ".
  iSpecialize ("Ht" with "[%//][$]").
  iApply (wpg_mono with "[-]").
  { iApply "Ht". done. }
  iIntros (?) "(?&Hwp)". iFrame. iIntros (?).
  rewrite monPred_at_sep monPred_at_pure.
  iIntros "? ((_&?)&?)". iApply ("Hwp" with "[$]").
  iFrame.
Qed.

Lemma triple_code E self arg code :
  ⊢ triple E True (Code self arg code) (fun v => ⌜v=VCode self arg code⌝).
Proof.
  iIntros (????) "_ HP".
  iApply dwpk_code_l.
  iSpecialize ("HP" with "[]").
  rewrite monPred_at_pure //.
  iApply dwpk_code_r. iApply (dwpk_mono_pre_r with "[$]").
  iIntros (?) "(_&?)". rewrite monPred_at_pure. by iFrame.
Qed.

Lemma triple_code_tac E P self arg code :
  ⊢ triple E P (Code self arg code) (fun v => ⌜v=VCode self arg code⌝ ∗ P).
Proof.
  iApply (triple_conseq (True ∗ P)%I _).
  { iIntros. by iFrame. }
  { eauto. }
  iApply triple_frame.
  iApply triple_code.
Qed.

Lemma lv_get_spec P (leq x:val) (l:loc) :
  ⊢ triple ⊤ (islvar P l) (lv_get [Val leq; Val l; Val x]) (fun x => ⌜x=VUnit⌝).
Proof.
  iStartProof.

  iApply (triple_call _ _ _ _ _ _ [_;_;_]). 1,2:reflexivity.  simpl.

  iApply (triple_bind _ _ _ (CtxLet _ _)).
Admitted.

Lemma lv_set_spec P (leq lub x:val) (l:loc) :
  ⊢ triple ⊤ (islvar P l) (lv_get [Val leq; Val lub; Val l; Val x]) (fun x => ⌜x=VUnit⌝).
Proof.
  iStartProof.
Admitted.
*)
