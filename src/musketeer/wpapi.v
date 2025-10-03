From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.

From intdet.lang Require Import syntax semantics atomic locations.
From intdet.utils Require Import more_cmras more_maps_and_sets.

Class IsWP (Σ : gFunctors) `{invGS_gen HasNoLc Σ} (pointsto : loc -> dfrac -> list val -> iProp Σ) (wp : coPset -> expr → (val → iProp Σ) → iProp Σ) :=
  { wp_strong_mono : forall E e P Q,
      wp E e P -∗ (∀ v, P v ={E}=∗ Q v) -∗ wp E e Q;
    fupd_wp : forall E e Q,
      (|={E}=> wp E e Q) -∗ wp E e Q;
    wp_val : forall E (v:val) Q,
      locs v = ∅ -> (* unusual, needed for wpr *)
      Q v -∗ wp E v Q;
    wp_let_val : forall E x (v:val) e Q,
      wp E (subst' x v e) Q -∗ wp E (Let x v e) Q;
    wp_if : forall E (b:bool) e1 e2 Q,
      wp E (if b then e1 else e2) Q -∗ wp E (If b e1 e2) Q;
    wp_bind : forall K E e Q,
      wp E e (fun v => wp E (fill_item K v) Q) -∗
      wp E (fill_item K e) Q;
    wp_load : forall E (l:loc) (i:Z) q v vs,
      (0 <= i < length vs)%Z ->
      vs !! (Z.to_nat i) = Some v ->
      pointsto l q vs -∗ wp E (Load l i) (fun v' => ⌜v'=v⌝ ∗ pointsto l q vs);
    wp_store : forall E (l:loc) (i:Z) vs (v:val),
      (0 <= i < length vs)%Z ->
      pointsto l (DfracOwn 1) vs -∗
      wp E (Store l i v) (fun v' => ⌜v'=VUnit⌝ ∗ pointsto l (DfracOwn 1) (<[Z.to_nat i:=v]>vs));
    wp_code : forall E self arg code,
      ⊢ wp E (Code self arg code) (fun v => ⌜v=VCode self arg code⌝);
    wp_call : forall E self args body ts vs Q,
      ts = Val vs ->
      ▷ wp E (substs' [(self,VCode self args body); (args,vs)] body) Q -∗
      wp E (Call (VCode self args body) ts) Q;
    wp_call_prim : forall E p v1 v2 v,
      eval_call_prim p v1 v2 = Some v ->
      ⊢ wp E (CallPrim p v1 v2) (fun v' => ⌜v'=v⌝);
    wp_cas : forall E (l:loc) (i:Z) vs (v0 v v':val),
      (0 <= i < Z.of_nat (length vs))%Z ->
      vs !! (Z.to_nat i) = Some v0 ->
      pointsto l (DfracOwn 1) vs -∗
      wp E (CAS l i v v') (fun x => ⌜x=bool_decide (v0 = v)⌝ ∗ pointsto l (DfracOwn 1) (if bool_decide (v0 = v) then <[Z.to_nat i := v']>vs else vs));
    wp_atomic : forall E1 E2 e Q,
      Atomic e \/ is_val e ->
      (|={E1,E2}=> wp E2 e (fun v => |={E2,E1}=> Q v)) ⊢ wp E1 e Q;
    wp_fst : forall E v1 v2,
      ⊢ wp E (Fst (VPair v1 v2)) (fun v' => ⌜v'=v1⌝);
    wp_snd : forall E v1 v2,
      ⊢ wp E (Snd (VPair v1 v2)) (fun v' => ⌜v'=v2⌝);
    wp_pair : forall E (v1 v2:val),
      ⊢ wp E (Pair v1 v2) (fun v' => ⌜v'=VPair v1 v2⌝);
    wp_length : forall E (l:loc) q vs,
      pointsto l q vs -∗
      wp E (Length l) (fun v => ⌜v=length vs⌝ ∗ pointsto l q vs);
    pointsto_valid l dq1 dq2 v1 v2 :
    pointsto l dq1 v1 -∗ pointsto l dq2 v2 -∗ ⌜✓ (dq1 ⋅ dq2)⌝;
  }.

Section derived.

Context `{IsWP Σ pointsto wp}.

Lemma wp_mono E e P Q :
  wp E e P -∗
  (∀ v, P v -∗ Q v) -∗
  wp E e Q.
Proof.
  iIntros "E1 E2". iApply (wp_strong_mono with "E1").
  iIntros. by iApply "E2".
Qed.

Lemma wp_fupd E e Q :
  wp E e (fun v => |={E}=> Q v)%I -∗
  wp E e Q.
Proof.
  iIntros "E".
  iApply (wp_strong_mono with "E").
  eauto.
Qed.

End derived.


Global Instance is_except_0_wp `{IsWP Σ pointsto wp} E e Q :
  IsExcept0 (wp E e Q).
Proof.
  rewrite /IsExcept0.
  iIntros. iApply fupd_wp.
  rewrite -except_0_fupd -fupd_intro //.
Qed.

Global Instance elim_modal_bupd_wp `{IsWP Σ pointsto wp} E e Q P p :
  ElimModal True p false (|==> P) P (wp E e Q) (wp E e Q).
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim
    (bupd_fupd E) fupd_frame_r bi.wand_elim_r.
  iIntros. by iApply fupd_wp.
Qed.

Global Instance elim_modal_fupd_wp `{IsWP Σ pointsto wp} E e Q P p :
  ElimModal True p false
    (|={E}=> P) P
    (wp E e Q) (wp E e Q)%I.
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim.
  rewrite fupd_frame_r bi.wand_elim_r.
  iIntros. by iApply fupd_wp.
Qed.

Global Instance elim_modal_fupd_wp_atomic `{IsWP Σ pointsto wp} E1 E2 e Q P p  :
  ElimModal (Atomic e \/ is_val e) p false
    (|={E1,E2}=> P) P
    (wp E1 e Q) (wp E2 e (fun v => |={E2,E1}=> Q v ))%I | 100.
Proof.
  intros ?.
  by rewrite bi.intuitionistically_if_elim
       fupd_frame_r bi.wand_elim_r wp_atomic.
Qed.

Global Instance add_modal_fupd_wp `{IsWP Σ pointsto wp} E e Q P :
  AddModal (|={E}=> P) P (wp E e Q).
Proof.
  rewrite /AddModal fupd_frame_r bi.wand_elim_r.
  iIntros. by iApply fupd_wp.
Qed.

Global Instance elim_acc_wp_atomic `{IsWP Σ pointsto wp} X E1 E2 e Q β γ α :
  ElimAcc (X:=X) (Atomic e \/ is_val e)
    (fupd E1 E2) (fupd E2 E1)
    α β γ (wp E1 e Q)
    (λ x, wp E2 e (fun v => |={E2}=> β x ∗ (γ x -∗? Q v)))%I | 100.
Proof.
  iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
  iSpecialize ("Hinner" with "[$]").
  iApply (wp_mono with "Hinner").
  iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
Qed.

Global Instance elim_acc_wp_nonatomic `{IsWP Σ pointsto wp} X E e Q β γ α :
  ElimAcc (X:=X) True (fupd E E) (fupd E E)
    α β γ (wp E e Q)
    (λ x, wp E e (fun v => |={E}=> β x ∗ (γ x -∗? Q v)))%I .
Proof.
  iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
  iApply wp_fupd.
  iSpecialize ("Hinner" with "[$]").
  iApply (wp_mono with "Hinner").
  iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
Qed.

From intdet.musketeer Require Import wpg dwp lockstep.

Global Instance IsWP_wpl `{intdetGS Σ} :
  IsWP Σ pointstol wpl.
Proof.
  econstructor.
  { eauto using wpg_strong_mono. }
  { eauto using fupd_wpg. }
  { eauto using wpg_val. }
  { eauto using wpg_let_val. }
  { iIntros. iApply wpg_if. done. iIntros (? Eq). inversion Eq. subst. done. }
  { eauto using wpg_bind. }
  { eauto using wpg_load_r. }
  { iIntros. iApply (wpg_mono with "[-]"). by iApply wpg_store.
    iIntros (?) "[% ((%Eq&->&_)&?)]". inversion Eq. subst. iFrame.
    eauto using wpg_store. }
  { eauto using wpg_code. }
  { eauto using wpg_call. }
  { iIntros. iApply wpg_mono. iApply wpg_call_prim. done.
    iIntros (? ?). iPureIntro. naive_solver. }
  { eauto using wpg_cas. }
  { eauto using wpg_atomic. }
  { eauto using wpg_fst. }
  { eauto using wpg_snd. }
  { eauto using wpg_pair. }
  { eauto using wpg_length. }
  { iIntros (?????) "X1 X2".
    iDestruct (pointsto_valid_2 with "X1 X2") as "(?&_)". done. }
Qed.

Global Instance IsWP_wpr `{intdetGS Σ} :
  IsWP Σ pointstor wpr.
Proof.
  econstructor.
  { iIntros (????) "X1 X2". iIntros (?) "#?".
    iApply (wpg_strong_mono with "[X1]").
    { by iApply "X1". }
    iIntros (?) "[% (?&?)]". iFrame. by iApply "X2". }
  { iIntros (???) ">?". done. }
  { iIntros (????) "?". iIntros (?) "#?".
    destruct e'; try done.
    iDestruct (ininj.eininj_noloc with "[$]") as "%Eq". done.
    inversion Eq. subst.
    iApply wpg_val. iExists _. by iFrame. }
  { eauto using wpr_let_val. }
  { eauto using wpr_if. }
  { eauto using (wpr_binds _ _ [_]). }
  { eauto using wpr_load. }
  { eauto using wpr_store. }
  { eauto using wpr_code. }
  { eauto using wpr_call. }
  { eauto using wpr_call_prim. }
  { eauto using wpr_cas. }
  { eauto using wpr_atomic. }
  { eauto using wpr_fst. }
  { eauto using wpr_snd. }
  { eauto using wpr_pair. }
  { eauto using wpr_length. }
  { eauto using pointstor_valid. }
Qed.
