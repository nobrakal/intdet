From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.bi Require Export monpred.

From intdet.utils Require Import more_cmras.
From intdet.lang Require Import semantics.
From intdet.musketeer Require Import dwp .

Canonical Structure lockstep_bi_index :=
  {| bi_index_type := bool; bi_index_rel := eq |}.

Definition vProp Σ := monPred lockstep_bi_index (uPredI (iResUR Σ)).
Definition vPropO Σ := monPredO lockstep_bi_index (uPredI (iResUR Σ)).
Definition vPropI Σ := monPredI lockstep_bi_index (uPredI (iResUR Σ)).

Section vprop.

Context `{intdetGS Σ}.

Lemma upclose_vprop `{intdetGS Σ} (P:bool -> iProp Σ) i :
  (∀ j : bool, ⌜i ⊑ j⌝ → P j) ⊣⊢ P i.
Proof.
  iSplit.
  { iIntros "X". iApply ("X" with "[%//]"). }
  { iIntros "X". iIntros (? Eq). inversion Eq. subst. done. }
Qed.

Lemma vprop_at_wand  `{intdetGS Σ} (P Q:vProp Σ) b :
  (P -∗ Q) b ⊣⊢ (P b -∗ Q b).
Proof.
  rewrite monPred_at_wand upclose_vprop //.
Qed.

Lemma vprop_at_fupd E1 E2 (P Q:vProp Σ) b :
  (P ={E1,E2}=∗ Q) b ⊣⊢ (P b ={E1,E2}=∗ Q b).
Proof.
  monPred.unseal. iSplit.
  { iIntros "X". by iApply "X". }
  { iIntros "X". iIntros (b' Eq). inversion Eq. subst. done. }
Qed.

Lemma vprop_at_bupd (P Q:vProp Σ) b :
  (P ==∗ Q) b ⊣⊢ (P b ==∗ Q b).
Proof.
  monPred.unseal. iSplit.
  { iIntros "X". by iApply "X". }
  { iIntros "X". iIntros (b' Eq). inversion Eq. subst. done. }
Qed.

Definition pointsto l q v : vProp Σ :=
  MonPred (fun (b:bool) => if b then pointstol l q v else pointstor l q v) _.

Global Instance poinsto_timeless l q v:
  Timeless (pointsto l q v).
Proof.
  constructor. intros. rewrite monPred_at_later monPred_at_except_0.
  destruct i; by iIntros ">?".
Qed.

Lemma pointstor_valid l q1 v1 q2 v2 :
  pointstor l q1 v1 -∗ pointstor l q2 v2 -∗ ⌜✓ (q1 ⋅ q2)⌝.
Proof.
  iIntros "[% [% ((X1&_)&_&Y1)]] [% [% ((X2&_)&_&Y2)]]".
  iDestruct (ghost_map_elem_agree with "X1 X2") as "->".
  iCombine "Y1 Y2" as "Y".
  by iApply ghost_map_elem_valid.
Qed.

Lemma pointsto_valid l q1 v1 q2 v2 :
  pointsto l q1 v1 -∗ pointsto l q2 v2 -∗ ⌜✓ (q1 ⋅ q2)⌝.
Proof.
  constructor. intros b. rewrite !vprop_at_wand. monPred.unseal.
  iIntros "_ X1 X2". destruct b.
  { iCombine "X1 X2"as "X". by iApply gen_heap.pointsto_valid. }
  { iApply (pointstor_valid with "X1 X2"). }
Qed.

Lemma big_sepL2_vininj_inj x1 x2 vs:
  ([∗ list] v;vl ∈ x1;vs, ininj.vininj v vl) -∗
  ([∗ list] v;vl ∈ x2;vs, ininj.vininj v vl) -∗
  ⌜x1 = x2⌝.
Proof.
  iIntros "X1 X2".
  iInduction vs as [] "IH" forall (x1 x2).
  { iDestruct (big_sepL2_nil_inv_r with "X1") as "->".
    iDestruct (big_sepL2_nil_inv_r with "X2") as "->".
    done. }
  { iDestruct (big_sepL2_cons_inv_r with "X1") as "[% [% (->&A1&X1)]]".
    iDestruct (big_sepL2_cons_inv_r with "X2") as "[% [% (->&A2&X2)]]".
    iDestruct (ininj.vininj_inj with "A1 A2") as "->".
    iDestruct ("IH" with "X1 X2") as "->".
    done. }
Qed.

(* XXX MOVE *)
Lemma pointstor_agree l q1 q2 x1 x2 :
  pointstor l q1 x1 -∗
  pointstor l q2 x2 -∗
  ⌜x1=x2⌝.
Proof.
  iIntros "(%&%&?&?&X1) (%&%&?&?&X2)".
  iDestruct (ininj.ininj_partial_func with "[$][$]") as "->".
  iDestruct (ghost_map_elem_agree with "[$][$]") as "->".
  iDestruct (big_sepL2_vininj_inj with "[$][$]") as "->".
  done.
Qed.

Lemma pointsto_agree l q1 q2 x1 x2  :
  pointsto l q1 x1 -∗
  pointsto l q2 x2 -∗
  ⌜x1=x2⌝.
Proof.
  rewrite bi.wand_curry.
  apply bi.entails_wand.
  constructor. intros b. monPred.unseal. destruct b; iIntros "(X1&X2)".
  { iApply (pointsto_agree with "X1 X2"). }
  { iApply (pointstor_agree with "X1 X2"). }
Qed.

Lemma pointstor_split l q1 q2 v:
  pointstor l (DfracOwn (q1 +q2)%Qp) v ⊣⊢ pointstor l (DfracOwn q1) v ∗ pointstor l (DfracOwn q2) v.
Proof.
  iSplit.
  { iIntros "(%&%&#?&#?&(?&?))". iFrame "#∗". }
  { iIntros "((%&%&#E1&#?&X1)&(%&%&#E2&_&X2))".
    unfold ininj.ininj.
    iDestruct (ininj.ininj_partial_func with "E1 E2") as "->".
    iCombine "X1 X2" as "X". iFrame "#∗". }
Qed.

(* XXX MOVE *)
Lemma pointsto_split l q1 q2 v:
  pointsto l (DfracOwn (q1 +q2)%Qp) v ⊣⊢ pointsto l (DfracOwn q1) v ∗ pointsto l (DfracOwn q2) v.
Proof.
  constructor. intros b. monPred.unseal. destruct b; simpl.
  { iSplit. iIntros "(?&?)". iFrame. iIntros "(X1&X2)". iCombine "X1 X2" as "X". done. }
  { iApply pointstor_split. }
Qed.

Lemma pointsto_confront l1 l2 q1 v1 q2 v2 :
  (1 < q1 + q2)%Qp ->
  pointsto l1 (DfracOwn q1) v1 -∗ pointsto l2 (DfracOwn q2) v2 -∗ ⌜l1 ≠ l2⌝.
Proof.
  iIntros (?) "X1 X2". iIntros (->).
  iDestruct (pointsto_valid with "X1 X2") as "%Hv".
  exfalso. rewrite dfrac_op_own dfrac_valid_own Qp.le_ngt // in Hv.
Qed.

Lemma pointsto_persist l q vs :
  pointsto l q vs ==∗ pointsto l DfracDiscarded vs.
Proof.
  constructor. iIntros (i) "_".
  rewrite vprop_at_bupd. simpl. destruct i.
  { iApply pointsto_persist.  }
  { iIntros "[% [% (?&?&?)]]". iFrame. by iApply ghost_map_elem_persist. }
Qed.

Definition pick P Q : vProp Σ :=
  MonPred (fun (b:bool) => if b then P else Q) _.

Lemma pick_combine (P:vProp Σ) :
  pick (P true) True%I ∗ pick True%I (P false) ⊢ P.
Proof.
  constructor. monPred.unseal. iIntros ([]) "(?&?)"; by iFrame.
Qed.

Global Instance pick_persistent P Q :
  Persistent P ->
  Persistent Q ->
  Persistent (pick P Q).
Proof.
  intros ??. constructor. intros b.
  rewrite monPred_at_persistently. simpl.
  destruct b; by iIntros "#?".
Qed.

Definition inv N (P:vProp Σ) :=
  MonPred (fun (b:bool) => inv N (P b)) _.

Global Instance inv_persistent N P :
  Persistent (inv N P).
Proof.
  constructor. intros b.
  rewrite monPred_at_persistently. simpl.
  destruct b; by iIntros "#?".
Qed.

Lemma inv_alloc P N E :
  ▷ P ={E}=∗ inv N P.
Proof.
  constructor. iIntros (b) "_". rewrite vprop_at_fupd. monPred.unseal.
  iApply inv_alloc.
Qed.

Lemma inv_acc N E P :
  ↑N ⊆ E → inv N P ={E,E ∖ ↑N}=∗ ▷ P ∗ (▷ P ={E ∖ ↑N,E}=∗ True).
Proof.
  intros ?. constructor. iIntros (b) "_".
  rewrite vprop_at_fupd monPred_at_sep vprop_at_fupd
    !monPred_at_later monPred_at_pure.
  simpl. by iApply inv_acc.
Qed.

Definition wp E e (Q:val -> vProp Σ) :=
  MonPred (fun (b:bool) => (if b then wpl else wpr) E e (fun v => Q v b)) _.

Lemma wp_atomic E1 E2 e Q :
  Atomic e ∨ is_val e ->
  (|={E1,E2}=> wp E2 e (fun v => |={E2,E1}=> Q v)) ⊢ wp E1 e Q.
Proof.
  intros. constructor. intros b. monPred.unseal. destruct b.
  { iApply wpg.wpg_atomic. done. }
  { iApply dwp.wpr_atomic. done. }
Qed.

Global Instance elim_modal_fupd_wp_atomic E1 E2 e Q P p  :
  ElimModal (Atomic e \/ is_val e) p false
    (|={E1,E2}=> P) P
    (wp E1 e Q) (wp E2 e (fun v => |={E2,E1}=> Q v ))%I | 100.
Proof.
  intros ?.
  rewrite bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r wp_atomic //.
Qed.

Lemma fupd_wp E e Q :
  (|={E}=> wp E e Q) ⊢ wp E e Q.
Proof.
  constructor. intros i. rewrite monPred_at_fupd. destruct i.
  { iApply wpg.fupd_wpg. }
  { iApply fupd_wpr. }
Qed.

Lemma bupd_wp E e Q :
  (|==> wp E e Q) ⊢ wp E e Q.
Proof.
  iIntros "X". iApply fupd_wp. iMod "X". done.
Qed.

Global Instance elim_modal_bupd_wp E e Q P p :
  ElimModal True p false (|==> P) P (wp E e Q) (wp E e Q).
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim
    (bupd_fupd E) fupd_frame_r bi.wand_elim_r.
  iIntros. by iApply fupd_wp.
Qed.

Global Instance elim_modal_fupd_wp E e Q P p :
  ElimModal True p false
    (|={E}=> P) P
    (wp E e Q) (wp E e Q)%I.
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim.
  rewrite fupd_frame_r bi.wand_elim_r.
  iIntros. by iApply fupd_wp.
Qed.

Global Instance is_except_0_wp E e (Q:val ->  vProp Σ) :
  IsExcept0 (wp E e Q).
Proof.
  rewrite /IsExcept0.
  iIntros. iApply fupd_wp.
  rewrite -except_0_fupd -fupd_intro //.
Qed.

End vprop.

Section rfwp.

Context `{intdetGS Σ}.

(* I need to use CPS here *)
Definition triple {A:Type} E (P:vProp Σ) (e:expr) (Q:val -> A -> vProp Σ) : iProp Σ :=
  ∀ C ks F Q1 Q2,
  P true -∗
  (∀ v x, Q v x true -∗ dwpk E ks (Val v) (fun _ => Q v x false ∗ F) ks (Val v) Q1 Q2) -∗
  dwpk (A:=C) E ks e (fun _ => P false ∗ F)%I ks e Q1 Q2.

Lemma triple_eq {A} E P e Q :
  triple (A:=A) E P e Q = (∀ C ks F Q1 Q2,
  P true -∗
  (∀ v x, Q v x true -∗ dwpk E ks (Val v) (fun _ => Q v x false ∗ F) ks (Val v) Q1 Q2) -∗
  dwpk (A:=C) E ks e (fun _ => P false ∗ F)%I ks e Q1 Q2)%I.
Proof. reflexivity. Qed.

(* This lemma asserts that if I have the vProp-level wp, I have the iProp triple.
   This ignores the benefits using using triple.
 *)
Lemma wp_triple {A} v s E P e Q :
  (P ⊢ wp E e (fun v' => ⌜v'=v⌝ ∗ Q v s)) ->
  ⊢ triple (A:=A) E P e Q.
Proof.
  intros [X]. iIntros (?????) "HP HPOST".
  iDestruct (X with "HP") as "Hwp".
  iApply wpg.wpg_binds.
  iApply (wpg.wpg_mono with "Hwp").
  iIntros (?). rewrite monPred_at_sep monPred_at_pure.
  iIntros "(->&?)". iSpecialize ("HPOST" with "[$]").
  iApply (wpg.wpg_mono with "[$]").
  iIntros (?) "[%c (?&HPOST)]". iFrame.
  iIntros "(HP&?)".
  iApply wpr_binds.
  iDestruct (X with "[$]") as "?".
  iApply (wpr_mono with "[$]"). iIntros (?).
  rewrite monPred_at_sep monPred_at_pure.
  iIntros "(->&?)". iApply "HPOST". by iFrame.
Qed.

Lemma fupd_triple {A} E P e Q :
  (|={E}=> triple E P e Q) -∗
  triple (A:=A) E P e Q.
Proof.
  iIntros "Hwp". iIntros (?????) "??".
  iMod "Hwp".
  iApply ("Hwp" with "[$][$]").
Qed.

Lemma triple_end {A B} E P e Q Q' :
  triple (A:=A) E P e Q' -∗
  (∀ v x, triple (A:=B) E (Q' v x) v Q) -∗
  triple (A:=B) E P e Q.
Proof.
  iIntros "E1 E2". rewrite !triple_eq.
  iIntros (C ks F Q1 Q2) "X1 X2".
  iApply ("E1" with "[$]"). iIntros.
  iSpecialize ("E2" $! v x). rewrite triple_eq.
  iSpecialize ("E2" with "[$]").
  iApply (wpg.wpg_mono with "[-]").
  { iApply "E2". done. }
  iIntros (?) "(%&(?&X))". iFrame.
Qed.

Lemma triple_conseq {A} P' Q' E P Q e :
  (P ⊢ P') ->
  (forall v x, Q' v x ⊢ Q v x) ->
  triple (A:=A) E P' e Q' -∗
  triple (A:=A) E P e Q.
Proof.
  iIntros ([EP] EQ) "Ht".
  iIntros (C ks F Q1 Q2) "HP Hf".
  iDestruct (EP with "[$]") as "HP".
  iSpecialize ("Ht" with "[$]").
  iApply (wpg.wpg_mono with "[-]").
  { iApply "Ht". iIntros.
    destruct (EQ v x) as [X].
    iDestruct (X with "[$]") as "?".
    iSpecialize ("Hf" with "[$]").
    iApply (wpg.wpg_mono with "[$]"). Unshelve.
    2:exact C. 2:exact F. 2:exact Q1. 2:exact Q2.
    iIntros (?) "[% (?&Hwp)]". iFrame.
    iIntros "(?&?)". iDestruct (X with "[$]") as "?".
    iApply ("Hwp" with "[$]"). }
  { iIntros (?) "[% (?&Hwp)]". iFrame.
    iIntros "(?&?)".
    iDestruct (EP with "[$]") as "HP".
    iApply ("Hwp" with "[$]"). }
Qed.

Lemma triple_conseq_pre {A} P' E P Q e :
  (P ⊢ P') ->
  triple (A:=A) E P' e Q -∗
  triple (A:=A) E P e Q.
Proof.
  intros. apply triple_conseq; done.
Qed.

Lemma triple_conseq_post {A} Q' E P Q e :
  (forall v x, Q' v x ⊢ Q v x) ->
  triple (A:=A) E P e Q' -∗
  triple (A:=A) E P e Q.
Proof.
  intros. apply triple_conseq; done.
Qed.

Lemma triple_extrude_existential {A B} E (P:B -> vProp Σ) e Q :
  (∀ x, P x true -∗ □ (∀ y, P y false -∗ ⌜x=y⌝)) -∗
  (∀ x, triple E (P x) e Q) -∗
  triple (A:=A) E (∃ x, P x) e Q.
Proof.
  iIntros "E X". rewrite !triple_eq.
  iIntros (?????). monPred.unseal. iIntros "[% Hx] HP".
  iDestruct ("E" with "Hx") as "#E".
  iSpecialize ("X" $! x). rewrite triple_eq.
  iSpecialize ("X" with "Hx HP").
  iApply (wpg.wpg_mono with "[$]").
  iIntros (?) "[% (?&Hp)]". iFrame. iIntros "([% Hx]&?)".
  iDestruct ("E" with "[$]") as "->". iApply "Hp". iFrame.
Qed.

(* This one does not break abstraction *)
Lemma triple_elim_exist {A B} U E (P:B -> vProp Σ) e Q:
  (forall x y, U x /\ U y -> x = y) ->
  (∀ x, P x ⊢ ⌜U x⌝) ->
  (∀ x, triple (A:=A) E (P x) e Q) -∗
  triple (A:=A) E (∃ x, P x) e Q.
Proof.
  iIntros (HU HP). iIntros.
  iApply triple_extrude_existential; last done.
  iIntros (x) "Hx".
  destruct (HP x) as [HPtrue].
  specialize (HPtrue true). rewrite monPred_at_pure in HPtrue.
  iDestruct (HPtrue with "Hx") as "%Ux".
  iModIntro. iIntros.
  destruct (HP y) as [HPfalse].
  specialize (HPfalse false). rewrite monPred_at_pure in HPfalse.
  iDestruct (HPfalse with "[$]") as "%Uy".
  iPureIntro. eauto.
Qed.

Lemma triple_give_back {A} X E P e Q :
  X -∗
  triple (A:=A) E (pick X True ∗ P) e Q -∗
  triple (A:=A) E P e Q.
Proof.
  iIntros "E1 E2".
  rewrite !triple_eq. iIntros (C ????) "HP ?".
  iApply dwpk_conseq_r. 2:iApply ("E2" with "[HP E1]"); try done.
  { iIntros (?) "(?&?)". monPred.unseal. by iFrame. }
  { rewrite monPred_at_sep. iFrame. }
Qed.

Lemma triple_give_back_embed {A} X E P e Q :
  Persistent X ->
  X -∗
  triple (A:=A) E (embed X ∗ P) e Q -∗
  triple (A:=A) E P e Q.
Proof.
  iIntros (?) "#E1 E2".
  rewrite !triple_eq. iIntros (C ????) "HP ?".
  iApply dwpk_conseq_r. 2:iApply ("E2" with "[HP E1]"); try done.
  { iIntros (?) "(?&?)". monPred.unseal. by iFrame "∗#". }
  { monPred.unseal. by iFrame. }
Qed.

Lemma triple_shift {A B} (f:A -> B) E P e Q :
  triple (A:=A) E P e (fun v x => Q v (f x)) -∗
  triple (A:=B) E P e Q.
Proof.
  iIntros "E". rewrite !triple_eq.
  iIntros (C ks F Q1 Q2) "X1 X2".
  iApply ("E" with "[$]").
  iIntros. by iApply "X2".
Qed.

Lemma triple_resolve {A} (x:A) E P e Q :
  triple (A:=unit) E P e (fun v _ => Q v x) -∗
  triple (A:=A) E P e Q.
Proof.
  iApply (triple_shift (fun _ => x)).
Qed.

Lemma triple_val {A} E (P:vProp Σ) (v:val) (Q:val -> A -> vProp Σ) :
  (∃ x, (P true -∗ Q v x true) ∗ (P false -∗ Q v x false)) -∗
  triple E P v Q.
Proof.
  iIntros "[%x (X1&X2)]".
  rewrite triple_eq.
  iIntros (?????) "X Hwp".
  iSpecialize ("X1" with "X").
  iSpecialize ("Hwp" with "X1").
  iApply (wpg.wpg_mono with "[$]").
  iIntros (?) "[% (?&Hwp)]". iFrame.
  iIntros "(?&?)".
  iSpecialize ("X2" with "[$]").
  iApply ("Hwp" with "[$]").
Qed.

Lemma triple_val' E P v Q :
  (P ⊢ Q v tt) ->
  ⊢ triple (A:=unit) E P (Val v) Q.
Proof.
  iIntros ([X]). iApply triple_val. iExists tt.
  rewrite !X. iSplitR; by iIntros.
Qed.

Lemma triple_frame {A} E P P' e (Q:val -> A -> vProp Σ):
  triple E P e Q -∗
  triple E (P ∗ P') e (fun v x => Q v x ∗ P').
Proof.
  iIntros "HT". monPred.unseal.
  iIntros (? ks F Q1 Q2) "(P1&P2) HPOST".
  iSpecialize ("HT" $! C ks (F ∗ P' false)%I Q1 Q2 with "[$]").
  iApply dwpk_conseq_r; last iApply "HT".
  { iIntros (?) "((?&?)&?)". iFrame. }
  iIntros (??) "?".
  iApply dwpk_conseq_r; last iApply "HPOST".
  { iIntros (?) "(?&?&?)". iFrame. }
  iFrame.
Qed.

Lemma triple_fupd_pre {A} E P e Q :
  triple E P e Q -∗
  triple (A:=A) E (|={E}=> P) e Q.
Proof.
  iIntros "HT".
  iIntros (? ks F Q1 Q2) "P HPOST".
  rewrite monPred_at_fupd. iMod "P".
  iSpecialize ("HT" $! C ks F Q1 Q2 with "[$]").
  iApply dwpk_conseq_r_strong; last iApply "HT".
  { iIntros (?) "(?&?)". monPred.unseal. by iFrame. }
  iIntros (??) "?".
  iApply dwpk_conseq_r; last iApply "HPOST".
  { iIntros (?) "(?&?)". iFrame. }
  iFrame.
Qed.

Lemma triple_fupd {A} E P e Q :
  triple E P e (fun x v => |={E}=> Q x v) -∗
  triple (A:=A) E P e Q.
Proof.
  iIntros "Ht". rewrite !triple_eq.
  iIntros (?????) "HP Hf". iApply ("Ht" with "[$]").
  iIntros (??). rewrite monPred_at_fupd.
  iIntros ">?". iSpecialize ("Hf" with "[$]").
  iApply (wpg.wpg_mono with "[$]").
  iIntros (?) "[% (?&Hf)]". iExists _.
  iFrame. rewrite monPred_at_fupd.
  iIntros "(>?&?)". iSpecialize ("Hf" with "[$]"). done.
Qed.

Lemma triple_frame_wand {A} P' E P e Q :
  triple E P e (fun x v => P' -∗ Q x v)-∗
  triple (A:=A) E (P' ∗ P) e Q.
Proof.
  iIntros "HT".
  iApply (triple_conseq (P ∗ P')%I (fun x v => (P' -∗ Q x v) ∗ P')%I).
  { iIntros "(?&?)". iFrame. }
  { iIntros (??) "(X&?)". by iApply "X". }
  by iApply triple_frame.
Qed.

Lemma triple_frame_wand_r {A} E P P' e Q  :
  triple E P e (λ x v, P' -∗ Q x v) -∗ triple (A:=A) E (P ∗ P') e Q.
Proof.
  iIntros "Hwp". iApply triple_conseq_pre. 2:by iApply triple_frame_wand.
  rewrite comm //.
Qed.

Lemma triple_use_pure_pre_unseal {A} X E (P:vProp Σ) e Q :
  (P true -∗ ⌜X⌝) -∗
  (⌜X⌝ -∗ triple (A:=A) E P e Q) -∗
  triple (A:=A) E P e Q.
Proof.
  iIntros "E1 E2".
  rewrite triple_eq. iIntros (?????) "??".
  iDestruct ("E1" with "[$]") as "%".
  iApply ("E2" with "[%//][$][$]").
Qed.

Lemma triple_use_pure_pre {A} X E P e Q :
  (P ⊢ ⌜X⌝) ->
  (⌜X⌝ -∗ triple E P e Q) -∗
  triple (A:=A) E P e Q.
Proof.
  iIntros (R) "X". iApply triple_use_pure_pre_unseal.
  { destruct R as [R]. specialize (R true). rewrite monPred_at_pure in R.
    iApply R. }
  done.
Qed.

Definition nm_left := nroot.@"left".
Definition nm_right := nroot.@"right".
Definition nm_base := nroot.@"base".

Definition meta_token l :=
  MonPred (fun (b:bool) => if b then meta_token l (↑nm_left) else meta_token l (↑nm_right)) _.

Definition meta `{Countable A} l (x1 x2:A) :=
  MonPred (fun (b:bool) => if b then meta l nm_left x1 else meta l nm_right x2) _.

Lemma triple_alloc E (v:val) :
  ⊢ triple (A:=(Z*loc)) E True (Alloc v) (fun v' '(i,l) => ⌜v=VInt i /\ (0<=i)%Z /\ v'=l⌝ ∗ pointsto l (DfracOwn 1) (replicate (Z.to_nat i) VUnit) ∗ meta_token l ∗ pick (gen_heap.meta_token l (↑nm_base)) True).
Proof.
  iIntros (C ks F Q1 Q2) "_ HPOST". monPred.unseal.
  iApply dwpk_alloc_l. iIntros (??) "(%&%) (?&Hw&X)".
  iDestruct (meta_token_difference with "X") as "(X1&X2)". shelve.
  iDestruct (meta_token_difference with "X2") as "(X2&X3)". shelve.
  iDestruct (meta_token_difference with "X3") as "(X3&X4)". shelve.
  iSpecialize ("HPOST" $! _ (n,l) with "[-Hw X1]").
  { simpl. iFrame. simpl. done. } subst.
  iApply (dwpk_alloc_r l with "[Hw][HPOST X1]"). 1-2:done.
  iApply (dwpk_conseq_r with "[X1][$]").
  iIntros (?) "(?&_&?)". simpl. by iFrame.
  Unshelve. set_solver. apply namespaces.coPset_subseteq_difference_r.
  2:set_solver. apply ndot_ne_disjoint. done.
  apply namespaces.coPset_subseteq_difference_r.
  apply ndot_ne_disjoint. done.
  apply namespaces.coPset_subseteq_difference_r.
  2:set_solver. apply ndot_ne_disjoint. done.
Qed.

Lemma triple_load E l (w:val) q vs :
  ⊢ triple (A:=Z) E (pointsto l q vs) (Load l w) (fun v i => ⌜w=VInt i /\ 0 <= i < length vs /\ vs !! (Z.to_nat i) = Some v⌝%Z ∗ pointsto l q vs).
Proof.
  iIntros (C ks F Q1 Q2) "? HPOST". monPred.unseal.
  iApply (dwpk_load_l with "[$]"). iIntros (i v) "(->&%&%) ?".
  iApply (dwpk_load_r (fun _ => F) with "[]"). 1,2:done. by iIntros.
  iSpecialize ("HPOST" $! v i with "[-]").
  { iFrame. eauto. }
  iApply (dwpk_conseq_r with "[][$]").
  iIntros (?) "(?&?)". iFrame. eauto.
Qed.

Lemma triple_length E l q vs :
  ⊢ triple (A:=unit) E (pointsto l q vs) (Length l) (fun v _ =>  ⌜v = length vs⌝%Z ∗ pointsto l q vs).
Proof.
  iIntros (C ks F Q1 Q2) "? HPOST". monPred.unseal.
  iApply (dwpk_length_l with "[$]"). iIntros "?".
  iApply (dwpk_length_r (fun _ => F) with "[]"). by iIntros.
  iSpecialize ("HPOST" $! (length vs) tt with "[-]").
  { by iFrame. }
  iApply (dwpk_conseq_r with "[][$]").
  iIntros (?) "(?&?)". by iFrame.
Qed.

Lemma triple_store E l (v':val) vs (v:val) :
  ⊢ triple (A:=Z) E (pointsto l (DfracOwn 1) vs) (Store l v' v)
      (fun w i => ⌜v'=VInt i /\ w=VUnit /\ 0 <= i < length vs⌝%Z ∗ pointsto l (DfracOwn 1) (<[Z.to_nat i:=v]>vs)).
Proof.
  iIntros (C ks F Q1 Q2) "X HPOST". monPred.unseal.
  iApply (dwpk_store_l with "[$]"). iIntros (?) "(->&%) ?".
  iApply (dwpk_store_r (fun _ => F) with "[]"). done.
  { by iIntros. }
  iSpecialize ("HPOST" $! VUnit i with "[-]").
  { by iFrame. }
  iApply (dwpk_conseq_r with "[][$]").
  iIntros (?) "(?&?)". by iFrame.
Qed.

Lemma triple_assert E (v:val) :
  ⊢ triple (A:=unit) E True (Assert v)
      (fun w _ => ⌜w=VUnit /\ v =VBool true⌝).
Proof.
  iIntros (C ks F Q1 Q2) "X HPOST". monPred.unseal.
  iApply dwpk_assert_l. iIntros "->".
  iApply dwpk_assert_r.
  iSpecialize ("HPOST" $! _ tt with "[%//]").
  iApply (dwpk_conseq_r with "[][$]").
  iIntros (?) "(_&?)". by iFrame.
Qed.

Lemma triple_bind K A B E Q' P e Q  :
  triple (A:=B) E P e Q' -∗
  (∀ v x, triple (A:=A) E (Q' v x) (fill_item K v) Q) -∗
  triple (A:=A) E P (fill_item K e) Q.
Proof.
  iIntros "HWP HC".
  iIntros (C ks F Q1 Q2) "? HPOST".
  iApply dwpk_push_l. iApply dwpk_push_r.
  iApply ("HWP" with "[$]").
  iIntros (v x) "?".
  iApply dwpk_pop_l. iApply dwpk_pop_r.
  iApply ("HC" with "[$]").
  done.
Qed.

Lemma triple_let_val {A} E P x (v:val) e Q :
  triple (A:=A) E P (subst' x v e) Q -∗
  triple (A:=A) E P (Let x v e) Q.
Proof.
  iIntros "Hwp".
  iIntros (C ks F Q1 Q2) "? HPOST".
  iApply dwpk_let_val_l. iApply dwpk_let_val_r.
  iApply ("Hwp" with "[$]"). done.
Qed.

Lemma triple_if {A} E P v e1 e2 Q :
  (∀ b, ⌜v=VBool b⌝ -∗ triple (A:=A) E P (if b then e1 else e2) Q) -∗
  triple (A:=A) E P (If v e1 e2) Q.
Proof.
  iIntros "Hwp".
  iIntros (C ks F Q1 Q2) "? HPOST".
  iApply dwpk_if_l. iIntros. subst. iApply dwpk_if_r.
  iApply ("Hwp" with "[%//][$]"). done.
Qed.

Lemma triple_call_prim E p (v1 v2:val) :
  ⊢ triple (A:=unit) E True%I (CallPrim p v1 v2) (fun v' _ => ⌜eval_call_prim p v1 v2 = Some v'⌝)%I.
Proof.
  iIntros (C ks F Q1 Q2) "? HPOST".
  iApply dwpk_call_prim_l. done. iIntros. iApply dwpk_call_prim_r. done.
  iSpecialize ("HPOST" $! v tt). monPred.unseal.
  unshelve iApply dwpk_conseq_r.  3:by iApply "HPOST".
  iIntros (?) "(?&?)". by iFrame.
Qed.

Lemma triple_call {A} E P self args body ts vs Q :
  ts = Val vs ->
  ▷ triple (A:=A) E P (substs' [(self,VCode self args body); (args,vs)] body) Q -∗
  triple (A:=A)  E (▷ P) (Call (VCode self args body) ts) Q.
Proof.
  iIntros (->) "Hwp".
  iIntros (C ks F Q1 Q2) "? HPOST".
  iApply dwpk_call_l. done.
  rewrite monPred_at_later. iModIntro.
  iApply dwpk_conseq_r; last first.
  { iApply dwpk_call_r. done.
    iApply ("Hwp" with "[$]"). done. }
  { iIntros (?) "(?&?)". rewrite monPred_at_later. iModIntro. iFrame. }
Qed.

Lemma triple_call' {A} E P self args body ts vs Q :
  ts = Val vs ->
  ▷ triple (A:=A) E P (substs' [(self,VCode self args body); (args,vs)] body) Q -∗
  triple (A:=A) E P (Call (VCode self args body) ts) Q.
Proof.
  iIntros. iApply triple_conseq_pre.
  2:{ by iApply triple_call. }
  iIntros. by iFrame.
Qed.

Lemma triple_code {A} E P self args body Q :
  triple (A:=A) E P (VCode self args body) Q -∗
  triple (A:=A) E P (Code self args body) Q.
Proof.
  iIntros "Hwp".
  iIntros (C ks F Q1 Q2) "? HPOST".
  iApply dwpk_code_l. iApply dwpk_code_r.
  iApply ("Hwp" with "[$][$]").
Qed.

Lemma triple_pair {A} E P (v1 v2:val) Q :
  triple (A:=A) E P (VPair v1 v2) Q -∗
  triple (A:=A) E P (Pair v1 v2) Q.
Proof.
  iIntros "Hwp" (C ks F Q1 Q2) "? HPOST".
  iApply dwpk_pair_l. iApply dwpk_pair_r.
  iApply ("Hwp" with "[$][$]").
Qed.

Lemma triple_pair' E P (v1 v2:val) :
  ⊢ triple E P (Pair v1 v2) (fun v (_:unit) => ⌜v=VPair v1 v2⌝ ∗ P).
Proof.
  iApply triple_pair. iApply triple_val'. iIntros. by iFrame.
Qed.

Lemma triple_fst {A} E P (v1 v2:val) Q :
  triple (A:=A) E P v1 Q -∗
  triple (A:=A) E P (Fst (VPair v1 v2)) Q.
Proof.
  iIntros "Hwp" (C ks F Q1 Q2) "? HPOST".
  iApply dwpk_fst_l. iApply dwpk_fst_r.
  iApply ("Hwp" with "[$][$]").
Qed.

Lemma triple_fst' E P (v1 v2:val) :
  ⊢ triple E P (Fst (VPair v1 v2)) (fun v (_:unit) => ⌜v=v1⌝ ∗ P).
Proof.
  iApply triple_fst. iApply triple_val'. iIntros. by iFrame.
Qed.

Lemma triple_snd {A} E P (v1 v2:val) Q :
  triple (A:=A) E P v2 Q -∗
  triple (A:=A) E P (Snd (VPair v1 v2)) Q.
Proof.
  iIntros "Hwp" (C ks F Q1 Q2) "? HPOST".
  iApply dwpk_snd_l. iApply dwpk_snd_r.
  iApply ("Hwp" with "[$][$]").
Qed.

Lemma triple_snd' E P (v1 v2:val) :
  ⊢ triple E P (Snd (VPair v1 v2)) (fun v (_:unit) => ⌜v=v2⌝ ∗ P).
Proof.
  iApply triple_snd. iApply triple_val'. iIntros. by iFrame.
Qed.

Lemma triple_par {A B} E P1 P2 e1 e2 Q1 Q2 :
  triple (A:=A) E P1 e1 Q1 -∗
  triple (A:=B) E P2 e2 Q2 -∗
  triple (A:=(A*B)) E (P1 ∗ P2) (Par e1 e2) (fun v '(x1,x2) => ∃ v1 v2, ⌜v=VPair v1 v2⌝ ∗ Q1 v1 x1 ∗ Q2 v2 x2).
Proof.
  iIntros "H1 H2". monPred.unseal.
  iIntros (C ks F Q1' Q2') "(E1&E2) HPOST".
  iApply (dwpk_par (A:=A) (B:=B)
            (fun _ => F) (fun _ => P1 false) (fun _ => P2 false)
            (fun v x => Q1 v x true) (fun v x => Q2 v x true)
            (fun x v => Q1 v x false) (fun x v => Q2 v x false)
           with "[H1 E1] [H2 E2]").
  { iSpecialize ("H1" $! _ nil True%I).
    iApply dwpk_conseq_r; last iApply ("H1" with "[$]").
    {  iIntros (?) "?". by iFrame. }
    iIntros (??) "?".
    iApply dwpk_val. iFrame. iIntros "(?&_)". iFrame. }
  { iSpecialize ("H2" $! _ nil True%I).
    iApply dwpk_conseq_r; last iApply ("H2" with "[$]").
    { iIntros (?) "?". by iFrame. }
    iIntros (??) "?".
    iApply dwpk_val. iFrame. iIntros "(?&_)". iFrame. }
  simpl.
  iIntros (????) "(?&?)".
  iSpecialize ("HPOST" $! _ (x,y) with "[-]").
  { iExists _,_. by iFrame. }
  iSplitR.
  { iIntros (?) "((?&?)&?)". iFrame. }
  iApply (dwpk_conseq_r with "[][$]").
  iIntros (?) "(?&?&?)". by iFrame.
Qed.

(* Triple gives you dwp for adequacy. *)
Lemma triple_dwpk E e :
  triple (A:=unit) E True e (fun _ _ => True) -∗
  dwp (A:=unit) E e (fun _ => True) e (fun _ _ => True%I) (fun _ _ => True%I).
Proof.
  iIntros "Hwp".
  iSpecialize ("Hwp" $! unit nil True%I).
  iApply (dwpk_conseq_r _ _  nil _ _ nil); last iApply "Hwp".
  {  iIntros. by monPred.unseal. }
  { by monPred.unseal. }
  { iIntros (??) "_".
    iApply dwpk_val. iExists tt. rewrite left_id. iIntros. done. }
Qed.

End rfwp.

Global Instance is_except_0_triple {A} `{intdetGS Σ} E P e (Q:val -> A -> vProp Σ) :
  IsExcept0 (triple E P e Q).
Proof.
  rewrite /IsExcept0.
  iIntros. iApply fupd_triple.
  rewrite -except_0_fupd -fupd_intro //.
Qed.

Global Instance elim_modal_bupd_triple {A} `{intdetGS Σ} E P P' e (Q:val -> A -> vProp Σ) p :
  ElimModal True p false (|==> P') P' (triple E P e Q) (triple E P e Q).
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim
    (bupd_fupd E) fupd_frame_r bi.wand_elim_r.
  iIntros. by iApply fupd_triple.
Qed.

Global Instance elim_modal_fupd_triple  {A} `{intdetGS Σ} E P P' e (Q:val -> A -> vProp Σ) p :
  ElimModal True p false (|={E}=> P') P' (triple E P e Q) (triple E P e Q).
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim.
  rewrite fupd_frame_r bi.wand_elim_r.
  iIntros. by iApply fupd_triple.
Qed.

Global Instance triple_proper {A} `{intdetGS Σ} E :
  Proper ((≡) ==> (=) ==> (=) ==> (≡)) (triple (A:=A) E).
Proof.
  intros ?? X1 ?? -> ?? X2. rewrite !triple_eq.
  do 12 f_equiv. rewrite X1 //.
  f_equiv.
  { do 3 f_equiv. rewrite X2 //. }
  { apply dwp_proper; try done. do 3 f_equiv. done. }
Qed.

Global Opaque triple.
