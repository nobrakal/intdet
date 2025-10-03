From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.

From intdet.lang Require Import reducible invert_step.
From intdet.lang Require Export syntax semantics atomic.

(* We define the WP w.r.t to an abstract [interp] predicate,
   quantified here. *)
Class wpGS (lr:bool) (Σ : gFunctors) (iinvgs : invGS_gen HasNoLc Σ) (A:Type) (interp : A -> store -> iProp Σ) (pointsto : loc -> dfrac -> list val -> iProp Σ) (wait:loc -> iProp Σ) (ininj:loc -> loc -> iProp Σ) :=
  WpGS {
      interp_store : forall v' a σ l v,
        interp a σ ∗ pointsto l (DfracOwn 1) v ==∗ (interp a (<[l:=v']>σ) ∗ pointsto l (DfracOwn 1) v');
      interp_alloc_loc : forall l l' v a σ,
        l ∉ dom σ ->
        interp a σ ∗ (if lr then True else wait l') ==∗ interp a (<[l:=v]>σ) ∗ pointsto l (DfracOwn 1) v ∗ (if lr then wait l else ininj l' l);
      use_pointsto : forall a σ l q v,
        interp a σ ∗ pointsto l q v -∗ ⌜σ !! l = Some v⌝;
    }.

Ltac intro_mod :=
  iApply fupd_mask_intro; [ set_solver | iIntros "Hclose"].
Ltac close_mod :=
  iMod "Hclose" as "_"; iModIntro.
Ltac intros_post := iIntros (??) "Hi".
Ltac intros_step := iIntros (?? Hstep).


Section wpg.

Context `{invGS_gen HasNoLc Σ}.

(* ------------------------------------------------------------------------ *)
(* The actual wpg *)

(* As usual, the WP is defined as a guarded fixpoint. [wpg_pre] is
   the "factored-out" version. *)

Definition reducible' `{wpGS b Σ A interp pointsto} e σ : Prop :=
  if b then True else reducible e σ.

Lemma reducible_reducible `{wpGS b Σ A interp pointsto} e σ :
  reducible e σ ->
  reducible' e σ.
Proof.
  intros. rewrite /reducible'. by destruct b.
Qed.

Definition wpg_pre `{wpGS b Σ A interp pointsto}
  (wpg : coPset -d> expr -d> (val -d> iPropO Σ) -d> iPropO Σ) :
  coPset -d> expr -d> (val -d> iPropO Σ) -d> iPropO Σ := λ E e Q,
   match to_val e with
   | Some v => |={E}=> Q v
   | None => ∀ a σ, interp a σ ={E,∅}=∗
       ⌜reducible' e σ⌝ ∗
       (∀ e' σ', ⌜step e σ e' σ'⌝  ={∅}=∗ ▷ |={∅,E}=> interp a σ' ∗ wpg E e' Q)
end%I.

Context `{wpGS lr Σ A interp pointsto}.

Local Instance wpg_pre_contractive : Contractive wpg_pre.
Proof.
  rewrite /wpg_pre /= => n wpg wp' Hwp ? e Q.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

(* wpg as the fixpoint of wpg_pre *)
Definition wpg : coPset -> expr -> (val -> iProp Σ) -> iProp Σ :=
  fixpoint wpg_pre.

Lemma wpg_unfold E e Q :
  wpg E e Q ⊣⊢ wpg_pre wpg E e Q.
Proof. apply (fixpoint_unfold wpg_pre). Qed.

Lemma wpg_properN n E e Q1 Q2 :
  (forall v, Q1 v ≡{n}≡ Q2 v) ->
  wpg E e Q1  ≡{n}≡ wpg E e Q2.
Proof.
  revert e. induction (lt_wf n) as [n _ IH]. intros e X.
  rewrite !wpg_unfold /wpg_pre /=.
  f_equiv.
  { f_equiv. apply X. }
  { do 13 f_equiv. f_contractive.
    do 2 f_equiv. rewrite IH //. intros ?. eapply dist_le; [apply X |lia]. }
Qed.

Lemma wpg_strong_mono E e P Q :
  wpg E e P -∗
  (∀ v, P v ={E}=∗ Q v) -∗
  wpg E e Q.
Proof.
  iIntros "Hwp HPQ".
  iLöb as "IH" forall (e).
  rewrite !wpg_unfold /wpg_pre.
  destruct (to_val e).
  { iMod "Hwp" as "X". iMod ("HPQ" with "X").
    iModIntro. iFrame. }
  { iIntros. iMod ("Hwp" with "[$]") as "(Hr&Hwp)".
    iModIntro. iFrame. iIntros.
    iMod ("Hwp" with "[%//]") as "Hwp". do 2 iModIntro.
    iMod "Hwp" as "(?&?)". iFrame. iApply ("IH" with "[$][$]"). }
Qed.

Lemma wpg_mono E e P Q :
  wpg E e P -∗
  (∀ v, P v -∗ Q v) -∗
  wpg E e Q.
Proof.
  iIntros "E1 E2". iApply (wpg_strong_mono with "[$]").
  iIntros. by iApply "E2".
Qed.

Lemma wpg_fupd E e Q :
  wpg E e (fun v => |={E}=> Q v)%I -∗
  wpg E e Q.
Proof.
  iIntros.
  iApply (wpg_strong_mono with "[$]").
  eauto.
Qed.

Lemma fupd_wpg E e Q :
  (|={E}=> wpg E e Q) -∗
  wpg E e Q.
Proof.
  iIntros "Hwp".
  rewrite !wpg_unfold /wpg_pre. destruct (to_val e).
  { by iMod "Hwp". }
  iIntros. iMod "Hwp" as "Hwp". by iApply "Hwp".
Qed.

Lemma wpg_frame_step P E e Q :
  ¬ is_val e ->
  ▷ P -∗
  wpg E e (fun v => P -∗ Q v) -∗
  wpg E e Q.
Proof.
  iIntros (Hv) "X1 X2".
  rewrite !wpg_unfold /wpg_pre.
  apply is_val_false in Hv. rewrite Hv.
  iIntros. iMod ("X2" with "[$]") as "(?&Hwp)".
  iFrame. iModIntro. iIntros.
  iMod ("Hwp" with "[%//]") as "Hwp". do 2 iModIntro.
  iMod "Hwp" as "(?&?)". iFrame.
  iModIntro. iApply (wpg_mono with "[$]"). iIntros (?) "X".
  by iApply "X".
Qed.

Lemma wpg_val E (v:val) Q :
  Q v -∗
  wpg E v Q.
Proof.
  iIntros. iApply wpg_unfold. rewrite /wpg_pre. simpl.
  iModIntro. by iFrame.
Qed.

Lemma wpg_let_val E x (v:val) e Q :
  wpg E (subst' x v e) Q -∗
  wpg E (Let x v e) Q.
Proof.
  iIntros "Hwp".
  iApply wpg_unfold. rewrite /wpg_pre. simpl. intros_post.
  intro_mod. iSplitR.
  { eauto using reducible_reducible, reducible_let_val. }
  intros_step.
  apply invert_step_let_val in Hstep. destruct Hstep as (->&->).
  do 2 iModIntro. close_mod. iFrame.
Qed.

Lemma wpg_if E (v:val) e1 e2 Q :
  (if lr then True else exists b, v=VBool b) ->
  (∀ b, ⌜v=VBool b⌝ -∗ wpg E (if b then e1 else e2) Q) -∗
  wpg E (If v e1 e2) Q.
Proof.
  iIntros (X) "Hwp".
  iApply wpg_unfold. rewrite /wpg_pre.
  simpl. intros_post.
  intro_mod. iSplitR.
  { rewrite /reducible'.
    destruct lr; first done. destruct X. subst.
    eauto using reducible_if. }
  intros_step.
  apply invert_step_if in Hstep. destruct Hstep as (?&->&->&->).

  do 2 iModIntro. close_mod. iFrame. by iApply "Hwp".
Qed.

Lemma wpg_bind K E e Q :
  wpg E e (fun v => wpg E (fill_item K v) Q) -∗
  wpg E (fill_item K e) Q.
Proof.
  iIntros "Hwp".
  iLöb as "IH" forall (e).
  rewrite (wpg_unfold E e) /wpg_pre.
  destruct_decide (decide (is_val e)) as He.
  { apply is_val_true in He. destruct He as (v&->). iApply fupd_wpg.
    iMod "Hwp" as "?". by iFrame. }
  iApply wpg_unfold. rewrite /wpg_pre.
  rewrite to_val_fill_item.

  simpl. intros_post.
  assert (to_val e = None) as ->.
  { by eapply is_val_false. }

  iMod ("Hwp" with "Hi") as "(%&Hwp)".

  intro_mod. iSplitR.
  { iPureIntro. unfold reducible' in *.
    destruct lr; eauto using RedCtx. }

  intros_step.
  apply invert_step_bind in Hstep; last done.
  destruct Hstep as (?&->&Hstep).

  iMod ("Hwp" with "[%//]") as "Hwp".
  do 2 iModIntro. iMod "Hwp" as "(?&?)". iModIntro. iFrame.
  by iApply "IH".
Qed.

Lemma reducible_bind_inv K e σ :
  ¬ is_val e ->
  reducible (fill_item K e) σ ->
  reducible e σ.
Proof.
  intros Hno Hred.
  remember (fill_item K e) as x.
  revert K e Heqx Hno.
  induction Hred; intros ????; subst.
  { exfalso. by eapply head_step_no_ctx. }
  { apply fill_item_inj in Heqx; eauto using reducible_no_val.
    destruct Heqx. subst. eauto. }
  { exfalso. elim_ctx. }
Qed.

Lemma wpg_bind_inv K E e Q :
  wpg E (fill_item K e) Q -∗
  wpg E e (fun v => wpg E (fill_item K v) Q).
Proof.
   iIntros "Hwp".
  iLöb as "IH" forall (e).
  rewrite (wpg_unfold E e) /wpg_pre.
  destruct_decide (decide (is_val e)) as He.
  { apply is_val_true in He. destruct He as (v&->). by iFrame. }

  assert (to_val e = None) as ->.
  { by eapply is_val_false. }
  iIntros (??) "Hi".

  rewrite wpg_unfold /wpg_pre.
  rewrite to_val_fill_item.
  iMod ("Hwp" with "[$]") as "(%&Hwp)".
  iModIntro. iSplitR.
  { iPureIntro. unfold reducible' in *.
    destruct lr; first done. eauto using reducible_bind_inv. }
  iIntros (?? Hstep). iMod ("Hwp" with "[%]") as "Hwp". eauto using step.
  do 2 iModIntro. iMod "Hwp" as "(?&Hwp)". iFrame. by iApply "IH".
Qed.

Lemma wpg_end E e Q :
  wpg E e (fun v => wpg E v Q) -∗
  wpg E e Q.
Proof.
  iIntros "Hwp".
  iLöb as "IH" forall (e).
  rewrite !wpg_unfold /wpg_pre.
  destruct (to_val e).
  { iMod "Hwp" as "Hwp".
    rewrite wpg_unfold /wpg_pre. simpl. done. }
  intros_post. iMod ("Hwp" with "Hi") as "(%&Hwp)". iModIntro.
  iFrame "%".
  intros_step. iMod ("Hwp" with "[%//]") as "Hwp".
  do 2 iModIntro. iMod "Hwp" as "(?&?)". iFrame. by iApply "IH".
Qed.

Lemma reducible_inv K e σ :
  ¬ is_val e ->
  reducible (fill_item K e) σ ->
  reducible e σ.
Proof.
  intros ?.
  inversion 1; subst.
  { exfalso. by eapply head_step_no_ctx. }
  { apply fill_item_inj in H3; eauto using reducible_no_val. naive_solver. }
  { elim_ctx. }
Qed.

Lemma reducible_inv' K e σ :
  ¬ is_val e ->
  reducible' (fill_item K e) σ ->
  reducible' e σ.
Proof.
  rewrite /reducible'. destruct lr; eauto using reducible_inv.
Qed.

Lemma wpg_binds E ks e Q :
  wpg E e (fun v => wpg E (fill_items ks v) Q) -∗
  wpg E (fill_items ks e) Q.
Proof.
  iInduction ks as [] "IH" forall (Q).
  { simpl. iIntros. by iApply wpg_end. }
  { iIntros. simpl. iApply wpg_bind.
    iApply "IH". iApply (wpg_mono with "[$]"). iIntros.
    by iApply wpg_bind_inv. }
Qed.

Lemma wpg_binds_inv E e ks Q :
  wpg E (fill_items ks e) Q -∗
  wpg E e (fun v => wpg E (fill_items ks v) Q ).
Proof.
  iIntros "Hwp".
  iInduction ks as [] "IH" forall (Q); simpl.
  { iApply (wpg_mono with "[$]"). iIntros. by iApply wpg_val. }
  { iDestruct (wpg_bind_inv with "[$]") as "Hwp".
    iDestruct ("IH" with "[$]") as "Hwp".
    iApply (wpg_mono with "[$]"). iIntros.
    by iApply wpg_bind. }
Qed.

Lemma wpg_load_l E (l:loc) (w:val) q vs :
  lr = true ->
  pointsto l q vs -∗
  wpg E (Load l w) (fun v => ∃ i, ⌜w = VInt i /\ (0 <= i < length vs)%Z  /\ vs !! (Z.to_nat i) = Some v ⌝ ∗ pointsto l q vs).
Proof.
  iIntros (Hlr) "Hl".
  iApply wpg_unfold. rewrite /wpg_pre. intros_post.
  iDestruct (use_pointsto with "[$]") as "%".
  intro_mod.
  iSplitR.
  { iPureIntro. rewrite /reducible' Hlr //. }
  intros_step.
  apply invert_step_load in Hstep.
  destruct Hstep as (vs'&v'&i&?&X2&X3&X5&X6&X7). subst.
  assert (vs' = vs) as -> by naive_solver.
  do 2 iModIntro. close_mod. iFrame.
  iApply wpg_val. iFrame. eauto.
Qed.

Lemma wpg_load_r E (l:loc) (i:Z) q vs v :
  (0 <= i < length vs)%Z ->
  vs !! (Z.to_nat i) = Some v ->
  pointsto l q vs -∗
  wpg E (Load l i) (fun v' => ⌜v'=v⌝ ∗ pointsto l q vs).
Proof.
  iIntros (? ?) "Hl".
  iApply wpg_unfold. rewrite /wpg_pre. intros_post.
  iDestruct (use_pointsto with "[$]") as "%".
  intro_mod.
  iSplitR.
  { eauto using reducible_reducible, reducible_load. }
  intros_step.
  apply invert_step_load in Hstep.
  destruct Hstep as (vs'&v'&i'&?&X2&X3&X5&X6&X7). subst.
  assert (i' = i) as -> by naive_solver.
  assert (vs' = vs) as -> by naive_solver.
  assert (v' = v) as -> by naive_solver.
  do 2 iModIntro. close_mod. iFrame.
  iApply wpg_val. by iFrame.
Qed.

Lemma wpg_code E self arg code :
  ⊢ wpg E (Code self arg code) (fun v => ⌜v=VCode self arg code⌝).
Proof.
  iStartProof. rewrite wpg_unfold /wpg_pre.
  intros_post. intro_mod.
  iSplitR.
  { eauto using reducible_reducible, reducible_code. }
  intros_step.
  apply invert_step_code in Hstep. destruct Hstep as (->&->).
  do 2 iModIntro. iFrame.
  close_mod. by iApply wpg_val.
Qed.

Lemma wpg_alloc E l' (w:val) :
  (if lr then True else exists n, w=VInt n /\ 0 <= n)%Z ->
  (if lr then True else wait l')
  ⊢ wpg E (Alloc w) (fun v' => ∃ n (l:loc), ⌜w=VInt n /\ v'=l /\ 0 <= n⌝%Z ∗ pointsto l (DfracOwn 1) (replicate (Z.to_nat n) VUnit) ∗  (if lr then wait l else ininj l' l))%I.
Proof.
  iIntros (X) "X". rewrite wpg_unfold /wpg_pre.
  intros_post. intro_mod.
  iSplitR.
  { iPureIntro. rewrite /reducible'.
    destruct lr; first done. destruct X as (?&->&?).
    eauto using reducible_alloc. }
  intros_step.
  apply invert_step_alloc in Hstep. destruct Hstep as (n&l0&->&?&?&->&->).
  do 2 iModIntro.
  iMod (interp_alloc_loc with "[$]") as "(?&?)"; last iFrame. done.
  close_mod. iApply wpg_val. iFrame. done.
Qed.

Lemma wpg_store E (l:loc) (w:val) vs (v:val) :
  (if lr then True else exists i, w=VInt i /\ 0 <= i < length vs)%Z ->
  pointsto l (DfracOwn 1) vs -∗
  wpg E (Store l w v) (fun v' => ∃ i, ⌜w=VInt i /\ v'=VUnit /\(0 <= i < length vs)%Z ⌝ ∗ pointsto l (DfracOwn 1) (<[Z.to_nat i:=v]>vs)).
Proof.
  iIntros (X) "Hl".
  rewrite wpg_unfold /wpg_pre.
  intros_post.
  iDestruct (use_pointsto with "[$]") as "%".
  intro_mod.
  iSplitR.
  { rewrite /reducible'. destruct lr; first done.
    destruct X as (?&->&?).
    eauto using reducible_store. }
  intros_step.
  apply invert_step_store in Hstep. destruct Hstep as (vs'&?&?&?&?&?&?). subst.
  assert (vs' = vs) as -> by naive_solver.
  do 2 iModIntro.
  iMod (interp_store with "[$]") as "(?&?)". iFrame.
  close_mod. iApply wpg_val. by iFrame.
Qed.

Lemma wpg_call E self args body ts vs Q :
  ts = Val vs ->
  ▷ wpg E (substs' [(self,VCode self args body); (args,vs)] body) Q -∗
  wpg E (Call (VCode self args body) ts) Q.
Proof.
  iIntros (?) "Hwp". iApply wpg_unfold. subst.
  intros_post. intro_mod.
  iSplitR.
  { eauto using reducible_reducible, reducible_call. }
  intros_step. subst.
  apply invert_step_call in Hstep.
  destruct Hstep as (->&->).
  do 2 iModIntro. close_mod. iFrame.
Qed.

(* A definitely strange lemma, allowing to give yourself a Plain assertion without consuming
   resources. I was not able to do without it. Maybe there is a simpler path. *)
Lemma give_plain E1 E2 Φ P (Ψ:iProp Σ) :
  Plain P ->
  (Φ ={E1,E2}=∗ P) -∗
   Φ ∗ (Φ ={E1,E2}=∗ P -∗ Ψ)
  ={E1,E2}=∗ Ψ.
Proof.
  iIntros (?) "E (H1&H2)".

  rewrite /fupd /bi_fupd_fupd /uPred_fupd. simpl.
  rewrite /uPred_fupd seal_eq /fancy_updates.uPred_fupd_def. simpl.
  iIntros "X".

  iAssert (◇ P)%I as "#P".
  { iMod ("E" with "H1 X") as "R". iMod "R" as "(?&?&?)". by iFrame. }
  iMod ("H2" with "[$][$]") as ">(?&?&Z)". iModIntro. iMod "P". iModIntro.
  iFrame. by iApply "Z".
Qed.

Local Lemma is_val_false1 e :
  ¬ is_val e ->
  to_val e = None.
Proof. intros. by apply is_val_false. Qed.

Lemma wpg_par_pre E e1 e2 Q1 Q2 :
  wpg E e1 Q1 ∗ wpg E e2 Q2 -∗
  wpg E (RunPar e1 e2)
    (fun v => ∃ (v1 v2:val), ⌜v=VPair v1 v2⌝ ∗ Q1 v1 ∗ Q2 v2).
Proof.
  iIntros "(Hwp1&Hwp2)".
  iLöb as "IH" forall (e1 e2).
  iApply wpg_unfold. rewrite /wpg_pre. simpl.
  intros_post.
  destruct_decide (decide (is_val e1 /\ is_val e2)) as Hv.
  { destruct Hv as (Hv1&Hv2).
    apply is_val_true in Hv1,Hv2.
    destruct Hv1 as (v1&->),Hv2 as (v2&->).
    iClear "IH".
    rewrite (wpg_unfold _ v1) (wpg_unfold _ v2) /wpg_pre. simpl.
    iMod "Hwp1" as "?". iMod "Hwp2" as "?".

    intro_mod.
    iSplitR.
    { eauto using reducible_reducible, reducible_join. }
    intros_step.
    apply invert_step_join in Hstep. destruct Hstep as (->&->).
    do 2 iModIntro. close_mod. iFrame.
    iApply wpg_val. iExists _,_. by iFrame. }

  (* We use [give_plain] to give "reducible" in the post, without consuming [interp]. *)
  iApply (give_plain _ _ (wpg E e1 Q1 ∗ interp a σ)%I (⌜¬ is_val e1 -> reducible' e1 σ⌝%I )).
  { iIntros "(H1&Hi)". rewrite !wpg_unfold.
    destruct_decide (decide (is_val e1)).
    { intro_mod. iPureIntro. naive_solver. }
    { rewrite /wpg_pre is_val_false1 //.
      iMod ("H1" with "[Hi]") as "X". by iFrame.
      iDestruct "X" as "(%&_)". eauto. } }
  iFrame. iIntros "(Hwp1&Hi)".

  iApply (give_plain _ _ (wpg E e2 Q2 ∗ interp a σ)%I (⌜¬ is_val e2 -> reducible' e2 σ⌝%I )).
  { iIntros "(H1&Hi)". rewrite !wpg_unfold.
    destruct_decide (decide (is_val e2)).
    { intro_mod. iPureIntro. naive_solver. }
    { rewrite /wpg_pre is_val_false1 //.
      iMod ("H1" with "[Hi]") as "X". by iFrame.
      iDestruct "X" as "(%&_)". eauto. } }
  iFrame. iIntros "(Hwp2&Hi)".

  intro_mod. iIntros (H1 H2). iSplitR.
  { iPureIntro. rewrite /reducible'.
    destruct lr; first done.
    eapply RedPar; eauto. destruct (is_val e1), (is_val 2); naive_solver. }

  intros_step. iMod "Hclose" as "_".
  apply invert_step_par in Hstep; last done.
  destruct Hstep as [(e1'&->&Hstep) | (e2'&->&Hstep)].
  { rewrite (wpg_unfold _ e1) /wpg_pre.
    assert (¬ is_val e1) by eauto using step_no_val.
    rewrite is_val_false1 //.
    iMod ("Hwp1" with "[$]") as "(%&Hwp1)".
    iMod ("Hwp1" with "[%//]") as "Hwp1".
    do 2 iModIntro. iMod "Hwp1" as "(?&Hwp1)".
    iModIntro. iFrame. iApply ("IH" with "Hwp1 Hwp2"). }
  { rewrite (wpg_unfold _ e2) /wpg_pre.
    assert (¬ is_val e2) by eauto using step_no_val.
    rewrite is_val_false1 //.
    iMod ("Hwp2" with "[$]") as "(%&Hwp2)".
    iMod ("Hwp2" with "[%//]") as "Hwp2".
    do 2 iModIntro. iMod "Hwp2" as "(?&Hwp2)".
    iModIntro. iFrame. iApply ("IH" with "Hwp1 Hwp2"). }
Qed.

Lemma wpg_par E e1 e2 Q1 Q2 :
  wpg E e1 Q1 -∗
  wpg E e2 Q2 -∗
  wpg E (Par e1 e2)
    (fun v => ∃ (v1 v2:val), ⌜v=VPair v1 v2⌝ ∗ Q1 v1 ∗ Q2 v2).
Proof.
  iIntros "Hwp1 Hwp2".
  iApply wpg_unfold. rewrite /wpg_pre. simpl.
  intros_post. intro_mod.
  iSplitR.
  { eauto using reducible_reducible, reducible_fork. }
  intros_step.
  apply invert_step_fork in Hstep.
  destruct Hstep as (->&->).
  do 2 iModIntro. close_mod. iFrame.
  iApply wpg_par_pre. iFrame.
Qed.

Lemma wpg_assert E v :
  (if lr then True else v=VBool true) ->
  ⊢ wpg E (Assert v) (fun w => ⌜w=VUnit /\ v = VBool true⌝ ).
Proof.
  iIntros (?).
  iApply wpg_unfold. rewrite /wpg_pre.
  simpl. intros_post.
  intro_mod. iSplitR.
  { iPureIntro. rewrite /reducible'.
    destruct lr; first done. subst. eauto using reducible_assert. }
  intros_step.
  apply invert_step_assert in Hstep. destruct Hstep as (->&->&->).
  do 2 iModIntro. close_mod. iFrame.
  by iApply wpg_val.
Qed.

Lemma wpg_call_prim E p v1 v2 :
  (if lr then True else is_Some (eval_call_prim p v1 v2)) ->
  ⊢ wpg E (CallPrim p v1 v2) (fun v' => ⌜eval_call_prim p v1 v2 = Some v'⌝).
Proof.
  iIntros (X).
  iApply wpg_unfold. rewrite /wpg_pre.
  simpl. intros_post.
  intro_mod. iSplitR.
  { iPureIntro.
    destruct lr. done. simpl.
    destruct X. eauto using reducible_call_prim. }
  intros_step.
  apply invert_step_call_prim in Hstep. destruct Hstep as (v'&Hv'&->&->).
  do 2 iModIntro. close_mod. iFrame.
  iApply wpg_val. iPureIntro. naive_solver.
Qed.

Lemma wpg_pair E (v1 v2:val) :
  ⊢ wpg E (Pair v1 v2) (fun v' => ⌜v'=VPair v1 v2⌝).
Proof.
  iApply wpg_unfold. rewrite /wpg_pre.
  simpl. intros_post.
  intro_mod. iSplitR.
  { iPureIntro. eauto using reducible_reducible, reducible_pair. }
  intros_step.
  apply invert_step_pair in Hstep. destruct Hstep as (->&->).
  do 2 iModIntro. close_mod. iFrame.
  iApply wpg_val. iPureIntro. naive_solver.
Qed.

Lemma wpg_fst E (v1 v2:val) :
  ⊢ wpg E (Fst (VPair v1 v2)) (fun v' => ⌜v'=v1⌝).
Proof.
  iApply wpg_unfold. rewrite /wpg_pre.
  simpl. intros_post.
  intro_mod. iSplitR.
  { iPureIntro. eauto using reducible_reducible, reducible_fst. }
  intros_step.
  apply invert_step_fst in Hstep. destruct Hstep as (->&->).
  do 2 iModIntro. close_mod. iFrame.
  iApply wpg_val. iPureIntro. naive_solver.
Qed.

Lemma wpg_snd E (v1 v2:val) :
  ⊢ wpg E (Snd (VPair v1 v2)) (fun v' => ⌜v'=v2⌝).
Proof.
  iApply wpg_unfold. rewrite /wpg_pre.
  simpl. intros_post.
  intro_mod. iSplitR.
  { iPureIntro. eauto using reducible_reducible, reducible_snd. }
  intros_step.
  apply invert_step_snd in Hstep. destruct Hstep as (->&->).
  do 2 iModIntro. close_mod. iFrame.
  iApply wpg_val. iPureIntro. naive_solver.
Qed.

Lemma wpg_length E (l:loc) q vs :
  pointsto l q vs -∗
  wpg E (Length l) (fun v => ⌜v=length vs⌝ ∗ pointsto l q vs).
Proof.
  iIntros. iApply wpg_unfold. rewrite /wpg_pre.
  simpl. intros_post.
  iDestruct (use_pointsto with "[$]") as "%".
  intro_mod. iSplitR.
  { eauto using reducible_reducible, reducible_length. }
  intros_step.
  eapply invert_step_length in Hstep. destruct Hstep as (vs'&R&->&->).
  assert (vs'=vs) as -> by naive_solver.
  do 2 iModIntro. close_mod. iFrame.
  iApply wpg_val. by iFrame.
Qed.

(* weak spec, because I never need the strong one *)
Lemma wpg_cas E (l:loc) (i:Z) vs (v v0 v':val) :
  (0 <= i < Z.of_nat (length vs))%Z ->
  vs !! (Z.to_nat i) = Some v0 ->
  pointsto l (DfracOwn 1) vs -∗
  wpg E (CAS l i v v') (fun x => ⌜x=bool_decide (v0 = v)⌝ ∗ pointsto l (DfracOwn 1) (if bool_decide (v0 = v) then <[Z.to_nat i := v']>vs else vs)).
Proof.
  iIntros (??) "Hl".
  rewrite wpg_unfold /wpg_pre.
  intros_post.
  iDestruct (use_pointsto with "[$]") as "%".
  intro_mod.
  iSplitR.
  { eauto using reducible_reducible, reducible_cas. }
  intros_step.
  apply invert_step_cas in Hstep. destruct Hstep as (i'&vs'&v0'&?&?&?&?&?&?).
  subst.
  assert (i'=i) as -> by naive_solver.
  assert (vs'=vs) as -> by naive_solver.
  assert (v0'=v0) as -> by naive_solver.
  do 2 iModIntro. case_bool_decide.
  { iMod (interp_store with "[$]") as "(?&?)". iFrame.
    close_mod. iApply wpg_val. by iFrame. }
  { close_mod. iFrame. iApply wpg_val. by iFrame. }
Qed.

Lemma wpg_atomic E1 E2 e Q :
  Atomic e \/ is_val e ->
  (|={E1,E2}=> wpg E2 e (fun v => |={E2,E1}=> Q v)) ⊢ wpg E1 e Q.
Proof.
  iIntros (Ha) "Hwp".
  rewrite !wpg_unfold /wpg_pre.
  destruct (to_val e).
  { do 2 iMod "Hwp". iDestruct "Hwp" as "?". by iFrame. }
  iIntros.
  iMod ("Hwp" with "[$]") as ">(?&Hwp)".
  iModIntro. iFrame. iIntros.
  iMod ("Hwp" with "[%//]") as "Hwp".
  do 2 iModIntro.
  iMod "Hwp" as "(?&Hwp)".

  apply Atomic_correct in H1.
  2:{ destruct Ha. done. exfalso. by eapply step_no_val. }
  destruct H1 as (?&?).
  subst. rewrite !wpg_unfold /wpg_pre. simpl.
  iMod "Hwp" as "X". iFrame.
  iMod "X". do 2 iModIntro. by iFrame.
Qed.

End wpg.

Global Instance wpg_proper `{wpGS lr Σ A interp pointsto} E e :
  Proper ((pointwise_relation _ (≡)) ==> (≡)) (wpg E e).
Proof.
  intros ?? X. apply equiv_dist. intros. apply wpg_properN.
  intros v. apply equiv_dist. done.
Qed.

Global Instance is_except_0_wp `{wpGS lr Σ A interp pointsto} E e Q :
  IsExcept0 (wpg E e Q).
Proof.
  rewrite /IsExcept0.
  iIntros. iApply fupd_wpg.
  rewrite -except_0_fupd -fupd_intro //.
Qed.

Global Instance elim_modal_bupd_wpg `{wpGS lr Σ A interp pointsto} E e Q P p :
  ElimModal True p false (|==> P) P (wpg E e Q) (wpg E e Q).
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim
    (bupd_fupd E) fupd_frame_r bi.wand_elim_r.
  iIntros. by iApply fupd_wpg.
Qed.

Global Instance elim_modal_fupd_wpg `{wpGS lr Σ A interp pointsto} E e Q P p :
  ElimModal True p false
    (|={E}=> P) P
    (wpg E e Q) (wpg E e Q)%I.
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim.
  rewrite fupd_frame_r bi.wand_elim_r.
  iIntros. by iApply fupd_wpg.
Qed.

Global Instance elim_modal_fupd_wpg_atomic `{wpGS lr Σ A interp pointsto} E1 E2 e Q P p  :
  ElimModal (Atomic e \/ is_val e) p false
    (|={E1,E2}=> P) P
    (wpg E1 e Q) (wpg E2 e (fun v => |={E2,E1}=> Q v ))%I | 100.
Proof.
  intros ?.
  by rewrite bi.intuitionistically_if_elim
       fupd_frame_r bi.wand_elim_r wpg_atomic.
Qed.

Global Instance add_modal_fupd_wpg `{wpGS lr Σ A interp pointsto} E e Q P :
  AddModal (|={E}=> P) P (wpg E e Q).
Proof.
  rewrite /AddModal fupd_frame_r bi.wand_elim_r.
  iIntros. by iApply fupd_wpg.
Qed.

Global Instance elim_acc_wpg_atomic `{wpGS lr Σ A interp pointsto} X E1 E2 e Q β γ α :
  ElimAcc (X:=X) (Atomic e \/ is_val e)
    (fupd E1 E2) (fupd E2 E1)
    α β γ (wpg E1 e Q)
    (λ x, wpg E2 e (fun v => |={E2}=> β x ∗ (γ x -∗? Q v)))%I | 100.
Proof.
  iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
  iSpecialize ("Hinner" with "[$]").
  iApply (wpg_mono with "[$]").
  iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
Qed.

Global Instance elim_acc_wpg_nonatomic `{wpGS lr Σ A interp pointsto} X E e Q β γ α :
  ElimAcc (X:=X) True (fupd E E) (fupd E E)
    α β γ (wpg E e Q)
    (λ x, wpg E e (fun v => |={E}=> β x ∗ (γ x -∗? Q v)))%I .
Proof.
  iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
  iApply wpg_fupd.
  iSpecialize ("Hinner" with "[$]").
  iApply (wpg_mono with "[$]").
  iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
Qed.
