From iris.proofmode Require Import proofmode.
From iris Require Import gmap saved_prop invariants.
From iris.bi Require Import monpred.

From intdet.lang Require Import syntax utils substitution2 notations.
From intdet.musketeer Require Import dwp lockstep.
From intdet.types Require Import utils.
From intdet.types.lvar Require Import typing logrel.

Definition log_typed `{intdetGS Σ, savedPropG Σ} (Γ:gmap string typ) (e:expr) (τ:typ) : iProp Σ :=
  □ ∀ vs, triple ⊤ (interp_env Γ vs) (msubsts (fmap fst vs) e) (fun v s => interp τ s v).

Section fundamental.

Context `{intdetGS Σ, savedPropG Σ}.

Lemma log_typed_var Γ (x:string) τ :
  Γ !! x = Some τ ->
  ⊢ log_typed Γ x τ.
Proof.
  iIntros (Hx). iModIntro.
  iIntros (vs). simpl.

  iApply (triple_use_pure_pre (exists v s, vs !! x = Some (v,s))).
  { iIntros. iDestruct (big_sepM2_lookup_l with "[$]") as "[%y (%&?)]". done.
    iPureIntro. destruct y. eauto. }
  iIntros ((v&s&Hvs)).

  rewrite lookup_fmap Hvs. simpl. iApply triple_val.
  iExists s. rewrite /interp_env !monPred_at_big_sepM2.
  iSplitL; iIntros.
  all:iDestruct (big_sepM2_lookup with "[$]") as "?"; done.
Qed.

Lemma log_typed_unit Γ :
  ⊢ log_typed Γ VUnit TUnit.
Proof.
  iIntros (?) "!>". simpl.
  iApply triple_val. iExists SNone. simpl. rewrite !monPred_at_pure.
  iSplitL; by iIntros.
Qed.

Lemma log_typed_bool Γ (b:bool) :
  ⊢ log_typed Γ (VBool b) TBool.
Proof.
  iIntros (?) "!>". simpl.
  iApply triple_val. iExists SNone. simpl. rewrite !monPred_at_pure.
  iSplitL; eauto.
Qed.

Lemma log_typed_int Γ (z:Z) :
  ⊢ log_typed Γ (VInt z) TInt.
Proof.
  iIntros (?) "!>". simpl.
  iApply triple_val. iExists SNone. simpl. rewrite !monPred_at_pure.
  iSplitL; eauto.
Qed.

Lemma log_typed_assert Γ e :
  log_typed Γ e TBool -∗
  log_typed Γ (Assert e) TUnit.
Proof.
  iIntros "#X". iIntros (vs) "!>". simpl.
  iApply (triple_bind CtxAssert). iApply "X".
  iIntros (v s). simpl.
  iApply (triple_use_pure_pre (s = SNone /\ exists (b:bool), v = b)).
  { iIntros "X". destruct s; simpl; try done. iDestruct "X" as "(%&->)". eauto. }
  iIntros ((->&(b&->))). simpl.
  iApply (triple_resolve SNone).
  iApply triple_conseq. 3:iApply triple_assert.
  { by iIntros. }
  { iIntros (? _) "(->&_)". done. }
Qed.

Lemma log_typed_let Γ x e1 e2 τ τ' :
  log_typed Γ e1 τ' -∗
  log_typed (binsert x τ' Γ) e2 τ -∗
  log_typed Γ (Let x e1 e2) τ.
Proof.
  iIntros "#E1 #E2 !>". iIntros (vs). simpl.

  iApply (triple_bind (CtxLet _ _) with "[E1]").
  { iApply (triple_conseq (interp_env Γ vs ∗ interp_env Γ vs)%I).
    iIntros "#?". by iFrame "#". done.
    iApply triple_frame.
    iApply (triple_conseq _ ); last iApply "E1". done. eauto. }
  iIntros (v s).
  iSpecialize ("E2" $! (binsert x (v,s) vs)). simpl.
  rewrite fmap_binsert -binsert_msubsts.
  iApply triple_conseq; last iApply (triple_let_val with "E2").
  { iIntros "(?&?)". iApply big_sepM2_binsert. simpl.
    iFrame. }
  { done. }
Qed.

Lemma log_typed_if Γ e1 e2 e3 τ :
  log_typed Γ e1 TBool -∗
  log_typed Γ e2 τ -∗
  log_typed Γ e3 τ -∗
  log_typed Γ (If e1 e2 e3) τ.
Proof.
  iIntros "#E1 #E2 #E3 !>". iIntros (vs). simpl.
  iApply (triple_bind (CtxIf _ _) with "[]").
  { iApply (triple_conseq (interp_env Γ vs ∗ interp_env Γ vs)%I).
    iIntros "#?". by iFrame "#". done.
    iApply triple_frame.
    iApply (triple_conseq _ ); last iApply "E1". done. eauto. }
  iIntros (??).
  iApply (triple_use_pure_pre (∃ b, v=VBool b /\ x = SNone)).
  { iIntros "(X&_)".
    destruct x; simpl; try done.
    iDestruct "X" as "(%&->)". eauto. }
  iIntros "[% (->&->)]".

  iApply triple_if. iIntros (b' X). inversion X. subst b'.
  iApply (triple_conseq_pre (interp_env Γ vs)).
  { iIntros "(?&?)". iFrame. }
  destruct b. by iApply "E2". by iApply "E3".
Qed.

Lemma log_typed_abs Γ self args code τs τ :
  log_typed (extend [self; args] [TArrow Weak τs τ; τs] Γ) code τ -∗
  log_typed Γ (Code self args code) (TArrow Weak τs τ).
Proof.
  iIntros "#E !>".
  iIntros (vs). cbn [msubsts].

  iMod (saved_prop_alloc (interp_env Γ vs false) DfracDiscarded) as "[%γ #Hsaved]".
  by constructor.

  iApply triple_code.
  iApply triple_val.
  iExists (SArrow γ); simpl.
  rewrite !monPred_at_exist.
  iSplitL; iIntros "#Hi"; iExists _;
    rewrite !monPred_at_sep monPred_at_embed monPred_at_intuitionistically; simpl;
    do 2 iFrame "#".
  iSplitR; first done.

  iLöb as "IH". simpl.

  iModIntro. iIntros.
  iApply (triple_conseq (▷ (pick True (interp_env Γ vs false) ∗ interp τs s v)) (fun v x => interp τ x v))%I.
  { iIntros "(?&?)". iFrame. iStopProof. constructor.
    iIntros ([]); rewrite monPred_at_later; iIntros; simpl; by iFrame. }
  { reflexivity. }

  iApply triple_call. done. iModIntro.
  rewrite (substs_msubsts_bdeletes [_;_] [_;_]). 2:done.
  2:{ rewrite (dom_bdeletes [_;_]) binders_set_cons. set_solver. }

  iSpecialize ("E" $! (extend [self;args] [(VCode self args
                                              (msubsts (bdelete self (bdelete args (fst <$> vs))) code),SArrow γ);(v,s)] (bdeletes [self; args] vs))).

  rewrite -extend_fmap2.
  2:simpl; lia.
  rewrite fmap_cons fmap_bdeletes. simpl.

  iApply (triple_give_back with "Hi").
  iApply (triple_give_back with "IH").
  iApply (triple_give_back_embed with "Hsaved").

  iApply triple_conseq.
  3:iExact "E". 2:done.

  iIntros "#(?&?&?&?&?)". unfold interp_env.
  iDestruct (pick_combine with "[$]") as "#X".
  rewrite (binserts_bdeletes_same (self::_) (_::_)); last (simpl; lia).
  iApply (big_sepM2_binserts_rev _ _ _ (_ ::_) (_::_) with "[-]"); try done.
  1,2:done.
  rewrite {1}big_sepL2_flip. simpl. iFrame "#".
Qed.

Lemma log_typed_call Γ e es τs τ :
  log_typed Γ e (TArrow Weak τs τ) -∗
  log_typed Γ es τs -∗
  log_typed Γ (Call e es) τ.
Proof.
  iIntros "#E #ES !>".
  iIntros (vs). cbn [msubsts]. simpl.

  iApply (triple_conseq_pre (interp_env Γ vs ∗ interp_env Γ vs)).
  { iIntros "#?". iFrame "#". }
  iApply (triple_bind (CtxCall1 _) _ _ _ (fun v s => interp τs s v ∗ interp_env Γ vs)%I with "[ES]").
  { iApply triple_frame. iApply "ES". }
  iClear "ES".
  iIntros (v s).

  iApply (triple_bind (CtxCall2 _) _ _ _ (fun v' s' => interp (TArrow Weak τs τ) s' v' ∗ interp τs s v)%I).
  { iApply triple_frame_wand.
    iApply triple_conseq_post. 2:iApply "E". iIntros (??) "? ?". iFrame. }

  iClear "E". iIntros (v' x). simpl.

  iApply (triple_use_pure_pre (exists γ, x = SArrow γ)).
  { iIntros "(?&_)".
    destruct x; simpl; try done. eauto. }
  iIntros ((γ&->)).

  unfold interp_arrow_weak. simpl.

  (* breaking abstraction here, RIP *)
  rewrite triple_eq.
  iIntros (C ks F Q1 Q2) "HP HPOST". monPred.unseal.
  iDestruct "HP" as "([%P (#HS&X2)]&X3)".
  rewrite monPred_at_intuitionistically.
  iDestruct "X2" as "(#HPtrue&#Htriple)".

  iApply dwpk_conseq_r; last first.
  { iSpecialize ("Htriple" $! v s). rewrite triple_eq. simpl.
    iSpecialize ("Htriple" $! C ks F Q1 Q2).
    iSpecialize ("Htriple" with "[$]").
    iApply "Htriple". done. }
  { iIntros (?) "(([%P' (HS'&X&_)]&?)&?)". iFrame.
    rewrite monPred_at_intuitionistically. simpl.
    iDestruct "X" as "#X".
    iDestruct (saved_prop_agree with "HS HS'") as "Equiv".
    iModIntro. iRewrite "Equiv". done. }
Qed.

Lemma log_typed_par Γ e1 e2 τ1 τ2 :
  log_typed Γ e1 τ1 -∗
  log_typed Γ e2 τ2 -∗
  log_typed Γ (Par e1 e2) (TProd τ1 τ2).
Proof.
  iIntros "#E1 #E2". iIntros (vs) "!>". simpl.
  iSpecialize ("E1" $! vs). iSpecialize ("E2" $! vs).
  iApply (triple_conseq_pre (interp_env Γ vs ∗ interp_env Γ vs)).
  { iIntros "#?". iFrame "#". }

  iApply (triple_shift (fun x => SProd x.1 x.2)).
  iApply triple_conseq_post.
  2:iApply (triple_par with "E1 E2").
  iIntros (? (x,y)) "[% [% (->&?&?)]]". simpl.
  eauto.
Qed.

Lemma get_result_call_prim p τ1 τ2 s1 s2 τ v1 v2 :
  prim_typed p τ1 τ2 τ ->
  interp τ1 s1 v1 ∗ interp τ2 s2 v2
  ⊢ ∃ v, ⌜eval_call_prim p v1 v2 =Some v⌝ ∗ interp τ SNone v.
Proof.
  destruct p; only 1:intros (->&->); only 2-4:intros (->&->&->); simpl.
  { iIntros "_". eauto. }
  { destruct s1,s2; try by iIntros "(?&?)".
    iIntros "([% ->]&[% ->])". destruct b; eauto. }
  { destruct s1,s2; try by iIntros "(?&?)".
    iIntros "([% ->]&[% ->])". destruct i; eauto. }
  { destruct s1,s2; try by iIntros "(?&?)".
    iIntros "([% ->]&[% ->])". destruct i; eauto. }
Qed.

Lemma log_typed_call_prim Γ e1 e2 p τ1 τ2 τ :
  prim_typed p τ1 τ2 τ ->
  log_typed Γ e1 τ1 -∗
  log_typed Γ e2 τ2-∗
  log_typed Γ (CallPrim p e1 e2) τ.
Proof.
  iIntros (?) "#E1 #E2". iIntros (vs) "!>". simpl.
  iApply (triple_bind (CtxCallPrim1 _ _) with "[]").
  { iApply (triple_conseq (interp_env Γ vs ∗ interp_env Γ vs)%I).
    iIntros "#?". by iFrame "#". done.
    iApply triple_frame.
    iApply (triple_conseq _ ); last iApply "E2". done. eauto. }
  iIntros (??).
  iApply (triple_bind (CtxCallPrim2 _ _) with "[]").
  { rewrite comm. iApply triple_frame. iApply "E1". }
  iIntros (??). simpl.

  iApply triple_conseq_pre.
  { iApply get_result_call_prim. done. }

  iApply (triple_use_pure_pre (exists v1, eval_call_prim p v0 v = Some v1)).
  { iIntros "[% (%&?)]". eauto. }
  iIntros "[%v1 %X]".

  iApply (triple_conseq_pre (interp τ SNone v1 ∗ True)).
  { iIntros "[% (%X'&?)]". rewrite X' in X. inversion X. subst. iFrame. }

  iApply triple_frame_wand.
  iApply (triple_resolve SNone).
  iApply triple_conseq.
  3:by iApply triple_call_prim. done.
  iIntros. assert (v1=v2) as -> by naive_solver. done.
Qed.

Lemma log_typed_alloc Γ e τ :
  log_typed Γ e τ -∗
  log_typed Γ (ref e) (TRef τ).
Proof.
  iIntros "#X". iIntros (vs) "!>". simpl.
  iApply (triple_bind (CtxCall1 _) ). iApply "X".
  iIntros (v s). simpl.
  iApply (triple_resolve SNone).
  iApply (triple_conseq_pre (interp τ s v ∗ True)%I).
  { rewrite right_id //. }
  iApply triple_fupd.
  iApply triple_frame_wand.
  iApply triple_conseq_post.
  2:iApply triple_ref. simpl.
  iIntros (? _) "[% (->&?&?)] ?". eauto.
  iExists l.
  iMod (lockstep.inv_alloc with "[-]"); last by iFrame.
  iFrame.
Qed.

End fundamental.


Definition log_typed_strong `{intdetGS Σ, savedPropG Σ} (Γ:gmap string typ) (e:expr) (τ:typ) : vProp Σ :=
  (□ ∀ vs, interp_env Γ vs -∗ wp ⊤ (msubsts (fmap fst vs) e) (fun v => ∃ s, interp τ s v))%I.

Section fundamental.

Context `{intdetGS Σ, savedPropG Σ}.

Lemma wp_mono E e Q' Q:
  wp E e Q' -∗
  (∀ v, Q' v -∗ Q v) -∗
  wp E e Q.
Proof.
  constructor. intros. rewrite !vprop_at_wand monPred_at_emp. simpl.
  rewrite monPred_at_forall. iIntros "_ X1 X2". destruct i.
  { iApply (wpg.wpg_mono with "[$]"). iIntros. iSpecialize ("X2" $! v).
    rewrite vprop_at_wand. by iApply "X2". }
  { iApply (wpr_mono with "[$]"). iIntros. iSpecialize ("X2" $! v).
    rewrite vprop_at_wand. by iApply "X2". }
Qed.

(* This allows to use a strong derivation to deduce a weak one.
   The result must be deterministic -- here, we force a unit return type.
 *)
Lemma log_typed_strong_impl_weak Γ e :
  (⊢ log_typed_strong Γ e TUnit) ->
  ⊢ log_typed Γ e TUnit.
Proof.
  intros X. iIntros "!>" (vs).
  iApply (wp_triple VUnit SNone).
  iIntros "?".
  iDestruct (X with "[$]") as "X".
  iApply (wp_mono with "[$]").
  iIntros (?) "[% ?]". simpl. destruct s; try done. simpl.
  by iFrame.
Qed.

(* XXX MOVE *)
Lemma wpr_val E (v:val) Q :
  Q v -∗ wpr E v Q.
Proof.
  iIntros. iIntros (?) "Hinj".
  destruct e'; try done.
  iApply wpg.wpg_val. iFrame.
Qed.

Lemma wp_val E (v:val) Q :
  Q v -∗ wp E v Q.
Proof.
  constructor. iIntros (?) "_". rewrite vprop_at_wand.
  iIntros "HQ". simpl.
  destruct i.
  { by iApply wpg.wpg_val. }
  { by iApply wpr_val. }
Qed.

Lemma log_typed_strong_var Γ (x:string) τ :
  Γ !! x = Some τ ->
  ⊢ log_typed_strong Γ x τ.
Proof.
  iIntros (??) "!> #E". simpl.
  iDestruct (big_sepM2_lookup_l with "E") as "[%v (%Eq&?)]". done.
  destruct v. simpl. rewrite lookup_fmap Eq. simpl.
  iApply wp_val. iFrame "#".
Qed.

Lemma log_typed_strong_unit Γ :
  ⊢ log_typed_strong Γ VUnit TUnit.
Proof.
  iIntros (?) "!> ?". simpl.
  iApply wp_val. iExists SNone. done.
Qed.

Lemma log_typed_strong_bool Γ (b:bool) :
  ⊢ log_typed_strong Γ (VBool b) TBool.
Proof.
  iIntros (?) "!> ?". simpl.
  iApply wp_val. iExists SNone. simpl. eauto.
Qed.

Lemma log_typed_strong_int Γ (z:Z) :
  ⊢ log_typed_strong Γ (VInt z) TInt.
Proof.
  iIntros (?) "!> ?". simpl.
  iApply wp_val. iExists SNone. simpl. eauto.
Qed.

Lemma wp_bind K E e Q :
  wp E e (fun v => wp E (fill_item K v) Q) -∗
  wp E (fill_item K e) Q.
Proof.
  constructor. iIntros (?) "_". rewrite vprop_at_wand.
  iIntros "Hwp". simpl. destruct i.
  { by iApply wpg.wpg_bind. }
  { by iApply (wpr_binds _ _ [_]). }
Qed.

Lemma wp_let_val E x (v:val) e Q :
  wp E (subst' x v e) Q -∗
  wp E (Let x v e) Q.
Proof.
  constructor. iIntros (?) "_". rewrite vprop_at_wand.
  iIntros "Hwp". simpl. destruct i.
  { by iApply wpg.wpg_let_val. }
  { by iApply wpr_let_val. }
Qed.

Lemma log_typed_strong_let Γ x e1 e2 τ1 τ2 :
  log_typed_strong Γ e1 τ1 -∗
  log_typed_strong (binsert x τ1 Γ) e2 τ2 -∗
  log_typed_strong Γ (Let x e1 e2) τ2.
Proof.
  iIntros "#X1 #X2". iIntros (vs) "!> #E". simpl.
  iSpecialize ("X1" with "E").
  iApply (wp_bind (CtxLet _ _)).
  iApply (wp_mono with "[$]").
  iIntros (v) "[%s #?]". simpl.

  iApply wp_let_val.
  iSpecialize ("X2" $! (binsert x (v,s) vs) with "[]").
  { iApply big_sepM2_binsert. iFrame "#". }

  rewrite binsert_msubsts fmap_binsert //.
Qed.

Lemma wp_if E (b:bool) e1 e2 Q :
  wp E (if b then e1 else e2) Q -∗ wp E (If b e1 e2) Q.
Proof.
  constructor. iIntros (?) "_". rewrite vprop_at_wand.
  iIntros "Hwp". simpl. destruct i.
  { iApply wpg.wpg_if. done. iIntros (b' Eq). inversion Eq. subst. done. }
  { by iApply wpr_if. }
Qed.

Lemma log_typed_strong_if Γ e1 e2 e3 τ :
  log_typed_strong Γ e1 TBool -∗
  log_typed_strong Γ e2 τ -∗
  log_typed_strong Γ e3 τ -∗
  log_typed_strong Γ (If e1 e2 e3) τ.
Proof.
  iIntros "#X1 #X2 #X3". iIntros (vs) "!> #E". simpl.
  iSpecialize ("X1" with "E").
  iSpecialize ("X2" with "E").
  iSpecialize ("X3" with "E").

  iApply (wp_bind (CtxIf _ _)).
  iApply (wp_mono with "X1").
  iIntros (?) "[%s T]". destruct s; try done. simpl.
  iDestruct "T" as "[%b ->]".

  iApply wp_if. by destruct b.
Qed.

Lemma wp_call_prim E p v1 v2 v :
  eval_call_prim p v1 v2 = Some v ->
  ⊢ wp E (CallPrim p v1 v2) (fun v' => ⌜v'=v⌝)%I.
Proof.
  intros. constructor. iIntros (?) "_". simpl. destruct i; monPred.unseal.
  { iApply wpg.wpg_mono. iApply wpg.wpg_call_prim. done.
    iIntros. iPureIntro. naive_solver. }
  { by iApply wpr_call_prim. }
Qed.

Lemma log_typed_strong_call_prim Γ e1 e2 p τ1 τ2 τ :
  prim_typed p τ1 τ2 τ ->
  log_typed_strong Γ e1 τ1 -∗
  log_typed_strong Γ e2 τ2-∗
  log_typed_strong Γ (CallPrim p e1 e2) τ.
Proof.
  iIntros (?) "#X1 #X2". iIntros (vs) "!> #E". simpl.
  iSpecialize ("X1" with "E"). iSpecialize ("X2" with "E").

  iApply (wp_bind (CtxCallPrim1 _ _)).
  iApply (wp_mono with "X2").
  iIntros (?) "[% I1]".

  iApply (wp_bind (CtxCallPrim2 _ _)).
  iApply (wp_mono with "X1").
  iIntros (?) "[% I2]". simpl.

  iDestruct (get_result_call_prim with "[I1 I2]") as "[%r (%&?)]". done. iFrame.
  iApply wp_mono. by iApply wp_call_prim.
  iIntros (?) "->". eauto.
Qed.

Lemma log_typed_call_strong_from_weak Γ e es τs :
  log_typed Γ e (TArrow Strong τs TUnit) -∗
  log_typed Γ es τs -∗
  log_typed Γ (Call e es) TUnit.
Proof.
  iIntros "#E #ES !>".
  iIntros (vs). cbn [msubsts]. simpl.

iApply (triple_conseq_pre (interp_env Γ vs ∗ interp_env Γ vs)).
  { iIntros "#?". iFrame "#". }
  iApply (triple_bind (CtxCall1 _) _ _ _ (fun v s => interp τs s v ∗ interp_env Γ vs)%I with "[ES]").
  { iApply triple_frame. iApply "ES". }
  iClear "ES".
  iIntros (v s).

  iApply (triple_bind (CtxCall2 _) _ _ _ (fun v' s' => interp (TArrow Strong τs TUnit) s' v' ∗ interp τs s v)%I).
  { iApply triple_frame_wand.
    iApply triple_conseq_post. 2:iApply "E". iIntros (??) "? ?". iFrame. }

  iClear "E". iIntros (v' x). simpl.

  iApply (triple_use_pure_pre (x = SNone)).
  { iIntros "(?&_)".
    destruct x; simpl; done. }
  iIntros (->).

  unfold interp_arrow_strong. simpl.

  iApply (wp_triple VUnit SNone). simpl.
  iIntros "(#Hwp&#?)".
  iApply wp_mono.
  { by iApply "Hwp". }
  iIntros (?) "[% X]". destruct s0; try done.
  by iDestruct "X" as "->".
Qed.

Local Lemma aux_to_vprop (P Q:vProp Σ) :
  (⊢ P -∗ Q) ->
  ⊢ (P true -∗ Q true) ∗ (P false -∗ Q false).
Proof.
  intros [X].
  rewrite -!vprop_at_wand -!X !monPred_at_emp. by iStartProof.
Qed.

Lemma wp_call E self args body ts vs Q :
  ts = Val vs ->
  ▷ wp E (substs' [(self,VCode self args body); (args,vs)] body) Q -∗
  wp E (Call (VCode self args body) ts) Q.
Proof.
  constructor. iIntros (?) "_". rewrite vprop_at_wand.
  iIntros "Hwp". rewrite monPred_at_later. simpl. destruct i.
  { by iApply wpg.wpg_call. }
  { by iApply wpr_call. }
Qed.

Local Lemma abs_helper Γ self args code τs τ vs :
  interp_env Γ vs -∗
  □ (∀ vs0,
     interp_env (extend [self; args] [TArrow Strong τs τ; τs] Γ) vs0 -∗
     wp ⊤ (msubsts (fst <$> vs0) code)
       (λ v, ∃ s, interp τ s v)) -∗
  interp_arrow_strong (interp τs) (interp τ)
    (VCode self args (msubsts (bdelete self (bdelete args (fst <$> vs))) code)).
Proof.
  iIntros "#E #Hcall".

  iLöb as "IH".
  simpl. iModIntro. iIntros (??) "#?".

  iApply wp_call. done. iModIntro.
  rewrite (substs_msubsts_bdeletes [_;_] [_;_]). 2:done.
  2:{ rewrite (dom_bdeletes [self; _]) binders_set_cons. set_solver. }

  iSpecialize ("Hcall" $! (extend [self;args] [(VCode self args
                                              (msubsts (bdelete self (bdelete args (fst <$> vs))) code),SNone); (v,s)] (bdeletes [self;args] vs))).

  rewrite -extend_fmap2.
  2:simpl; lia.
  rewrite fmap_cons fmap_bdeletes. simpl.

  rewrite !(binserts_bdeletes_same (self::_) (_::_)); try (simpl;lia).

  iApply "Hcall". iClear "Hcall".

  iApply (big_sepM2_binserts_rev _ _ _ (_ ::_) (_::_) with "[-]"); try done.
  1,2:done.
  rewrite {1}big_sepL2_flip. simpl. iFrame "#".
Qed.

Lemma log_typed_abs_strong_from_weak Γ self args code τs τ :
  (⊢ log_typed_strong (extend [self; args] [TArrow Strong τs τ; τs] Γ) code τ) ->
  ⊢ log_typed Γ (Code self args code) (TArrow Strong τs τ).
Proof.
  intros X.
  iIntros (vs). iModIntro. simpl.

  iApply triple_code. iApply triple_val.
  iExists SNone. iApply aux_to_vprop.

  iIntros "#E".
  iPoseProof X as "#Hcall". by iApply (abs_helper with "E Hcall").
Qed.

Lemma wp_code E self args code :
  ⊢ wp E (Code self args code) (fun v => ⌜v = VCode self args code⌝).
Proof.
  constructor. iIntros (?) "_". simpl. monPred.unseal.
  destruct i.
  { iApply wpg.wpg_code. }
  { iApply wpr_code. }
Qed.

Lemma log_typed_abs_strong_from_strong Γ self args code τs τ :
  log_typed_strong (extend [self; args] [TArrow Strong τs τ; τs] Γ) code τ -∗
  log_typed_strong Γ (Code self args code) (TArrow Strong τs τ).
Proof.
  iIntros "#Hcall".
  iIntros (vs) "!> #E". simpl.

  iApply wp_mono. iApply wp_code.
  iIntros (?) "->". iExists SNone.

  by iApply (abs_helper with "E Hcall").
Qed.

(* Overall, the idea is as follows:
   + In non-strong mode, one can call a strong functions _only if
   it returns unit (in order to ensure determinism)
   + In a strong mode, one can only call strong functions.
 *)

Lemma log_typed_call_strong_from_strong Γ e es τs τ :
  log_typed_strong Γ e (TArrow Strong τs τ) -∗
  log_typed_strong Γ es τs -∗
  log_typed_strong Γ (Call e es) τ.
Proof.
  iIntros "#E #ES". iIntros (vs) "!> #X".
  cbn [msubsts]. simpl.

  iApply (wp_bind (CtxCall1 _)).
  iApply wp_mono. by iApply "ES".
  iIntros (?) "[% ?]". simpl.
  iApply (wp_bind (CtxCall2 _)).
  iApply wp_mono. by iApply "E".
  simpl.
  iIntros (?) "[% Hv]". destruct s0; try done.
  by iApply "Hv".
Qed.

Lemma wp_load E (l:loc) i q vs v :
  (0 <= i < length vs)%Z ->
  vs !! (Z.to_nat i) = Some v ->
  pointsto l q vs -∗ wp E (Load l i) (fun v' => ⌜v'=v⌝ ∗ pointsto l q vs).
Proof.
  constructor. iIntros (b) "_". rewrite vprop_at_wand. monPred.unseal.
  destruct b.
  { by iApply wpg.wpg_load_r. }
  { by iApply wpr_load. }
Qed.

Lemma wpr_frame_step P E e Q :
  ¬ is_val e ->
  ▷ P -∗
  wpr E e (fun v => P -∗ Q v) -∗
  wpr E e Q.
Proof.
  iIntros (?) "? Hwp".
  iIntros (?) "?".
  iDestruct (ininj.eininj_not_val with "[$]") as "%". done.
  iApply (wpg.wpg_frame_step with "[$]"). done.
  iSpecialize ("Hwp" with "[$]").
  iApply (wpg.wpg_mono with "[$]").
  iIntros (?) "[% (?&X)] ?". iFrame. by iApply "X".
Qed.

Lemma wp_frame_step P E e Q :
  ¬ is_val e ->
  ▷ P -∗
  wp E e (fun v => P -∗ Q v) -∗
  wp E e Q .
Proof.
  intros. constructor. iIntros (b) "_". rewrite !vprop_at_wand monPred_at_later. simpl.
  iIntros "? Hwp". destruct b.
  { iApply (wpg.wpg_frame_step with "[$]"). done.
    iApply (wpg.wpg_mono with "[$]"). iIntros (?).
    rewrite vprop_at_wand. iIntros "X Y". by iApply "X". }
  { iApply (wpr_frame_step with "[$]"). done.
    iApply (wpr_mono with "[$]"). iIntros (?).
    rewrite vprop_at_wand. iIntros "X Y". by iApply "X". }
Qed.

Lemma log_typed_strong_load Γ e τ :
  log_typed_strong Γ e (TRef τ) -∗
  log_typed_strong Γ (Load e 0) τ.
Proof.
  iIntros "#X". iIntros (vs) "!> #E".
  iSpecialize ("X" with "E"). cbn [msubsts].
  iApply (wp_bind (CtxLoad2 _)). iApply (wp_mono with "[$]").
  iIntros (v) "[%s #H]".
  destruct s; try done. iClear "X". simpl.
  iDestruct "H" as "[%l (->&#Hinv)]".
  iMod (lockstep.inv_acc with "Hinv") as "(X&Hclose)". done. eauto using Atomic.
  iDestruct "X" as "[% [% (>Hp&Hi)]]".

  iApply (wp_frame_step with "Hi"). naive_solver.
  iApply (wp_frame_step with "Hclose"). naive_solver.

  iApply (wp_mono with "[Hp]").
  { iApply (wp_load with "Hp"); done. }
  iIntros (?) "(->&Hp) Hclose #Hi".
  iMod ("Hclose" with "[$]"). by iFrame "#".
Qed.

Lemma wp_cas E (l:loc) (i:Z) vs (v0 v v':val) :
  (0 <= i < Z.of_nat (length vs))%Z ->
  vs !! (Z.to_nat i) = Some v0 ->
  pointsto l (DfracOwn 1) vs -∗
  wp E (CAS l i v v') (fun x => ⌜x=bool_decide (v0 = v)⌝ ∗ pointsto l (DfracOwn 1) (if bool_decide (v0 = v) then <[Z.to_nat i := v']>vs else vs)).
Proof.
  constructor. iIntros (b) "_". rewrite vprop_at_wand.
  iIntros "Hl". simpl. monPred.unseal.
  destruct b.
  { by iApply wpg.wpg_cas. }
  { by iApply wpr_cas. }
Qed.

Lemma log_typed_strong_cas Γ e1 e2 e3 τ :
  log_typed_strong Γ e1 (TRef τ) -∗
  log_typed_strong Γ e2 τ -∗
  log_typed_strong Γ e3 τ -∗
  log_typed_strong Γ (CAS e1 0 e2 e3) TBool.
Proof.
  iIntros "#X1 #X2 #X3". iIntros (vs) "!> #E".
  iSpecialize ("X1" with "E").
  iSpecialize ("X2" with "E").
  iSpecialize ("X3" with "E"). cbn [msubsts].

  iApply (wp_bind (CtxCas1 _ _ _)).
  iApply (wp_mono with "X3").
  iIntros (v1) "[%s #?]".

  iApply (wp_bind (CtxCas2 _ _ _)).
  iApply (wp_mono with "X2").
  iIntros (v2) "[%s2 #?]".

  iApply (wp_bind (CtxCas4 _ _ _)).
  iApply (wp_mono with "X1").
  iIntros (v3) "[%s3 #Hi]".

  destruct s3; try done. simpl.
  iDestruct "Hi" as "[% (->&Hinv)]".

  iMod (lockstep.inv_acc with "Hinv") as "(X&Hclose)". done. eauto using Atomic.
  iDestruct "X" as "[% [% (>Hp&Hi)]]".

  iApply (wp_frame_step with "Hi"). naive_solver.
  iApply (wp_frame_step with "Hclose"). naive_solver.

  iApply (wp_mono with "[Hp]").
  { iApply (wp_cas with "Hp"); done. }
  iIntros (?) "(->&Hp) Hclose #Hi".
  iMod ("Hclose" with "[Hp Hi]").
  { iModIntro. case_bool_decide; iFrame "∗#". }
  iModIntro. iExists SNone. simpl. eauto.
Qed.

Lemma wp_pair E (v1 v2:val) :
  ⊢ wp E (Pair v1 v2) (fun v' => ⌜v'=VPair v1 v2⌝).
Proof.
  constructor. iIntros (?) "_". monPred.unseal.
  destruct i; simpl. iApply wpg.wpg_pair. iApply wpr_pair.
Qed.

Lemma log_typed_pair_strong Γ e1 τ1 e2 τ2 :
  log_typed_strong Γ e1 τ1 -∗
  log_typed_strong Γ e2 τ2 -∗
  log_typed_strong Γ (Pair e1 e2) (TProd τ1 τ2).
Proof.
  iIntros "#E1 #E2". iIntros (vs) "!> #X". simpl.
  iSpecialize ("E1" with "[$]"). iSpecialize ("E2" with "[$]").
  iApply (wp_bind (CtxPair1 _)). iApply (wp_mono with "E2").
  iIntros (?) "[% #?]".
  iApply (wp_bind (CtxPair2 _)). iApply (wp_mono with "E1").
  iIntros (?) "[% #?]". simpl.

  iApply wp_mono. iApply wp_pair. iIntros (?) "->".
  iExists (SProd _ _). by iFrame "#".
Qed.

Lemma log_typed_pair Γ e1 τ1 e2 τ2 :
  log_typed Γ e1 τ1 -∗
  log_typed Γ e2 τ2 -∗
  log_typed Γ (Pair e1 e2) (TProd τ1 τ2).
Proof.
  iIntros "#E1 #E2". iIntros (vs) "!>".
  iSpecialize ("E1" $! vs). iSpecialize ("E2" $! vs). cbn [msubsts].

  iApply (triple_conseq_pre (interp_env Γ vs ∗ interp_env Γ vs)).
  { iIntros "#?". iFrame "#". }
  iApply (triple_bind (CtxPair1 _) _ _ _ (fun v s => interp τ2 s v ∗ interp_env Γ vs)%I with "[E1]").
  { iApply triple_frame. iApply "E2". }
  iIntros (??).

  iApply triple_frame_wand.
  iApply (triple_bind (CtxPair2 _) with "E1").
  iIntros. simpl. iApply triple_pair. iApply triple_val.
  iExists (SProd _ _). rewrite !vprop_at_wand. simpl. monPred.unseal.
  iSplitR; iIntros; by iFrame "#".
Qed.

End fundamental.
