From iris.proofmode Require Import proofmode.
From iris Require Import gmap saved_prop.
From iris.bi Require Import monpred.

From intdet.musketeer Require Import dwp lockstep.
From intdet.types.affine Require Export typing shape op_related.

From intdet.utils Require Import more_iris.
From intdet.examples Require Export priority.
From intdet.examples Require Import hashtbl_pure hashtbl.

Canonical Structure valO := leibnizO val.

Class typeG Σ :=
  { typeg1 : savedPredG Σ bool;
    typeg2 : priorityG Σ;
    typeg3 : hashsetG Σ;
  }.

Global Existing Instance typeg1.
Global Existing Instance typeg2.
Global Existing Instance typeg3.

(** interp : is a unary logical relation. *)
Section logrel.

Context `{intdetGS Σ, typeG Σ}.

Notation D := (val -> (vPropI Σ)).
Notation env := (gmap string D)%type.

Local Arguments ofe_car !_.

Definition interp_unit : D := (λ w, ⌜w = VUnit⌝)%I.
Definition interp_int : D := (λ w, ⌜∃ n, w = VInt n⌝)%I.
Definition interp_bool : D := (λ w, ⌜∃ n, w = VBool n⌝)%I.

Definition interp_prod (interp1 interp2 : D) : D :=
  λ w, (∃ w1 w2, ⌜w = VPair w1 w2⌝ ∗ interp1 w1 ∗ interp2 w2)%I.

Definition savedp γ (P:vProp Σ) :=
  saved_pred_own γ DfracDiscarded P.

Definition is_code v :=
  match v with
  | VCode _ _ _ => true
  | _ => false end.

Definition interp_arrow γ (interps:shape -> D) (interp2:shape -> D) : D :=
  fun (w:val) => (⌜is_code w⌝ ∗
    ∃ P, embed (savedp γ P) ∗ □ P ∗
         pick (□ ∀ v s, triple ⊤ ((▷ P) ∗ interps s v) (Call w (Val v)) (fun v s => interp2 s v)) True)%I.

Local Lemma interp_arrow_inv_code γ xs x v :
  interp_arrow γ xs x v -∗ ⌜is_code v⌝.
Proof.
  iIntros "(?&_)". done.
Qed.

Definition interp_ref (w:val) s (interp:shape -> D) : D :=
  fun (v:val) => (∃ l, ⌜v=VLoc l⌝ ∗  pointsto l (DfracOwn 1) [w] ∗ interp s w)%I.

Definition interp_pref_read (n:Z) q : D :=
  fun (v:val) => (∃ l, ⌜v=VLoc l⌝ ∗ is_priority_is l q n)%I.

Definition interp_pref_write (n:Z) q : D :=
  fun (v:val) => (∃ l, ⌜v=VLoc l⌝ ∗ is_priority_at_least l q n)%I.

Definition interp_hashset q g : D :=
  fun (v:val) => (vhashset' v q g ∗ [∗ set] x ∈ g, ⌜exists (n:Z), x=VInt n⌝)%I.

Definition interp_array q vs : D :=
  fun (v:val) => (∃ l, ⌜v=VLoc l⌝ ∗ pointsto l (DfracOwn q) vs ∗ [∗ list] v ∈ vs, ⌜exists (n:Z), v=VInt n⌝)%I.

Fixpoint interp (τ:typ) (s:shape) : D :=
  match τ,s with
  | TUnit, SNone => interp_unit
  | TInt, SNone => interp_int
  | TBool, SNone => interp_bool
  | TProd τ1 τ2, SProd s1 s2 => interp_prod (interp τ1 s1) (interp τ2 s2)
  | TArrow τs τ, SArrow γ => interp_arrow γ (interp τs) (interp τ)
  | TRef τ, SRef w s => interp_ref w s (interp τ)
  | TPRead q, SPRead n => interp_pref_read n q
  | TPWrite q, SPWrite n => interp_pref_write n q
  | THashSet q, SHashSet g =>  interp_hashset q g
  | TIntArray q, SArray vs => interp_array q vs
  | TEmpty, SNone => fun _ => True%I
  | _,_ => fun _ => False%I
  end.

Local Lemma interp_unit_inv t2 s v :
  interp (TUnit ⋅ t2) s v ⊣⊢ ⌜t2 = TUnit /\ s=SNone⌝ ∗ interp_unit v.
Proof.
  destruct t2,s; simpl.
  all:try (iSplit; [ by iIntros | iIntros "((%&%)&?)"; congruence]).
  iSplit; first by iFrame. iIntros "(_&?)". iFrame.
Qed.

Local Lemma interp_tint_inv t2 s v :
  interp (TInt ⋅ t2) s v ⊣⊢ ⌜t2 = TInt /\ s=SNone⌝ ∗ interp_int v.
Proof.
  destruct t2,s; simpl.
  all:try (iSplit; [ by iIntros | iIntros "((%&%)&?)"; congruence]).
  iSplit; first by iFrame. iIntros "(_&?)". iFrame.
Qed.

Local Lemma interp_tbool_inv t2 s v :
  interp (TBool ⋅ t2) s v ⊣⊢ ⌜t2 = TBool /\ s=SNone⌝ ∗ interp_bool v.
Proof.
  destruct t2,s; simpl.
  all:try (iSplit; [ by iIntros | iIntros "((%&%)&?)"; congruence]).
  iSplit; first by iFrame. iIntros "(_&?)". iFrame.
Qed.

Local Lemma interp_arrow_inv xs t t2 s v :
  interp (TArrow xs t ⋅ t2) s v ⊣⊢ ∃ g, ⌜s=SArrow g /\ t2 = TArrow xs t⌝ ∗ interp (TArrow xs t) s v.
Proof.
  destruct t2, s; simpl.
  all:try (iSplit; [ by iIntros | iIntros "[% ((%&%)&?)]"; congruence]).
  all:rewrite typ_op_unfold; simpl.
  all:try (case_decide; (iSplit; [ by iIntros | iIntros "[% (?&?)]"; done])).
  case_decide as X.
  { destruct X. subst. simpl. iSplit. iIntros. iFrame "#". eauto.
    iIntros "[% ((%X1&%X2)&?)]". inversion X1. inversion X2. subst. done. }
  { iSplit. by iIntros. iIntros "[% ((%X1&%X2)&?)]". inversion X1. inversion X2.
    subst. exfalso. naive_solver. }
Qed.

Local Lemma interp_tpread_inv   q t2 s v :
  interp (TPRead q ⋅ t2) s v ⊣⊢ ∃ q' n, ⌜s=SPRead n /\ t2=TPRead q'⌝ ∗ interp_pref_read n (q+q') v.
Proof.
  destruct t2, s; simpl.
  all:try (iSplit; [by iIntros | iIntros "[% [% ((%&%)&_)]]"; congruence]).
  iSplit. iIntros. by iFrame.
  iIntros "[% [% ((%E1&%E2)&?)]]". inversion E1. inversion E2.
  subst. done.
Qed.

Local Lemma interp_tempty_inv t2 s v :
  interp (TEmpty ⋅ t2) s v ⊣⊢ ⌜s=SNone /\ t2=TEmpty⌝.
Proof.
  destruct t2, s; simpl.
  all:try (iSplit; [by iIntros | iIntros "(%&%)"; congruence]).
  iSplit; done.
Qed.

Local Lemma interp_tprod_inv t1_1 t1_2 t2 s v :
  interp (TProd t1_1 t1_2 ⋅ t2) s v ⊣⊢ ∃ t2_1 t2_2 s1 s2 v1 v2, ⌜t2=TProd t2_1 t2_2 /\ s = SProd s1 s2 /\ v = VPair v1 v2⌝ ∗ interp (typ_op t1_1 t2_1) s1 v1 ∗ interp (typ_op t1_2 t2_2) s2 v2.
Proof.
  destruct t2, s; simpl.
  all:try (iSplit; [by iIntros | iIntros "(%&%&%&%&%&%&(%&%&%)&_)"; congruence]).
  rewrite /typ_op_instance /interp_prod.
  iSplit.
  { iIntros "[% [% (->&?&?)]]". by iFrame. }
  { iIntros "(%&%&%&%&%&%&(%E1&%E2&%E3)&?&?)". inversion E1. inversion E2.
    subst. by iFrame. }
Qed.

Local Lemma interp_tpwrite_inv  q t2 s v :
  interp (TPWrite q ⋅ t2) s v ⊣⊢ ∃ q' n, ⌜s=SPWrite n /\ t2=TPWrite q'⌝ ∗ interp_pref_write n (q+q') v.
Proof.
  destruct t2, s; simpl.
  all:try (iSplit; [by iIntros | iIntros "[% [% ((%&%)&_)]]"; congruence]).
  iSplit. iIntros. by iFrame.
  iIntros "[% [% ((%E1&%E2)&?)]]". inversion E1. inversion E2.
  subst. done.
Qed.

Local Lemma interp_vpair_inv t1 t2 s v1 v2 :
  interp (TProd t1 t2) s (VPair v1 v2) -∗ ∃ s1 s2, ⌜s=SProd s1 s2⌝ ∗ interp t1 s1 v1 ∗ interp t2 s2 v2.
Proof.
  iIntros "X"; destruct s; try done.
  { simpl. iDestruct "X" as "[% [% (%E&?&?)]]".
    inversion E. subst. by iFrame. }
Qed.

Local Lemma interp_hashset_inv q s v :
  interp (THashSet q) s v ⊣⊢ ∃ g, ⌜s=SHashSet g⌝ ∗ vhashset' v q g ∗ ([∗ set] x ∈ g, ⌜exists (n:Z), x=VInt n⌝)%I.
Proof.
  destruct s; simpl.
  all:try (iSplit; [by iIntros | iIntros "(%&%&_)"; congruence]).
  iSplit.
  { iIntros "?". by iFrame. }
  { iIntros "(%&%X&?&?)". inversion X. subst. iFrame. }
Qed.

Local Lemma interp_array_inv q s v :
  interp (TIntArray q) s v ⊣⊢ (∃ vs, ⌜s=SArray vs⌝ ∗ interp_array q vs v)%I.
Proof.
  destruct s; simpl.
  all:try (iSplit; [by iIntros | iIntros "(%&%&%&%&_)"; congruence]).
  iSplit.
  { iIntros "(%&?&?&?)". by iFrame. }
  { iIntros "(%&%X&?)". inversion X. subst. iFrame. }
Qed.

Lemma interp_pref_split_join n q q' v :
  interp_pref_read n (q + q') v ⊣⊢ interp_pref_read n q v ∗ interp_pref_read n q' v.
Proof.
  iSplit.
  { iIntros "[% (->&?)]".
    iDestruct (is_priority_is_split with "[$]") as "(?&?)".
    by iFrame "#∗". }
  { iIntros "([% (->&X1)]&[% (%Eq&X2)])". inversion Eq. subst.
    iExists _. iSplitR; first done. iApply (is_priority_is_join with "X1 X2"). }
Qed.

Lemma interp_pref_write_join n1 n2 q1 q2 v :
  interp_pref_write (Z.max n1 n2) (q1 + q2) v ⊣⊢ interp_pref_write n1 q1 v ∗ interp_pref_write n2 q2 v.
Proof.
  iSplit.
  { iIntros "[% (->&?)]".
    iDestruct (is_priority_at_least_split with "[$]") as "(?&?)".
    by iFrame "#∗". }
  { iIntros "([% (->&X1)]&[% (%Eq&X2)])". inversion Eq. subst.
    iExists _. iSplitR; first done.
    iApply (is_priority_at_least_join with "X1 X2"). }
Qed.

Lemma interp_pref_agree n1 n2 q q' v :
  interp_pref_read n1 q v -∗ interp_pref_read n2 q' v -∗ ⌜n1=n2⌝.
Proof.
  iIntros "[% (->&X1)] [% (%Eq&X2)]". inversion Eq. subst.
  iApply (is_priority_is_agree with "X1 X2").
Qed.

Lemma interp_shape_valid τ s v :
  interp τ s v -∗ ⌜✓s⌝.
Proof.
  iIntros "X". iInduction τ as [] "IH" forall (s v).
  all:destruct s; try done; simpl.
  { iDestruct "X" as "[% [% (->&X1&X2)]]".
    iDestruct ("IH" with "X1") as "%".
    iDestruct ("IH1" with "X2") as "%". done. }
  { iDestruct "X" as "[% (?&?&X)]".
    iDestruct ("IH" with "X") as "%". done. }
Qed.

Lemma interp_op t1 t2 s1 s2 v :
  ✓ (t1 ⋅ t2) ->
  similar_shape s1 s2 ->
  interp (t1 ⋅ t2) (s1 ⋅ s2) v ⊣⊢ interp t1 s1 v ∗ interp t2 s2 v.
Proof.
  revert t2 s1 s2 v. induction t1; simpl; intros ???? V1 V2; try done.
  { rewrite interp_unit_inv. iSplit.
    { iIntros "((->&%E)&->)".
      apply shape_op_none_inv in E. destruct E. subst.
      done. }
    { iIntros "(X&?)". destruct s1; try done.
      iDestruct "X" as "->".
      assert (t2 = TUnit) as -> by (destruct t2; done).
      assert (s2 = SNone) as -> by (destruct s2; done). done. } }
  { rewrite interp_tint_inv. iSplit.
    { iIntros "((->&%E)&[% ->])".
      apply shape_op_none_inv in E. destruct E. subst.
      eauto. }
    { iIntros "(X&?)". destruct s1; try done.
      assert (t2 = TInt) as -> by (destruct t2; done).
      assert (s2 = SNone) as -> by (destruct s2; done).
      iDestruct "X" as "[% ->]".
      iSplitR; first done. eauto. } }
  { rewrite interp_tbool_inv. iSplit.
    { iIntros "((->&%E)&[% ->])".
      apply shape_op_none_inv in E. destruct E. subst.
      eauto. }
    { iIntros "(X&?)". destruct s1; try done.
      assert (t2 = TBool) as -> by (destruct t2; done).
      assert (s2 = SNone) as -> by (destruct s2; done).
      iDestruct "X" as "[% ->]".
      iSplitR; first done. eauto. } }
  { rewrite interp_tprod_inv. iSplit.
    { iIntros "(%&%&%&%&%&%&(->&%E&->)&X1&X2)". inversion V1.
      apply shape_op_prod_inv in E. destruct E as (?&?&?&?&->&->&->&->).
      iDestruct (interp_shape_valid with "X1") as "%".
      iDestruct (interp_shape_valid with "X2") as "%".
      inversion V2.
      rewrite IHt1_1 // IHt1_2 //.
      iDestruct "X1" as "(?&?)". iDestruct "X2" as "(?&?)". by iFrame. }
    { iIntros "(X1&X2)". destruct s1; try done.
      assert (t2 ≠ TEmpty) by (intros ->; done).
      iDestruct "X1" as "[% [% (->&?&?)]]".
      destruct t2; try done.
      iDestruct (interp_vpair_inv with "X2") as "[% [% (->&?&?)]]".
      iExists _,_,_,_,_,_. simpl. iSplitR; first done. fold shape_op.
      inversion V1. inversion V2.
      rewrite IHt1_1 // IHt1_2 //. iFrame. } }
  { rewrite interp_arrow_inv.
    iSplit.
    { iIntros "(%&(%X&%)&E)". subst. simpl.
      rewrite X. apply shape_op_arrow_inv in X. destruct X. subst.
      iDestruct "E" as "#E". iFrame "#". }
    { iIntros "(X1&X2)". destruct s1; try done.
      assert (t2 ≠ TEmpty) by (intros ->; done).
      destruct t2; try done. rewrite typ_op_unfold in V1. simpl in V1.
      case_decide as X; last done. destruct X. subst.
      destruct s2; try done. inversion V2. subst.
      iExists g0.
      rewrite shape_op_unfold. simpl. rewrite decide_True //.
      by iFrame. } }
  { rewrite interp_tempty_inv. iSplit.
    { iIntros ((E&->)).
      apply shape_op_none_inv in E. destruct E. subst. eauto. }
    { iIntros "(?&?)". destruct s1; try done. destruct s2; try done.
      destruct t2; done. } }
  { rewrite interp_tpread_inv //.
    iSplit.
    { iIntros "(%&%&(%E&->)&X)".
      apply shape_op_srprio_inv in E. destruct E. subst.
      rewrite interp_pref_split_join //. }
    { iIntros "(X1&X2)". destruct s1; try done.
      destruct t2; try done. destruct s2; try done. simpl.
      iDestruct (interp_pref_agree with "[$][$]") as "->".
      iExists _,_. iSplitR.
      2:{ rewrite interp_pref_split_join. iFrame. }
      { iPureIntro. split. rewrite shape_op_unfold. simpl.
        rewrite decide_True //. done. } } }
  { rewrite interp_tpwrite_inv //.
    iSplit.
    { iIntros "(%&%&(%E&->)&X)".
      apply shape_op_swprio_inv in E. destruct E as (n1&n2&->&->&->).
      rewrite interp_pref_write_join //. }
    { iIntros "(X1&X2)". destruct s1; try done.
      destruct t2; try done. destruct s2; try done. simpl.
      iExists _,_. iSplitR.
      2:{ iApply interp_pref_write_join. iFrame. }
      { iPureIntro. done. } } }
  { destruct t2; try done.
    rewrite typ_op_unfold. cbn [typ_op].
    rewrite interp_hashset_inv.
    iSplit.
    { iIntros "(%&%E&X&?)".
      apply shape_op_hashset_inv in E. destruct E as (g1&g2&->&->&->).
      rewrite -vhashset_sep'.
      iDestruct "X" as "(?&?)". iFrame.
      rewrite big_sepS_union_persistent //. }
    { iIntros "(X1&X2)". destruct s1; try done. destruct s2; try done.
      iDestruct "X1" as "(?&?)".
      iDestruct "X2" as "(?&?)".
      iExists _. iSplitR; first done.
      rewrite -vhashset_sep' big_sepS_union_persistent. iFrame. } }
  { destruct t2; try done.
    rewrite typ_op_unfold. cbn [typ_op].
    rewrite interp_array_inv. iSplit.
    { iIntros "(%vs&%X&E)".
      apply shape_op_array_inv in X. destruct X. subst. simpl.
      iDestruct "E" as "[% (->&X&#?)]".
      rewrite pointsto_split. iDestruct "X" as "(?&?)". by iFrame "#∗". }
    { iIntros "(X1&X2)". destruct s1; try done.
      destruct s2; try done. simpl in *. subst.
      iDestruct "X1" as "(%&->&X1&#?)".
      iDestruct "X2" as "(%&%E&X2&#?)". inversion E. subst.
      iDestruct (pointsto_agree with "X1 X2") as "->".
      iCombine "X1 X2" as "X". rewrite -pointsto_split. iFrame "#∗".
      iSplitR; last done. iPureIntro. rewrite shape_op_unfold. simpl.
      rewrite decide_True //. } }
Qed.

Inductive upd_typ_strong : typ -> shape -> typ -> shape -> Prop :=
| URefl : forall τ s , upd_typ_strong τ s τ s
| UProd : forall τ1 s1 τ2 s2 τ1' s1' τ2' s2',
  upd_typ_strong τ1 s1 τ1' s1' ->
  upd_typ_strong τ2 s2 τ2' s2' ->
  upd_typ_strong (TProd τ1 τ2) (SProd s1 s2) (TProd τ1' τ2') (SProd s1' s2')
| URefEmpty : forall τ τ' v0 s,
  τ' = TEmpty ->
  upd_typ_strong (TRef τ) (SRef v0 s) (TRef τ') (SRef v0 SNone)
| UPRtoW : forall n,
  upd_typ_strong (TPRead 1) (SPRead n) (TPWrite 1) (SPWrite n)
| UPWtoR : forall n,
  upd_typ_strong (TPWrite 1) (SPWrite n) (TPRead 1) (SPRead n).

Lemma upd_typ_to_strong τ1 τ2 s1 v :
  upd_typ τ1 τ2 ->
  interp τ1 s1 v -∗
  ⌜exists s2, upd_typ_strong τ1 s1 τ2 s2⌝.
Proof.
  iIntros (X) "X".
  iInduction X as [] "IH" forall (v s1); eauto using upd_typ_strong.
  { destruct s1; try done. simpl.
    iDestruct "X" as "(%&%&->&?&?)".
    iDestruct ("IH" with "[$]") as "(%&%)".
    iDestruct ("IH1" with "[$]") as "(%&%)".
    eauto using upd_typ_strong. }
  all:destruct s1; try done; eauto using upd_typ_strong.
Qed.

Record upd_typ_strong_env (Γ1:gmap string typ) (m1:gmap string shape) (Γ2:gmap string typ) (m2:gmap string shape) :=
  { utse1 : dom Γ1 = dom m1;
    utse2 : dom Γ1 = dom Γ2;
    utse3 : dom Γ1 = dom m2;
    utse4 : forall i τ1 s1 τ2 s2, Γ1 !! i = Some τ1 -> m1 !! i = Some s1 -> Γ2 !! i = Some τ2 -> m2 !! i = Some s2 -> upd_typ_strong τ1 s1 τ2 s2
  }.

Lemma interp_upd_typ τ1 τ2 s1 s2 v :
  upd_typ_strong τ1 s1 τ2 s2 ->
  interp τ1 s1 v ={⊤}=∗ interp τ2 s2 v.
Proof.
  iIntros (U1) "X".
  iInduction U1 as [] "IH" forall (v); simpl.
  { eauto. }
  { iDestruct "X" as "(%&%&->&?&?)".
    iMod ("IH" with "[$]") as "?".
    iMod ("IH1" with "[$]") as "?".
    by iFrame. }
  { subst. iDestruct "X" as "(%&->&?&?)".
    iDestruct (interp_shape_valid with "[$]") as "%".
    by iFrame. }
  { iDestruct "X" as "(%&->&?)".
    iMod (is_prio_is_to_at_least with "[$]").
    by iFrame. }
  { iDestruct "X" as "(%&->&?)".
    iMod (is_prio_at_least_to_is with "[$]").
    by iFrame. }
Qed.

End logrel.

Definition interp_env `{intdetGS Σ, typeG Σ}
  (Γ:gmap string typ) (m:gmap string shape) (vs:gmap string val) : vProp Σ :=
  (⌜dom m = dom Γ⌝ ∗ [∗ map] k ↦ τ;v ∈ (map_zip Γ m);vs, interp τ.1 τ.2 v)%I.

Definition log_typed `{intdetGS Σ, typeG Σ} (Γ:gmap string typ) (e:expr) (τ:typ) (Γ':gmap string typ): iProp Σ :=
  □ ∀ m vs, triple ⊤
            (interp_env Γ m vs)
            (substitution2.msubsts vs e)
            (fun v '(s,m') => ⌜similar_env Γ Γ' /\ similar_shape_env m m'⌝ ∗ interp τ s v ∗ interp_env Γ' m' (restrict.restrict (dom Γ') vs)).
