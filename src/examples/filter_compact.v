From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.bi.lib Require Import fractional.

From intdet.examples Require Export tactics_triple.

From intdet.lang Require Import notations.
From intdet.musketeer Require Import dwp lockstep.

From intdet.examples Require Import reference.

(******************************************************************************)
(* The code *)

Definition seqfor : val :=
  μ: "self" "i" "j" "f",
    if: "i" '== "j" then VUnit else
      let: "ni" := "i" '+ 1 in
      "f" "i";;
      "self" "ni" "j" "f".

Definition count_occ : val :=
  λ: "l"  "e",
    let: "r" := ref 0 in
    let: "f" := (λ: "i", let: "x" := "l".["i"] in if: "x" '== "e" then "r".[0] <- ("r".[0] '+ 1) else VUnit) in
    let: "length" := Length "l" in
    seqfor 0 "length" "f";;
    "r".[0].

Definition filter : val :=
  λ: "l" "length" "r" "e",
    let: "i" := ref 0 in
    let: "f" := λ: "j",
        let: "x" := "l".["j"] in
        if: "x" '== "e" then VUnit else
          let: "j" := "i".[0] in
          "i".[0] <- ("j" '+ 1) ;;
          "r".["j"] <- "x" in
    seqfor 0 "length" "f".

Definition filter_compact : val :=
  λ: "l" "e",
    let: "length" := Length "l" in
    let: "num_elem" := count_occ "l" "e" in
    let: "new_length" := "length" '- "num_elem" in
    let: "r" := alloc "new_length" in
    filter "l" "length" "r" "e";; "r".

(******************************************************************************)
(* Spec *)

Section spec.

Context `{intdetGS Σ}.

Lemma triple_seqfor {A} E P (i j:nat) (f:val) Q :
  triple E P (if (decide (i=j)) then VUnit else f i ;; seqfor (S i) j f)%E Q -∗
  triple (A:=A) E P (seqfor i j f) Q.
Proof.
  iIntros "X".
  iApply (triple_bind (CtxCall2 _)).
  { iApply (triple_bind (CtxCall2 _)).
    call1. call2. call3. fold seqfor.
    call1. call2. }
  call3. call1.

  iApply (triple_bind (CtxIf _ _)).
  { iApply triple_call_prim'. done. }
  call3.

  iApply triple_if.
  iIntros (? X). inversion X. subst. clear X.
  case_bool_decide; subst.
  { rewrite decide_True //. naive_solver. }
  rewrite decide_False; last naive_solver.
  iApply (triple_bind (CtxLet _ _)).
  { by iApply triple_call_prim'. }
  call3. iApply triple_let_val. simpl.
  replace (Z.of_nat i + 1%nat)%Z with (Z.of_nat (S i)) by lia.
  done.
Qed.

Lemma count_occ_spec E (l:loc) (q:dfrac) (vs:list val) (e:val) :
  ⊢ triple E (pointsto l q vs) (count_occ l e) (fun v (_:unit) => ⌜v=VInt (List.count_occ val_eq_dec vs e)⌝ ∗ pointsto l q vs).
Proof.
  iStartProof.

  iApply (triple_bind (CtxCall2 _)).
  call1. call2. call3. fold seqfor.
  call1.

  iApply (triple_conseq_pre (True ∗ (pointsto l q vs)))%I.
  rewrite left_id //.
  iApply (triple_bind_frame (CtxLet _ _)). iApply triple_ref.
  iIntros (? []).
  rewrite bi.sep_exist_r.
  iApply triple_extrude_existential.
  { monPred.unseal. iIntros (?) "((->&_)&_)". iModIntro.
    iIntros (?) "((%Eq&_)&_)". iPureIntro. naive_solver. }
  iIntros (l'). rewrite -assoc. iApply triple_extract_pure_pre.
  iIntros (->). rewrite -assoc. iApply triple_let_val. simpl.

  iApply (triple_bind (CtxLet _ _)).
  iApply triple_code'. simpl.
  call3. iApply triple_let_val. simpl.

  iApply (triple_conseq_pre (pointsto l q vs ∗ pointsto l' (DfracOwn 1) [(^0%nat)%V])).
  { iIntros "(?&?&?)". iFrame. }

  iApply (triple_bind_frame (CtxLet _ _)).
  iApply triple_length.
  iIntros (? []). rewrite -assoc.
  iApply triple_extract_pure_pre. iIntros (->).
  iApply triple_let_val. simpl.

  iApply (triple_bind (CtxLet _ _)).
  { iAssert (□ (∀ (x:nat) i,
     ⌜i <= length vs /\ x = List.count_occ val_eq_dec (take i vs) e⌝ -∗
     triple E (pointsto l q vs ∗ pointsto l' (DfracOwn 1) [VInt x]) (seqfor i (length vs) _) (fun v (_:unit) => pointsto l q vs ∗ pointsto l' (DfracOwn 1) [VInt (List.count_occ val_eq_dec vs e)])))%I as "#X"; last first.
    { iApply triple_conseq_pre. 2:iApply "X". done.
      iPureIntro. split. lia. compute_done. }
    { shelve. } }
  { iIntros (? []). simpl. iApply triple_let_val.
    rewrite comm. iApply triple_frame. simpl.
    iApply triple_end. iApply triple_load.
    iIntros (w i). iApply triple_extract_pure_pre.
    iIntros ((X&?&?)). simpl in *.
    iApply triple_val'. iIntros. iPureIntro. naive_solver. }

  (* now we verify the closure *)
  Unshelve.
  iModIntro.
  iIntros (v i) "(%Hi&%Hx)".
  remember (length vs - i) as j.
  iInduction j as [|] "IH" forall (i v Hx Hi Heqj).
  { iApply triple_seqfor.
    assert (i = length vs) by lia. rewrite decide_True //.
    rewrite take_ge in Hx; last lia. subst v.
    iApply triple_val'. done. }
  { iApply triple_seqfor.
    rewrite decide_False; last lia. simpl.

    iApply (triple_bind (CtxLet _ _)). Unshelve.
    4:exact (fun v (_:unit) => pointsto l' (DfracOwn 1) [(^(List.count_occ val_eq_dec (take (S i) vs) e))%V] ∗ pointsto l q vs)%I.
    { iApply triple_call'. done. iModIntro. simpl.
      iApply (triple_bind_frame (CtxLet _ _)).
      iApply triple_load. iIntros (? ?). rewrite -!assoc.
      iApply triple_extract_pure_pre. iIntros ((X'&?&?&X)). simpl.
      inversion X'. subst x. clear X'.
      iApply triple_let_val. simpl.
      iApply (triple_bind (CtxIf _ _)).
      { iApply triple_call_prim'. done. }
      iIntros (? []). iApply triple_extract_pure_pre. iIntros (->).

      simpl.

      iApply (triple_conseq_pre (pointsto l' (DfracOwn 1) [(^v)%V] ∗ pointsto l q vs)).
      iIntros "(?&?)". iFrame.

      replace (Z.to_nat i) with i in X by lia.

      triple_if.
      case_bool_decide.
      { subst.
        iApply (triple_bind (CtxStore1 _ _)).
        iApply (triple_bind_frame (CtxCallPrim2 _ _)).
        iApply triple_load. iIntros (? ?). rewrite -!assoc.
        iApply triple_extract_pure_pre. iIntros ((->&?&?&X1)).
        simpl in *. assert (x=0) by lia. subst.
        simpl in X1. inversion X1. subst. iApply triple_call_prim'. done.
        simpl. iIntros (? []).
        iApply triple_extract_pure_pre. iIntros (->).
        iApply triple_frame.
        iApply triple_end.
        iApply triple_store.
        iIntros (? ?). iApply triple_val'.
        iIntros "((%X1&->&%)&?)". inversion X1. subst. simpl in *.
        rewrite -Nat2Z.inj_add.
        replace (List.count_occ _ (take i vs) e + 1) with (List.count_occ val_eq_dec (take (S i) vs) e). done.
        replace (i+1) with (S i) by lia.
        erewrite take_S_r; eauto. rewrite count_occ_app. simpl.
        rewrite decide_True //. }
      { iApply triple_val'. simpl. iIntros "(?&?)".
        iFrame. subst.
        replace (List.count_occ val_eq_dec (take i vs) e) with (List.count_occ val_eq_dec (take (S i) vs) e). done.
        erewrite take_S_r; eauto. rewrite count_occ_app. simpl.
        rewrite decide_False //. } }
    iIntros (? []). simpl. iApply triple_let_val. simpl.
    iApply (triple_conseq_pre ( pointsto l q vs ∗ pointsto l' (DfracOwn 1) [(^(List.count_occ val_eq_dec (take (S i) vs) e))%V])).
    { iIntros "(?&?)". iFrame. }
    iApply ("IH" with "[%][%][%]"). reflexivity. 1,2:lia. }
Qed.

Definition filter_pure e (vs:list val) := base.filter (fun x => (x ≠ e)) vs.

Definition count_nocc xs x := length xs - List.count_occ val_eq_dec xs x.

Lemma count_nocc_cons1 e a vs :
  e ≠ a ->
  count_nocc (a :: vs) e = S (count_nocc vs e).
Proof.
  intros.
  rewrite /count_nocc. simpl.
  rewrite decide_False //.
  rewrite Nat.sub_succ_l //. apply count_occ_bound.
Qed.

Lemma count_nocc_cons2 e vs :
  count_nocc (e :: vs) e = count_nocc vs e.
Proof.
  intros.
  rewrite /count_nocc. simpl.
  rewrite decide_True //.
Qed.

Lemma length_filter_pure (vs:list val) e :
  length (filter_pure e vs) = count_nocc vs e.
Proof.
  rewrite /filter_pure.
  induction vs; simpl; first done.
  rewrite filter_cons. case_decide; simpl; subst.
  { rewrite count_nocc_cons1 //. lia. }
  { rewrite count_nocc_cons2 //. }
Qed.

Lemma lookup_filter_pure e i vs v :
  vs !! i = Some v ->
  v ≠ e ->
  filter_pure e vs !! count_nocc (take i vs) e = Some v.
Proof.
  revert i. induction vs. done.
  intros i Hv ?. destruct i; simpl in *.
  { inversion Hv.
    replace ( count_nocc [] e) with 0 by compute_done.
    rewrite /filter_pure filter_cons. rewrite decide_True //. }
  { rewrite /filter_pure filter_cons. case_decide.
    { rewrite count_nocc_cons1 //. eauto. }
    { subst. rewrite count_nocc_cons2. eauto. } }
Qed.

Lemma count_nocc_nil e :
  count_nocc [] e = 0.
Proof. done. Qed.

Lemma count_nocc_prefix i vs e :
  count_nocc (take i vs) e <= count_nocc vs e.
Proof.
  revert i. induction vs; intros i; simpl.
  { rewrite take_nil. lia. }
  { destruct i; simpl.
    { rewrite count_nocc_nil. lia. }
    destruct_decide (decide (a=e)).
    { subst. rewrite !count_nocc_cons2. eauto. }
    { rewrite !count_nocc_cons1 //. specialize (IHvs i). lia. } }
Qed.

Lemma length_count_nocc_prefix i vs e :
  length (take (count_nocc (take i vs) e) (filter_pure e vs))
  = count_nocc (take i vs) e.
Proof.
  rewrite take_length length_filter_pure.
  pose proof (count_nocc_prefix i vs e).
  lia.
Qed.

Lemma ugly vs i v e :
  vs !! i = Some v ->
  v ≠ e ->
  count_nocc (take i vs) e < count_nocc vs e.
Proof.
  revert i. induction vs; first done.
  intros []; simpl.
  { inversion 1. intros. rewrite count_nocc_nil count_nocc_cons1 //. lia. }
  { intros. destruct_decide (decide (a=e)); subst.
    { rewrite !count_nocc_cons2. eauto. }
    { rewrite !count_nocc_cons1 //. apply IHvs in H0. lia. done. } }
Qed.

Lemma drop_cons_strange {A} (v:A) n vs :
  0 ≠ length vs - n ->
  <[0:=v]> (drop n vs) = v :: drop (S n) vs.
Proof.
  intros. apply list_eq. intros i.
  destruct i.
  { rewrite list_lookup_insert //.
    rewrite drop_length. lia. }
  { rewrite list_lookup_insert_ne //. simpl.
    rewrite !lookup_drop. f_equal. lia. }
Qed.

Lemma filter_spec E (l r:loc) (q:dfrac) (vs vs':list val) (e:val) :
  length vs' = count_nocc vs e ->
  ⊢ triple E (pointsto l q vs ∗ pointsto r (DfracOwn 1) vs') (filter l (length vs) r e) (fun v (_:unit) => ⌜v=VUnit⌝ ∗ pointsto l q vs ∗ pointsto r (DfracOwn 1) (filter_pure e vs)).
Proof.
  iIntros (?).

  iApply (triple_bind (CtxCall2 _)).
  iApply (triple_bind (CtxCall2 _)).
  iApply (triple_bind (CtxCall2 _)).
  call1. call2. call3.
  call1. call2. call3.
  call1. call2. call3.
  call1.

  iApply (triple_conseq_pre (True ∗ _))%I.
  rewrite left_id //.
  iApply (triple_bind_frame (CtxLet _ _)). iApply triple_ref.
  iIntros (? []).
  rewrite bi.sep_exist_r.
  iApply triple_extrude_existential.
  { monPred.unseal. iIntros (?) "((->&_)&_)". iModIntro.
    iIntros (?) "((%Eq&_)&_)". iPureIntro. naive_solver. }
  iIntros (l'). rewrite -assoc. iApply triple_extract_pure_pre.
  iIntros (->). rewrite -assoc. iApply triple_let_val. simpl.

  iApply (triple_bind (CtxLet _ _)).
  iApply triple_code'. simpl.
  call3. iApply triple_let_val. simpl.
  rename l' into z.
  iAssert (□ ∀ (i j:nat),
     ⌜i <= length vs /\ j=count_nocc (take i vs) e⌝ -∗
     triple E (pointsto z (DfracOwn 1) [VInt j] ∗ pointsto l q vs ∗ pointsto r (DfracOwn 1) (take j (filter_pure e vs) ++ drop j vs')) (seqfor i (length vs) _) (fun v (_:unit) => ⌜v=VUnit⌝ ∗ pointsto l q vs ∗ pointsto r (DfracOwn 1) (filter_pure e vs)))%I with "[]" as "#Hwp"; first shelve.
  { iApply triple_conseq. 3:iApply "Hwp".
    { iIntros "(?&?&?&?)". iFrame.
      rewrite take_0 drop_0 left_id_L //. }
    { iIntros (? []) "(->&?&?)". by iFrame. }
    { iPureIntro. split. lia. eauto. } }

  (* Now we verify the closure *)
  Unshelve.
  iModIntro. iIntros (??) "(%X1&%X2)".
  remember (length vs - i) as k.
  iInduction k as [|] "IH" forall (i j X1 X2 Heqk).
  { iApply triple_seqfor.
    assert (i=length vs) as -> by lia.
    rewrite decide_True //.
    subst. rewrite !firstn_all //.
    rewrite drop_ge; last lia.
    rewrite right_id_L.
    rewrite take_ge.
    2:{ rewrite length_filter_pure. rewrite /count_nocc. done. }
    iApply triple_val'.
    iIntros "(?&?&?)". by iFrame. }
  { iApply triple_seqfor. rewrite decide_False; last lia.

    unshelve iApply (triple_bind (CtxLet _ _)).
    2:exact (fun v (_:unit) => (pointsto z (DfracOwn 1) [VInt (count_nocc (take (S i) vs) e)%V] ∗ pointsto l q vs ∗
             pointsto r (DfracOwn 1) (take (count_nocc (take (S i) vs) e) (filter_pure e vs) ++ drop (count_nocc (take (S i) vs) e) vs')) )%I.
    2:{ iIntros (? []). simpl. iApply triple_let_val.
        iApply ("IH" with "[%][%][%]"). lia. done. lia. }

    call1. iClear "IH".
    iApply (triple_conseq_pre (pointsto l q vs ∗ _)).
    { iIntros "(?&?&?)". iFrame. rewrite left_id. iStopProof. reflexivity. }
    iApply (triple_bind_frame (CtxLet _ _)).
    iApply triple_load.
    iIntros (? ?).
    rewrite -assoc. iApply triple_extract_pure_pre.
    iIntros ((X'&?&Hi)). inversion X'. subst x.
    iApply triple_let_val. simpl.

    iApply (triple_bind (CtxIf _ _)).
    iApply triple_call_prim'. done.
    iIntros (? []). simpl.
    iApply triple_extract_pure_pre. iIntros (->).
    triple_if.

    replace (Z.to_nat i) with i in Hi by lia.

    case_bool_decide; subst.
    { iApply triple_val'. iIntros "(?&Hl&?)". iFrame.
      replace (count_nocc (take i vs) e) with (count_nocc (take (S i) vs) e).
      iFrame.
      rewrite /count_nocc.
      erewrite take_S_r; eauto. rewrite count_occ_app. simpl.
      rewrite decide_True //. rewrite app_length. simpl. lia. }
    { iApply triple_frame_wand.

      iApply (triple_bind_frame (CtxLet _ _)).
      iApply triple_load.
      iIntros (??). rewrite -assoc.
      iApply triple_extract_pure_pre.
      iIntros "(%Eq&_&%X)". inversion Eq. subst x. clear Eq.
      simpl in X. inversion X. subst. clear X.
      iApply triple_let_val. simpl.
      iApply (triple_bind_frame (CtxLet _ _)).
      { iApply (triple_conseq_pre (True ∗ _))%I.
        rewrite left_id //.
        iApply (triple_bind_frame (CtxStore1 _ _)).
        iApply triple_call_prim.
        iIntros (? []).
        iApply triple_extract_pure_pre. iIntros (Eq).
        simpl in Eq. inversion Eq. subst.
        iApply triple_store. }
      iIntros (??). simpl. rewrite -assoc.
      iApply triple_extract_pure_pre. iIntros "(%Eq&->&_)".
      inversion Eq. subst. clear Eq.
      simpl.
      iApply triple_let_val. simpl.

      iApply triple_frame_wand.
      iApply triple_end. iApply triple_store.
      iIntros (??). iApply triple_val'.
      iIntros "((%Eq&->&_)&?) ? ?".
      inversion Eq. subst. iFrame.
      rewrite -Nat2Z.inj_add.

      assert (List.count_occ val_eq_dec (take i vs) e <= length (take i vs)).
      apply List.count_occ_bound.

      assert (count_nocc (take (S i) vs) e = count_nocc (take i vs) e + 1) as Hne.
      { rewrite /count_nocc.
        erewrite take_S_r; eauto. rewrite count_occ_app. simpl.
        rewrite decide_False //. rewrite app_length. simpl.
        lia. }

      rewrite Hne. iFrame.
      iFrame.
      replace (Z.to_nat (count_nocc (take i vs) e)) with (count_nocc (take i vs) e) by lia.
      replace  (<[(count_nocc (take i vs) e):=v]>
           (take (count_nocc (take i vs) e) (filter_pure e vs) ++
            drop (count_nocc (take i vs) e) vs')) with (take (count_nocc (take i vs) e + 1) (filter_pure e vs) ++ drop (count_nocc (take i vs) e + 1) vs').
      iFrame.
      symmetry. rewrite Nat.add_1_r.
      erewrite take_S_r; eauto. 2:by erewrite lookup_filter_pure.
      rewrite insert_app_r_alt.
      2:rewrite length_count_nocc_prefix //.
      rewrite length_count_nocc_prefix Nat.sub_diag.
      rewrite -assoc_L. simpl. f_equal.
      rewrite drop_cons_strange //. rewrite H0.
      pose proof (ugly vs i v e Hi H2). lia. } }
Qed.

Lemma filter_compact_spec E (l:loc) (q:dfrac) (vs:list val) (e:val) :
  ⊢ triple E (pointsto l q vs) (filter_compact l e) (fun (v:val) (_:unit) => ∃ r, ⌜v=VLoc r⌝ ∗ pointsto l q vs ∗ pointsto r (DfracOwn 1) (filter_pure e vs)).
Proof.
  iIntros.

  iApply (triple_bind (CtxCall2 _)).
  call1. call2. call3. call1.

  iApply (triple_bind (CtxLet _ _)). iApply triple_length.
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_let_val. simpl.

  iApply (triple_bind (CtxLet _ _)). iApply count_occ_spec.
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_let_val. simpl.

  iApply (triple_bind (CtxLet _ _)). iApply triple_call_prim'. done.
  simpl.
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_let_val. simpl.

  rewrite -Nat2Z.inj_sub. 2:apply count_occ_bound.
  iApply triple_let_alloc.
  iIntros (l'). simpl.

  iApply (triple_bind (CtxLet _ _)).
  { iApply triple_conseq_pre. 2:iApply filter_spec.
    iIntros "(?&?&?)". iFrame.
    rewrite replicate_length //. }

  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_let_val. simpl.
  iApply triple_val'. iIntros "(?&?)". by iFrame.
Qed.

End spec.
