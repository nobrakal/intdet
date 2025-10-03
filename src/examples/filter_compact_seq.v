From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export cancelable_invariants.
From iris.algebra Require Import gmap gmultiset agree frac_auth gset.

From intdet.lang Require Import syntax syntax_instances notations head_semantics.
From intdet.utils Require Import elems big_opN more_maps_and_sets.
From intdet.angelic Require Import run.

From intdet.examples Require Import reference fill filter_compact tactics.

Section proof.

Context `{seqlogGS Σ}.

Lemma seqfor_spec (i j:nat) (f:val) (Q:val -> iProp Σ) :
  (if (decide (i=j)) then Q VUnit else run (f i) (fun _ => run (seqfor (i+1) j f) Q))
  -∗ run (seqfor i j f) Q.
Proof.
  iIntros "Hwp".
  do 2 iApply (run_bind (CtxCall2 _)).
  do 2 (iApply run_call; iApply run_code; iApply run_val).
  iApply run_call. simpl. fold seqfor.

  iApply (run_bind (CtxIf _ _)).
  iApply run_mono. iApply run_call_prim. done.
  iIntros (?) "->". simpl.

  iApply run_if.
  case_decide; subst.
  { rewrite bool_decide_eq_true_2 //. by iApply run_val. }
  { rewrite bool_decide_eq_false_2; last naive_solver.
    iApply (run_bind (CtxLet _ _)).
    iApply run_mono. iApply run_call_prim. done.
    iIntros (?) "->". iApply run_let_val. simpl.
    iApply (run_bind (CtxLet _ _)).
    iApply (run_mono with "[$]").
    iIntros (?) "Hwp". iApply run_let_val. simpl.
    rewrite Nat2Z.inj_add //. }
Qed.

Lemma ref_spec (v:val) :
  ⊢ run (ref v) (fun w => ∃ l, ⌜w=VLoc l⌝ ∗ pointsto l (DfracOwn 1) [v]).
Proof.
  iIntros.
  iApply run_call. simpl.
  iApply (run_bind (CtxLet _ _)).
  iApply run_mono. iApply run_alloc. done.
  iIntros (?) "(%&->&?)". iApply run_let_val. simpl.
  iApply (run_bind (CtxLet _ _)).
  iApply (run_mono with "[-]"). iApply (run_store with "[$]"). done.
  iIntros (?) "(->&?)". simpl. iApply run_let_val. iApply run_val.
  eauto.
Qed.

Lemma count_occ_spec (l:loc) (q:dfrac) (vs:list val) (e:val) :
  pointsto l q vs -∗
  run (count_occ l e) (fun v => ⌜v=VInt (List.count_occ val_eq_dec vs e)⌝ ∗ pointsto l q vs).
Proof.
  iIntros "Hl".

  iApply (run_bind (CtxCall2 _)).
  iApply run_call; iApply run_code; iApply run_val.
  iApply run_call.

  iApply (run_bind (CtxLet _ _)).
  iApply (run_mono with "[]").
  { iApply ref_spec. }
  iIntros (?) "(%r&->&?)". iApply run_let_val. simpl.
  iApply (run_bind (CtxLet _ _)).
  iApply run_code. iApply run_val. iApply run_let_val. simpl.

  iApply (run_bind (CtxLet _ _)).
  iApply (run_mono with "[Hl]"). iApply (run_length with "[$]").
  iIntros (?) "(->&?)". iApply run_let_val. simpl.

  iAssert (∀ (x:nat) i, ⌜i <= length vs /\ x = List.count_occ val_eq_dec (take i vs) e⌝ -∗ pointsto l q vs ∗ pointsto r (DfracOwn 1) [VInt x] -∗ run (seqfor i (length vs) _) (fun _ => pointsto l q vs ∗ pointsto r (DfracOwn 1) [VInt (List.count_occ val_eq_dec vs e)]))%I with "[]" as "Hwp"; last first.
  { iApply (run_bind (CtxLet _ _)).
    iApply (run_mono with "[-]").
    { iApply "Hwp"; try iFrame.
      { iPureIntro. split. lia. rewrite take_0 //. } }
    { iIntros (?) "(?&Hr)". iApply run_let_val.
      iApply (run_mono with "[Hr]"). iApply (run_load with "[$]"). done. done.
      iIntros (?) "(->&?)". by iFrame. } }
  { iIntros (x i) "(%X1&%X2) (Hl&Hr)".
    remember (length vs - i) as j.
    iInduction j as [] "IH" forall (i x X1 X2 Heqj).
    { assert (i=length vs) by lia. subst.
      iApply seqfor_spec.
      rewrite decide_True //. rewrite firstn_all. iFrame. }
    { iApply seqfor_spec.
      rewrite decide_False. 2:lia.
      iApply run_call. simpl.
      iApply (run_bind (CtxLet _ _)).

      assert (is_Some (vs !! Z.to_nat i)) as (v&Hv).
      { apply lookup_lt_is_Some_2. lia. }

      iApply (run_mono with "[Hl]").
      iApply (run_load with "Hl").
      lia. done.
      iIntros (?) "(->&Hl)". iApply run_let_val. simpl.
      iApply (run_bind (CtxIf _ _)).
      iApply run_mono. iApply run_call_prim. done.
      iIntros (?) "->". simpl.
      iApply run_if. case_bool_decide.
      { subst.
        iApply (run_bind (CtxStore1 _ _)).
        iApply (run_bind (CtxCallPrim2 _ _)).
        iApply (run_mono with "[Hr]"). iApply (run_load with "Hr").
        done. done. iIntros (?) "(->&Hr)". simpl.
        iApply run_mono. iApply run_call_prim. done.
        iIntros (?) "->". simpl.
        iApply (run_mono with "[Hr]").
        iApply (run_store with "Hr"). done.
        iIntros (?) "(->&Hr)". simpl.

        rewrite -Nat2Z.inj_add.
        replace (List.count_occ _ (take i vs) e + 1) with (List.count_occ val_eq_dec (take (S i) vs) e).
        2:{ replace (i+1) with (S i) by lia.
            erewrite take_S_r; eauto. rewrite count_occ_app. simpl.
            rewrite decide_True //. rewrite -Hv. f_equal. lia. }
        replace (i + 1) with (S i) by lia.

        iApply ("IH" with "[%][%][%][$] Hr"); lia. }
      { iApply run_val.
        iApply ("IH" with "[%][%][%][$][$]"); try lia.
        replace (i+1) with (S i) by lia.
        erewrite take_S_r; eauto. rewrite count_occ_app. simpl.
        rewrite decide_False //. lia. rewrite -Hv. f_equal. lia. } } }
Qed.

Lemma count_nocc_app vs1 vs2 v :
  count_nocc (vs1 ++ vs2) v = count_nocc vs1 v + count_nocc vs2 v.
Proof.
  rewrite /count_nocc. rewrite app_length. rewrite List.count_occ_app.
  assert (List.count_occ val_eq_dec vs1 v <= length vs1)
    by apply List.count_occ_bound.
  assert (List.count_occ val_eq_dec vs2 v <= length vs2)
    by apply List.count_occ_bound.
  lia.
Qed.

Lemma count_nocc_cons vs x v :
  count_nocc (v::vs) x = if val_eq_dec v x then (count_nocc vs x) else S (count_nocc vs x).
Proof.
  rewrite /count_nocc. simpl.
  destruct (val_eq_dec v x); subst.
  { lia. }
  { assert (List.count_occ val_eq_dec vs x <= length vs)
      by apply List.count_occ_bound.
    lia. }
Qed.

Lemma filter_spec (l r:loc) (q:dfrac) (vs vs':list val) (e:val) :
  length vs' = count_nocc vs e ->
  pointsto l q vs -∗
  pointsto r (DfracOwn 1) vs' -∗
  run (filter l (length vs) r e) (fun v => ⌜v=VUnit⌝ ∗ pointsto l q vs ∗ pointsto r (DfracOwn 1) (filter_pure e vs)).
Proof.
  iIntros (?) "Hl Hr".

  do 3 iApply (run_bind (CtxCall2 _)).
  do 3 (iApply run_call; iApply run_code; iApply run_val).
  iApply run_call. simpl.

  iApply (run_bind (CtxLet _ _)).
  iApply run_mono.
  by iApply ref_spec.
  iIntros (?) "[%z (->&Hz)]". iApply run_let_val. simpl.

  iApply (run_bind (CtxLet _ _)). iApply run_code. iApply run_val.
  iApply run_let_val. simpl.

  iAssert (□ ∀ (i j:nat),
     ⌜i <= length vs /\ j=count_nocc (take i vs) e⌝ -∗
     pointsto z (DfracOwn 1) [VInt j] -∗ pointsto l q vs -∗ pointsto r (DfracOwn 1) (take j (filter_pure e vs) ++ drop j vs') -∗ run (seqfor i (length vs) (λ:"j",
         let: "x" := #l.["j"] in
         if: CallPrim PrimEq "x" e then VUnit else
         let: "j" := #z.[^0] in
          #z.[^0] <- (CallPrim (PrimIntOp IntAdd) "j" ^1%nat) ;; #r.["j"] <- "x")%V) (fun v => ⌜v=VUnit⌝ ∗ pointsto l q vs ∗ pointsto r (DfracOwn 1) (filter_pure e vs)))%I with "[]" as "#Hwp"; last first.
  { iApply ("Hwp" $! 0 (count_nocc (take 0 vs) e) with "[%][$][$][$]").
    rewrite take_0 //.
    rewrite /count_nocc List.count_occ_nil //. split. lia. simpl. lia. }

  iModIntro. iIntros (i j (Hi&Hj)) "Hz Hl Hr".
  remember (length vs - i) as k.
  iInduction k as [] "IH" forall (i j Heqk Hi Hj).
  { iApply seqfor_spec.
    assert (i = length vs) as -> by lia.
    rewrite decide_True //.
    rewrite firstn_all in Hj. subst. rewrite -H0.
    rewrite drop_ge // right_id_L.
    rewrite take_ge.
    2:{ rewrite length_filter_pure. lia. }
    by iFrame. }
  { iApply seqfor_spec. rewrite decide_False; last lia.
    iApply run_call. simpl.

    assert (is_Some (vs !! i)) as (v&Hv).
    { apply lookup_lt_is_Some_2. lia. }

    iApply (run_bind (CtxLet _ _)).
    iApply (run_mono with "[Hl]").
    iApply (run_load with "[$]"). lia.
    rewrite Nat2Z.id //.

    iIntros (?) "(->&?)". iApply run_let_val. simpl.

    iApply (run_bind (CtxIf _ _)).
    iApply run_mono. iApply run_call_prim. done.
    iIntros (?) "->". simpl.
    iApply run_if. case_bool_decide; subst.
    { iApply run_val.
      iApply ("IH" with "[%][%][%][$][$][$]"). 1,2:lia.
      rewrite /count_nocc. rewrite Nat.add_1_r.
      erewrite take_S_r; eauto. rewrite count_occ_app. simpl.
      rewrite decide_True //. rewrite app_length. simpl. lia. }
    { iApply (run_bind (CtxLet _ _)).
      iApply (run_mono with "[Hz]").
      iApply (run_load with "Hz"). done. done.
      iIntros (?) "(->&Hz)". iApply run_let_val. simpl.

      iApply (run_bind (CtxLet _ _)).
      iApply (run_bind (CtxStore1 _ _)).
      iApply run_mono. iApply run_call_prim. done.
      iIntros (?) "->". simpl.
      iApply (run_mono with "[Hz]").
      iApply (run_store with "Hz"). done.
      iIntros (?) "(->&Hz)". iApply run_let_val. simpl.

      assert (List.count_occ val_eq_dec (take i vs) e <= length (take i vs)).
      apply List.count_occ_bound.

      assert (count_nocc (take (S i) vs) e = count_nocc (take i vs) e + 1) as Hne.
      { rewrite /count_nocc.
        erewrite take_S_r; eauto. rewrite count_occ_app. simpl.
        rewrite decide_False //. rewrite app_length. simpl.
        lia. }

      iApply (run_mono with "[Hr]").
      iApply (run_store with "[$]").
      { split; first lia.
        rewrite app_length take_length drop_length.
        rewrite length_filter_pure. rewrite H0.
        assert (count_nocc (take i vs) e < count_nocc vs e); last lia.
        rewrite -{2}(take_drop_middle _ _ _ Hv).
        rewrite count_nocc_app. rewrite count_nocc_cons.
        destruct (val_eq_dec v e); subst; first done. lia. }
      iIntros (?) "(->&?)".

      rewrite -Nat2Z.inj_add.

      iApply ("IH" with "[%][%][%][Hz][$]").
      { lia. }
      { lia. }
      { rewrite Nat.add_1_r Hne //.  }
      { rewrite Hne //. }
      { replace (Z.to_nat (count_nocc (take i vs) e)) with (count_nocc (take i vs) e) by lia.
        rewrite Hne.
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
        pose proof (ugly vs i v e Hv H1). lia.  } } }
Qed.

Lemma filter_compact_spec (l:loc) (q:dfrac) (vs:list val) (e:val) :
  pointsto l q vs -∗
  run (filter_compact l e) (fun (v:val) => ∃ r, ⌜v=VLoc r⌝ ∗ pointsto l q vs ∗ pointsto r (DfracOwn 1) (filter_pure e vs)).
Proof.
  iIntros "Hl".

  iApply (run_bind (CtxCall2 _)).
  iApply run_call. iApply run_code. iApply run_val.
  iApply run_call. simpl.

  iApply (run_bind (CtxLet _ _)).
  iApply (run_mono with "[Hl]").
  iApply (run_length with "Hl").
  iIntros (?) "(->&Hl)". iApply run_let_val. simpl.

  iApply (run_bind (CtxLet _ _)).

  iApply (run_mono with "[-]").
  iApply (count_occ_spec with "[$]").
  iIntros (?) "(->&Hl)". iApply run_let_val. simpl.

  iApply (run_bind (CtxLet _ _)).
  iApply run_mono. iApply run_call_prim. done.
  iIntros (?) "->". iApply run_let_val. simpl.

  iApply (run_bind (CtxLet _ _)).
  iApply run_mono. iApply run_alloc.
  { assert (List.count_occ val_eq_dec vs e <= length vs)
      by apply List.count_occ_bound. lia. }

  iIntros (?) "(%&->&?)". iApply run_let_val. simpl.
  iApply (run_bind (CtxLet _ _)).
  iApply (run_mono with "[-]").
  { iApply (filter_spec with "[Hl][$]").
    { rewrite replicate_length // /count_nocc. lia. }
    { done. } }

  iIntros (?) "(->&?&?)". iApply run_let_val. simpl.
  iApply run_val. by iFrame.
Qed.

End proof.
