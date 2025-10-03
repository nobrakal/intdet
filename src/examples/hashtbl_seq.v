From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export cancelable_invariants.
From iris.algebra Require Import gmap gmultiset agree frac_auth gset.

From intdet.lang Require Import syntax syntax_instances notations head_semantics.
From intdet.utils Require Import elems big_opN more_maps_and_sets.
From intdet.angelic Require Import run.

From intdet.examples Require Import reference fill filter_compact_seq tactics hashtbl hashtbl_pure fill_seq.

Local Opaque run.

Section proof.

Context `{seqlogGS Σ}.

(* The option represents the debt *)
Definition hashset_inner l p M vs (o:option val) : iProp Σ :=
    (* The points-tos of l and the dummy *)
    pointsto l (DfracOwn 1) vs ∗ pointsto p.(dummy) (DfracOwn 1) [VUnit] ∗
    (* Pure invariants. *)
    ⌜hashtbl_invariant p (option_to_set o) M vs⌝.

Definition not_full p (vs:list val) :=
  Exists (fun v => v = VLoc p.(dummy)) vs.

Definition filled_from_upto p (vs:list val) i n :=
  forall j, j < n ->
       exists v, vs !! ((i + j) `mod` cap p) = Some v /\ v ≠ VLoc (dummy p).

Lemma filled_from_upto_insert_not_dumm p vs i n j v :
  v ≠ VLoc (dummy p) ->
  filled_from_upto p vs i n ->
  filled_from_upto p (<[j:=v]>vs) i n.
Proof.
  intros ? X.
  destruct_decide (decide (j < length vs)).
  2:{ rewrite list_insert_ge //. lia. }
  intros k Hk.
  destruct_decide (decide (j=((i + k) `mod` cap p))).
  { subst. exists v. rewrite list_lookup_insert //. }
  destruct (X k Hk) as (v'&?&?).
  exists v'. rewrite list_lookup_insert_ne //.
Qed.

Lemma Exists_iff_lookup {A:Type} P (xs:list A):
  Exists P xs <-> exists i x, xs !! i = Some x /\ P x.
Proof.
  split.
  { induction 1.
    { exists 0. simpl. eauto. }
    { destruct IHExists as (i&x'&Hi&Hx).
      exists (S i). simpl. eauto. } }
  { intros (i&x&Hi&Hx).
    revert xs Hi. induction i; intros xs Hi.
    { destruct xs; try done. simpl in *. inversion Hi. constructor. done. }
    { destruct xs; simpl in *; try done.
      apply IHi in Hi. apply Exists_cons_tl. done. } }
Qed.

Lemma before_full_length_not_not_full p vs u u' :
  cap p ≠ 0 ->
  cap p = length vs ->
  not_full p vs ->
  cap p <= u' ->
  filled_from_upto p vs u u' ->
  ¬ not_full p vs.
Proof.
  intros Hp Hlength Hnot Hn0 Hfull Hex.
  apply Exists_iff_lookup in Hex. destruct Hex as (i&?&Hi&->).
  assert (i < length vs) by by eapply lookup_lt_Some.
  unfold filled_from_upto in Hfull.
  destruct_decide (decide (u `mod` length vs <= i)).
  { destruct (Hfull (i - u `mod` length vs)) as (v'&Hv'&?). lia.
    replace ((u + (i - u `mod` length vs)) `mod` cap p) with i in Hv'.
    naive_solver.

    (* We go to Z. *)
    apply Nat2Z.inj.
    rewrite Nat2Z.inj_mod Nat2Z.inj_add Nat2Z.inj_sub // Nat2Z.inj_mod.
    rewrite -Hlength.
    rewrite -Zplus_mod_idemp_l.
    replace (u `mod` cap p + (i - u `mod` cap p))%Z with (Z.of_nat i) by lia.
    rewrite Z.mod_small //. lia. }
  { destruct (Hfull (i + (length vs - u `mod` cap p))) as (v'&Hv'&?).
    { rewrite Hlength. lia. }
    replace ((u + (i + (length vs - u `mod` cap p))) `mod` cap p) with i in Hv'.
    naive_solver.
    rewrite -Hlength.

    (* We go to Z. *)
    apply Nat2Z.inj.
    rewrite Nat2Z.inj_mod !Nat2Z.inj_add Nat2Z.inj_sub.
    2:{ apply (Nat.mod_upper_bound u) in Hp. lia. }
    rewrite Nat2Z.inj_mod.
    rewrite -Zplus_mod_idemp_l.
    replace (u `mod` cap p + (i + (cap p - u `mod` cap p)))%Z with (i + 1 * cap p)%Z by lia.
    rewrite Z.mod_add. 2:lia. rewrite Z.mod_small //. lia. }
Qed.

Lemma filled_from_upto_S p vs u0 u v :
  vs !! ((u0 + u) `mod` cap p) = Some v ->
  v ≠ VLoc (dummy p) ->
  filled_from_upto p vs u0 u  ->
  filled_from_upto p vs u0 (S u).
Proof.
  intros X1 X2 X3. intros j Hj.
  destruct_decide (decide (j=u)).
  { subst. exists v. eauto. }
  { apply X3. lia. }
Qed.

Lemma modulo_mono_S a b c :
  a `mod` c = b `mod` c ->
  (S a) `mod` c = (S b) `mod` c.
Proof.
  intros E.
  rewrite -(Nat.add_1_r a) -(Nat.add_1_r b).
  rewrite Nat.Div0.add_mod E -Nat.Div0.add_mod //.
Qed.

Lemma not_full_replace p vs i x1 x2 :
  x1 ≠ VLoc (dummy p) ->
  x2 ≠ VLoc (dummy p) ->
  vs !! i = Some x1 ->
  not_full p vs ->
  not_full p (<[i:=x2]>vs).
Proof.
  rewrite /not_full. rewrite !Exists_iff_lookup.
  intros ??? (j&Hj).
  exists j. rewrite list_lookup_insert_ne //.
  intros ->. naive_solver.
Qed.

Lemma rank_succ p v i :
  cap p ≠ 0 ->
  hash p v ≤ i ->
  rank p v (S i) = Z.to_nat ((rank p v i + 1) `mod` cap p)%Z.
Proof.
  intros. rewrite /rank. f_equal.
  rewrite Z2Nat.id.
  2:{ apply Z.mod_pos. lia. }
  replace (S i - hash p v)%Z with (i - hash p v + 1)%Z by lia.
  rewrite Z.add_mod. 2:lia.
  rewrite Zplus_mod_idemp_r //.
Qed.

Lemma before_full_cons1 p vs v i v':
  cap p ≠ 0 ->
  vs !! (i `mod` cap p) = Some v' ->
  v' ≠ (#(dummy p))%V ->
  cmp p v' v -> v' ≠ v ->
  hash p v ≤ i ->
  before_full p vs (rank p v i) v ->
  before_full p vs (rank p v (S i)) v.
Proof.
  intros ?????? Hf. intros j Hj.
  destruct_decide (decide (j = rank p v i)).
  { subst. exists v'. rewrite probe_rank //. }
  { apply Hf.
    rewrite rank_succ // in Hj.
    assert (S (rank p v i) `mod` cap p <= S (rank p v i))%Z; last lia.
    apply Z.mod_le. 1,2:lia. }
Qed.

Lemma before_full_mod p vs j x :
  before_full p vs j x ->
  before_full p vs (j `mod` cap p) x.
Proof.
  intros X. intros k Hk. apply X.
  pose proof (Nat.Div0.mod_le j (cap p)). lia.
Qed.

Lemma before_full_cons2 p vs v i v':
  cap p ≠ 0 ->
  vs !! (probe p v i) = Some v' ->
  v' ≠ (#(dummy p))%V ->
  cmp p v' v -> v' ≠ v ->
  before_full p vs i v ->
  before_full p vs (S i) v.
Proof.
  intros ????? Hfull. intros k Hk.
  destruct_decide (decide (k=i)).
  { subst. exists v'. eauto. }
  { apply Hfull. lia. }
Qed.

Lemma before_full_insert_at p x j v vs :
  vs !! probe p x j = Some x ->
  before_full p vs j x ->
  before_full p (<[probe p x j:=v]> vs) j x.
Proof.
  intros Hx X. intros k Hk.
  destruct (X k) as (v'&?&?&?&?). lia.
  exists v'. split_and !; try done.
  rewrite list_lookup_insert_ne //.
  intros E. rewrite E in Hx. naive_solver.
Qed.

Lemma hs_put_spec p (c:val)  (u0 u:nat) M vs (i i':nat) (l:loc) (v:val) :
  v ≠ VLoc p.(dummy) ->
  p.(cap) ≠ 0 ->
  i = i' mod p.(cap) ->
  p.(hash) v ≤ i' ->
  not_full p vs ->
  before_full p vs (rank p v i') v ->
  filled_from_upto p vs u0 u ->
  (u0 + u) `mod` cap p = i ->
  □ (∀ (x y:val), run (c x y) (fun v => ⌜v = VBool (p.(cmp) x y)⌝)) -∗
  hashset_inner l p M vs (Some v) -∗
  run (htbl_add_aux c l p.(dummy) (cap p) v i)
    (fun w => ⌜w=VUnit⌝ ∗ ∃ M' vs',  ⌜dom M' = dom M ∪ {[v]}⌝ ∗ hashset_inner l p M' vs' None).
Proof.
  iIntros (Hvd Hcap -> Hh Hnot Hfull Hfilled Hu0) "#Hc Hl".

  remember (p.(cap) - u) as u'.
  iInduction u' as [|] "IH" forall (u i' v M vs Hequ' Hvd Hh Hnot Hfull Hfilled Hu0).
  (* the hashtbl is full! *)
  { assert (cap p ≤ u) by lia.
    iDestruct "Hl" as "(_&_&%Hpure)".
    exfalso.
    destruct Hpure as [Hlength Htie Hmod Hopt].
    eapply before_full_length_not_not_full; try done. }

  do 5 iApply (run_bind (CtxCall2 _)).
  do 5 (iApply run_call; iApply run_code; iApply run_val).
  iApply run_call. simpl.
  fold htbl_add_aux.

  iApply (run_bind (CtxLet _ _)).

  iDestruct "Hl" as "(Hl&Hd&%Hpure)".
  destruct Hpure as [Hlength Htie Hmod Hopt].

  assert (i' `mod` cap p < length vs).
  { rewrite Hlength. by apply Nat.mod_upper_bound. }
  assert (is_Some (vs !! (i' `mod` cap p))) as (x&Hx).
  { apply lookup_lt_is_Some_2. lia. }

  iApply (run_mono with "[Hl]").
  iApply (run_load with "Hl").
  { lia. }
  { replace (Z.to_nat (i' `mod` cap p)%nat) with (i' `mod` cap p) by lia.
    rewrite Hx //. }

  iIntros (?) "(->&Hl)". simpl.

  iApply run_let_val. simpl.

  iApply (run_bind (CtxIf _ _)).
  iApply run_mono. iApply run_call_prim. done.
  iIntros (?) "->". simpl.

  iApply run_if.
  case_bool_decide.
  { iApply run_val. iSplitR; first done. subst.
    iExists (<[v:=i' `mod` cap p]> M), _. iFrame.
    iPureIntro. split.
    { rewrite dom_insert_L. set_solver. }
    apply Htie in Hx. apply Hx in Hvd.
    rewrite insert_id //.
    simpl in *. assert (v ∈ dom M) by by eapply elem_of_dom.
    replace (dom M ∪ {[v]}) with (dom M) in Hopt by set_solver.
    constructor; try done. rewrite right_id_L //. }

  iApply (run_bind (CtxIf _ _)).
  iApply run_mono. iApply run_call_prim. done.
  iIntros (?) "->". simpl.

  iApply run_if.
  case_bool_decide.
  { subst.

    iApply (run_bind (CtxIf _ _)).
    iApply (run_mono  with "[Hl]").
    iApply (run_cas with "[$]"). lia.
    { replace (Z.to_nat (i' `mod` cap p)%nat) with (i' `mod` cap p) by lia.
      done. }
    iIntros (?) "(->&?)". simpl.

    iApply run_if.
    rewrite bool_decide_eq_true_2 //.

    assert (i' `mod` cap p = probe p v (rank p v i')) as X.
    { rewrite probe_rank //. }

    apply before_full_weak with (n:=rank p v i') in Hfull.
    2:done.

    iApply run_val.
    iSplitR; first done.
    iExists (<[v:=(i' `mod` cap p)]>M),_. iFrame. iPureIntro.
    rewrite Nat2Z.id. simpl.
    split.
    { rewrite dom_insert_L //. set_solver. }
    constructor.
    { rewrite insert_length //. }
    { eauto using tie_add1, before_full_confront. }
      { eauto using model_add1, rank_lt_cap. }
      { rewrite dom_insert_L right_id_L. rewrite X.
        simpl in Hopt.
        eapply opt_add1; eauto using rank_lt_cap, deduce_all_are_probe.
        rewrite -X //. set_solver. rewrite comm_L //. } }

  iApply (run_bind (CtxLet _ _)).
  iApply run_mono. iApply "Hc".
  iIntros (?) "->". simpl.
  iClear "Hc".

  iApply run_let_val. simpl.

  iApply (run_bind (CtxLet _ _)).
  iApply (run_bind (CtxCallPrim2 _ _)).
  iApply run_mono. iApply run_call_prim. done.
  iIntros (? ->). simpl.
  iApply run_mono. iApply run_call_prim. done.
  iIntros (? ->). simpl.

  replace ((i' `mod` cap p)%nat + Z.of_nat 1%nat)%Z with (Z.of_nat (S (i' `mod` cap p))) by lia.
  replace (S (i' `mod` cap p) `mod` Z.of_nat (cap p))%Z with (Z.of_nat ((1 + (i' `mod` cap p)) `mod` cap p)).
  2:{ simpl. rewrite Nat2Z.inj_mod. lia. }
  rewrite Nat.Div0.add_mod_idemp_r.

  iApply run_let_val. simpl.

  iApply run_if.
  destruct_decide (decide (cmp p x v)) as Hvx.
  { rewrite (Is_true_true_1 _ Hvx).
    iApply ("IH" $! (S u) with "[%][%][%][%][%][%][%]"); try done; try lia.
    { eauto using before_full_cons1. }
    { eapply filled_from_upto_S. rewrite Hu0 //. done. done. }
    { replace (u0 + S u) with (S (u0 + u)) by lia.
      apply modulo_mono_S. rewrite Hu0 //. }
    { iFrame. iPureIntro. by constructor. } }

  rewrite (Is_true_false_1 _ Hvx).
  iApply (run_bind (CtxIf _ _)).

  iApply (run_mono with "[Hl]").
  iApply (run_cas with "[$]"). lia.
  { replace (Z.to_nat (i' `mod` cap p)%nat) with (i' `mod` cap p) by lia.
    done. }
  iIntros (?) "(->&?)". simpl.

  iApply run_if. rewrite bool_decide_eq_true_2 //.

  assert (cmp p v x).
  { subst.
    destruct (trichotomy (strict p.(cmp)) v x) as [ X | [ X | X ] ].
    { destruct X. done. }
    { done. }
    { destruct X. congruence. } }

  replace (Z.to_nat (i' `mod` cap p)%nat) with (i' `mod` cap p) by lia.

  pose proof (Htie _ _ Hx H2) as Hx'.
  apply Hmod in Hx'. destruct Hx' as (_&_&j'&Heq'&_&Hfullj').

  replace (S i' `mod` cap p) with (probe p x (S j')).
  2:{ rewrite /probe.
      replace (S i') with (i' + 1) by lia.
      rewrite -(Nat.Div0.add_mod_idemp_l i').
      rewrite Heq'.
      rewrite Nat.Div0.add_mod_idemp_l. f_equal. lia. }

  assert (x ∈ dom M).
  { apply Htie in Hx. apply Hx in H2. by eapply elem_of_dom. }

  assert ({[v]} ∪ dom M ∖ {[x]} ∪ {[x]} = dom M ∪ {[v]}) as Heq.
  { rewrite -assoc_L difference_union_L. set_solver. }

  iApply (run_mono with "[-]").
  { iApply ("IH" $! (S u) _  _ (<[v:=i' `mod` cap p]>(delete x M))  (<[i' `mod` cap p:=v]> vs) with "[%][%][%][%][%][%][%]").
    { lia. }
    { done. }
    { lia. }
    { eapply not_full_replace; last done. 3:done. all:done. }
    { rewrite rank_add_mod. fold (probe p x (S j')).
      rewrite rank_probe //. 2:lia.
      apply before_full_mod.
      apply before_full_cons2 with (v':=v); try done.
      { rewrite -Heq' list_lookup_insert //. }
      rewrite Heq'. apply before_full_insert_at.
      rewrite -Heq' //. done. }
    { eapply filled_from_upto_S.
      { rewrite Hu0 list_lookup_insert //. }
      { done. }
      { eauto using filled_from_upto_insert_not_dumm. } }
    { replace (u0 + S u) with (S (u0 + u)) by lia.
      replace (hash p x + S j') with (S (hash p x + j')) by lia.
      apply modulo_mono_S. rewrite Hu0 Heq' //. }
    { iFrame. iPureIntro.

      assert (i' `mod` cap p = probe p v (rank p v i')) as X.
      { rewrite probe_rank //. }

      eapply before_full_weak in Hfull; last done.

      assert (v ∉ dom M).
      { eapply before_full_confront; try done.
        naive_solver.  }

      constructor.
      { rewrite insert_length //. }
      { eauto using tie_add2. }
      { eauto using model_add2, rank_lt_cap. }
      { simpl. rewrite dom_insert_L dom_delete_L Heq X.
        eapply opt_add2; eauto using rank_lt_cap, deduce_all_are_probe.
        set_solver.
        rewrite probe_rank //. } } }
  simpl.
  iIntros (?) "(->&[% [% (%Hdom&?&?)]])".
  iSplitR; first done.
  iFrame. iPureIntro.
  rewrite Hdom.
  rewrite dom_insert_L dom_delete_L Heq //.
Qed.
Definition cmp_spec cmp (c:val) : iProp Σ :=
  □ (∀ (x y:val), run (c x y) (fun v => ⌜v = VBool (cmp x y)⌝)).
Definition hash_spec hash (h:val) : iProp Σ :=
  □ (∀ (x:val), run (h x) (fun v => ⌜v = VInt (hash x)⌝)).
Definition hashset p v (g:gset val) : iProp Σ :=
  ∃ l h c M vs,
    ⌜v=vprods [VLoc l; h; c] (VLoc p.(dummy)) /\ p.(cap) ≠ 0 /\ dom M = g⌝ ∗
    hash_spec (hash p) h ∗ cmp_spec (cmp p) c ∗
    hashset_inner l p M vs None.
Lemma length_hashset l p M vs o :
  hashset_inner l p M vs o -∗
  run (Length l) (fun v => ⌜v=length vs ⌝ ∗ hashset_inner l p M vs o).
Proof.
  iIntros "(Hl&?)".
  iApply (run_mono with "[Hl]"). iApply (run_length with "[$]").
  iIntros (?) "(->&?)".
  iSplitR; first done. by iFrame.
Qed.
Lemma add_to_debt x l p M vs :
  hashset_inner l p M vs None -∗
  hashset_inner l p M vs (Some x).
Proof.
  iIntros "(?&?&%X)". iFrame.
  iPureIntro. simpl in *. destruct X as [X1 X2 X3 X4].
  constructor; try done.
  rewrite right_id_L in X4.
  destruct_decide (decide (x ∈ dom M)).
  { replace (dom M ∪ {[x]}) with (dom M) by set_solver. done. }
  { rewrite comm_L. eauto using opt_add. }
Qed.
Local Lemma NodDup_except_NoDup `{EqDecision A} (vs:list A) v :
  Forall (λ x, x ≠ v) vs ->
  NoDup_except v vs ->
  NoDup vs.
Proof.
  induction 1. done.
  unfold NoDup_except. rewrite filter_cons.
  case_decide.
  { inversion 1. subst. constructor; last eauto.
    intros ?. apply H6. apply elem_of_list_filter. done. }
  { exfalso. done. }
Qed.
Local Lemma tie_card_NoDup p M vs :
  Forall (λ x, x ≠ VLoc (dummy p)) vs ->
  NoDup vs ->
  tie p M vs ->
  length vs <= size M.
Proof.
  intros Hfor Hnd Htie.
  revert M Htie. induction vs; intros M Htie. simpl. lia.
  simpl. inversion Hnd. subst. inversion Hfor. subst.
  assert (M !! a = Some 0) as Ha.
  { apply Htie. done. done. }
  rewrite -(insert_id _ _ _ Ha) -insert_delete_insert.
  rewrite map_size_insert lookup_delete.
  specialize (IHvs H5 H3 (pred <$> (delete a M))).
  rewrite map_size_fmap in IHvs.
  assert  (length vs ≤ size (delete a M)). 2:lia.
  apply IHvs.
  intros i v Hiv X. rewrite lookup_fmap lookup_delete_ne.
  2:{ intros ->. apply elem_of_list_lookup_2 in Hiv. congruence. }
  rewrite (Htie (S i) v) //.
Qed.
Lemma size_lt_not_full p M vs :
  cap p = length vs ->
  size (dom M) < cap p ->
  tie p M vs ->
  hashset_inv_model p M vs ->
  not_full p vs.
Proof.
  intros ? Hcap Htie Hmod.
  unfold not_full.
  destruct_decide (decide (Exists (λ v : val, v = (#(dummy p))%V) vs)) as Hex.
  done. exfalso.
  apply Forall_Exists_neg in Hex.
  assert (NoDup vs) by eauto using NodDup_except_NoDup, nodup_ok.
  eapply tie_card_NoDup in Htie; try done. rewrite size_dom in Hcap.
  lia.
Qed.
Lemma wp_insert p (v:val) (g:gset val) (x:val) :
  size g < cap p ->
  can_insert v x ->
  hashset p v g -∗
  run (htbl_add v x)
    (fun w => ⌜w=VUnit⌝ ∗ hashset p v ({[x]} ∪ g)).
Proof.
  iIntros (Hsize Hcan) "(%l&%h&%c&%M&%vs&(->&%Hp&%Hdom)&#Hh&#Hc&Hinner)".
  iApply (run_bind (CtxCall2 _)).
  iApply run_call; iApply run_code; iApply run_val.
  iApply run_call. simpl.
  iApply (run_bind (CtxLet _ _)).
  iApply run_mono. iApply run_fst. iIntros (?) "->".
  iApply run_let_val. simpl.
  iApply (run_bind (CtxLet _ _)).
  iApply (run_bind CtxFst).
  iApply run_mono. iApply run_snd. iIntros (?) "->". simpl.
  iApply run_mono. iApply run_fst. iIntros (?) "->". simpl.
  iApply run_let_val.
  iApply (run_bind (CtxLet _ _)).
  iApply (run_bind CtxFst). iApply (run_bind CtxSnd).
  iApply run_mono. iApply run_snd. iIntros (?) "->". simpl.
  iApply run_mono. iApply run_snd. iIntros (?) "->". simpl.
  iApply run_mono. iApply run_fst. iIntros (?) "->". simpl.
  iApply run_let_val.
  iApply (run_bind (CtxLet _ _)).
  iApply (run_bind CtxSnd). iApply (run_bind CtxSnd).
  iApply run_mono. iApply run_snd. iIntros (?) "->". simpl.
  iApply run_mono. iApply run_snd. iIntros (?) "->". simpl.
  iApply run_mono. iApply run_snd. iIntros (?) "->". simpl.
  iApply run_let_val. simpl.
  iApply (run_bind (CtxLet _ _)).
  iApply (run_mono with "[Hinner]"). iApply (length_hashset with "[$]").
  iIntros (?) "(->&Hinner)".
  iApply run_let_val. simpl.
  iApply (run_bind (CtxLet _ _)).
  iApply (run_bind (CtxCallPrim2 _ _)).
  iApply run_mono. iApply "Hh". iIntros (?) "->".
  iApply run_mono. iApply run_call_prim. done. iIntros (?) "->". simpl.
  iApply run_let_val. simpl.
  iDestruct (add_to_debt x with "[$]") as "Hinner".
  rewrite -Nat2Z.inj_mod.
  iAssert (⌜cap p = length vs /\ tie p M vs /\ hashset_inv_model p M vs⌝)%I as "(%Hlength&%&%)".
  { iDestruct "Hinner" as "(_&_&%X)". destruct X. eauto. }
  rewrite -Hlength.
  iApply (run_mono with "[-]").
  { iApply (hs_put_spec p c (hash p x) 0 _ _ _ _ _ x with "[]"); try done.
    { destruct Hcan as (?&?&?&?&E&?). simpl in E. inversion E. subst. done. }
    { subst. eauto using size_lt_not_full. }
    { rewrite rank_add_mod //.
      replace (hash p x `mod` cap p) with (probe p x 0).
      2:{ rewrite /probe right_id_L //. }
      rewrite rank_probe Nat.Div0.mod_0_l.
      intros ??. lia. }
    { intros ??. lia. }
    { rewrite right_id_L //. } }
  iIntros (?) "(->&(%&%&%&?))".
  iSplitR; first done. iFrame "#∗".
  iPureIntro. split_and !; try done.
  set_solver.
Qed.

Lemma elems_spec p v g :
  hashset p v g -∗
  run (htbl_elems v) (fun w => ∃ l vs, ⌜w=VLoc l /\ deduped vs g⌝ ∗ pointsto l (DfracOwn 1) vs).
Proof.
  iIntros "Hv".
  iApply run_call. simpl.
  iDestruct "Hv" as "(%&%&%&%&%&(->&%&%)&?&?&Hl&?&%Hinv)".

  iApply (run_bind (CtxLet _ _)).
  iApply run_mono. iApply run_fst.
  iIntros (?) "->". iApply run_let_val. simpl.

  iApply (run_bind (CtxLet _ _)).
  iApply (run_bind CtxSnd).
  iApply (run_bind CtxSnd).
  iApply run_mono. iApply run_snd. iIntros (?) "->".
  iApply run_mono. iApply run_snd. iIntros (?) "->".
  iApply run_mono. iApply run_snd. iIntros (?) "->".
  simpl. iApply run_let_val. simpl.

  iApply (run_mono with "[Hl]").
  { iApply (filter_compact_spec with "[$]"). }

  iIntros (?) "(%r&->&?&?)".
  iFrame. iPureIntro. split; first done.
  eapply correct_result_dedup. rewrite -H1.
  eapply hashset_gives_correct_result. done.
Qed.

Lemma hstbl_alloc_spec (i:Z) c (h:val) (hash0:val -> nat) (cmp0:val -> val -> bool) :
  (0 < i)%Z ->
  TotalOrder cmp0 ->
  □ cmp_spec cmp0 c -∗
  □ hash_spec hash0 h -∗
  run (htbl_init h c i) (fun v => ∃ p, hashset p v ∅ ∗  ⌜cap p=Z.to_nat i⌝).
Proof.
  iIntros (??) "#X1 #X2".
  do 2 iApply (run_bind (CtxCall2 _)).
  do 2 (iApply run_call; iApply run_code; iApply run_val; simpl).
  iApply run_call. simpl.
  iApply (run_bind (CtxLet _ _)).
  iApply (run_bind CtxAssert).
  iApply run_mono. iApply run_call_prim. done.
  iIntros (? ->). simpl.
  iApply run_mono. iApply run_assert.
  { by apply Z.ltb_lt. }
  iIntros (? ->). iApply run_let_val. simpl.

  iApply (run_bind (CtxLet _ _)).
  iApply run_mono. iApply ref_spec.
  iIntros (?) "(%&->&?)". iApply run_let_val. simpl.

  iApply (run_bind (CtxLet _ _)).
  iApply run_mono. iApply run_alloc. lia.
  iIntros (a) "(%&->&Ha)". iApply run_let_val. simpl.

  iApply (run_bind (CtxLet _ _)).
  iApply (run_mono with "[Ha]").
  { iApply (run_fill with "Ha"). }

  iIntros (?) "(->&?)". iApply run_let_val. simpl.

  iApply (run_bind (CtxPair1 _)).
  iApply (run_bind (CtxPair1 _)).
  iApply run_mono. iApply run_pair. iIntros (? ->).
  iApply run_mono. iApply run_pair. iIntros (? ->).
  iApply run_mono. iApply run_pair. iIntros (? ->).

  iExists (mkp (Z.to_nat i) hash0 cmp0 l H1). simpl. iFrame. simpl.
  iSplitR; last done. iFrame "#".
  iPureIntro. exists ∅. split_and !. done. lia. done.
  rewrite replicate_length.
  assert (Z.to_nat i = cap (mkp (Z.to_nat i) hash0 cmp0 l H1)) as X. done.
  rewrite {2}X. eauto using hashtbl_invariant_init.
Qed.

End proof.
