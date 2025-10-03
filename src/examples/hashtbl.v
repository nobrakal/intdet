From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export cancelable_invariants.
From iris.algebra Require Import gmap gmultiset agree frac_auth gset.

From intdet.lang Require Import syntax syntax_instances notations head_semantics.
From intdet.utils Require Import elems big_opN more_maps_and_sets.
From intdet.musketeer Require Import wpapi.

From intdet.examples Require Import reference fill filter_compact tactics hashtbl_pure.

(* Adapted from https://dl.acm.org/doi/pdf/10.1145/2612669.2612687 *)

Definition prods xs x :=
  foldr Pair x xs.

Definition vprods xs x :=
  foldr VPair x xs.

Fixpoint proj_aux i x :=
  match i with
  | 0 => x
  | S i => Snd (proj_aux i x) end.

Definition proj n i x :=
  if (bool_decide (i=n))
  then proj_aux i x
  else Fst (proj_aux i x).

Definition htbl_init : val :=
  λ: "h" "c" "n",
    Assert (0 '< "n");;
    let: "d" := ref VUnit in
    let: "l" := Alloc "n" in
    fill "l" "d";;
    prods [Var "l"; Var "h"; Var "c"] "d".

Definition htbl_add_aux : val :=
  μ: "f" "c" "l" "d" "len" "v" "i",
    (* Let [x] be the current value at [i] *)
    let: "x" := "l".["i"] in
    (* If [v] is already inside, we stop *)
    if: "x" '== "v" then VUnit else
    (* If [x] is the dummy, we try to insert here *)
    if: "x" '== "d" then
      if: CAS "l" "i" "x" "v" then VUnit
      else
        "f" "c" "l" "d" "len" "v" "i"
    else
    (* We ask the cmp function to return its arguments for typing reasons *)
    let: "b" := "c" "x" "v" in
    let: "j" := (("i" '+ 1 ) 'mod "len") in
    (* If [x] has a lower priority than [v], we keep trying to insert [v] *)
    if: "b" then
      "f" "c" "l" "d" "len" "v" "j"
    else
    (* Else, we replace [x] by [v] and insert [x] *)
    if: CAS "l" "i" "x" "v" then
      "f" "c" "l" "d" "len" "x" "j"
    else
      "f" "c" "l" "d" "len" "v" "i".

Definition htbl_add : val :=
  λ: "a" "v",
    let: "l" := proj 3 0 "a" in
    let: "h" := proj 3 1 "a" in
    let: "c" := proj 3 2 "a" in
    let: "d" := proj 3 3 "a" in
    let: "len" := Length "l" in
    let: "i" := "h" "v" 'mod "len" in
    htbl_add_aux "c" "l" "d" "len" "v" "i".

Definition htbl_elems : val :=
  λ: "a",
    let: "l" := proj 3 0 "a" in
    let: "d" := proj 3 3 "a" in
    filter_compact "l" "d".

(******************************************************************************)
(* The cmras we need. *)

Local Canonical Structure valO := leibnizO val.
Class hashsetG Σ :=
  HashSetG {
      hashset_modelG : inG Σ (frac_authUR (gsetUR val));
      hashset_modelDG : inG Σ (frac_authUR (gmultisetUR val));
      hashset_elemsG  : inG Σ (authUR (gmapR nat (gsetUR val)));
      hashset_invG : cinvG Σ;
      typeg4 : inG Σ (agreeR (leibnizO params));
    }.

Definition hashsetΣ : gFunctors :=
  #[ GFunctor (frac_authUR (gsetUR val));
     GFunctor (frac_authUR (gmultisetUR val));
     GFunctor (authUR (gmapR nat (gsetUR val)));
     cinvΣ;
     GFunctor (agreeR (leibnizO params))
    ].

Global Instance subG_queuΣ {Σ} : subG hashsetΣ Σ → hashsetG Σ.
Proof. solve_inG. Qed.

Local Existing Instance hashset_modelG.
Local Existing Instance hashset_elemsG.
Local Existing Instance hashset_modelDG.
Local Existing Instance hashset_invG.
Local Existing Instance typeg4.

(******************************************************************************)
(* Parameters. *)

Record ghashset :=
  mk_ghs { gm:gname; (* model *)
           ge:gname; (* elements *)
           gd:gname; (* debt *)
           gc:gname; (* cancelable invariant *)
    }.

Global Instance ghashset_eq_dec : EqDecision ghashset.
Proof. solve_decision. Qed.

Global Instance ghashset_countable : Countable ghashset.
Proof.
  apply inj_countable with
    (f:= fun x => (x.(gm),x.(ge), x.(gd), x.(gc)))
    (g:= fun '(x1,x2,x3,x4) => Some (mk_ghs x1 x2 x3 x4)).
  intros []; eauto.
Qed.

(******************************************************************************)
(* We are going to work with a total order *)

Section proof.

Context `{IsWP Σ pointsto wp}.
Context `{forall l q v, Timeless (pointsto l q v)}.
Context `{gen_heap.gen_heapGS loc (list val) Σ}.
Context `{hashsetG Σ}.
Context {N:namespace}.

(******************************************************************************)
(* Invariant. *)

(* The actual invariant *)
Definition hashset_inv (γ:ghashset) (p:params) (l:loc) : iProp Σ :=
  ∃ (M:gmap val nat) (D:gmultiset val) (vs:list val),
    (* The points-tos of l and the dummy *)
    pointsto l (DfracOwn 1) vs ∗ pointsto p.(dummy) (DfracOwn 1) [VUnit] ∗
    (* The authoritative content of the set (with missing elements in D). *)
    own γ.(gm) (●F (dom M ∪ dom D)) ∗
    (* The authoritative content of the "debt", ie. elements we
       promised to insert. *)
    own γ.(gd) (●F D) ∗
    (* Records that elements that were logically set are no dummies and
       that each index can only decrease in priority *)
    elems γ.(ge) (fun x => x ≠ (VLoc p.(dummy))) (flip p.(cmp)) vs ∗
    (* Each elements that is not a dummy was registered in [elems] *)
    ([∗ list] i ↦ v ∈ vs, ⌜v ≠ VLoc p.(dummy)⌝ -∗ elem_int γ.(ge) i v) ∗
    (* Pure invariants. *)
    ⌜hashtbl_invariant p (dom D) M vs⌝.

Local Definition invpatinner := ">(%M&%D&%vs&Hl&Hd&HM&HD&He&Hvs&%Hinv)".
Local Definition invpat := "(" +:+ invpatinner +:+ "&Hkey)".

Ltac open_inv I :=
  iInv "I" as invpat; only 1:( left; constructor);
  match goal with
  | [ Hinv : hashtbl_invariant _ _ _ _ |- _ ] =>
    destruct Hinv as [Hlength Htie Hmodel Hopt] end.

Definition content γ q (S:gset val) := own γ.(gm) (◯F{q} S).
Definition debt γ q (S:gmultiset val) := own γ.(gd) (◯F{q} S).

Definition nm_hashset := nroot.@"hashset".

Definition cmp_spec cmp (c:val) : iProp Σ :=
  □ (∀ (x y:val), wp ⊤ (c x y) (fun v => ⌜v = VBool (cmp x y)⌝)).

Definition hashset p v (q:Qp) (S:gset val) : iProp Σ :=
  ∃ l h c γ,
    ⌜v=vprods [VLoc l; h; c] (VLoc p.(dummy)) /\ p.(cap) ≠ 0⌝ ∗
    gen_heap.meta l N γ ∗ cmp_spec (cmp p) c ∗
    cinv nm_hashset γ.(gc) (hashset_inv γ p l) ∗ cinv_own γ.(gc) q ∗ content γ q S ∗ debt γ q ∅.

Lemma hashset_sep p v q1 q2 g1 g2 :
  hashset p v q1 g1 ∗ hashset p v q2 g2 ⊣⊢ hashset p v (q1+q2) (g1 ∪ g2).
Proof.
  iSplit.
  { iIntros "((%l&%h&%c&%γ&(%E&%)&#X1&#?&#?&K1&C1&D1)&(%&%&%&%&(->&%)&X2&_&_&K2&C2&D2))".
    simpl in E. inversion E. subst. clear E.
    iDestruct (gen_heap.meta_agree with "X1 X2") as "<-".
    iCombine "K1 K2" as "K".
    iCombine "C1 C2" as "C".
    iCombine "D1 D2" as "D".
    iFrame "#∗". iExists h. done. }
  { iIntros "(%l&%h&%c&%γ&(%E&%)&#X1&#?&#?&(K1&K2)&C&(D1&D2))".
    iFrame "#∗". replace  (g1 ∪ g2) with (g1 ⋅ g2) by done.
    unfold content. rewrite frac_auth_frag_op own_op.
    iDestruct "C" as "(?&?)".
    iFrame "#∗". iSplit; iExists h; done. }
Qed.

(* The SL counterpart of [before_full]. *)
Definition ibefore_full p γ x j : iProp Σ :=
  [∗ nat] i ∈ [0; j], ∃ v, elem_int γ.(ge) (probe p x i) v ∗ ⌜x ≠ v /\ p.(cmp) v x⌝.
Local Instance ibefore_full_persistent p l x j : Persistent (ibefore_full p l x j).
Proof. apply _. Qed.

Local Lemma wp_length γ p a q :
  cinv nm_hashset γ.(gc) (hashset_inv γ p a) -∗
  cinv_own γ.(gc) q -∗
  wp ⊤ (Length a) (fun v => ⌜v=p.(cap)⌝ ∗ cinv_own γ.(gc) q).
Proof.
  iIntros "I Hkey".
  open_inv "I".
  iApply (wp_mono with "[Hl]"). by iApply wp_length.
  iIntros (?) "(->&?)". rewrite Hlength. by iFrame.
Qed.

Lemma ibefore_full_use γ p (x:val) i' (vs:list val)  :
  ibefore_full p γ x i' -∗
  elems γ.(ge) (fun x => x ≠ VLoc p.(dummy)) (flip p.(cmp)) vs -∗
  ⌜before_full p vs i' x⌝.
Proof.
  iIntros "#X HE". iIntros (z Hz).
  iDestruct (big_sepN_elem_of_acc _ _ z with "[$]") as "([% (?&(%Heq&%))]&_)".
  { lia. }

  iDestruct (use_elem_int with "[$][$]") as "(%&%&%Hvi&%)".

  iPureIntro. exists v'. split_and !; try done.
  { by etrans. }
  { intros X. subst. eapply Heq. eauto using anti_symm_cmp. }
Qed.

Lemma before_full_confront (x:val) p i i' M (vs:list val) v0 :
  cap p ≠ 0 ->
  cap p = length vs ->
  i = probe p x i' ->
  hashset_inv_model p M vs ->
  vs !! i = Some v0 ->
  (v0 = VLoc p.(dummy) \/ (cmp p x v0 /\ x ≠ v0)) ->
  before_full p vs i' x ->
  x ∉ dom M.
Proof.
  intros ?? -> Hmap Hvs X Hfull Hdx.

  (* if x ∈ dom M, x is already in vs at index (j `mod` cap). *)
  apply elem_of_dom in Hdx. destruct Hdx as (j,Hj).
  apply Hmap in Hj. destruct Hj as (?&?&k&?&_&Hbef).
  destruct_decide (decide (i'=k)) as Eq.
  { subst. assert (v0 = x) by naive_solver. subst.
    destruct X as [ | (?&Hv)]; first done.
    apply Hv. eauto using anti_symm_cmp. }
  destruct (Nat.le_gt_cases i' k).
  { exfalso. destruct (Hbef i') as (?&?&?&?&Heq). lia.
    assert (x0=v0) as -> by naive_solver. eapply Heq.
    destruct X as [|(?&?)]. done. eauto using anti_symm_cmp. }
  destruct (Hfull k) as (?&?&?&?&?). lia.
  assert (x0=x) by naive_solver. subst.
  apply H14. eauto using anti_symm_cmp.
Qed.

Lemma generate_ibefore_full p γ vs i x :
  before_full p vs i x ->
  elems γ.(ge) (fun x => x ≠ (VLoc p.(dummy))) (flip p.(cmp)) vs ==∗
  elems γ.(ge) (fun x => x ≠ (VLoc p.(dummy))) (flip p.(cmp)) vs ∗ ibefore_full p γ x i.
Proof.
  iIntros (Hfull) "He".
  iInduction i as [] "IH" forall (Hfull).
  { iFrame. rewrite /ibefore_full.
    rewrite big_sepN_0 //. }
  { iMod ("IH" with "[%][$]") as "(He&?)".
    { intros ??. apply Hfull. lia. }
    destruct (Hfull i) as (v&Hv1&Hv2&Hv3&Hv4). lia.
    unshelve iMod (elems_insert v with "He") as "(?&#Hx)".
    { apply flip_PreOrder. apply _. }
    3:done. done.
    { naive_solver. }
    rewrite list_insert_id //. iFrame. iModIntro.
    rewrite /ibefore_full. rewrite big_sepN_snoc; last lia.
    iFrame "#∗". done. }
Qed.

Lemma gmultiset_dom_difference_1 `{Countable A} (X:gmultiset A) v :
  dom (X ∖ {[+v+]}) = if decide (v ∈ (X ∖ {[+v+]})) then dom X else dom X ∖ {[v]}.
Proof.
  apply set_eq. intros i.
  rewrite !gmultiset_elem_of_dom.
  case_decide as E.
  { rewrite gmultiset_elem_of_dom. multiset_solver. }
  { rewrite (elem_of_difference (dom X)) gmultiset_elem_of_dom.
    multiset_solver. }
Qed.

Local Lemma a_set_eq `{Countable A} (v x:A) (X:gset A) (D:gmultiset A) :
  x ∈ X ->
  v ∈ D ->
  {[v]} ∪ X ∖ {[x]} ∪ dom (D ∖ {[+ v +]} ⊎ {[+ x +]}) = X ∪ dom D.
Proof.
  intros.
  rewrite dom_disj_union dom_msingleton.
  rewrite (comm_L _ _ {[x]}) assoc_L -(assoc_L _ {[v]}).
  rewrite difference_union_L.
  replace (X ∪ {[x]}) with X by set_solver.
  assert (v ∈ dom D).
  { rewrite gmultiset_elem_of_dom. multiset_solver. }
  rewrite gmultiset_dom_difference_1.
  case_decide. set_solver.
  rewrite (comm_L _ _ (dom D ∖ {[v]})) assoc_L.
  rewrite difference_union_L. set_solver.
Qed.

Lemma before_full_weak p vs m n v :
  n <= m ->
  before_full p vs m v ->
  before_full p vs n v.
Proof.
  intros ? X. intros ??. apply X. lia.
Qed.

Lemma rank_le_diff p v i :
  hash p v <= i ->
  rank p v i ≤ i - hash p v.
Proof.
  intros. rewrite /rank.
  rewrite Z2Nat.inj_mod. 2,3:lia.
  rewrite !Z2Nat.inj_sub. 2:lia.
  rewrite !Nat2Z.id. apply Nat.Div0.mod_le.
Qed.

Lemma hs_put_spec p (c:val) γ a q (i i':nat) (v:val) :
  v ≠ VLoc p.(dummy) ->
  p.(cap) ≠ 0 ->
  i = i' mod p.(cap) ->
  p.(hash) v ≤ i' ->
  □ (∀ (x y:val), wp ⊤ (c x y) (fun v => ⌜v = VBool (p.(cmp) x y)⌝)) -∗
  cinv nm_hashset γ.(gc) (hashset_inv γ p a) -∗
  ibefore_full p γ v (i' - p.(hash) v) -∗
  cinv_own γ.(gc) q -∗
  debt γ q {[+v+]} -∗
  wp ⊤ (htbl_add_aux c a p.(dummy) (cap p) v i)
    (fun w => ⌜w=VUnit⌝ ∗ cinv_own γ.(gc) q ∗ debt γ q ∅).
Proof.
  iIntros (X1 X2 -> X3) "#Hc #I #Hfull Hkey Hf".
  iLöb as "IH" forall (i' v X1 X3) "Hfull".

  do 5 iApply (wp_bind (CtxCall2 _)).
  do 5 autocall.
  iApply wp_call; first done; iModIntro. simpl. fold htbl_add_aux.

  iApply (wp_bind (CtxLet _ _)).

  open_inv "I".

  assert (i' `mod` cap p < length vs).
  { rewrite Hlength. by apply Nat.mod_upper_bound. }
  assert (is_Some (vs !! (i' `mod` cap p))) as (x&Hx).
  { apply lookup_lt_is_Some_2. lia. }

  iApply (wp_mono with "[Hl]").
  { iApply (wp_load with "Hl").
    { lia. }
    { replace (Z.to_nat (i' `mod` cap p)%nat) with (i' `mod` cap p) by lia.
      rewrite Hx //. }  }

  iIntros (?) "(->&Hl)".

  (* Is v already in the set? *)
  simpl.
  destruct_decide (decide (x = v)) as Hveq.
  { subst.
    iMod (own_update_2 with "HD Hf") as "(?&Hf)".
    { apply frac_auth_update.
      apply gmultiset_local_update_dealloc. reflexivity. }
    replace (({[+ v +]} ∖ {[+ v +]})) with (∅:gmultiset val) by multiset_solver.
    iSplitR "Hf Hkey".
    { do 2 iModIntro. iExists M. iFrame.
      assert (dom M ∪ dom (D ∖ {[+ v +]}) = dom M ∪ dom D) as X.
      2:{ rewrite X. iFrame. iPureIntro. constructor; try done.
          rewrite X //. }
      eapply tie_in_dom in Hx; try done.
      rewrite gmultiset_dom_difference_1.
      case_decide; first done.
      (* ugly *)
      apply set_eq. intros v'.
      destruct_decide (decide (v'=v)); set_solver. }
    iModIntro. iApply wp_let_val.
    iApply (wp_bind (CtxIf _ _)).
    iApply wp_mono. iApply wp_call_prim. done.
    iIntros (?) "->". simpl.
    iApply wp_if. rewrite bool_decide_eq_true_2 //.
    iApply wp_val. set_solver. by iFrame. }

  iDestruct (big_sepL_lookup with "Hvs") as "#Hiv". done.
  assert (x ≠ (#(dummy p))%V -> exists i'', i' `mod` cap p = probe p x i'') as Hprobe.
  { intros U. apply (Htie _ _ Hx) in U.
    apply Hmodel in U. destruct U as (?&_&?&?&?). eauto. }

  iModIntro. iSplitR "Hf Hkey". by iFrame.
  clear dependent M D vs.
  iApply wp_let_val. simpl.
  iApply (wp_bind (CtxIf _ _)).
  iApply wp_mono. iApply wp_call_prim. done.
  iIntros (?) "->". simpl.
  iApply wp_if. rewrite bool_decide_eq_false_2 //.
  iApply (wp_bind (CtxIf _ _)).
  iApply wp_mono. iApply wp_call_prim. done.
  iIntros (?) "->". simpl.
  iApply wp_if.

  (* Is the current slot empty? *)
  destruct_decide (decide (x = (p.(dummy)))) as Heqxd.
  { subst. rewrite bool_decide_eq_true_2 //.
    iApply (wp_bind (CtxIf _ _)).
    open_inv "I".

    assert (i' `mod` cap p < length vs).
    { rewrite Hlength. by apply Nat.mod_upper_bound. }
    assert (is_Some (vs !! (i' `mod` cap p))) as (x'&Hx').
    { apply lookup_lt_is_Some_2. lia. }

    iApply (wp_mono with "[Hl]").
    { iApply (wp_cas with "Hl"). lia.
      { replace (Z.to_nat (i' `mod` cap p)%nat) with (i' `mod` cap p) by lia.
        rewrite Hx' //. } }
    iIntros (?) "(->&?)".

    (* Did the CAS succeed? *)
    case_bool_decide as Hdx'.
    { subst.
      iDestruct (ibefore_full_use with "[$][$]") as "%Hifull".
      eapply before_full_weak in Hifull. 2:by eapply rank_le_diff.

      iDestruct (own_valid_2 with "HD Hf") as "%Hv".
      apply frac_auth_included_total in Hv.
      rewrite gmultiset_included in Hv.
      (* We update models *)
      iMod (own_update_2 with "HD Hf") as "(?&Hf)".
      { apply frac_auth_update. apply gmultiset_local_update_dealloc.
        reflexivity. }
      replace (({[+ v +]} ∖ {[+ v +]})) with (∅:gmultiset val) by multiset_solver.
      iSplitR "Hf Hkey".
      2:{ simpl. iModIntro. iApply wp_if. iApply wp_val. done. by iFrame. }
      unshelve iMod (elems_insert v with "He") as "(?&#Hx)".
      { apply flip_PreOrder. apply _. }
      3:done. done.
      { naive_solver. }
      replace (Z.to_nat (i' `mod` cap p)%nat) with (i' `mod` cap p) by lia.
      assert (i' `mod` cap p = probe p v (rank p v i')) as X.
      { rewrite probe_rank //. }
      iExists (<[v:=(i' `mod` cap p)]>M),_,_. iFrame.

      assert (v ∈ dom D).
      { rewrite gmultiset_elem_of_dom. multiset_solver. }

      assert ({[v]} ∪ dom M ∪ dom (D ∖ {[+ v +]}) = dom M ∪ dom D) as HD.
      { rewrite gmultiset_dom_difference_1. case_decide. set_solver.
        rewrite (comm_L _ _ (dom D ∖ {[v]})) assoc_L.
        rewrite difference_union_L. set_solver. }
      rewrite dom_insert_L HD.

      iFrame "#∗". iModIntro. iSplitL.
      { iModIntro. iDestruct (big_sepL_insert_acc with "[$]") as "(_&X)". done.
        iApply "X". by iFrame "#". }
      iPureIntro. constructor.
      { rewrite insert_length //. }
      { eauto using tie_add1, before_full_confront. }
      { eauto using model_add1, rank_lt_cap. }
      { rewrite dom_insert_L.
        rewrite X HD.
        eapply opt_add1; eauto using rank_lt_cap, deduce_all_are_probe.
        rewrite -X //. set_solver. } }
    { iModIntro.
      iSplitR "Hf Hkey". by iFrame.
      iApply wp_if. iApply ("IH" with "[%][%//][$][$][$]"). done. } }

  rewrite bool_decide_eq_false_2 //.
  iApply (wp_bind (CtxLet _ _)).
  iApply wp_mono. iApply "Hc". iIntros (?) "->". iApply wp_let_val. simpl.

  simpl.
  iApply (wp_bind (CtxLet _ _)).
  iApply (wp_bind (CtxCallPrim2 _ _)).
  iApply wp_mono. iApply wp_call_prim. done. simpl. iIntros (?) "->".
  iApply wp_mono. iApply wp_call_prim. done. simpl. iIntros (?) "->".

  replace ((i' `mod` cap p)%nat + Z.of_nat 1%nat)%Z with (Z.of_nat (S (i' `mod` cap p))) by lia.
  replace (S (i' `mod` cap p) `mod` Z.of_nat (cap p))%Z with (Z.of_nat ((1 + (i' `mod` cap p)) `mod` cap p)).
  2:{ simpl. rewrite Nat2Z.inj_mod. lia. }
  rewrite Nat.Div0.add_mod_idemp_r.

  iApply wp_let_val. simpl.

  iApply wp_if.

  (* Is x <= v ? *)
  destruct_decide (decide (cmp p x v)) as Hvx.
  { rewrite (Is_true_true_1 _ Hvx).
    iApply ("IH" with "[%] [%] Hkey Hf [-]"). done. lia. iModIntro.
    rewrite /ibefore_full.
    replace (S i' - hash p v) with (S (i' - hash p v)) by lia.
    iApply big_opN_snoc. lia. iFrame "#".
    iExists _. iSplitR. rewrite probe_diff //. by iApply "Hiv". done. }

  (* We try to replace x by v *)

  rewrite (Is_true_false_1 _ Hvx).
  iApply (wp_bind (CtxIf _ _)).

  open_inv "I".

  assert (i' `mod` cap p < length vs).
  { rewrite Hlength. by apply Nat.mod_upper_bound. }
  assert (is_Some (vs !! (i' `mod` cap p))) as (x'&Hx').
  { apply lookup_lt_is_Some_2. lia. }

  iApply (wp_mono with "[Hl]").
  iApply (wp_cas with "Hl").
  { lia. }
  { replace (Z.to_nat (i' `mod` cap p)%nat) with (i' `mod` cap p) by lia.
    rewrite Hx' //. }
  iIntros (?) "(->&?)".

  case_bool_decide as Heqxx'.
  { iDestruct (own_valid_2 with "HD Hf") as "%HDv".
    apply frac_auth_included_total in HDv.
    rewrite gmultiset_included in HDv.
    iMod (own_update_2 with "HD Hf") as "(HD&Hf)".
    { apply frac_auth_update with (a' := D ∖ {[+ v+]} ⊎ {[+x+]}) (b':={[+x+]}).
      apply gmultiset_local_update. multiset_solver. }

    assert (cmp p v x).
    { subst.
      destruct (trichotomy (strict p.(cmp)) v x) as [ X | [ X | X ] ].
      { destruct X. done. }
      { done. }
      { destruct X. congruence. } }

    iDestruct (ibefore_full_use with "[$][$]") as "%Hifull".
    eapply before_full_weak in Hifull. 2:by eapply rank_le_diff.

    inversion Heqxx'. subst. clear H7.
    pose proof (Htie _ _ Hx' Heqxd) as Hx''.
    apply Hmodel in Hx''. destruct Hx'' as (_&_&j'&Heq'&_&Hfullj').

    (* Generate witnesses for the possible rec call. *)
    iMod (generate_ibefore_full _ _ _ j' x with "[$]") as "(He&#?)".
    done.

    unshelve iMod (elems_insert v with "He") as "(?&#Hx)".
    { apply flip_PreOrder. apply _. }
    3:done. 1,2:naive_solver.

    iSplitR "Hf Hkey".
    { replace (Z.to_nat (i' `mod` cap p)%nat) with (i' `mod` cap p) by lia.
      do 2 iModIntro.
      iExists (<[v:=_]>(delete x M)),(D ∖ {[+ v +]} ⊎ {[+ x +]}),(<[i' `mod` cap p:=v]> vs). iFrame.

      assert (x ∈ dom M) by (eapply tie_in_dom; naive_solver).
      assert (v ∈ D) by multiset_solver.

      rewrite dom_insert_L dom_delete_L a_set_eq //.

      iFrame.
      iSplitL "Hvs".
      { iDestruct (big_sepL_insert_acc with "[$]") as "(_&X)". done.
        iApply "X". by iFrame "#". }

      assert (i' `mod` cap p = probe p v (rank p v i')) as X.
      { rewrite probe_rank //. }

      assert (v ∉ dom M).
      { eapply before_full_confront; try done. naive_solver. }

      iPureIntro. constructor.
      { rewrite insert_length //. }
      { eauto using tie_add2. }
      { eauto using model_add2, rank_lt_cap. }
      { rewrite dom_insert_L dom_delete_L a_set_eq // X.
        eapply opt_add2; eauto using rank_lt_cap, deduce_all_are_probe.
        set_solver.
        rewrite probe_rank //. } }

    replace (S i' `mod` cap p) with (probe p x (S j')).
    2:{ rewrite /probe.
        replace (S i') with (i' + 1) by lia.
        rewrite -(Nat.Div0.add_mod_idemp_l i').
        rewrite Heq'.
        rewrite Nat.Div0.add_mod_idemp_l. f_equal. lia. }

    iModIntro. simpl. iApply wp_if.

    iApply ("IH" with "[%][%][$][$][]").
    { naive_solver. }
    { lia. }
    { iModIntro.
      replace ( (hash p x + S j' - hash p x)) with (S j') by lia.
      rewrite /ibefore_full.
      iApply big_opN_snoc. lia. iFrame "#".
      { iExists _. iSplitR. rewrite Heq'. done. iPureIntro. naive_solver. } } }
  { iModIntro. iSplitR "Hf Hkey". by iFrame "#∗".
    iApply wp_if. iApply ("IH" with "[%][%//][$][$][$]"). done. }
Qed.

Lemma add_to_debt x γ p q a X  :
  cinv nm_hashset γ.(gc) (hashset_inv γ p a) -∗
  cinv_own γ.(gc) q -∗
  own (gm γ) (◯F{q} X) -∗
  debt γ q ∅ ={⊤}=∗
  cinv_own γ.(gc) q ∗ own (gm γ) (◯F{q} ({[x]} ∪ X)) ∗ debt γ q {[+x+]} .
Proof.
  iIntros "I Hkey Hf1 Hf2".
  iInv "I" as invpat. destruct Hinv.
  iMod (own_update_2 with "HM Hf1") as "(?&Hf1)".
  { apply frac_auth_update with (a':=dom M ∪ ({[x]}) ∪ dom D) (b':={[x]} ∪ X).
    rewrite local_update_unital_discrete. intros ? _ E.
    split; first done. set_solver. }
  iMod (own_update_2 with "HD Hf2") as "(?&Hf2)".
  { apply frac_auth_update with (a':= {[+x+]} ⊎ D) (b':={[+x+]}).
    apply gmultiset_local_update. multiset_solver. }
  iSplitR "Hf1 Hf2 Hkey".
  { do 2 iModIntro. iFrame.
    rewrite dom_disj_union dom_msingleton -assoc_L. iFrame.
    iPureIntro. constructor; try done.
    destruct_decide (decide (x ∈ dom M)).
    { replace (dom M ∪ ({[x]} ∪ dom D)) with (dom M ∪ dom D) by set_solver.
      done. }
    { replace (dom M ∪ ({[x]} ∪ dom D)) with ( {[x]} ∪ (dom M ∪ dom D)) by set_solver.
      eauto using opt_add. } }
  by iFrame.
Qed.

Definition can_insert (v:val) (x:val) :=
  exists l h c d, v=vprods [l; h; c] d /\ x ≠ d.

Definition is_loc (v:val) :=
  match v with
  | VLoc _ => true
  | _ => false end.

Lemma deduce_can_insert1 p (v x:val) q X :
  ¬ is_loc x ->
  hashset p v q X -∗
  ⌜can_insert v x⌝.
Proof.
  iIntros (?) "(%&%&%&%&(->&_)&_)". iPureIntro.
  eexists _,_,_,_. split; first done. naive_solver.
Qed.

Lemma deduce_can_insert2 p (v:val) l q q' xs X :
  pointsto l q xs -∗
  hashset p v q' X ={↑nm_hashset}=∗
  ⌜can_insert v l⌝ ∗ pointsto l q xs ∗ hashset p v q' X.
Proof.
  iIntros "H (%&%&%&%&(->&%)&?&?&#I&?&?)".
  destruct_decide (decide (l=(dummy p))).
  { subst.
    iInv "I" as invpat.
    iDestruct (pointsto_valid (dummy p) with "H Hd") as "%Hv".
    exfalso. apply dfrac_valid_own_r in Hv.
    by apply irreflexivity in Hv. }
  { iFrame "#∗". iModIntro. iPureIntro.
    split_and !; try done. eexists _,_,_,_. split; first reflexivity.
    naive_solver. eexists. done. }
Qed.

Ltac wp_let GO :=
  iApply (wp_bind (CtxLet _ _));
  iApply wp_mono; first GO; iIntros (?) "->";
  iApply wp_let_val.

Ltac wp_bind K GO :=
  iApply (wp_bind K);
  iApply wp_mono; first GO; iIntros (?) "->";
  iApply wp_let_val.

Lemma wp_insert p (v:val) a h c (q:Qp) (X:gset val) (x:val) :
  v = vprods [VLoc a; h; c] (VLoc p.(dummy)) ->
  can_insert v x ->
  hashset p v q X -∗
  wp ⊤ (htbl_add_aux c a p.(dummy) (cap p) x (hash p x `mod` cap p))
    (fun w => ⌜w=VUnit⌝ ∗ hashset p v q ({[x]} ∪ X)).
Proof.
  iIntros (E Hcan) "Hv".

  iDestruct "Hv" as "(%&%&%&%γ&((%E'&%)&?&#Hc&#I&Hkey&?&?))".
  rewrite E' in E. simpl in E. inversion E. subst. clear E.

  iMod (add_to_debt x with "[$][$][$][$]") as "(Hkey&X1&X2)".
  iApply (wp_mono with "[X2 Hkey]").
  { iApply (hs_put_spec p c _ _ _ _ _ x with "[$][$][][$]"); try done.
    { destruct Hcan as (?&?&?&?&E&?). simpl in E. inversion E. subst. done. }
    { rewrite /ibefore_full big_sepN_0 //. lia. } }
  iIntros (?) "(->&?&?)". iSplitR; first done. iFrame "#∗".
  iExists h. by iFrame.
Qed.

Lemma hashset_create p (l:loc) h c :
  cap p ≠ 0 -> cmp_spec (cmp p) c -∗
  pointsto l (DfracOwn 1) (replicate (cap p) (VLoc p.(dummy))) -∗
  pointsto p.(dummy) (DfracOwn 1) [VUnit] -∗
  gen_heap.meta_token l (↑N) ={⊤}=∗
  hashset p (vprods [VLoc l; h; c] (VLoc p.(dummy))) 1 ∅.
Proof.
  iIntros (?) "#Hc Hl Hd Hm". unfold hashset, hashset_inv. simpl.
  iMod (own_alloc (●F (∅: gset val) ⋅ ◯F ∅)) as "[%γ1 (H1&H1')]".
  { apply frac_auth_valid. done. }
  iMod (own_alloc (●F (∅: gmultiset val) ⋅ ◯F ∅)) as "[%γ2 (H2&H2')]".
  { apply frac_auth_valid. done. }
  iMod elems_alloc as "[%γ3 H3]".

  iMod (cinv_alloc_strong (fun _ => True)) as "[%γ4 (_&Hkey&Hbuild)]".
  apply pred_infinite_True.

  iMod (gen_heap.meta_set _ _ (mk_ghs γ1 γ3 γ2 γ4) N with "[$]") as "#?".
  set_solver. iExists _,_. iFrame "#∗".
  iSplitR; first done.
  iApply "Hbuild". iModIntro. iExists ∅,∅,_. iFrame.
  rewrite !dom_empty_L dom_mempty left_id_L. iFrame.
  iSplitR.
  { iApply big_opN.big_sepL_replicate. iModIntro. iIntros. exfalso. congruence. }
  { eauto using hashtbl_invariant_init. }
Qed.

Lemma hashset_cancel p v S :
  hashset p v 1 S ={↑nm_hashset}=∗ ∃ (l:loc) h c d vs, ⌜v=vprods [VLoc l; h; c] d⌝ ∗  ⌜deterministic_support p S vs /\ deduped (filter_pure d vs) S /\  p.(hashtbl_pure.cap) ≠ 0⌝ ∗ pointsto l (DfracOwn 1) vs.
Proof.
  iIntros "(%l&%h&%c&%γ&((->&%)&?&#Hc&#I&Hkey&?&?))".
  iMod (cinv_cancel with "[$][$]") as invpatinner. reflexivity.
  iExists l,h,c,_.
  iFrame.

  iDestruct (own_valid_2 with "HD [$]") as "%HDv".
  apply frac_auth_agree, leibniz_equiv in HDv. subst.
  rewrite dom_mempty in Hinv.
  rewrite dom_mempty right_id_L.

  iDestruct (own_valid_2 with "HM [$]") as "%HMv".
  apply frac_auth_agree, leibniz_equiv in HMv. subst.

   iPureIntro. split_and !; first reflexivity.
  { unfold deterministic_support. eauto. }
  { eauto using hashset_gives_correct_result, correct_result_dedup. }
  { done. }
Qed.

End proof.

From intdet.musketeer Require Import wpg dwp lockstep.

Definition hash_spec `{intdetGS Σ} hash (h:val) : iProp Σ :=
  (∀ (x:val), triple ⊤ True%I (h x) (fun v (_:unit) => ⌜v=hash x⌝)).

Section vprop.

Context `{intdetGS Σ, hashsetG Σ}.

Definition vhashset_inner (p:params) (v:val) (q:Qp) (g:gset val) : vProp Σ :=
  MonPred (fun (b:bool) => @hashset _ _ (if b then pointstol else pointstor) (if b then wpl else wpr) _ _ _ _ (if b then nm_left else nm_right) p v q g) _.

Lemma vhashset_sep_inner p v q1 q2 g1 g2 :
  vhashset_inner p v q1 g1 ∗ vhashset_inner p v q2 g2 ⊣⊢ vhashset_inner p v (q1+q2) (g1 ∪ g2).
Proof.
  constructor. intros b. monPred.unseal. apply hashset_sep.
Qed.

Definition savedparams a (p:params) : iProp Σ :=
  (∃ γ, gen_heap.meta a nm_base γ ∗ @own _ _ typeg4 γ (to_agree p))%I.

Definition vhashset p v q g : vProp Σ :=
  (∃ a h c, ⌜v=vprods [VLoc a; h; c] (VLoc (dummy p))⌝ ∗ embed (savedparams a p) ∗ pick (□  hash_spec (hash p) h) True ∗ vhashset_inner p v q g)%I.

Lemma saved_params_confront a p1 p2 :
  savedparams a p1 -∗ savedparams a p2 -∗ ⌜p1 =p2⌝.
Proof.
  iIntros "(%&?&X1) (%&?&X2)".
  iDestruct (gen_heap.meta_agree with "[$][$]") as "->".
  iDestruct (own_valid_2 with "X1 X2") as "%Eq".
  rewrite to_agree_op_valid_L in Eq. done.
Qed.

Definition vhashset' v q g := (∃ p, vhashset p v q g)%I.

Lemma vhashset_sep' v q1 q2 g1 g2 :
  vhashset' v q1 g1 ∗ vhashset' v q2 g2 ⊣⊢ vhashset' v (q1+q2) (g1 ∪ g2).
Proof.
  iSplit.
  { iIntros "((%&(%&%&%&%E1&#X1&?&?))&(%&(%&%&%&%E2&#X2&_&?)))".
    rewrite E2 in E1. simpl in E1. inversion E1. subst.
    iDestruct (saved_params_confront with "X1 X2") as "->".
    iExists _,_,_,_. iSplitR; first done. iFrame "#∗".
    rewrite -vhashset_sep_inner //. iFrame. }
  { iIntros "(%&%&%&%&%E1&#?&#?&X)".
    rewrite -vhashset_sep_inner.
    iDestruct "X" as "(?&?)".
    iFrame "#∗". iSplit; eauto. }
Qed.

Lemma vhashset_cancel p v S :
  vhashset p v 1 S ={⊤}=∗ ∃ (l:loc) h c d vs, ⌜v=vprods [VLoc l; h; c] d⌝ ∗  ⌜deterministic_support p S vs /\ deduped (filter_pure d vs) S /\ p.(hashtbl_pure.cap) ≠ 0⌝ ∗ pointsto l (DfracOwn 1) vs.
Proof.
  iIntros "(%&%&%&_&_&_&X)". iRevert "X". iStopProof.
  constructor. iIntros (b) "_". rewrite vprop_at_fupd. monPred.unseal.
  iIntros "X".
  iMod (fupd_mask_subseteq _). shelve.
  iMod (hashset_cancel with "X") as "(%&%&%&%&%&?&?)". iFrame.
  destruct b; iFrame.
  Unshelve. set_solver. intros. destruct b; apply _.
Qed.

Local Lemma triple_set {A} p l P e Q :
  (triple ⊤ (embed (savedparams l p) ∗ P) e Q) -∗
  triple (A:=A) ⊤ (pick (gen_heap.meta_token l (↑nm_base)) True ∗ P) e Q.
Proof.
  iIntros "Hwp".
  rewrite !triple_eq. iIntros (?????) "X HPOST".
  unfold savedparams. monPred.unseal.
  iDestruct "X" as "(?&?)".

  iMod (@own_alloc _ _ typeg4 (to_agree p)) as "(%γ&#X)".
  constructor.
  iMod (gen_heap.meta_set _ _ γ with "[$]") as "#?". reflexivity.
  iSpecialize ("Hwp" $! C ks F Q1 Q2 with "[-HPOST][$]").
  { iFrame "#∗". }
  iApply (wpg.wpg_mono with "[$]").
  iIntros (?) "(%&?&Hwp)". iFrame. iIntros "((_&?)&?)".
  iApply "Hwp". iFrame "#∗".
Qed.

Lemma hstbl_alloc_spec (i:Z) c (h:val) (hash0:val -> nat) (cmp0:val -> val -> bool) :
  TotalOrder cmp0 ->
  (forall `{X:IsWP Σ pt wpx}, ⊢ @cmp_spec _ wpx cmp0 c) ->
  □ hash_spec hash0 h -∗
  triple ⊤ True%I (htbl_init h c i) (fun v (_:unit) => vhashset' v 1%Qp ∅).
Proof.
  iIntros (? Hc) "#Hh".

  iApply (triple_bind (CtxCall2 _)).
  { iApply (triple_bind (CtxCall2 _)).
    call1. call2. call3. fold seqfor.
    call1. call2. }
  call3. call1.

  iApply (triple_bind (CtxLet _ _)).
  { iApply (triple_bind CtxAssert _ _ _ _ _ _ (fun _ (_:unit) => ⌜0%nat < i⌝%Z%I)).
    iApply triple_call_prim. simpl.
    iIntros (? []).
    iApply (triple_use_pure_pre (v = (0%nat <? i))%Z).
    { iIntros "%E". inversion E. done. }
    iIntros "->".
    iApply triple_conseq. 3:iApply triple_assert. by iIntros.
    iIntros (? []) "(_&%X)". iPureIntro.
    inversion X. eapply (Z.ltb_lt 0%nat i) in H3. done. }

  iIntros (? []).

  iApply (triple_use_pure_pre ((0%nat < i))%Z).
  { reflexivity. }
  iIntros. iApply triple_let_val. simpl. clear v.

  iApply (triple_bind (CtxLet _ _)).
  iApply triple_conseq_pre.
  2:iApply triple_ref. by iIntros. iIntros (? []). simpl.

  iApply (triple_use_pure_pre (exists l, v = VLoc l)).
  { iIntros "(%&->&_)". eauto. }
  iIntros ((l&->)).
  iApply triple_conseq_pre.
  { iIntros "(%&%E&?&_)". inversion E. subst. iStopProof. reflexivity. }
  iApply triple_let_val. simpl.

  assert (exists n, i = Z.of_nat n /\ 0 < n) as (n&->&?).
  { exists (Z.to_nat i). split. lia. lia. }

  iApply triple_let_alloc. iIntros (l').

  iApply (triple_conseq_pre (pick _ _ ∗ _)).
  { iIntros "(?&?&?&?)". iFrame. rewrite left_id. iStopProof. reflexivity. }

  iApply (triple_set (mkp n hash0 cmp0 l _)).

  iApply (triple_conseq_pre (pointsto l' _ _ ∗ _)).
  { iIntros "(X&?&?&?)". iFrame. rewrite left_id. iStopProof. reflexivity. }

  iApply (triple_bind_frame (CtxLet _ _)).
  { iApply triple_fill. }
  iIntros (? []).
  iApply triple_let_val. simpl.

  rewrite -assoc.
  iApply triple_extract_pure_pre.
  iIntros "->".

  iApply (triple_bind (CtxPair1 _)).
  { iApply (triple_bind (CtxPair1 _)).
    iApply triple_pair'.
    iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
    iApply triple_pair'. }
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".

  iApply triple_pair.
  iApply triple_fupd.
  iApply triple_val.

  rewrite replicate_length //. iExists tt.
  (* iExists (mkp n hash0 cmp0 l _). *) simpl. monPred.unseal.
  iSplitR.
  all:iIntros "(X1&#X0&X2&X3)".
  { iMod (@hashset_create _ _ pointstol (@wpl Σ H) _ _ _ _ _ (mkp n hash0 cmp0 l _) _ h with "[][X1][X2][X3]") as "Hs"; simpl; try done.
    { lia.  }
    { iApply Hc. }
    { iModIntro. unfold vhashset', vhashset. monPred.unseal.
      iFrame "#∗". eauto. } }
  { iMod (@hashset_create _ _ pointstor (@wpr Σ H) _ _ _ _ _ (mkp n hash0 cmp0 l _) with "[][X1][X2][X3]"); simpl; try done.
    { lia. }
    { iApply Hc. }
    { iModIntro. unfold vhashset', vhashset. monPred.unseal.
      iFrame "#∗". eauto. } }
Qed.

Local Lemma triple_length_hs p (a:loc) b q X :
  ⊢ triple ⊤ (vhashset p (VPair a b) q X) (Length a) (fun v (_:unit) => ⌜v=cap p⌝ ∗ vhashset p (VPair a b) q X).
Proof.
  rewrite triple_eq.  iIntros (?????) "X HPOST".
  iApply wpg_binds.

  unfold vhashset, vhashset_inner. monPred.unseal.
  iDestruct "X" as "(%&%&%&%E&?&?&X)".
  iDestruct "X" as "(%&%&%&%&(%E'&%)&?&?&#?&Hk&?&?)".
  inversion E. subst. simpl in E'. inversion E'. subst. clear E E'.
  iApply (wpg_mono with "[Hk]").
  by iApply (@wp_length _ _ _ _ IsWP_wpl with "[$]").
  iIntros (?) "(%&?)". subst.
  iSpecialize ("HPOST" $! _ tt with "[-]").
  { iSplitR; first done. iFrame "#∗". eauto 10. }
  iApply (wpg_mono with "[$]").
  iIntros (?) "[% (HF&HP)]". iFrame.
  iIntros "(X&?)". iApply wpr_binds.
  iDestruct "X" as "(%&%&%&%E&?&?&X)".
  iDestruct "X" as "(%&%&%&%&(%E'&%)&?&?&#?&Hk&?&?)".
  inversion E. subst. simpl in E'. inversion E'. subst. clear E E'.
  iApply (wpr_mono with "[Hk]").
  { by iApply (@wp_length _ _ _ _ IsWP_wpr with "[$]"). }
  iIntros (?) "(->&?)".
  iApply "HP". iFrame "#∗".
  iSplitR; first done.
  eauto 15.
Qed.

Local Lemma triple_hash p (a:loc) h b q g (x:val) :
  ⊢ triple ⊤ (vhashset p (VPair #a (VPair h b)) q g) (h x) (fun v (_:unit) => ⌜v=hash p x⌝ ∗ vhashset p (VPair #a (VPair h b)) q g).
Proof.
  rewrite triple_eq. iIntros (?????) "X HPOST".
  unfold vhashset, vhashset_inner. monPred.unseal.
  iDestruct "X" as "(%&%&%&%E&#Hs&#Hh&X)".
  simpl in E. inversion E. subst.
  iDestruct ("Hh" $! x) as "Hx".
  rewrite triple_eq. simpl.

  iSpecialize ("Hx" $! C ks ((∃ (x3 : loc) (x4 x5 : val),
          ⌜VPair #x0 (VPair x1 (VPair x2 #(dummy p))) =
           VPair #x3 (VPair x4 (VPair x5 #(dummy p)))⌝ ∗ True ∗
          hashset p (VPair #x0 (VPair x1 (VPair x2 #(dummy p)))) q g) ∗ F)%I Q1 Q2 with "[][-]"). monPred.unseal. done.
  2:{ iApply (wpg.wpg_mono with "[$]").
      iIntros (?) "(%&?&HP)". iFrame. iIntros "((%&%&%&%E'&?&?&?)&?)".
      inversion E'. subst.
      iApply "HP". monPred.unseal. iFrame. eauto. }
  monPred.unseal. iIntros (? []) "->".
  iSpecialize ("HPOST" $! (hash p x) tt with "[-]"); last first.
  { iApply (wpg.wpg_mono with "[$]").
    iIntros (?) "(%&?&HP)". iFrame. iIntros "(_&(%&%&%&%E'&?)&?)".
    iApply "HP". inversion E'. subst. unfold savedparams in *.
    iFrame "#∗". eauto. }
  iSplitR; first done. iFrame "#∗". eauto.
Qed.

Lemma triple_insert (v:val) (q:Qp) (X:gset val) (x:val) :
  can_insert v x ->
  ⊢ triple ⊤ (vhashset' v q X) (htbl_add v x) (fun w (_:unit) => ⌜w=VUnit⌝ ∗ vhashset' v q ({[x]} ∪ X)).
Proof.
  iIntros.

  iApply (triple_bind (CtxCall2 _)).
  call1. call2. call3. call1.

  iApply triple_extrude_existential.
  { iIntros (p). unfold vhashset. monPred.unseal.
    iIntros "(%&%&%&%E&#X1&_)". iModIntro.
    iIntros (p'). iIntros "(%&%&%&%E'&#X2&_)".
    rewrite E in E'. inversion E'. subst.
    iApply (saved_params_confront with "X1 X2"). }
  iIntros (p).

  iApply (triple_use_pure_pre (exists a h c, v=vprods [VLoc a; h; c] (VLoc (dummy p)))).
  { iIntros "(%&%&%&->&_)". eauto. }
  iIntros "(%a&%h&%c&->)". simpl.

  iApply (triple_bind (CtxLet _ _)).
  iApply triple_fst'.
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_let_val. simpl.

  iApply (triple_bind (CtxLet _ _)).
  iApply (triple_bind CtxFst).
  iApply triple_snd'.
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_fst'.
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_let_val. simpl.

  iApply (triple_bind (CtxLet _ _)).
  iApply (triple_bind CtxFst).
  iApply (triple_bind CtxSnd).
  iApply triple_snd'.
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_snd'.
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_fst'.
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_let_val. simpl.

  iApply (triple_bind (CtxLet _ _)).
  iApply (triple_bind CtxSnd).
  iApply (triple_bind CtxSnd).
  iApply triple_snd'.
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_snd'.
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_snd'.
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_let_val. simpl.

  iApply (triple_bind (CtxLet _ _)).
  iApply triple_length_hs.
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_let_val. simpl.

  iApply (triple_bind (CtxLet _ _)).
  iApply (triple_bind (CtxCallPrim2 _ _)).
  { iApply triple_hash. }
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_call_prim'. done.

  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_let_val. simpl.

  rewrite -Nat2Z.inj_mod.

  rewrite triple_eq. iIntros (?????) "X HPOST".
  iApply wpg_binds.

  unfold vhashset', vhashset, vhashset_inner. monPred.unseal.
  iDestruct "X" as "(%&%&%&%E&#?&#?&X)".
  inversion E. subst. clear E.

  iApply (wpg_mono with "[-HPOST]").
  { by iApply (@wp_insert _ _ _ _ IsWP_wpl with "[$]"). }
  iIntros (?) "(->&?)". iSpecialize ("HPOST" $! VUnit tt with "[-]").
  { iFrame "#∗". eauto 10. }
  iApply (wpg_mono with "[$]").
  iIntros (?) "[% (?&HP)]". iFrame.
  iIntros "(X&?)". iApply wpr_binds.

  iDestruct "X" as "(%&%&%&%E&_&_&X)".
  inversion E. subst. clear E.
  iApply (wpr_mono with "[X]").
  { by iApply (@wp_insert _ _ _ _ IsWP_wpr with "[$]"). }
  iIntros (?) "(->&?)".
  iApply "HP". iFrame "#∗". eauto.
Qed.

Lemma triple_elems v S :
  ⊢ triple ⊤ (vhashset' v 1%Qp S) (htbl_elems v) (fun w (vs:list val) => ∃ l, ⌜w=VLoc l /\ deduped vs S⌝ ∗ pointsto l (DfracOwn 1) vs).
Proof.
  iIntros.

  iApply triple_extrude_existential.
  { iIntros (p). unfold vhashset. monPred.unseal.
    iIntros "(%&%&%&%E&#X1&_)". iModIntro.
    iIntros (p'). iIntros "(%&%&%&%E'&#X2&_)".
    rewrite E in E'. inversion E'. subst.
    iApply (saved_params_confront with "X1 X2"). }
  iIntros (p).

  iApply triple_conseq_pre.
  iApply vhashset_cancel.
  iApply triple_fupd_pre.

  iApply (triple_use_pure_pre (∃ l h c d vs, v = vprods [(#l)%V; h; c] d /\ deterministic_support p S vs ∧ deduped (filter_pure d vs) S ∧ hashtbl_pure.cap p ≠ 0)).
  { iIntros "(%&%&%&%&%&%&(%&%&%)&_)". eauto 10. }
  iIntros ((l&h&c&d&vs&->&Hdet&Hdedup&Hcap)).

  iApply (triple_conseq_pre (pointsto l (DfracOwn 1) vs)).
  { iIntros "(%&%&%&%&%vs'&%E1&(%&%)&?)". simpl in E1.
    inversion E1. subst.
    replace vs' with vs by eauto using use_deterministic_support.
    iFrame. }

  iApply triple_call'. done. iModIntro. simpl.

  iApply (triple_bind (CtxLet _ _)).
  iApply triple_fst'.
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_let_val. simpl.

  iApply (triple_bind (CtxLet _ _)).
  iApply (triple_bind CtxSnd).
  iApply (triple_bind CtxSnd).
  iApply triple_snd'.
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_snd'.
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_snd'.
  iIntros (? []). iApply triple_extract_pure_pre. iIntros "->".
  iApply triple_let_val. simpl.

  iApply (triple_resolve (filter_pure d vs)).
  iApply triple_conseq_post.
  2:iApply filter_compact_spec.

  iIntros (? []). iIntros "(%&->&?&?)".
  by iFrame.
Qed.

Lemma vdeduce_can_insert1 (v x:val) q X :
  ¬ is_loc x ->
  vhashset' v q X ⊢
  ⌜can_insert v x⌝.
Proof.
  intros. constructor. intros b. simpl. rewrite monPred_at_pure.
  unfold vhashset', vhashset. monPred.unseal. iIntros "(%&%&%&%&->&_&_&?)".
  by iApply deduce_can_insert1.
Qed.
End vprop.
