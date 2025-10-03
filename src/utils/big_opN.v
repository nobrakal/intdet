From Coq.ssr Require Import ssreflect.
From stdpp Require Import base list numbers.

Definition range (n m:nat) : list nat := seq n (m-n).

Lemma lookup_range n m i :
  n <= m ->
  i < (m-n) ->
  range n m !! i = Some (n + i).
Proof.
  intros. rewrite /range.
  destruct (nth_lookup_or_length (seq n (m - n)) i 0) as [->|Hnth].
  2:{ rewrite seq_length in Hnth. lia. }
  f_equal. rewrite seq_nth; lia.
Qed.

Lemma lookup_range_lt_Some n  m i e :
  range n m !! i = Some e ->
  i < (m - n).
Proof.
  rewrite /range =>HE.
  apply lookup_lt_Some in HE.
  rewrite seq_length in HE. eauto.
Qed.

Lemma lookup_range_inv n m i j :
  range n m !! i = Some j ->
  j = (n + i).
Proof.
  intros E.
  assert (i < (m - n)) by eauto using lookup_range_lt_Some.
  destruct_decide (decide (n ≤ m)); try lia.
  rewrite lookup_range // in E. naive_solver.
Qed.

Lemma elem_of_range i n m :
  i ∈ range n m ->
  n <= i < m.
Proof.
  rewrite elem_of_list_lookup.
  intros (j,Hj).
  assert (j < (m - n)) by eauto using lookup_range_lt_Some.
  apply lookup_range_inv in Hj. subst. lia.
Qed.

Lemma NoDup_range n m :
  NoDup (range n m).
Proof. apply NoDup_ListNoDup. apply seq_NoDup. Qed.

Lemma length_range n m :
  length (range n m) = (m - n).
Proof. apply seq_length. Qed.

Lemma range_zero n m : m <= n -> range n m = nil.
Proof.
  rewrite -(Nat.sub_0_le m n) /range.
  intros ->. easy.
Qed.

Lemma range_S n m :
  n < m ->
  range n m = n::range (S n) m.
Proof.
  intros. rewrite /range.
  destruct m. lia.
  replace (S m - n) with (S (m - n)) by lia.
  apply cons_seq.
Qed.

Lemma range_app n1 n2 n3 :
  n1 <= n2 <= n3 ->
  range n1 n3 = range n1 n2 ++ range n2 n3.
Proof.
  intros. rewrite /range.
  replace (n3-n1) with ((n2-n1) + (n3-n2)) by lia.
  rewrite seq_app. f_equal. f_equal. lia.
Qed.

From iris.bi.lib Require Import fractional.
From iris.algebra Require Import big_op.
Local Existing Instances monoid_ne monoid_assoc monoid_comm
  monoid_left_id monoid_right_id monoid_proper
  monoid_homomorphism_rel_po monoid_homomorphism_rel_proper
  monoid_homomorphism_op_proper
  monoid_homomorphism_ne weak_monoid_homomorphism_proper.

Definition big_opN {M:ofe} {o:M → M → M} `{!Monoid o} (f:nat → M) (n m:nat) : M :=
  big_opL o (fun _ => f) (range n m).

Lemma big_opN_eq {M:ofe} {o:M → M → M} `{!Monoid o} (f:nat → M) (n m:nat) :
  big_opN f n m = big_opL o (fun _ => f) (range n m).
Proof. reflexivity. Qed.
Global Instance: Params (@big_opN) 3 := {}.
Global Arguments big_opN {M} o {_} _ !_ /.

Section big_opN.
Context {M : ofe} {o : M → M → M} `{!Monoid o}.
Infix "`o`" := o (at level 50, left associativity).
Implicit Types n m: nat.
Implicit Types f : nat -> M.

Lemma big_opN_0 f n m : m <= n -> big_opN o f n m = monoid_unit.
Proof. intros. rewrite /big_opN range_zero //. Qed.

Lemma big_opN_S f n m :
  n < m ->
  big_opN o f n m = f n `o` big_opN o f (S n) m.
Proof.
  intros.
  rewrite /big_opN range_S //.
Qed.

Lemma big_opN_add f n1 n2 n3 :
  n1 <= n2 <= n3 ->
  big_opN o f n1 n3 ≡ big_opN o f n1 n2 `o` big_opN o f n2 n3.
Proof.
  intros.
  rewrite /big_opN (range_app n1 n2 n3) // big_opL_app //.
Qed.

Lemma big_opN_snoc f n m :
  n <= m ->
  big_opN o f n (S m) ≡ big_opN o f n m `o` f m.
Proof.
  intros. rewrite (big_opN_add _ n m (S m)); last lia.
  rewrite (big_opN_S _ m (S m)); last lia.
  rewrite (big_opN_0 _ (S m)); last lia.
  rewrite assoc comm left_id //.
Qed.

Lemma big_opN_gen_proper R f g n m :
  Reflexive R →
  Proper (R ==> R ==> R) o →
  (∀ i, n <= i < m -> R (f i) (g i)) →
  R (big_opN o f n m) (big_opN o g n m).
Proof.
  intros ? ? HR. rewrite /big_opN. apply big_opL_gen_proper; eauto.
  intros ? ? Hk.
  pose proof (lookup_range_lt_Some _ _ _ _ Hk).
  rewrite lookup_range in Hk; eauto; try lia.
  apply HR. naive_solver lia.
Qed.

Lemma big_opN_proper f g n m :
  (∀ i, n <= i < m -> (f i) ≡ (g i)) →
  big_opN o f n m ≡ big_opN o g n m.
Proof.
  apply big_opN_gen_proper. apply _. apply monoid_proper.
Qed.

Lemma big_opN_ext f g n m :
  (∀ i, n <= i < m -> (f i) = (g i)) ->
  big_opN o f n m = big_opN o g n m.
Proof.
  apply big_opN_gen_proper; try easy.
  intros ? ? ->. naive_solver.
Qed.

Global Instance big_opN_proper' :
  Proper (pointwise_relation nat (≡) ==> (=) ==> (=) ==> (≡))
    (big_opN o).
Proof. intros f f' Hf ? ? -> ? ? ->. apply big_opN_proper. intros. apply Hf. Qed.

Lemma big_opN_op f g n m :
  big_opN o (fun x => f x `o` g x) n m
    ≡  big_opN o f n m `o` big_opN o g n m.
Proof.
  induction m.
  { rewrite /big_opN. rewrite range_zero. 2:lia. simpl. rewrite left_id. easy. }
  destruct_decide (decide (n ≤ m)).
  { rewrite !big_opN_snoc // IHm. rewrite !assoc.
    apply monoid_proper. 2:easy.
    rewrite -!assoc. apply monoid_proper. easy.
    apply comm. apply _. }
  { rewrite /big_opN. rewrite range_zero. 2:lia. simpl. rewrite left_id. easy. }
Qed.

Lemma big_opN_reindex_sub f n m i :
  i <= n <= m ->
  big_opN o f n m ≡ big_opN o (fun x => f (x+i)) (n-i) (m-i).
Proof.
  intros. induction m.
  { rewrite big_opN_0 //. lia. }
  destruct_decide (decide (n<=m)).
  2:{ rewrite !big_opN_0 //; lia. }
  rewrite big_opN_snoc //.
  rewrite Nat.sub_succ_l; last lia.
  rewrite big_opN_snoc //; last lia.
  f_equiv.
  { rewrite IHm //; last lia. }
  f_equiv. apply leibniz_equiv_iff. lia.
Qed.

Lemma big_opN_factorize_gen f n m p r :
  n <= m ->
  (m-n) = r*p ->
  big_opN o f n m ≡ big_opN o (fun i => big_opN o f (n+p*i) (n+p*(i+1))) 0 r.
Proof.
  revert m n.
  induction r; intros m n Hmn1 Hmn2.
  { rewrite !big_opN_0 //; try lia. }
  rewrite big_opN_snoc; last lia.
  rewrite Nat.mul_succ_l in Hmn2.
  rewrite (big_opN_add _ n (m-p) m); last lia. f_equiv.
  { rewrite IHr //; lia. }
  { f_equiv; apply leibniz_equiv_iff; lia. }
Qed.

Lemma big_opN_factorize f m p r :
  m = r*p ->
  big_opN o f 0 m ≡ big_opN o (fun i => big_opN o f (p*i) (p*(i+1))) 0 r.
Proof.
  intros.
  rewrite (big_opN_factorize_gen _ 0 m p r) //; lia.
Qed.

Lemma big_opN_factorize' f m p r q :
  m = r*p + q ->
  big_opN o f 0 m ≡ big_opN o (fun i => big_opN o f (p*i) (p*(i+1))) 0 r `o` big_opN o f (r*p) m.
Proof.
 intros.
  rewrite (big_opN_add _ 0 (r*p) m); last lia.
  rewrite big_opN_factorize //.
Qed.

Lemma big_opN_factorize'' f m r :
  big_opN o f 0 m ≡ big_opN o (fun i => if decide (i=r) then big_opN o f (r*(m / r)) m else big_opN o f ((m/r)*i) ((m/r)*(i+1))) 0 (S r).
Proof.
 intros.
  rewrite (big_opN_factorize' f m).
  2:{ apply (Nat.div_mod_eq m r). }
  rewrite big_opN_snoc; last lia.
  f_equiv.
  { apply big_opN_proper. intros. rewrite decide_False //; last lia.  }
  rewrite decide_True //.
Qed.

End big_opN.

From iris.proofmode Require Import proofmode.
From iris.bi Require Import derived_laws_later.
From iris.prelude Require Import options.
Import interface.bi derived_laws.bi derived_laws_later.bi.
From iris.bi Require Import big_op.

Notation "'[∗' 'nat]' i ∈ '[' n ; m ']' , P" :=
  (big_opN bi_sep (λ i, P%I) n m) (at level 200, i at level 1, n,m at level 10, right associativity) : bi_scope.

Section big_sepN.
Context {PROP : bi}.
Implicit Types P Q : PROP.
Implicit Types Φ Ψ : nat → PROP.

Global Instance big_sepN_persistent Φ n m :
  (forall i, Persistent (Φ i)) ->
  Persistent ([∗ nat] i ∈ [n;m], Φ i).
Proof. apply _. Qed.

Global Instance big_sepN_timeless Φ n m :
  Timeless (emp%I : PROP) ->
  (forall i, Timeless (Φ i)) ->
  Timeless ([∗ nat] i ∈ [n;m], Φ i).
Proof. apply _.  Qed.

Lemma big_sepN_0 n m Φ :
  m <= n ->
  ([∗ nat] i ∈ [ n ; m ], Φ i) ⊣⊢ emp.
Proof. intros. rewrite big_opN_0 //. Qed.

Lemma big_sepN_S n m Φ :
  n < m ->
  ([∗ nat] i ∈ [ n ; m ], Φ i) ⊣⊢ Φ n ∗ ([∗ nat] i ∈ [ S n ; m ], Φ i).
Proof. intros. by rewrite big_opN_S. Qed.

Lemma big_sepN_add n2 n1 n3 Φ :
  n1 <= n2 <= n3 ->
  ([∗ nat] i ∈ [ n1 ; n3 ], Φ i)
  ⊣⊢ ([∗ nat] i ∈ [ n1 ; n2 ], Φ i) ∗ ([∗ nat] i ∈ [ n2 ; n3 ], Φ i).
Proof. intros. by rewrite big_opN_add. Qed.

Lemma big_sepN_snoc n m Φ :
  n <= m ->
  ([∗ nat] i ∈ [ n ; S m ], Φ i) ⊣⊢ ([∗ nat] i ∈ [ n ; m ], Φ i) ∗ Φ m.
Proof. intros.  by rewrite big_opN_snoc. Qed.

Lemma big_sepN_mono Φ Ψ n m :
  (∀ i, n <= i < m ->  Φ i ⊢ Ψ i) →
  ([∗ nat] i ∈ [ n ; m ], Φ i) ⊢ ([∗ nat] i ∈ [ n ; m ], Ψ i).
Proof. apply big_opN_gen_proper; apply _. Qed.

Lemma big_sepN_proper Φ Ψ n m :
  (∀ i, n <= i < m ->  Φ i ⊣⊢ Ψ i) →
  ([∗ nat] i ∈ [ n ; m ], Φ i) ⊣⊢ ([∗ nat] i ∈ [ n ; m ], Ψ i).
Proof. apply big_opN_proper. Qed.

Lemma big_sepN_intro Φ n m :
  □ (∀ i, ⌜n <= i < m⌝ → Φ i) ⊢ ([∗ nat] i ∈ [ n ; m ], Φ i).
Proof.
  revert Φ. induction m; intros Φ.
  { rewrite intuitionistically_elim_emp (big_sepN_0 n) //. lia. }
  { iIntros "#H". destruct_decide (decide (n <= m)).
    { rewrite big_opN_snoc; last lia. iSplitL.
      { iApply IHm. iModIntro. iIntros. iApply "H". iPureIntro. lia. }
      { iApply "H". iPureIntro. lia. } }
    { rewrite big_sepN_0 //. lia. } }
Qed.

Lemma big_sepN_sep Φ Ψ n m :
  ([∗ nat] i ∈ [ n ; m ], Φ i ∗ Ψ i) ⊣⊢
  ([∗ nat] i ∈ [ n ; m ], Φ i) ∗ ([∗ nat] i ∈ [ n ; m ], Ψ i).
Proof. apply big_opN_op. Qed.

Lemma big_sepN_impl Φ Ψ n m :
  ([∗ nat] i ∈ [ n ; m ], Φ i) -∗
  □ (∀ i, ⌜n <= i < m⌝ → Φ i -∗ Ψ i) -∗
  ([∗ nat] i ∈ [ n ; m ], Ψ i).
Proof.
  apply wand_intro_l. rewrite big_sepN_intro //.
  iIntros "(?&?) ?".
  iDestruct (big_sepN_sep with "[$]") as "?".
  iApply (big_sepN_mono with "[$]"). iIntros (? ?) "(H1&?)".
  iApply "H1". iFrame.
Qed.

Lemma big_sepL_sepN n m Φ:
  ([∗ list] i ∈ range n m, Φ i)%I ⊣⊢ ([∗ nat] i ∈ [n; m], Φ i)%I.
Proof. easy. Qed.

Lemma big_sepN_elem_of_acc Φ n i m :
  n <= i < m ->
  ([∗ nat] j ∈ [n; m], Φ j)%I ⊢ Φ i ∗ (Φ i -∗ ([∗ nat] j ∈ [n; m], Φ j)%I).
Proof.
  iIntros (?) "H".
  rewrite (big_sepN_add i); last lia.
  rewrite (big_sepN_add (S i) i); last lia.
  rewrite (big_sepN_S i (S i)); last lia.
  iDestruct "H" as "(?&(?&?)&?)". iFrame. iIntros. iFrame.
Qed.

Lemma big_sepN_pure `{BiAffine PROP} n m (P:nat -> Prop) :
  ([∗ nat] i ∈ [n;m], ⌜P i⌝) ⊣⊢@{PROP} ⌜∀ i, n <= i < m → P i⌝.
Proof.
  rewrite /big_opN big_sepL_pure. f_equiv.
  split; intros HP.
  { intros. apply HP with (k:=i-n). rewrite lookup_range; try lia. f_equiv. lia. }
  { intros ?? Hk. generalize Hk. intros.
    apply lookup_range_inv in Hk; try lia.
    apply HP. apply elem_of_range. eauto using elem_of_list_lookup_2. }
Qed.

Lemma list_snoc_exists {A} (xs:list A) :
  length xs ≠ 0 ->
  exists y ys, xs = ys ++ [y].
Proof.
  intros.
  induction xs as [|y xs]; simpl in *; first lia.
  destruct xs as [|x xs].
  { exists y,nil. eauto. }
  destruct (IHxs) as (z,(zs,?)).
  { simpl. lia. }
  { exists z, (y::zs). rewrite H0. naive_solver. }
Qed.

Lemma big_sepN_exists `{Inhabited A} `{BiAffine PROP} (Φ : A -> nat -> PROP) n m :
  ([∗ nat] j ∈ [n; m], (∃ x, Φ x j))%I ⊣⊢ (∃ xs:list A, ⌜length xs = (m-n)⌝ ∗ ([∗ nat] j ∈ [n; m], (Φ (xs!!!(j-n)) j)))%I.
Proof.
  induction m.
  { rewrite big_sepN_0; last lia .
    iSplit.
    { iIntros "_". iExists nil. rewrite big_sepN_0 //. lia. }
    { iIntros "[% (_&?)]". rewrite big_sepN_0 //; last lia. } }
  destruct_decide (decide (n ≤ m)).
  2:{ rewrite big_sepN_0; last lia .
      iSplit.
      { iIntros "_". iExists nil. rewrite big_sepN_0 //; last lia.
        iPureIntro. simpl. split; lia. }
    { iIntros "[% (_&?)]". rewrite big_sepN_0 //; last lia. } }
  rewrite big_sepN_snoc; last lia. rewrite IHm. clear IHm.
  iSplit.
  { iIntros "([%xs (%&?)]&[%x ?])".
    iExists (xs++[x]).
    iSplitR.
    { rewrite app_length. simpl. iPureIntro. lia. }
    iApply big_sepN_snoc; first lia.
    rewrite lookup_total_app_r; last lia.
    replace (m - n - length xs) with 0 by lia. simpl. iFrame.
    iApply (big_sepN_impl with "[$]"). iModIntro. iIntros.
    rewrite lookup_total_app_l; last lia. iFrame. }
  { iIntros "[% (%Hlength&E)]".
    destruct (list_snoc_exists xs) as (y,(ys,->)); first lia.
    rewrite big_sepN_snoc; last lia. iDestruct "E" as "(E1&?)".
    rewrite app_length in Hlength. simpl in *.
    iSplitL "E1".
    { iExists ys. iSplitR.
      { iPureIntro. lia. }
      iApply (big_sepN_impl with "[$]"). iModIntro. iIntros.
      rewrite lookup_total_app_l; last lia. iFrame. }
    iExists y. rewrite lookup_total_app_r; last lia. iFrame.
    replace (m - n - length ys) with 0 by lia. easy. }
Qed.

Lemma big_sepN_exists_from_zero `{Inhabited A} `{BiAffine PROP} (Φ : A -> nat -> PROP) n :
  ([∗ nat] j ∈ [0; n], (∃ x, Φ x j))%I ⊣⊢ (∃ xs:list A, ⌜length xs = n⌝ ∗ ([∗ nat] j ∈ [0; n], (Φ (xs!!!j)) j))%I.
Proof.
  rewrite big_sepN_exists. do 2 f_equiv. rewrite Nat.sub_0_r. do 3 f_equiv. rewrite Nat.sub_0_r //.
Qed.

Lemma big_sepN_factorize Φ m p r :
  m = r*p ->
  ([∗ nat] i ∈ [0; m], Φ i)%I ≡ ([∗ nat] i ∈ [0; r], ([∗ nat] j ∈ [(p*i); (p*(i+1))], Φ j))%I.
Proof. apply big_opN_factorize. Qed.

Definition nat_to_Qp (n:nat) : Qp := pos_to_Qp (Pos.of_nat n).

Lemma nat_to_Qp_succ n : n ≠ 0 -> nat_to_Qp (S n) = (1 + nat_to_Qp n)%Qp.
Proof.
  intros. rewrite /nat_to_Qp Nat2Pos.inj_succ //.
  rewrite Pplus_one_succ_l pos_to_Qp_add //.
Qed.

Lemma fractional_split_n_times (P:Qp -> PROP) n p :
  Fractional P ->
  n ≠ 0 ->
  (P p)%I ≡ ([∗ nat] _ ∈ [0; n], P (p/nat_to_Qp n)%Qp)%I.
Proof.
  intros ? Hn. remember (p/nat_to_Qp n)%Qp as p'.
  replace p with (nat_to_Qp n * p')%Qp.
  2:{ subst p'. rewrite Qp.mul_div_r //. } generalize p'. intros. clear Heqp' p'.
  induction n as [|n].
  { naive_solver. }
  destruct n.
  { replace (nat_to_Qp 1) with 1%Qp by compute_done. rewrite Qp.mul_1_l. simpl. rewrite right_id //. }
  { rewrite big_opN_snoc. 2:lia. rewrite -IHn. 2:lia.
    rewrite nat_to_Qp_succ //. rewrite Qp.mul_add_distr_r Qp.mul_1_l.
    rewrite fractional.
    iSplit; iIntros "(?&?)"; iFrame. }
Qed.

Lemma big_sepN_to_list `{Inhabited A} (P :A -> PROP) xs n :
  length xs = n ->
  ([∗ nat] i ∈ [0; n], P (xs !!! i)) -∗ [∗ list] x ∈ xs, P x.
Proof.
  iIntros (Hxs).
  iInduction xs as [|] "IH" using List.rev_ind forall (n Hxs).
  { destruct n; try done. rewrite big_sepN_0 // big_sepL_nil. eauto. }
  { rewrite app_length in Hxs. destruct n.
    { simpl in Hxs; lia. }
    rewrite big_sepN_snoc; last lia. iIntros "(?&?)".
    iApply big_sepL_snoc. simpl in *. rewrite lookup_total_app_r; last lia.
    replace (length xs) with n by lia. rewrite Nat.sub_diag. iFrame.
    iApply "IH". { iModIntro. eauto. }
    iApply (big_sepN_impl with "[$]"). iModIntro. iIntros.
    rewrite lookup_total_app_l //. lia. }
Qed.

Lemma big_sepL_replicate `{BiAffine PROP} {A} (P:nat -> A -> PROP) n x :
  □ (∀ i, ⌜i<n⌝ -∗ P i x) -∗
  [∗ list] i ↦ x ∈ replicate n x, P i x.
Proof.
  iIntros "#X". iInduction n as [] "IH" forall (P); first done.
  rewrite replicate_S big_sepL_cons. iSplitR.
  { iApply "X". iPureIntro. lia. }
  { iApply "IH".
    iModIntro. iIntros (??). iApply "X". iPureIntro. lia. }
Qed.

Lemma big_sepN_add_bounds n m k (P:nat -> PROP) :
  ([∗ nat] i ∈ [n;m], P i) ⊣⊢ [∗ nat] i ∈ [n + k; m + k], P (i - k)%I.
Proof.
  intros. induction m.
  { rewrite !big_sepN_0 //; lia. }
  { destruct_decide (decide (n ≤ m)).
    { replace (S m + k) with (S (m + k)) by lia.
      rewrite !big_sepN_snoc; try lia. f_equiv.
      { apply IHm. }
      { f_equiv. assert (m + k - k = m) as -> by lia. done. } }
    { rewrite !big_sepN_0 //; lia. } }
Qed.

End big_sepN.

Definition big_sepZ `{PROP : bi} (P:Z -> PROP) (n m:Z) :=
  big_opN bi_sep (fun i => P (n+i)%Z) 0 (Z.to_nat (m - n)).

Notation "'[∗' 'Z]' i ∈ '[' n ; m ']' , P" :=
  (big_sepZ (λ i, P%I) n m) (at level 200, i at level 1, n,m at level 10, right associativity) : bi_scope.

Section big_sepZ.
Context {PROP : bi}.
Implicit Types P Q : PROP.
Implicit Types Φ Ψ : Z → PROP.

Open Scope Z_scope.

Lemma big_sepZ_0 n m Φ :
  m <= n ->
  ([∗ Z] i ∈ [ n ; m ], Φ i) ⊣⊢ emp.
Proof. intros. rewrite /big_sepZ big_opN_0 //. lia. Qed.

Lemma big_sepZ_S n m Φ :
  n < m ->
  ([∗ Z] i ∈ [ n ; m ], Φ i) ⊣⊢ Φ n ∗ ([∗ Z] i ∈ [ n + 1 ; m ], Φ i).
Proof.
  intros. rewrite /big_sepZ big_sepN_S. 2:lia.
  rewrite right_id. f_equiv.
  rewrite (big_sepN_add_bounds 0 _ 1). rewrite left_id.
  replace ((Z.to_nat (m - (n + 1)) + 1))%nat with (Z.to_nat (m-n)) by lia.
  iApply big_sepN_proper. intros.
  replace (n + i) with (n + 1 + (i - 1)%nat) by lia. done.
Qed.

Lemma big_sepZ_add (n2 n1 n3:Z) Φ :
  n1 <= n2 <= n3 ->
  ([∗ Z] i ∈ [ n1 ; n3 ], Φ i)
  ⊣⊢ ([∗ Z] i ∈ [ n1 ; n2 ], Φ i) ∗ ([∗ Z] i ∈ [ n2 ; n3 ], Φ i).
Proof.
  intros. rewrite /big_sepZ.
  rewrite (big_sepN_add (Z.to_nat (n2-n1))). 2:lia.
  f_equiv.
  rewrite (big_sepN_add_bounds 0 _ (Z.to_nat (n2 - n1))).
  rewrite left_id.
  replace (Z.to_nat (n3 - n2) + Z.to_nat (n2 - n1))%nat with (Z.to_nat (n3 - n1)) by lia.
  apply big_sepN_proper.
  intros.
  replace (n1 + i)  with (n2 + (i - Z.to_nat (n2 - n1))%nat) by lia. done.
Qed.

End big_sepZ.

Global Opaque big_opN.
