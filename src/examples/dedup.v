From iris.proofmode Require Import base proofmode.
From iris.algebra Require Import cmra gmap.

From intdet.utils Require Import big_opN more_maps_and_sets.
From intdet.lang Require Import utils syntax syntax_instances notations head_semantics.
From intdet.examples Require Import hashtbl parfor.
From intdet.types.affine Require Import typing syntactical.

Section proof.

Context (h:val).
Context (c:val).
Context (hash : val -> nat).
Context (cmp: val -> val -> bool).

Axiom (HTotal : TotalOrder cmp).
Axiom (Hhspec : forall {Σ} `{X:dwp.intdetGS Σ}, ⊢ @hash_spec Σ X hash h).
Axiom (Hcspec : ∀ `{wpapi.IsWP Σ pt wpx}, ⊢ @cmp_spec Σ wpx cmp c).

Lemma TYLet' Γ1 e1 t1 Γ1' e2 t2 Γ2 x Γ2' :
  typed Γ1 e1 t1 Γ1' ->
  typed (binsert x t1 Γ1') e2 t2 Γ2 ->
  Γ2' = bdelete x Γ2 ->
  typed Γ1 (Let x e1 e2) t2 Γ2'.
Proof. intros. subst. eauto using TYLet. Qed.

Definition dedup : expr :=
  λ: "l",
    let: "start" := 0 in
    let: "length" := Length "l" in
    let: "table" := htbl_init h c ("length" '+ 1) in
    parfor "start" "length"  (λ: "i", let: "x" := "l".["i"] in htbl_add "table" "x") ;;
    let: "r" := htbl_elems "table" in
    Pair "l" "r".

Fixpoint iter_sep' {A:cmra} n (x:A) :=
  match n with
  | 0 => x
  | S n => x ⋅ iter_sep' n x end.

Lemma iter_sep_S' {A:cmra} n (x:A) :
  iter_sep' (S n) x = x ⋅ (iter_sep' n x).
Proof. done. Qed.

Lemma iter_sep_int' n :
  iter_sep' n TInt = TInt.
Proof. induction n. done. simpl. rewrite IHn //. Qed.

Lemma iter_sep_insert `{Countable K} {V:cmra} n k (v:V) (m:gmap K V):
  n ≠ 0 ->
  iter_sep n (<[k:=v]> m) = <[k:=iter_sep' (n-1) v]> (iter_sep n m).
Proof.
  intros.
  induction n; first done.
  simpl. destruct_decide (decide (n=0)).
  { subst. simpl. rewrite !right_id_L //. }
  { rewrite IHn // -insert_op. f_equal.
    rewrite -iter_sep_S'. f_equal. lia. }
Qed.

Lemma iter_sep_empty' `{Countable K} {A:cmra} n :
  iter_sep n ∅ = (∅ : gmap K A).
Proof. induction n; first done. simpl. rewrite IHn //. Qed.


Lemma iter_sep_hs n q :
  n ≠ 0 ->
  iter_sep' (n - 1) (THashSet (q / nat_to_Qp n)) = THashSet q.
Proof.
  remember (q/nat_to_Qp n)%Qp as q'.
  replace q with (nat_to_Qp n * q')%Qp.
  2:{ subst q'. rewrite Qp.mul_div_r //. }
  generalize q'. intros. clear Heqq' q'.

  induction n; first done.
  destruct_decide (decide (n=0)).
  { subst. simpl. replace (nat_to_Qp 1) with 1%Qp by compute_done.
    rewrite Qp.mul_1_l //. }
  { rewrite nat_to_Qp_succ //.
    rewrite Qp.mul_add_distr_r Qp.mul_1_l.
    replace (S n - 1) with (S (n-1)) by lia.
    simpl. rewrite IHn //. }
Qed.

Lemma iter_sep_ia n q :
  n ≠ 0 ->
  iter_sep' (n - 1) (TIntArray (q / nat_to_Qp n)) = TIntArray q .
Proof.
  remember (q/nat_to_Qp n)%Qp as q'.
  replace q with (nat_to_Qp n * q')%Qp.
  2:{ subst q'. rewrite Qp.mul_div_r //. }
  generalize q'. intros. clear Heqq' q'.

  induction n; first done.
  destruct_decide (decide (n=0)).
  { subst. simpl. replace (nat_to_Qp 1) with 1%Qp by compute_done.
    rewrite Qp.mul_1_l //. }
  { rewrite nat_to_Qp_succ //.
    rewrite Qp.mul_add_distr_r Qp.mul_1_l.
    replace (S n - 1) with (S (n-1)) by lia.
    simpl. rewrite IHn //. }
Qed.

Lemma typed_dedup q :
  typed ∅ dedup (TArrow (TIntArray q) (TProd (TIntArray q) (TIntArray 1))) ∅.
Proof.
  eapply TYAbs. done. rewrite /extend. simpl.
  eapply TYLet'. 3:shelve.
  { assert ( (<["l":=TIntArray q]> ∅) = {["l" := TIntArray q]} ⋅ (∅ : gmap _ _)) as ->.
    done.
    apply TYFrame. apply TYInt. } simpl. rewrite right_id_L.
  eapply TYLet'. 3:shelve.
  { assert ({["start" := TInt; "l" := TIntArray q]} = {["start" := TInt ]} ⋅ {["l" := TIntArray q]}) as ->. done.
    apply TYFrame. apply TYIALength. }
  simpl.

  assert(({["start" := TInt]} ⋅ {["l" := TIntArray q]}) = {["start" := TInt; "l" := TIntArray q]}) as ->. done.

  eapply TYLet'. 3:shelve.
  { assert ({["length" := TInt; "start" := TInt; "l" := TIntArray q]} = {["length" := TInt; "start" := TInt; "l" := TIntArray q]} ⋅ {["length" := TInt]}) as ->.
    { done. }
    apply TYFrame.
    eapply TYHSAlloc. apply HTotal. intros. apply Hhspec. intros. apply Hcspec.
    eapply TYCallPrim. done.
    assert ({["length" := TInt]} = {["length" := TInt]} ⋅ ∅) as -> by done.
    apply TYFrame. apply TYInt. rewrite right_id_L.
    apply TYVar. }
  simpl. rewrite right_id_L.
  eapply TYLet'. 3:reflexivity.
  { apply TYParFor with (Γf := fun n => {["table" := THashSet (1/nat_to_Qp n); "length" := TInt; "start" := TInt; "l" := TIntArray (q/nat_to_Qp n)]}).
    1-2:done. compute_done.
    { intros n Hn.
      rewrite !iter_sep_insert //. rewrite iter_sep_empty' insert_empty.
      f_equal.
      { rewrite iter_sep_hs //. }
      f_equal.
      { rewrite iter_sep_int' //. }
      f_equal.
      { rewrite iter_sep_int' //. }
      f_equal.
      { rewrite iter_sep_ia //. }  }
    { intros n. simpl.
      assert ({["i" := TInt;
      "table" := THashSet (1 / nat_to_Qp n);
      "length" := TInt;
      "start" := TInt;
                 "l" := TIntArray (q / nat_to_Qp n)]} =
              {[
      "length" := TInt;
      "start" := TInt
              ]} ⋅
 {["i" := TInt;
       "table" := THashSet (1 / nat_to_Qp n);
       "l" := TIntArray (q / nat_to_Qp n) ]}
             ) as ->. done.
      assert ({["table" := THashSet (1 / nat_to_Qp n);
      "length" := TInt;
      "start" := TInt;
                 "l" := TIntArray (q / nat_to_Qp n)]} =
              {[
      "length" := TInt;
      "start" := TInt
              ]} ⋅
 {["table" := THashSet (1 / nat_to_Qp n);
       "l" := TIntArray (q / nat_to_Qp n) ]}
             ) as ->. done.
      apply TYFrame.

      eapply TYLet'. 3:shelve.
      { assert ({["i" := TInt;
      "table" := THashSet (1 / nat_to_Qp n);
      "l" := TIntArray (q / nat_to_Qp n)]} = {["table" := THashSet (1 / nat_to_Qp n)]} ⋅{["i" := TInt;
                                                                                                 "l" := TIntArray (q / nat_to_Qp n)]} ) as -> by done.
        apply TYFrame.
        eapply TYIALoad.
        2:{ assert ({["i" := TInt; "l" := TIntArray (q / nat_to_Qp n)]} = {["l" := TIntArray (q / nat_to_Qp n)]} ⋅ {["i" := TInt]}) as -> by done.
            apply TYFrame. apply TYVar. }
        done. }
      simpl. rewrite right_id_L.
      assert ((<["x":=TInt]>
       ({["table" := THashSet (1 / nat_to_Qp n)]}
        ⋅ {["l" := TIntArray (q / nat_to_Qp n)]})) = {["l" := TIntArray (q / nat_to_Qp n)]} ⋅ {["x":=TInt; "table" := THashSet (1 / nat_to_Qp n)]} ) as -> by done.
      apply TYFrame.
      eapply TYHSInsert.
      2:{ assert ({["x" := TInt; "table" := THashSet (1 / nat_to_Qp n)]} = {["table" := THashSet (1 / nat_to_Qp n)]} ⋅ {["x" := TInt]}) as -> by done.
          apply TYFrame. apply TYVar. }
      done. } }
  simpl.

  eapply TYWeak with (Γ1' := {["table" := THashSet 1; "l" := TIntArray q]}).
  { intros x. rewrite !lookup_insert_case. case_decide; first done.
    case_decide; subst; simpl. done. rewrite lookup_empty.
    by repeat case_decide. }
  reflexivity.

  eapply TYLet'. 3:shelve.
  { assert ({["table" := THashSet 1; "l" := TIntArray q]}  = {["l" := TIntArray q]} ⋅ {["table" := THashSet 1]} ) as -> by done.
    apply TYFrame. apply TYHSElem. apply TYVar. }
  simpl.

  rewrite right_id_L.
  eapply TYProd.
  { assert ({["r" := TIntArray 1; "l" := TIntArray q]} = {["l" := TIntArray q]} ⋅ {["r" := TIntArray 1]}) as -> by done.
    apply TYFrame. apply TYVar. }
  rewrite right_id_L. apply TYVar.
  Unshelve. all:try done. compute_done.
Qed.

End proof.
