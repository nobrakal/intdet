From stdpp Require Import base ssreflect gmap.

Section restrict.

Context `{Countable K} {V:Type}.

Definition restrict (g:gset K) (m:gmap K V) : gmap K V :=
  filter (fun '(k,_) => k ∈ g) m.

Definition dom_restrict (g:gset K) (m:gmap K V) :
  dom (restrict g m) = dom m ∩ g.
Proof.
  apply dom_filter_L.
  intros k. rewrite elem_of_intersection.
  split.
  { intros (Hk&?). apply elem_of_dom in Hk. destruct Hk. eauto. }
  { intros (x&Hk&?). apply elem_of_dom_2 in Hk. eauto. }
Qed.

Lemma lookup_restrict (g:gset K) (m:gmap K V) l :
  restrict g m !! l = if decide (l ∈ g) then m !! l else None.
Proof.
  rewrite /restrict.
  rewrite map_lookup_filter.
  case_decide.
  { destruct (m !! l); last done. simpl.
    rewrite option_guard_True //. }
  { destruct (m !! l); last done. simpl.
    rewrite option_guard_False //. }
Qed.

Lemma restrict_subseteq (g:gset K) (m:gmap K V) :
  restrict g m ⊆ m.
Proof. apply map_filter_subseteq. Qed.

Lemma restrict_empty g :
  restrict g ∅ = ∅.
Proof.
  rewrite /restrict map_filter_empty //.
Qed.

Lemma restrict_empty' (m:gmap K V) :
  restrict ∅ m = ∅.
Proof.
  apply map_eq. intros i. rewrite lookup_restrict.
  case_decide. set_solver. rewrite lookup_empty //.
Qed.

Lemma restrict_insert (g:gset K) i v (m:gmap K V) :
  i ∉ dom m ->
  restrict g (<[i:=v]> m) = if (decide (i ∈ g)) then <[i:=v]> (restrict g m) else (restrict g m).
Proof.
  intros. rewrite /restrict. case_decide.
  { rewrite map_filter_insert_True //. }
  { rewrite map_filter_insert_False //. f_equal.
    rewrite delete_notin //.
    by eapply not_elem_of_dom. }
Qed.

Lemma restrict_difference_not_in (g1 g2:gset K) (m:gmap K V) :
  dom m ## g2 ->
  restrict (g1 ∖ g2) m = restrict g1 m.
Proof.
  intros. apply map_eq.
  intros i. rewrite !lookup_restrict.
  case_decide.
  { rewrite decide_True //. set_solver. }
  { case_decide; last done.
    assert (i ∉ dom m) by set_solver.
    rewrite not_elem_of_dom_1 //. }
Qed.

Lemma restrict_split g (m:gmap K V):
  m = restrict g m ∪ restrict (dom m ∖ g) m.
Proof.
  apply map_eq.
  intros k. rewrite lookup_union !lookup_restrict.
  case_decide.
  { rewrite decide_False; last set_solver. rewrite right_id //. }
  { rewrite left_id.
    destruct_decide (decide (k ∈ dom m)).
    { rewrite decide_True //; set_solver. }
    { rewrite decide_False //. by eapply not_elem_of_dom. set_solver. } }
Qed.

Lemma restrict_restrict (g1 g2:gset K) (m:gmap K V) :
  restrict g1 (restrict g2 m) = restrict (g1 ∩ g2) m.
Proof.
  apply map_eq. intros i.
  rewrite !lookup_restrict.
  case_decide.
  { case_decide. rewrite decide_True //. set_solver.
    rewrite decide_False //. set_solver. }
  { rewrite decide_False //. set_solver. }
Qed.

Lemma restrict_singleton g (x:K) (v:V) :
  restrict g {[x:=v]} = if decide (x ∈ g) then {[x:=v]} else ∅.
Proof.
  apply map_eq. intros i. rewrite lookup_restrict.
  case_decide.
  { destruct_decide (decide (x=i)); subst.
    { rewrite decide_True //. }
    { rewrite lookup_singleton_ne //. case_decide.
      rewrite lookup_singleton_ne //. done. } }
  { case_decide. rewrite lookup_singleton_ne //. set_solver. done. }
Qed.

Lemma restrict_id g (m:gmap K V) :
  dom m ⊆ g ->
  restrict g m = m.
Proof.
  intros.
  apply map_eq. intros. rewrite lookup_restrict.
  case_decide. done. rewrite not_elem_of_dom_1 //.
  set_solver.
Qed.

Lemma delete_restrict x g (m:gmap K V):
  delete x (restrict g m) = restrict (g ∖ {[x]}) m.
Proof.
  apply map_eq. intros i.
  destruct_decide (decide (x=i)); subst.
  { rewrite lookup_restrict. rewrite lookup_delete decide_False //. set_solver. }
  { rewrite lookup_delete_ne // !lookup_restrict.
    case_decide. rewrite decide_True //. set_solver. rewrite decide_False //.
    set_solver. }
Qed.

End restrict.
