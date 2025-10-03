From stdpp Require Import base ssreflect gmap gmultiset.

Section more_stdpp.
Context `{Countable K} {V:Type}.

Lemma lookup_insert_case (X:gmap K V) x y i :
  <[y:=i]> X !! x = if (decide (y=x)) then Some i else X !! x.
Proof. case_decide; subst. rewrite lookup_insert //. rewrite lookup_insert_ne //. Qed.

Lemma lookup_total_insert_case `{Inhabited V} (X:gmap K V) x y i :
  <[y:=i]> X !!! x = if (decide (y=x)) then i else X !!! x.
Proof. rewrite !lookup_total_alt lookup_insert_case. by case_decide. Qed.

Lemma gmap_included_insert_notin (σ1 σ2:gmap K V) (l:K) (v:V) :
  l ∉ dom σ1 ->
  σ1 ⊆ σ2 ->
  σ1 ⊆ <[l:=v]>σ2.
Proof.
  intros ?? l'. destruct_decide (decide (l=l')).
  { subst. rewrite lookup_insert // not_elem_of_dom_1 //. }
  { rewrite !lookup_insert_ne //. }
Qed.

Lemma insert_insert_ne i j vi vj (m:gmap K V) :
  i ≠ j ->
  <[i:=vi]> (<[j:=vj]> m) = <[j:=vj]> (<[i:=vi]> m).
Proof.
  intros. apply map_eq. intros k.
  rewrite !lookup_insert_case.
  repeat case_decide; try done. congruence.
Qed.

Lemma insert_delete_ne k1 k2 v (e:gmap K V) :
  k1 ≠ k2 ->
  <[k1:=v]> (delete k2 e) = delete k2 (<[k1:=v]> e).
Proof.
  intros. apply map_eq. intros ?.
  rewrite !lookup_insert_case. case_decide; subst.
  { rewrite lookup_delete_ne // lookup_insert //. }
  { destruct_decide (decide (k2=i)).
    { subst. rewrite !lookup_delete //. }
    { rewrite !lookup_delete_ne // lookup_insert_ne //. } }
Qed.

Lemma insert_id_delete (k:K) (v:V) (m:gmap K V) :
  m !! k = Some v ->
  m = <[k:=v]> (delete k m).
Proof.
  intros. rewrite insert_delete_insert insert_id //.
Qed.

End more_stdpp.

Section map_zip.
Context `{Countable K} {A B:Type}.

Lemma map_zip_singleton (x:K) (y1:A) (y2:B) :
  map_zip ({[x:=y1]} : gmap _ _) {[x:=y2]} = {[x := (y1,y2)]}.
Proof.
  apply merge_singleton. done.
Qed.

Lemma map_zip_empty :
  map_zip (∅:gmap K A) (∅:gmap K B) = ∅.
Proof. done. Qed.

Lemma map_zip_empty_inv (m1:gmap K A) (m2:gmap K B) :
  dom m1 = dom m2 ->
  map_zip m1 m2 = ∅ ->
  m1 = ∅ /\ m2 = ∅.
Proof.
  intros Hd X. split.
  all:apply map_eq; intros i; apply (@f_equal _ _ (fun x => x !! i)) in X.
  all:rewrite /map_zip lookup_merge lookup_empty in X.
  all:destruct (m1 !! i) eqn:E1, (m2 !! i) eqn:E2; simpl in *; try done.
  { apply elem_of_dom_2 in E1. apply not_elem_of_dom in E2. set_solver. }
  { apply elem_of_dom_2 in E2. apply not_elem_of_dom in E1. set_solver. }
Qed.

Lemma dom_map_zip (x1:gmap K A) (x2:gmap K B) :
  dom (map_zip x1 x2) = dom x1 ∩ dom x2.
Proof.
  apply leibniz_equiv. intros i.
  rewrite elem_of_intersection !elem_of_dom.
  rewrite /map_zip lookup_merge.
  destruct (x1 !! i), (x2 !! i); simpl.
  all:rewrite ?is_Some_Some ?is_Some_None //.
  all:split; [ intros (?&?) | intros ((?&?)&(?&?))]; done.
Qed.

Lemma map_zip_insert (m1:gmap K A) (m2:gmap K B) i x1 x2 :
  map_zip (<[i:=x1]> m1) (<[i:=x2]> m2) = <[i:=(x1,x2)]> (map_zip m1 m2).
Proof.
  rewrite /map_zip. erewrite insert_merge; try done.
Qed.

Lemma map_zip_delete (m1:gmap K A) (m2:gmap K B) i :
  map_zip (delete i m1) (delete i m2) = delete i (map_zip m1 m2).
Proof.
  rewrite /map_zip delete_merge //.
Qed.

End map_zip.


Section multiset.

Context `{Countable K}.

Lemma dom_disj_union (m1 m2:gmultiset K) :
  dom (m1 ⊎ m2) = dom m1 ∪ dom m2.
Proof.
  apply set_eq. intros i. rewrite elem_of_union !gmultiset_elem_of_dom.
  multiset_solver.
Qed.

Lemma dom_msingleton (x:K) :
  dom ({[+x+]} : gmultiset K) = {[x]}.
Proof.
  apply set_eq. intros i. rewrite !gmultiset_elem_of_dom.
  multiset_solver.
Qed.

Lemma dom_mempty :
  dom (∅ : gmultiset K) = ∅.
Proof. compute_done. Qed.

End multiset.
