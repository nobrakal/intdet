From Coq.ssr Require Import ssreflect.
From stdpp Require Import strings binders gmap gmultiset sets ssreflect.

Definition graph (K:Type) `{Countable K} := (gset (K*K)).

Section Graph.

Context `{Countable K}.

Implicit Type G : graph K.
Implicit Type x y : K.

Definition edge G x y := (x,y) ∈ G.

Lemma edge_mon G G' x y :
  G ⊆ G' ->
  edge G x y ->
  edge G' x y.
Proof. set_solver. Qed.

Definition reachable G x y := rtc (edge G) x y.

Lemma edge_reachable G x y :
  edge G x y -> reachable G x y.
Proof. apply rtc_once. Qed.

Global Instance reachable_pre_order G : PreOrder (reachable G).
Proof. apply rtc_po. Qed.

Lemma reachable_mon G G' x y :
  G ⊆ G' ->
  reachable G x y ->
  reachable G' x y.
Proof.
  intros ?. rewrite /reachable. revert x.
  apply rtc_ind_l.
  { apply rtc_refl. }
  { intros ? z ? ? ?.
    apply rtc_l with z; eauto using edge_mon. }
Qed.

(* ------------------------------------------------------------------------ *)
(* [graph_upd] *)

Definition edges (x:K) (X:gset K) : gset (K*K) := set_map (fun y => (x,y)) X.

Definition graph_upd G x (X:gset K) := (edges x X) ∪ G.

Lemma elem_of_edges x y X :
  y ∈ X <-> (x, y) ∈ edges x X.
Proof. set_solver. Qed.

Lemma edge_graph_upd G X x y :
  y ∈ X ∨ edge G x y ->
  edge (graph_upd G x X) x y.
Proof.
  rewrite /edge /graph_upd.
  rewrite elem_of_union. intros [|]; eauto. left. by apply elem_of_edges.
Qed.

Lemma graph_upd_incl G t S :
  G ⊆ (graph_upd G t S).
Proof. set_solver. Qed.

(* ------------------------------------------------------------------------ *)
(* [vertices] *)

Definition vertices G : gset K := set_fold (fun '(x,y) acc => {[x;y]} ∪ acc) ∅ G.

Lemma elem_of_vertices x (g:graph K) :
  x ∈ vertices g <-> exists y, ((x,y) ∈ g \/ (y,x) ∈ g).
Proof.
  apply set_fold_ind_L with (P := fun f g => x ∈ f  <-> exists y, ((x,y) ∈ g \/ (y,x) ∈ g)).
  set_solver.
  intros (?,?). set_solver.
Qed.

Lemma vertices_singleton (x:(K*K)) :
  vertices {[x]} = {[x.1;x.2]}.
Proof.
  rewrite /vertices set_fold_singleton. destruct x as (?&?); set_solver.
Qed.

Lemma vertices_union (g1 g2:graph K) :
  vertices (g1 ∪ g2) = vertices g1 ∪ vertices g2.
Proof.
  revert g2. induction g1 using set_ind_L; intros g2.
  { rewrite /vertices set_fold_empty !left_id_L //. }
  replace ({[x]} ∪ X ∪ g2) with (X ∪ ({[x]} ∪ g2)) by set_solver.
  rewrite (union_comm_L _  X).
  rewrite !IHg1. rewrite -union_assoc_L. f_equal.
  destruct_decide (decide (x ∈ g2)).
  { replace ({[x]} ∪ g2) with g2 by set_solver.
    rewrite vertices_singleton.
    assert ({[x.1; x.2]} ⊆ vertices g2); last by set_solver.
    intros l Hl. apply elem_of_vertices.
    rewrite elem_of_union !elem_of_singleton in Hl. destruct x as (?,?). set_solver. }
  rewrite {1}/vertices /set_fold. simpl.
  rewrite (foldr_permutation _ _ _ _ (x::elements g2)).
  { simpl. rewrite vertices_singleton. destruct x as (?,?). set_solver. }
  { intros. destruct a1 as (?,?),a2 as (?,?); set_solver. }
  { by apply elements_union_singleton. }
Qed.

(******************************************************************************)
(* fork/join *)

Definition graph_fork (G:graph K) (t v w:K) :=
  graph_upd G t {[v;w]}.
Definition graph_join (G:graph K) (t v w:K) :=
  graph_upd (graph_upd G t {[w]}) v {[w]}.

Lemma graph_fork_incl G t v w :
  G ⊆ (graph_fork G t v w).
Proof. apply graph_upd_incl. Qed.

Lemma graph_join_incl G t v w :
  G ⊆ (graph_join G t v w).
Proof.
  rewrite /graph_join.
  transitivity (graph_upd G t {[w]}); apply graph_upd_incl.
Qed.

Lemma vertices_fork (g:graph K) t0 t1 t2 :
  vertices (graph_fork g t0 t1 t2) = {[t0;t1;t2]} ∪ vertices g.
Proof.
  unfold graph_fork, graph_upd, edges.
  rewrite vertices_union. f_equal.
  rewrite set_map_union_L !set_map_singleton_L.
  rewrite vertices_union !vertices_singleton.
  set_solver.
Qed.

Lemma vertices_join (g:graph K) t0 t1 t2 :
  vertices (graph_join g t0 t1 t2) = {[t0;t1;t2]} ∪ vertices g.
Proof.
  unfold graph_join, graph_upd, edges.
  rewrite !vertices_union !set_map_singleton_L !vertices_singleton.
  set_solver.
Qed.

Lemma graph_fork_inv_edge (g:graph K) t1 t2 t3 x1 x2 :
  edge (graph_fork g t1 t2 t3) x1 x2 ->
  (x1=t1 /\ (x2=t2 \/ x2=t3)) \/ edge g x1 x2.
Proof.
  unfold edge,graph_fork,graph_upd, edges.
  rewrite !elem_of_union. set_solver.
Qed.

Lemma graph_join_inv_edge (g:graph K) t1 t2 t3 x1 x2 :
  edge (graph_join g t1 t2 t3) x1 x2 ->
  (x2=t3 /\ (x1=t1 \/ x1=t2)) \/ edge g x1 x2.
Proof.
  unfold edge,graph_join,graph_upd, edges.
  rewrite !elem_of_union.
  intros [X|[X|X]].
  1,2:rewrite set_map_singleton_L in X; set_solver.
  naive_solver.
Qed.

Lemma reachable_in_vertices (g:graph K) t1 t2 :
  reachable g t1 t2 ->
  t1 = t2 \/ (t1 ∈ vertices g /\ t2 ∈ vertices g).
Proof.
  inversion 1. eauto. subst.
  right. rewrite !elem_of_vertices.
  eapply rtc_inv_r in H2. set_solver.
Qed.

End Graph.
