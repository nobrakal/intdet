From Coq Require Import ssreflect.
From stdpp Require Import base binders list sets gmap mapset ssreflect.

From intdet.utils Require Import more_maps_and_sets.
From intdet.lang Require Import syntax.

Section more_zip.

Lemma zip_app {A B:Type} (xs1 xs2:list A) (ys1 ys2:list B) :
  length xs1 = length ys1 ->
  zip (xs1 ++ xs2) (ys1 ++ ys2) = zip xs1 ys1 ++ zip xs2 ys2.
Proof.
  revert xs2 ys1 ys2. induction xs1; intros xs2 ys1 ys2 Hl.
  all:destruct ys1; try done.
  simpl. f_equal. apply IHxs1. simpl in Hl. lia.
Qed.

Lemma rev_zip {A B:Type} (xs:list A) (ys:list B) :
  length xs = length ys ->
  rev (zip xs ys) = zip (rev xs) (rev ys).
Proof.
  revert ys; induction xs. done.
  intros []; try done; simpl. intros.
  rewrite IHxs ?zip_app //.
  { rewrite !rev_length. lia. }
  { lia. }
Qed.

End more_zip.

Section more_rev.

Lemma fmap_rev {A B} (f:A -> B) xs :
  fmap f (rev xs) = rev (fmap f xs).
Proof.
  induction xs; first done.
  simpl. rewrite fmap_app IHxs //.
Qed.

End more_rev.

Section binders.

Definition binder_set (x:binder) : gset string :=
  match x with BAnon => ∅ | BNamed s => {[s]} end.

Definition binders_set (xs:list binder) : gset string := ⋃ (binder_set <$> xs).

Lemma binders_set_cons x xs :
  binders_set (x :: xs) = binder_set x ∪ binders_set xs.
Proof. done. Qed.

Lemma binders_set_app xs ys:
  binders_set (xs ++ ys) = binders_set xs ∪ binders_set ys.
Proof.
  rewrite /binders_set fmap_app union_list_app_L //.
Qed.

Lemma binders_set_rev xs :
  binders_set (rev xs) = binders_set xs.
Proof.
  induction xs. done. simpl.
  rewrite binders_set_cons binders_set_app. set_solver.
Qed.

End binders.

Section delete.
Context {A:Type}.

Implicit Type (e:gmap string A).

Definition bdelete (b:binder) (e:gmap string A) : gmap string A :=
  match b with
  | BAnon => e
  | BNamed s => delete s e end.

Lemma bdelete_empty b : bdelete b (∅:gmap string A) = ∅.
Proof. destruct b; first done; simpl. rewrite delete_empty //. Qed.

Lemma bdelete_union (e1 e2:gmap string A) x :
  bdelete x (e1 ∪ e2) = bdelete x e1 ∪ bdelete x e2.
Proof.
  destruct x; simpl; first done.
  rewrite delete_union //.
Qed.

Lemma bdelete_singleton_ne (b:binder) (x:string) (v:A):
  b ≠ x ->
  (bdelete b {[x := v]}) = {[x:=v]}.
Proof.
  intros ?.
  destruct b; first done. simpl. rewrite delete_singleton_ne //. naive_solver.
Qed.

Definition bdeletes (bs:list binder) (e:gmap string A) : gmap string A :=
  foldr bdelete e bs.

Lemma bdelete_bdeletes b bs e :
  bdelete b (bdeletes bs e) = (bdeletes bs (bdelete b e)).
Proof.
  rewrite /bdeletes. induction bs; first done. simpl.
  rewrite -IHbs. destruct a,b; try done. simpl.
  rewrite delete_commute //.
Qed.

Lemma bdeletes_empty bs : bdeletes bs (∅:gmap string A) = ∅.
Proof. induction bs; first done. simpl. rewrite IHbs bdelete_empty //. Qed.

Lemma bdeletes_cons (x:binder) xs e :
  bdeletes (x::xs) e = bdelete x (bdeletes xs e).
Proof. done. Qed.

Lemma bdeletes_app xs ys (m:gmap string A) :
  bdeletes (xs++ys) m = bdeletes xs (bdeletes ys m).
Proof. rewrite /bdeletes foldr_app //. Qed.

Lemma bdeletes_union (e1 e2:gmap string A) xs :
  bdeletes xs (e1 ∪ e2) = bdeletes xs e1 ∪ bdeletes xs e2.
Proof.
  induction xs; simpl; first done.
  rewrite IHxs bdelete_union //.
Qed.

Lemma dom_bdeletes xs e :
  dom (bdeletes xs e) = dom e ∖ binders_set xs.
Proof.
  induction xs. set_solver.
  rewrite bdeletes_cons binders_set_cons.
  destruct a; first set_solver.
  simpl. rewrite dom_delete_L. set_solver.
Qed.

Lemma bdeletes_already_in x xs e :
  x ∈ binders_set xs ->
  bdelete (BNamed x) (bdeletes xs e) = bdeletes xs e.
Proof.
  revert e. induction xs; first done.
  rewrite binders_set_cons.
  intros e ?.
  rewrite !bdeletes_cons.
  destruct a as [|a].
  { simpl. apply IHxs. set_solver. }
  destruct (decide (a=x)).
  { subst. simpl. rewrite delete_idemp //. }
  { rewrite -IHxs; last set_solver. simpl.
    rewrite delete_commute delete_idemp //. }
Qed.

Lemma bdeletes_disj xs e :
  binders_set xs ## dom e ->
  bdeletes xs e = e.
Proof.
  revert e. induction xs; first done.
  rewrite binders_set_cons. simpl. intros.
  rewrite IHxs; last (destruct a; set_solver).
  destruct a; first done. simpl.
  rewrite delete_notin // -not_elem_of_dom. set_solver.
Qed.

Lemma insert_bdeletes_notin s v xs (e:gmap string A) :
  s ∉ binders_set xs ->
  bdeletes xs (<[s:=v]> e) = <[s:=v]> (bdeletes xs e).
Proof.
  revert e; induction xs; first done; intros e.
  rewrite binders_set_cons. intros E.
  simpl. rewrite IHxs; last set_solver.
  destruct a; try done. simpl.
  rewrite delete_insert_ne //. set_solver.
Qed.

Lemma insert_bdeletes_in s v xs (e:gmap string A) :
  s ∈ binders_set xs ->
  bdeletes xs (<[s:=v]> e) = bdeletes xs e.
Proof.
  revert e; induction xs; first done; intros e.
  rewrite binders_set_cons. intros E.
  simpl.
  destruct a as [|s'].
  { simpl. apply IHxs. set_solver. }
  destruct_decide (decide (s'=s)).
  { subst. rewrite !bdelete_bdeletes.
    simpl. rewrite delete_insert_delete //. }
  rewrite IHxs //; last set_solver.
Qed.

End delete.

Lemma fmap_bdelete {A B} (f:A-> B) x (m:gmap string A) :
  fmap f (bdelete x m) = bdelete x (fmap f m).
Proof. destruct x; first done. apply fmap_delete. Qed.

Lemma fmap_bdeletes {A B} (f:A-> B) xs (m:gmap string A) :
  fmap f (bdeletes xs m) = bdeletes xs (fmap f m).
Proof.
  induction xs; first done.
  simpl. rewrite fmap_bdelete IHxs //.
Qed.

Section binserts.

Context {A:Type}.

Definition binsert b x (e:gmap string A) :=
  match b with
  | BAnon => e
  | BNamed b => <[b:=x]> e end.

Definition binserts (xs:list (binder * A)) (e:gmap string A) :=
  foldr (fun '(b,x) acc => binsert b x acc) e xs.

Lemma binserts_cons x (v:A) xs e :
  binserts ((x,v)::xs) e = binsert x v (binserts xs e).
Proof. done. Qed.

Lemma binserts_app (xs ys: list (binder*A)) e :
  binserts (xs ++ ys) e = binserts xs (binserts ys e).
Proof. rewrite /binserts foldr_app //. Qed.

Lemma lookup_binserts_ne l xs (e:gmap string A) :
  l ∉ binders_set xs.*1 ->
  binserts xs e !! l = e !! l .
Proof.
  revert e; induction xs as [|(s,?)]; try done. intros e.
  rewrite fmap_cons binders_set_cons. simpl. intros ?.
  destruct s; simpl.
  { apply IHxs. set_solver. }
  { rewrite lookup_insert_ne; last set_solver. apply IHxs. set_solver. }
Qed.

Lemma lookup_binserts s xs (e:gmap string A) :
  s ∈ binders_set xs.*1 ->
  binserts xs e !! s = binserts xs ∅ !! s.
Proof.
  induction xs as [|(s',?)]; first done.
  rewrite fmap_cons binders_set_cons.
  simpl. intros E.
  destruct s' as [|s'].
  { apply IHxs. set_solver. }
  simpl. rewrite !lookup_insert_case.
  case_decide. done. apply IHxs. set_solver.
Qed.

Lemma binserts_insert_in xs s v (e:gmap string A) :
  s ∈ binders_set xs.*1 ->
  binserts xs (<[s:=v]>e) = binserts xs e.
Proof.
  intros ?.
  apply map_eq. intros i.
  destruct_decide (decide (i ∈ binders_set xs.*1)).
  { rewrite !lookup_binserts //. }
  { rewrite !lookup_binserts_ne //. rewrite lookup_insert_ne //. set_solver. }
Qed.

Lemma binserts_insert_notin xs s v (e:gmap string A) :
  s ∉ binders_set xs.*1 ->
  binserts xs (<[s:=v]>e) = <[s:=v]> (binserts xs e).
Proof.
  intros ?.
  apply map_eq. intros i.
  destruct_decide (decide (i ∈ binders_set xs.*1)).
  { rewrite !lookup_binserts //. rewrite lookup_insert_ne // ?lookup_binserts //. set_solver. }
  { rewrite lookup_binserts_ne //.
    rewrite !lookup_insert_case. case_decide; first done.
    rewrite lookup_binserts_ne //. }
Qed.

Lemma lookup_binserts_binserts `{Inhabited A} xs ys s (e:gmap string A)  :
  s ∉ (binders_set ys.*1 ∖ binders_set xs.*1) ->
  (binserts xs (binserts ys e)) !!! s = binserts xs e !!! s.
Proof.
  intros.
  rewrite !lookup_total_alt. f_equal.
  destruct_decide (decide (s ∈ binders_set xs.*1)).
  { rewrite !lookup_binserts //. }
  { rewrite !lookup_binserts_ne //. set_solver. }
Qed.

Lemma dom_binserts xs (e:gmap string A) :
  dom (binserts xs e) = binders_set xs.*1 ∪ dom e.
Proof.
  induction xs as [|(?,?)]. set_solver.
  rewrite fmap_cons. simpl. rewrite binders_set_cons.
  destruct b; set_solver.
Qed.

Lemma binsert_binserts_inv x v xs (e:gmap string A) :
  exists xs', binsert x v (binserts xs e) = binserts xs' (binsert x v e) /\
  binders_set xs'.*1 ⊆ binders_set xs.*1 ∖ binder_set x.
Proof.
  destruct x as [|s]; simpl.
  { exists xs; set_solver. }
  induction xs as [|(b&?) ?].
  { exists nil. done. }
  rewrite fmap_cons binserts_cons binders_set_cons.
  destruct IHxs as (xs'&E&?).
  destruct b as [|s']; simpl.
  { exists xs'. split; first done. set_solver. }
  { destruct_decide (decide (s=s')); subst.
    { rewrite insert_insert. exists xs'. rewrite E //. set_solver. }
    { exists ((BNamed s',a)::xs').
      rewrite binserts_cons insert_insert_ne // fmap_cons binders_set_cons.
      rewrite E. set_solver. } }
Qed.

Lemma binserts_binserts_commut ys xs (e:gmap string A) :
  exists xs',
    binserts ys (binserts xs e) = binserts xs' (binserts ys e) /\
    binders_set xs'.*1 = binders_set xs.*1 ∖ binders_set ys.*1.
Proof.
  revert ys e.
  induction xs as [|(b,?)]; intros ys e; simpl in *.
  { exists nil. simpl. split_and !; try done. set_solver. }
  { destruct (IHxs ys e) as (xs'&He&?); try lia.
    destruct b as [|s].
    { exists xs'. split_and !; try done. set_solver. }
    simpl.
    destruct_decide (decide (s ∈ binders_set ys.*1)).
    { exists xs'. split_and !.
      { rewrite binserts_insert_in //. }
      { rewrite binders_set_cons. set_solver. } }
    { eexists ((BNamed s,_)::xs').
      split_and !.
      { simpl. rewrite -He binserts_insert_notin //. }
      { rewrite !binders_set_cons. set_solver. } } }
Qed.

End binserts.

Lemma fmap_binsert {A B} (f:A -> B) x v (m:gmap string A) :
  fmap f (binsert x v m) = binsert x (f v) (fmap f m).
Proof.
  destruct x; first done. apply fmap_insert.
Qed.

Definition extend {A} xs ys (e:gmap string A) :=
  binserts (rev (zip xs ys)) e.

Section extend.

Context {A:Type}.

Implicit Type (e:gmap string A).

Lemma extend_nil (e:gmap string A) :
  extend nil nil e = e.
Proof. done. Qed.

Lemma extend_cons x (v:A) xs vs e :
  extend (x::xs) (v::vs) e = (extend xs vs (binsert x v e)).
Proof. rewrite /extend. simpl. rewrite binserts_app //. Qed.

Lemma lookup_extend_singleton `{Inhabited A} x y (e:gmap string A) :
  extend [BNamed x] [y] e !!! x = y.
Proof.
  rewrite lookup_total_alt /extend. simpl.
  rewrite lookup_insert //.
Qed.

Lemma extend_app x1 y1 x2 y2 e:
  length x1 = length y1 ->
  extend (x1 ++ x2) (y1 ++ y2) e = extend x2 y2 (extend x1 y1 e).
Proof.
  intros.
  rewrite /extend zip_app // rev_app_distr // binserts_app //.
Qed.

Lemma aneq xs (ys:list A) :
  length xs = length ys ->
  binders_set (rev (zip xs ys)).*1 = binders_set xs.
Proof.
  intros.
  rewrite fmap_rev fst_zip // ?binders_set_rev //. lia.
Qed.

Lemma extend_insert_in xs ys s v (e:gmap string A) :
  length xs = length ys ->
  s ∈ binders_set xs ->
  extend xs ys (<[s:=v]> e) = extend xs ys e.
Proof.
  intros.
  rewrite /extend binserts_insert_in // aneq //.
Qed.

Lemma extend_insert_notin xs ys s v (e:gmap string A) :
  length xs = length ys ->
  s ∉ binders_set xs ->
  extend xs ys (<[s:=v]>e) = <[s:=v]> (extend xs ys e).
Proof.
  intros.
  rewrite /extend binserts_insert_notin // aneq //.
Qed.

Lemma binsert_bdelete_same x y (e:gmap string A) :
  binsert x y (bdelete x e) = binsert x y e.
Proof.
  destruct x; first done. simpl. rewrite insert_delete_insert //.
Qed.

Lemma binserts_bdeletes_same xs ys (e:gmap string A) :
  length xs = length ys ->
  extend xs ys (bdeletes xs e) = extend xs ys e.
Proof.
  revert e ys. induction xs; intros e [] Hl; try done. simpl in *.
  rewrite !extend_cons.
  destruct a.
  { simpl. apply IHxs. lia. }
  simpl. rewrite insert_delete_insert.
  destruct_decide (decide (s ∈ binders_set xs)).
  { rewrite /extend !binserts_insert_in //; try lia.
    apply IHxs. lia. all:rewrite aneq //; lia. }
  { rewrite -insert_bdeletes_notin // IHxs //. lia. }
Qed.

Lemma lookup_extend_ne l xs ys (e:gmap string A) :
  length xs = length ys ->
  l ∉ binders_set xs ->
  extend xs ys e !! l = e !! l .
Proof. intros. rewrite /extend lookup_binserts_ne // aneq //. Qed.

Definition bmap (xs:list binder) (ys:list A) :=
  extend xs ys ∅.

Lemma lookup_extend s xs ys (e:gmap string A) :
  length xs = length ys ->
  s ∈ binders_set xs ->
  extend xs ys e !! s = bmap xs ys !! s.
Proof. intros. rewrite /extend lookup_binserts // aneq //. Qed.

Lemma lookup_extend_binserts `{Inhabited A} xs ys zs s (e:gmap string A)  :
  length xs = length ys ->
  s ∉ (binders_set zs.*1 ∖ binders_set xs) ->
  (extend xs ys (binserts zs e)) !!! s = extend xs ys e !!! s.
Proof. intros. rewrite lookup_binserts_binserts // aneq //. Qed.

Lemma dom_extend xs ys (e:gmap string A) :
  length xs = length ys ->
  dom (extend xs ys e) = binders_set xs ∪ dom e.
Proof. intros. rewrite /extend dom_binserts aneq //. Qed.

Lemma extend_binserts_commut x1 y1 xs (e:gmap string A) :
  length x1 = length y1 ->
  exists xs',
    extend x1 y1 (binserts xs e) = binserts xs' (extend x1 y1 e) /\
   binders_set xs'.*1 = binders_set xs.*1 ∖ binders_set x1.
Proof.
  intros. rewrite /extend.
  destruct (binserts_binserts_commut (rev (zip x1 y1)) xs e) as (zs&eq&X).
  exists zs. rewrite eq. split; first done. rewrite aneq // in X.
Qed.

Lemma extend_fmap2 {B} (f:A -> B) xs (ys:list A) (e:gmap string A) :
  length xs = length ys ->
  extend xs (f <$> ys) (f <$> e) = (f <$> (extend xs ys e) : gmap string B).
Proof.
  revert e ys. induction xs; intros e []; try done.
  rewrite fmap_cons !extend_cons. simpl. intros.
  rewrite -IHxs; last lia. unfold extend. simpl.
  rewrite binserts_app. simpl. destruct a; first done. simpl.
  rewrite fmap_insert //.
Qed.

Lemma dom_bmap xs (ys:list A) :
  length xs = length ys ->
  dom (bmap xs ys) = ⋃ (binder_set <$> xs).
Proof.
  intros.
  rewrite /bmap dom_extend //. set_solver.
Qed.

Lemma dom_binsert x v (xs:gmap _ A) :
  dom (binsert x v xs) = binder_set x ∪ dom xs.
Proof.
  destruct x; first set_solver. simpl.
  rewrite dom_insert_L //.
Qed.

Lemma lookup_bdelete_ne x i (m:gmap _ A):
  i ∉ binder_set x ->
  bdelete x m !! i = m !! i.
Proof.
  intros. destruct x; first done. simpl.
  rewrite lookup_delete_ne //. set_solver.
Qed.

Lemma lookup_binsert_ne x y i (m:gmap _ A):
  i ∉ binder_set x ->
  binsert x y m !! i = m !! i.
Proof.
  intros. destruct x; first done. simpl.
  rewrite lookup_insert_ne //. set_solver.
Qed.

Lemma bdelete_mono x (m1 m2:gmap _ A) :
  m1 ⊆ m2 ->
  bdelete x m1 ⊆ bdelete x m2.
Proof.
  destruct x; try done.
  apply delete_mono.
Qed.

Lemma bdelete_binsert x v (m:gmap _ A) :
  bdelete x (binsert x v m) = bdelete x m.
Proof. destruct x; first done. apply delete_insert_delete. Qed.

Lemma bdelete_subseteq x (m:gmap _ A) :
  bdelete x m ⊆ m.
Proof. destruct x; first reflexivity. apply delete_subseteq. Qed.

Lemma binsert_bdelete x v (m:gmap _ A) :
  binsert x v m = binsert x v (bdelete x m).
Proof.
  destruct x; try done. simpl.
  rewrite insert_delete_insert //.
Qed.

End extend.
