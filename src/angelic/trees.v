From stdpp Require Import gmap sets ssreflect.

From intdet.lang Require Import invert_step.
From intdet.lang Require Export syntax semantics atomic.
From intdet.utils Require Import restrict.

Section paths.

Inductive task_tree : Type :=
| Leaf : task_tree
| Node : task_tree -> task_tree -> task_tree.

Definition path := list bool.

Fixpoint paths_aux (p:path) (T:task_tree) : gset path :=
  match T with
  | Leaf => {[p]}
  | Node T1 T2 => {[p]} ∪ paths_aux (true::p) T1 ∪ paths_aux (false::p) T2 end.

Definition paths := paths_aux nil.

Lemma elem_of_paths_aux p suf T :
  p ∈ paths_aux suf T ->
  suf `suffix_of` p.
Proof.
  revert suf. induction T; simpl; intros suf Hp.
  { replace p with suf by set_solver. reflexivity. }
  { rewrite !elem_of_union in Hp.
    destruct Hp as [ [ | Hp ] | Hp ].
    { replace p with suf by set_solver. reflexivity. }
    all:eauto using suffix_cons_l. }
Qed.

End paths.

Section rebuild.

Inductive status :=
| Running : expr -> status
| Paused : list ctx -> status.

Inductive rebuild (m:gmap path status) : path -> task_tree -> expr -> Prop :=
| rebuild_leaf : forall p e,
  m !! p = Some (Running e) ->
  rebuild m p Leaf e
| rebuild_node : forall p ks T1 T2 e1 e2,
  m !! p = Some (Paused ks) ->
  rebuild m (true::p) T1 e1 ->
  rebuild m (false::p) T2 e2 ->
  rebuild m p (Node T1 T2) (fill_items ks (RunPar e1 e2)).

Lemma rebuild_restrict m m' pr T e :
  m' ⊆ m ->
  paths_aux pr T ⊆ dom m' ->
  rebuild m pr T e ->
  rebuild m' pr T e.
Proof.
  intros E1 E2 Hr. revert m' E1 E2.
  induction Hr; intros m' E1 E2; simpl in *.
  { constructor.
    assert (is_Some (m' !! p)) as (x&Hx).
    { apply elem_of_dom. set_solver. }
    rewrite Hx. eapply lookup_weaken in Hx. 2:done. naive_solver. }
  { constructor.
    { assert (is_Some (m' !! p)) as (x&Hx).
      { apply elem_of_dom. set_solver. }
      rewrite Hx. eapply lookup_weaken in Hx. 2:done. naive_solver. }
    { apply IHHr1; set_solver. }
    { apply IHHr2; set_solver. } }
Qed.

Definition tctx : Type := task_tree + task_tree.

Definition fill_tctx (k:tctx) (t:task_tree) : task_tree :=
  match k with
  | inl t' => Node t t'
  | inr t' => Node t' t end.

Definition fill_tctxs (ks:list tctx) (t:task_tree) : task_tree :=
  fold_right fill_tctx t ks.

Definition is_left {A B:Type} (x:A+B) :=
  match x with inl _ => true | inr _ => false end.

Definition follow_path {A B:Type} (p:path) (ks:list (A+B)) :=
  Forall2 (fun b k => b = is_left k) p ks.

Lemma app_eq_same_r {A} (l1 l2:list A) :
  l1 ++ l2 = l2 ->
  l1 = nil.
Proof.
  destruct l1. done. intro E. exfalso.
  apply (@f_equal _ _ length) in E.
  rewrite app_length cons_length in E. lia.
Qed.

Lemma app_eq_same_r' {A} (l1 l2:list A) :
  length l1 ≠ 0 ->
  l1 ++ l2 ≠ l2.
Proof.
  intros X E. apply X. apply app_eq_same_r in E.
  subst. done.
Qed.

Lemma in_paths_aux_node p b suf T1 T2 :
  (p ++ b :: suf) ∈ paths_aux suf (Node T1 T2) ->
  (p ++ b :: suf) ∈ paths_aux (b::suf) (if b then T1 else T2).
Proof.
  simpl. intros Hp.
  assert (p ++ b :: suf ≠ suf).
  { intros E. rewrite cons_middle assoc_L in E.
    apply app_eq_same_r in E. by destruct p. }
  assert (p ++ b :: suf ∉ paths_aux (negb b :: suf) (if b then T2 else T1)).
  { intros E. apply elem_of_paths_aux in E.
    rewrite cons_middle assoc_L in E.
    replace (negb b :: suf) with ((nil ++ [negb b]) ++ suf ) in E by done.
    apply suffix_app_inv in E. apply suffix_snoc_inv_1 in E.
    by destruct b. }
  destruct b; set_solver.
Qed.

Definition pctx : Type := (list ctx * expr) + (list ctx * expr).

Definition fill_pctx (k:pctx) (e:expr) : expr :=
  match k with
  | inl (ks,e') => fill_items ks (RunPar e e')
  | inr (ks,e') => fill_items ks (RunPar e' e) end.

Definition fill_pctxs (ks:list pctx) (e:expr) : expr :=
  fold_right fill_pctx e ks.

Lemma running_is_leaf_aux prefix m T e e' p :
  dom m = paths_aux prefix T ->
  rebuild m prefix T e ->
  m !! (p++prefix) = Some (Running e') ->
  exists kts kps, T = fill_tctxs kts Leaf /\ follow_path (rev p) kts
             /\ e = fill_pctxs kps e' /\ follow_path (rev p) kps.
Proof.
  revert m prefix p e. induction T; intros m prefix p e Hd Hb Hp; inversion Hb; subst.
  { simpl in *.
    assert (p=nil); subst.
    { apply elem_of_dom_2 in Hp.
      assert (p++prefix=prefix) by set_solver.
      eauto using app_eq_same_r. }
    exists nil,nil.
    simpl in *. rewrite H in Hp. inversion Hp. subst.
    split_and !; try done; constructor.  }
  { destruct (last p) eqn:Hl.
    2:{ exfalso. apply last_None in Hl. subst. simpl in Hp. congruence. }
    apply last_Some in Hl. destruct Hl as (?&->).
    rewrite -assoc_L in Hp.
    rewrite rev_app_distr. simpl in *. destruct b.
    { edestruct (IHT1 (restrict (paths_aux (true::prefix) T1) m) (true::prefix))
        as (kts'&kps'&?&?&?&?).
      { rewrite dom_restrict. set_solver. }
      { eapply rebuild_restrict; last done. apply restrict_subseteq.
        rewrite dom_restrict. set_solver. }
      { rewrite lookup_restrict decide_True //.
        apply elem_of_dom_2 in Hp.
        pose proof in_paths_aux_node. set_solver. }
      subst.
      eexists ((inl _)::kts'), ((inl (_,_))::kps').
      split_and !; try done; by constructor. }
    { edestruct (IHT2 (restrict (paths_aux (false::prefix) T2) m) (false::prefix))
        as (kts'&kps'&?&?&?&?).
      { rewrite dom_restrict. set_solver. }
      { eapply rebuild_restrict; last done. apply restrict_subseteq.
        rewrite dom_restrict. set_solver. }
      { rewrite lookup_restrict decide_True //.
        apply elem_of_dom_2 in Hp.
        pose proof in_paths_aux_node. set_solver. }
      subst.
      eexists ((inr _)::kts'), ((inr (_,_))::kps').
      split_and !; try done; by constructor. } }
Qed.

Lemma running_is_leaf m T e e' p :
  dom m = paths T ->
  rebuild m nil T e ->
  m !! p = Some (Running e') ->
  exists kts kps, T = fill_tctxs kts Leaf /\ follow_path (rev p) kts
             /\ e = fill_pctxs kps e' /\ follow_path (rev p) kps.
Proof.
  intros.
  edestruct (running_is_leaf_aux nil m T e e' p) as (?&?&?&?&?); eauto.
  rewrite right_id_L //.
Qed.

Lemma running_is_join_aux prefix m T e ks e1 e2 p :
  dom m = paths_aux prefix T ->
  rebuild m prefix T e ->
  m !! (true::p++prefix) = Some (Running e1) ->
  m !! (false::p++prefix) = Some (Running e2) ->
  m !! (p++prefix) = Some (Paused ks) ->
  exists kts kps, T = fill_tctxs kts (Node Leaf Leaf) /\ follow_path (rev p) kts
             /\ e = fill_pctxs kps (fill_items ks (RunPar e1 e2)) /\ follow_path (rev p) kps.
Proof.
  revert m prefix p e. induction T; intros m prefix p e Eq Hb E1 E2 E3; inversion Hb; subst.
  { exfalso. simpl in *. apply elem_of_dom_2 in E1.
    assert (true :: p ++ prefix ≠ prefix); last set_solver.
    rewrite app_comm_cons. apply app_eq_same_r'. done. }
  { destruct (last p) eqn:Hlast; last first.
    { apply last_None in Hlast. subst. simpl in *.
      rewrite H1 in E3. inversion E3. subst. clear E3.
      inversion H3; subst; last first.
      { exfalso. naive_solver. }
      rewrite E1 in H. inversion H. clear H. subst.
      inversion H5; subst; last first.
      { exfalso. naive_solver. }
      rewrite E2 in H. inversion H. clear H. subst.
      clear H3 H5 E1 E2 H1.
      exists nil,nil. split_and !; try done. all:by constructor. }
    { apply last_Some in Hlast. destruct Hlast as (p'&->).
      rewrite -assoc_L in E1, E2, E3.
      rewrite rev_app_distr. simpl. destruct b.
      { edestruct (IHT1 (restrict (paths_aux (true::prefix) T1) m) (true::prefix))
        as (kts'&kps'&?&?&?&?).
        { rewrite dom_restrict. set_solver. }
        { eapply rebuild_restrict; last done. apply restrict_subseteq.
          rewrite dom_restrict. set_solver. }
        { rewrite lookup_restrict decide_True //.
          apply elem_of_dom_2 in E1. rewrite app_comm_cons.
          eapply (in_paths_aux_node _ true _ T1 T2). rewrite -app_comm_cons.
          set_solver. }
        { rewrite lookup_restrict decide_True //.
          apply elem_of_dom_2 in E2. rewrite app_comm_cons.
          eapply (in_paths_aux_node _ true _ T1 T2). rewrite -app_comm_cons.
          set_solver. }
        { rewrite lookup_restrict decide_True //.
          apply elem_of_dom_2 in E3.  eapply (in_paths_aux_node _ true _ T1 T2).
          set_solver. }
        subst. eexists ((inl _)::kts'), ((inl (_,_))::kps').
        split_and !; try done; by constructor. }
    (* XXX ugly copy/pasta *)
    { edestruct (IHT2 (restrict (paths_aux (false::prefix) T2) m) (false::prefix))
        as (kts'&kps'&?&?&?&?).
      { rewrite dom_restrict. set_solver. }
        { eapply rebuild_restrict; last done. apply restrict_subseteq.
          rewrite dom_restrict. set_solver. }
        { rewrite lookup_restrict decide_True //.
          apply elem_of_dom_2 in E1. rewrite app_comm_cons.
          eapply (in_paths_aux_node _ false _ T1 T2). rewrite -app_comm_cons.
          set_solver. }
        { rewrite lookup_restrict decide_True //.
          apply elem_of_dom_2 in E2. rewrite app_comm_cons.
          eapply (in_paths_aux_node _ false _ T1 T2). rewrite -app_comm_cons.
          set_solver. }
        { rewrite lookup_restrict decide_True //.
          apply elem_of_dom_2 in E3.  eapply (in_paths_aux_node _ false _ T1 T2).
          set_solver. }
        subst. eexists ((inr _)::kts'), ((inr (_,_))::kps').
        split_and !; try done; by constructor. } } }
Qed.

Lemma running_is_join m T e ks e1 e2 p :
  dom m = paths T ->
  rebuild m nil T e ->
  m !! (true::p) = Some (Running e1) ->
  m !! (false::p) = Some (Running e2) ->
  m !! p = Some (Paused ks) ->
  exists kts kps, T = fill_tctxs kts (Node Leaf Leaf) /\ follow_path (rev p) kts
             /\ e = fill_pctxs kps (fill_items ks (RunPar e1 e2)) /\ follow_path (rev p) kps.
Proof.
  intros.
  edestruct (running_is_join_aux nil m T e ks e1 e2 p) as (?&?&?&?&?&?); eauto 10.
  1-3:rewrite right_id_L //.
Qed.

Lemma rev_nil_inv {A} (p:list A) :
  rev p = nil ->
  p = nil.
Proof.
  intros Hf.
  apply (@f_equal _ _ length) in Hf.
  rewrite rev_length in Hf. by destruct p.
Qed.

Lemma leads_to_leaf_no_more p' p kts xs :
  follow_path p kts ->
  (p' ++ rev p ++ xs) ∈ paths_aux xs (fill_tctxs kts Leaf) ->
  p' = nil.
Proof.
  revert p xs. induction kts; simpl; intros p xs Hp Hl.
  { apply Forall2_nil_inv_r in Hp. subst. simpl in *.
    apply elem_of_singleton in Hl.
    apply app_eq_same_r in Hl. done. }
  { apply Forall2_cons_inv_r in Hp.
    destruct Hp as (b&p''&->&Hf&->).
    rename p'' into p. simpl in*.
    replace (p' ++ (rev p ++ [is_left a]) ++ xs) with (p' ++ rev p ++ (is_left a :: xs)) in Hl by rewrite -assoc_L //.
    assert (p' ++ rev p ++ is_left a :: xs ≠ xs).
    { rewrite cons_middle !assoc_L. apply app_eq_same_r'.
      rewrite !app_length cons_length. lia. }

    destruct a; simpl in *.
    { pose proof (in_paths_aux_node (p' ++ rev p) true xs (fill_tctxs kts Leaf) t).
      rewrite -assoc_L in H0. set_solver. }
    { pose proof (in_paths_aux_node (p' ++ rev p) false xs t (fill_tctxs kts Leaf)).
      rewrite -assoc_L in H0. set_solver. } }
Qed.

Lemma running_no_succ m T e e' p :
  dom m = paths T ->
  rebuild m nil T e ->
  m !! p = Some (Running e') ->
  forall b, (b::p) ∉ paths T.
Proof.
  intros Hd Hb Hp b X.
  eapply running_is_leaf in Hb; try done.
  destruct Hb as (kts&?&?&?&_). subst.
  pose proof (leads_to_leaf_no_more [b] (rev p) kts nil) as Z.
  rewrite right_id_L in Z. simpl in Z.
  rewrite rev_involutive in Z. naive_solver.
Qed.

Lemma step_fill_items ks e σ e' σ' :
  step e σ e' σ' ->
  step (fill_items ks e) σ (fill_items ks e') σ'.
Proof.
  induction ks; eauto using step.
Qed.

Lemma step_fills p kps e σ e' σ' :
  follow_path p kps ->
  step e σ e' σ' ->
  step (fill_pctxs kps e) σ (fill_pctxs kps e') σ'.
Proof.
  revert kps. induction p; intros  kps Hfp Hs.
  { apply Forall2_nil_inv_l in Hfp. subst. done. }
  { apply Forall2_cons_inv_l in Hfp.
    destruct Hfp as (x&?&?&?&?). subst. simpl.
    destruct x as [ (?&?) | (?&?)]; simpl in *; try congruence.
    apply step_fill_items.
    all:eauto using step_fill_items,step. }
Qed.

Lemma paths_fork pref p kts :
  follow_path p kts ->
  {[false :: rev p ++ pref]} ∪ ({[true :: rev p ++ pref]} ∪ paths_aux pref (fill_tctxs kts Leaf)) =
  paths_aux pref (fill_tctxs kts (Node Leaf Leaf)).
Proof.
  revert pref kts; induction p; intros pref kts E.
  { apply Forall2_nil_inv_l in E. subst. simpl. set_solver. }
  apply Forall2_cons_inv_l in E.
  destruct E as (k&kts'&?&?&?). subst. simpl.
  replace ((rev p ++ [is_left k]) ++ pref) with (rev p ++ is_left k::pref) by rewrite -assoc_L //.
  destruct k; simpl; rewrite -IHp //; set_solver.
Qed.

Lemma cons_not_same {A} x (xs:list A) :
  x::xs ≠ xs.
Proof.
  intros E. apply (@f_equal _ _ length) in E.
  simpl in E. lia.
Qed.

Lemma is_val_fill_items ks e:
  is_val (fill_items ks e) ->
  ks = nil /\ is_val e.
Proof.
  intros. destruct ks; try done. elim_ctx.
Qed.

Lemma is_val_fill_pctxs ks e:
  is_val (fill_pctxs ks e) ->
  ks = nil /\ is_val e.
Proof.
  intros Hv. destruct ks as [| [ (?&?) | (?&?) ]]; try done; simpl in *.
  all:apply is_val_fill_items in Hv; naive_solver.
Qed.

Lemma fill_items_par_inv ks e1 e2 ks' e1' e2' :
  fill_items ks (RunPar e1 e2) = fill_items ks' (RunPar e1' e2') ->
  ks=ks' /\ e1=e1' /\ e2=e2'.
Proof.
  revert ks'; induction ks; intros ks'; intros Eq.
  { destruct ks'. naive_solver. elim_ctx. }
  { destruct ks'. elim_ctx. simpl in *.
    apply fill_item_inj in Eq. naive_solver.
    all:intros E; apply is_val_fill_items in E; naive_solver. }
Qed.

Lemma rebuild_rem_insert_not_in p xs T e m a :
  p ∉ paths_aux xs T ->
  rebuild m xs T e ->
  rebuild (<[p:=a]>m) xs T e.
Proof.
  revert xs e; induction T; intros xs e Hp Hr.
  { inversion Hr; subst. constructor.
    rewrite lookup_insert_ne //. set_solver. }
  { inversion Hr; subst.
    constructor. rewrite lookup_insert_ne //. set_solver.
    all:set_solver. }
Qed.

Lemma rebuild_delete_not_in p xs T e m :
  p ∉ paths_aux xs T ->
  rebuild m xs T e ->
  rebuild (delete p m) xs T e.
Proof.
  revert xs e; induction T; intros xs e Hp Hr.
  { inversion Hr; subst. constructor.
    rewrite lookup_delete_ne //. set_solver. }
  { inversion Hr; subst.
    constructor. rewrite lookup_delete_ne //. set_solver.
    all:set_solver. }
Qed.

Local Lemma suffix_special_case {A} (x1 x2:A) (xs ys:list A):
  x1 :: xs `suffix_of` ys ++ x2 :: xs ->
  x1 = x2.
Proof.
  intros E.
  rewrite cons_middle assoc_L in E.
  replace (x1 :: xs) with (([] ++ [x1]) ++ xs) in E by done.
  apply suffix_app_inv, suffix_snoc_inv_1 in E. done.
Qed.

Lemma rebuild_fork p ks e1 e2 m kts kps xs :
  follow_path p kts ->
  follow_path p kps ->
  rebuild m xs (fill_tctxs kts Leaf) (fill_pctxs kps (fill_items ks (Par e1 e2))) ->
  rebuild
    (<[false :: rev p ++ xs:=Running e2]> (<[true :: rev p ++ xs:=Running e1]> (<[rev p ++ xs:=Paused ks]> m)))
    xs
    (fill_tctxs kts (Node Leaf Leaf))
    (fill_pctxs kps (fill_items ks (RunPar e1 e2))).
Proof.
  revert xs kts kps. induction p; simpl; intros xs kts kps E1 E2 Hr.
  { apply Forall2_nil_inv_l in E1,E2. subst. simpl in *.
    constructor.
    { do 2 (rewrite lookup_insert_ne; last apply cons_not_same).
      rewrite lookup_insert //. }
    { constructor. rewrite lookup_insert_ne //.
      rewrite lookup_insert //. }
    { constructor. rewrite lookup_insert //. } }
  { apply Forall2_cons_inv_l in E1,E2.
    destruct E1 as (kt&kts'&->&E1&->).
    destruct E2 as (kp&kps'&X&E2&->). simpl in *.
    rewrite -assoc_L.
    destruct kt as [ T | T ], kp as [ [ks' e'] | [ks' e'] ]; simpl in *; try congruence.
    { inversion Hr; subst.
      apply fill_items_par_inv in H1. destruct H1 as (?&?&?). subst.
      constructor; eauto.
      { rewrite !cons_middle !assoc_L !lookup_insert_ne //.
        all:try rewrite app_comm_cons.
        all:apply app_eq_same_r'; rewrite ?cons_length !app_length; simpl; lia. }
      { apply rebuild_rem_insert_not_in.
        { intros E. apply elem_of_paths_aux in E.
          rewrite app_comm_cons in E.
          apply suffix_special_case in E. congruence. }
        apply rebuild_rem_insert_not_in.
        { intros E. apply elem_of_paths_aux in E.
          rewrite app_comm_cons in E.
          apply suffix_special_case in E. congruence. }
        apply rebuild_rem_insert_not_in.
        { intros E. apply elem_of_paths_aux in E.
          apply suffix_special_case in E. congruence. }
        done. } }
    (* ugly copy/pasta *)
    { inversion Hr; subst.
      apply fill_items_par_inv in H1. destruct H1 as (?&?&?). subst.
      constructor; eauto.
      { rewrite !cons_middle !assoc_L !lookup_insert_ne //.
        all:try rewrite app_comm_cons.
        all:apply app_eq_same_r'; rewrite ?cons_length !app_length; simpl; lia. }
      { apply rebuild_rem_insert_not_in.
        { intros E. apply elem_of_paths_aux in E.
          rewrite app_comm_cons in E.
          apply suffix_special_case in E. congruence. }
        apply rebuild_rem_insert_not_in.
        { intros E. apply elem_of_paths_aux in E.
          rewrite app_comm_cons in E.
          apply suffix_special_case in E. congruence. }
        apply rebuild_rem_insert_not_in.
        { intros E. apply elem_of_paths_aux in E.
          apply suffix_special_case in E. congruence. }
        done. } } }
Qed.

Lemma rebuild_join m xs kts kps ks (v1 v2:val) p :
  follow_path p kts ->
  follow_path p kps ->
  rebuild m xs (fill_tctxs kts (Node Leaf Leaf)) (fill_pctxs kps (fill_items ks (RunPar v1 v2))) ->
  rebuild
    (<[rev p ++ xs:=Running (fill_items ks (VPair v1 v2))]>
       (delete (false :: rev p ++ xs) (delete (true :: rev p ++ xs) m))) xs
    (fill_tctxs kts Leaf) (fill_pctxs kps (fill_items ks (VPair v1 v2))).
Proof.
  revert xs kts kps. induction p; simpl; intros xs kts kps E1 E2 Hr.
  { apply Forall2_nil_inv_l in E1,E2. subst. simpl in *.
    constructor. rewrite lookup_insert //. }
  { apply Forall2_cons_inv_l in E1,E2.
    destruct E1 as (kt&kts'&->&E1&->).
    destruct E2 as (kp&kps'&X&E2&->). simpl in *.
    rewrite -assoc_L.
    destruct kt as [ T | T ], kp as [ [ks' e'] | [ks' e'] ]; simpl in *; try congruence.
    { inversion Hr; subst.
      apply fill_items_par_inv in H1. destruct H1 as (?&?&?). subst.
      constructor; eauto.
      { rewrite !lookup_insert_ne //.
        rewrite !lookup_delete_ne // app_comm_cons.
        all:rewrite  cons_middle assoc_L.
        all:apply app_eq_same_r'; rewrite ?cons_length !app_length; simpl; lia. }
      { apply rebuild_rem_insert_not_in.
        { intros E. apply elem_of_paths_aux in E.
          apply suffix_special_case in E. congruence. }
        apply rebuild_delete_not_in.
        { intros E. apply elem_of_paths_aux in E.
          rewrite app_comm_cons in E.
          apply suffix_special_case in E. congruence. }
        apply rebuild_delete_not_in.
        { intros E. apply elem_of_paths_aux in E.
          rewrite app_comm_cons in E.
          apply suffix_special_case in E. congruence. }
        done. } }
    (* XXX ugly copy/pasta *)
    { inversion Hr; subst.
      apply fill_items_par_inv in H1. destruct H1 as (?&?&?). subst.
      constructor; eauto.
      { rewrite !lookup_insert_ne //.
        rewrite !lookup_delete_ne // app_comm_cons.
        all:rewrite  cons_middle assoc_L.
        all:apply app_eq_same_r'; rewrite ?cons_length !app_length; simpl; lia. }
      { apply rebuild_rem_insert_not_in.
        { intros E. apply elem_of_paths_aux in E.
          apply suffix_special_case in E. congruence. }
        apply rebuild_delete_not_in.
        { intros E. apply elem_of_paths_aux in E.
          rewrite app_comm_cons in E.
          apply suffix_special_case in E. congruence. }
        apply rebuild_delete_not_in.
        { intros E. apply elem_of_paths_aux in E.
          rewrite app_comm_cons in E.
          apply suffix_special_case in E. congruence. }
        done. } } }
Qed.

Lemma paths_join xs p kts :
  follow_path p kts ->
  paths_aux xs (fill_tctxs kts (Node Leaf Leaf)) ∖ {[true :: rev p++xs]} ∖ {[false :: rev p++xs]} = paths_aux xs (fill_tctxs kts Leaf).
Proof.
  revert xs kts. induction p; intros xs kts Hf.
  { apply Forall2_nil_inv_l in Hf. subst. simpl.
    pose proof (cons_not_same true xs).
    pose proof (cons_not_same false xs).
    set_solver. }
  { apply Forall2_cons_inv_l in Hf. destruct Hf as (?&?&->&?&->).
    assert (forall b1 ys b2, b1 :: ys ++ [b2] ++ xs ≠ xs).
    { intros ???. rewrite app_comm_cons assoc_L.
      apply app_eq_same_r'. rewrite cons_length !app_length. lia. }
    simpl. destruct x; simpl.
    { rewrite -IHp //.
      assert (forall b1 ys, b1 :: ys ++ [true] ++ xs ∉ paths_aux (false :: xs) t).
      { intros ?? E. apply elem_of_paths_aux in E.
        rewrite app_comm_cons in E.
        apply suffix_special_case in E. congruence. }
      rewrite -!(assoc_L app). set_solver. }
    { rewrite -IHp //.
      assert (forall b1 ys, b1 :: ys ++ [false] ++ xs ∉ paths_aux (true :: xs) t).
      { intros ?? E. apply elem_of_paths_aux in E.
        rewrite app_comm_cons in E.
        apply suffix_special_case in E. congruence. }
      rewrite -!(assoc_L app). set_solver. } }
Qed.

Lemma follow_in_path_aux xs p kts :
  follow_path p kts ->
  rev p ++ xs ∈ paths_aux xs (fill_tctxs kts Leaf).
Proof.
  revert xs kts; induction p; intros xs kts Hf.
  { apply Forall2_nil_inv_l in Hf. subst. set_solver. }
  { apply Forall2_cons_inv_l in Hf.
    destruct Hf as (?&?&->&Hf&->).
    simpl. rewrite -assoc_L. simpl.
    specialize (IHp (is_left x::xs) _ Hf).
    destruct x; set_solver. }
Qed.

Lemma follow_in_path p kts :
  follow_path p kts ->
  rev p ∈ paths (fill_tctxs kts Leaf).
Proof.
  intros E.
  apply (follow_in_path_aux nil) in E.
  rewrite right_id_L // in E.
Qed.

Lemma rebuild_step_task p kts kps m xs e e' :
  follow_path p kts ->
  follow_path p kps ->
  rebuild m xs (fill_tctxs kts Leaf) (fill_pctxs kps e) ->
  rebuild (<[rev p ++ xs:=Running e']> m) xs (fill_tctxs kts Leaf) (fill_pctxs kps e').
Proof.
  revert xs kts kps. induction p; simpl; intros xs kts kps E1 E2 Hr.
  { apply Forall2_nil_inv_l in E1,E2. subst. simpl in *.
    constructor. rewrite lookup_insert //. }
  { apply Forall2_cons_inv_l in E1,E2.
    destruct E1 as (kt&kts'&->&E1&->).
    destruct E2 as (kp&kps'&X&E2&->). simpl in *.
    rewrite -assoc_L.
    destruct kt as [ T | T ], kp as [ [ks' e0] | [ks' e0] ]; simpl in *; try congruence.
    { inversion Hr; subst.
      apply fill_items_par_inv in H1. destruct H1 as (?&?&?). subst.
      constructor; eauto.
      { rewrite lookup_insert_ne //.
        rewrite cons_middle assoc_L.
        apply app_eq_same_r'. rewrite app_length. simpl. lia. }
      { apply rebuild_rem_insert_not_in; last done.
        intros E. apply elem_of_paths_aux in E.
        apply suffix_special_case in E. congruence. } }
    (* XXX ugly *)
    { inversion Hr; subst.
      apply fill_items_par_inv in H1. destruct H1 as (?&?&?). subst.
      constructor; eauto.
      { rewrite lookup_insert_ne //.
        rewrite cons_middle assoc_L.
        apply app_eq_same_r'. rewrite app_length. simpl. lia. }
      { apply rebuild_rem_insert_not_in; last done.
        intros E. apply elem_of_paths_aux in E.
        apply suffix_special_case in E. congruence. } } }
Qed.

End rebuild.
