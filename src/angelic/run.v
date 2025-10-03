From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.base_logic.lib Require Export gen_heap ghost_map.
From iris.bi.lib Require Export fixpoint.

From intdet.lang Require Import invert_step.
From intdet.lang Require Export syntax semantics atomic.
From intdet.utils Require Import restrict.

From intdet.angelic Require Import trees.

Class seqlogGS (Σ:gFunctors) :=
  SeqlogGS {
      iinvgs : invGS_gen HasLc Σ;
      istore : gen_heapGS loc (list val) Σ; (* the store *)
      γsplit : gname;
      isplit : ghost_mapG Σ path status;
    }.

#[global] Existing Instance iinvgs.
#[global] Existing Instance istore.
#[global] Existing Instance isplit.

Section interp.

Context `{seqlogGS Σ}.

Definition interp e σ : iProp Σ :=
  ∃ T m, gen_heap_interp σ ∗ ghost_map_auth γsplit 1 m ∗ ⌜dom m = paths T /\ rebuild m nil T e⌝.

Definition running p e :=
  ghost_map_elem γsplit p (DfracOwn 1) (Running e).

Definition paused p ks :=
  ghost_map_elem γsplit p (DfracOwn 1) (Paused ks).

Lemma interp_run e' p e e0 σ :
  running p e -∗ interp e0 σ ==∗
  ∃ e0', interp e0' σ ∗ running p e' ∗ ⌜∀ σ1 σ2, step e σ1 e' σ2 -> step e0 σ1 e0' σ2⌝.
Proof.
  iIntros "Hr [%T [%m (Hs&Hm&(%Hdom&%Hbuild))]]".
  iDestruct (ghost_map_lookup with "Hm Hr") as "%".
  iMod (ghost_map_update (Running e') with "Hm Hr") as "(Hm&?)".
  iFrame. iPureIntro.
  edestruct (running_is_leaf m T e0) as (kts&kps&X1&X2&X3&X4); try done. subst.
  exists (fill_pctxs kps e'). split.
  { exists (fill_tctxs kts Leaf). split.
    { rewrite dom_insert_lookup_L //. }
    { eapply rebuild_step_task in Hbuild; try done.
      rewrite rev_involutive right_id_L // in Hbuild. } }
  { intros. eauto using step_fills. }
Qed.

Lemma interp_fork p ks e1 e2 e σ :
  running p (fill_items ks (Par e1 e2)) -∗
  interp e σ ==∗
  running (true::p) e1 ∗ running (false::p) e2 ∗ paused p ks ∗
  ∃ e', interp e' σ ∗ ⌜step e σ e' σ⌝.
Proof.
  iIntros "Hr [%T [%m (Hs&Hm&(%Hdom&%Hbuild))]]".
  iDestruct (ghost_map_lookup with "Hm Hr") as "%".
  iMod (ghost_map_update (Paused ks) with "Hm Hr") as "(Hm&?)".
  iMod (ghost_map_insert (true::p) (Running e1) with "Hm") as "(Hm&?)".
  { apply not_elem_of_dom. rewrite dom_insert_lookup_L //.
    rewrite Hdom. eauto using running_no_succ. }
  iMod (ghost_map_insert (false::p) (Running e2) with "Hm") as "(?&?)".
  { apply not_elem_of_dom. rewrite dom_insert_L. rewrite dom_insert_lookup_L //.
    apply not_elem_of_union. split. set_solver.
    rewrite Hdom. eauto using running_no_succ. }
  iFrame.
  do 2 rewrite dom_insert_L. rewrite dom_insert_lookup_L //.

  iFrame. iModIntro. iPureIntro. simpl.

  edestruct (running_is_leaf m T e) as (kts&kps&X1&X2&X3&X4); try done. subst.
  exists (fill_pctxs kps (fill_items ks (RunPar e1 e2))). split.
  { exists (fill_tctxs kts (Node Leaf Leaf)). split.
    { apply (paths_fork nil) in X2.
      rewrite right_id_L rev_involutive // in X2. rewrite Hdom //. }
    { eapply (rebuild_fork (rev p)) in Hbuild; try done.
      rewrite rev_involutive right_id_L // in Hbuild. } }
  { eapply step_fills; try done.
    eauto using step,step_fill_items,head_step. }
Qed.

Lemma interp_join p ks (v1 v2:val) e σ :
  running (true::p) v1 ∗ running (false::p) v2 ∗ paused p ks -∗
  interp e σ ==∗
  running p (fill_items ks (VPair v1 v2)) ∗
  ∃ e', interp e' σ ∗ ⌜step e σ e' σ⌝.
Proof.
  iIntros "(E1&E2&EP) [%T [%m (Hs&Hm&(%Hdom&%Hbuild))]]".
  iDestruct (ghost_map_lookup with "Hm E1") as "%R1".
  iDestruct (ghost_map_lookup with "Hm E2") as "%R2".
  iDestruct (ghost_map_lookup with "Hm EP") as "%".

  iMod (ghost_map_delete with "Hm E1") as "Hm".
  iMod (ghost_map_delete with "Hm E2") as "Hm".

  iMod (ghost_map_update (Running (fill_items ks (VPair v1 v2))) with "Hm EP") as "(?&?)". iFrame.
  iModIntro. iPureIntro. simpl.

  edestruct (running_is_join m T e) as (kts&kps&X1&X2&X3&X4); try done.
  subst.
  exists (fill_pctxs kps (fill_items ks (VPair v1 v2))). split.
  { exists (fill_tctxs kts Leaf). split.
    { rewrite dom_insert_L !dom_delete_L Hdom.
      pose proof (paths_join nil (rev p) kts) as X.
      rewrite rev_involutive right_id_L in X. rewrite X //.
      apply follow_in_path in X2. rewrite rev_involutive in X2.
      set_solver. }
    { eapply rebuild_join in Hbuild; eauto.
      rewrite rev_involutive right_id_L // in Hbuild. } }
  { eapply step_fills; try done. eauto using step,step_fill_items,head_step. }
Qed.

Lemma interp_root e e' σ :
  running [] e  -∗
  interp e' σ -∗
  ⌜e'=e⌝.
Proof.
  iIntros "E [%T [%m (Hs&Hm&(%Hdom&%Hbuild))]]".
  iDestruct (ghost_map_lookup with "Hm E") as "%R".

  inversion Hbuild; subst.
  2:{ exfalso. rewrite H0 in R. inversion R. }
  iPureIntro. naive_solver.
Qed.

End interp.

Definition goal_pre `{seqlogGS Σ} (goal:iPropO Σ) : iPropO Σ :=
   (∀ e σ, ⌜¬ is_val e⌝ -∗ interp e σ ={⊤}=∗ ∃ e' σ',
       ⌜step e σ e' σ'⌝ ∗ interp e' σ' ∗ goal)%I.

Section goal.

Context `{seqlogGS Σ}.

Local Lemma goal_pre_mono (wp1 wp2 : iProp Σ) :
  ⊢ □ (wp1 -∗ wp2) → goal_pre wp1 -∗ goal_pre wp2.
Proof.
  iIntros "HX". rewrite /goal_pre.
  iIntros "Hwp" (e σ) "??". iMod ("Hwp" with "[$][$]") as "(%&%&?&?&?)".
  iFrame. by iApply "HX".
Qed.

Local Definition goal_pre' : (unitO → iPropO Σ) → unitO → iPropO Σ :=
  fun wp _ => goal_pre (wp tt).

Local Instance goal_pre_mono' : BiMonoPred goal_pre'.
Proof.
  constructor.
  { iIntros (wp1 wp2 ??) "#H". iIntros ([]).
    iApply goal_pre_mono. iModIntro. iApply "H". }
  { intros wp Hwp n [] [] _. reflexivity. }
Qed.

Definition goal : iProp Σ := bi_least_fixpoint goal_pre' tt.

Lemma goal_unfold :
  goal ⊣⊢ goal_pre goal.
Proof. rewrite {1}/goal least_fixpoint_unfold //. Qed.

Lemma to_val_Some e v :
  to_val e = Some v ->
  e = v.
Proof. destruct e; naive_solver. Qed.

Local Ltac startproof :=
  iIntros "Hr Hwp";
  iApply goal_unfold; rewrite /goal_pre;
  iIntros (e0 σ) "%Hv Hi".

Local Ltac conclude :=
  iModIntro; iExists _,_; iFrame;
  eauto 10 using step_fill_items, step, head_step.

Local Ltac endproof :=
  iMod (interp_run with "[$][$]") as "[% (?&?&%Hpropagate)]";
  iSpecialize ("Hwp" with "[$]").

Local Ltac doproof := startproof; endproof; conclude.

Lemma goal_let_val p ks x (v:val) e :
  running p (fill_items ks (Let x v e)) -∗
  (running p (fill_items ks (subst' x v e)) -∗ goal) -∗
  goal.
Proof. doproof. Qed.

Lemma goal_if p ks (b:bool) e1 e2 :
  running p (fill_items ks (If b e1 e2)) -∗
  (running p (fill_items ks (if b then e1 else e2)) -∗ goal) -∗
  goal.
Proof. doproof. Qed.

Lemma goal_code p ks self arg code :
  running p (fill_items ks (Code self arg code)) -∗
  (running p (fill_items ks (VCode self arg code)) -∗ goal) -∗
  goal.
Proof. doproof. Qed.

Lemma goal_call_prim x (v1 v2 v:val) p ks :
  eval_call_prim x v1 v2 = Some v ->
  running p (fill_items ks (CallPrim x v1 v2)) -∗
  (running p (fill_items ks v) -∗ goal) -∗
  goal.
Proof. intros. doproof. Qed.

Lemma goal_call p ks vs self args body :
  running p (fill_items ks (Call (VCode self args body) (Val vs))) -∗
  (running p (fill_items ks (substs' [(self,VCode self args body); (args,vs)] body)) -∗ goal) -∗
  goal.
Proof. doproof. Qed.

Lemma goal_fork p ks e1 e2 :
  (running (true::p) e1 -∗ running (false::p) e2 -∗ paused p ks -∗ goal) -∗
  running p (fill_items ks (Par e1 e2)) -∗ goal.
Proof.
  iIntros "Hwp Hr".
  iApply goal_unfold. rewrite /goal_pre.
  iIntros (e σ) "%Hv Hi".
  iMod (interp_fork with "[$][$]") as "(?&?&?&[% (?&%)])".
  iModIntro. iExists _,_.
  iSplit. iPureIntro. done.
  iFrame.
  iApply ("Hwp" with "[$][$][$]").
Qed.

Lemma goal_join p ks (v1 v2:val) :
  (running p (fill_items ks (VPair v1 v2)) -∗ goal) -∗
  (running (true::p) v1 -∗ running (false::p) v2 -∗ paused p ks -∗ goal).
Proof.
  iIntros "Hwp E1 E2 EP".
  iApply goal_unfold. rewrite /goal_pre.
  iIntros (e σ) "%Hv Hi".
  iMod (interp_join with "[$] Hi") as "(?&[% (?&%)])".
  iModIntro. iExists _,_.
  iSplit. iPureIntro. done.
  iFrame.
  iApply ("Hwp" with "[$]").
Qed.

Lemma interp_alloc l v e σ :
  l ∉ dom σ ->
  interp e σ ==∗
  interp e (<[l:=v]>σ) ∗ pointsto l (DfracOwn 1) v.
Proof.
  iIntros (Hl) "[% [% (?&?)]]".
  iMod (gen_heap_alloc with "[$]") as "(?&?&_)".
  by eapply not_elem_of_dom.
  by iFrame.
Qed.

Lemma interp_lookup e σ l q vs:
  pointsto l q vs -∗
  interp e σ -∗
  ⌜σ !! l = Some vs⌝.
Proof.
  iIntros "Hl [% [% (?&?)]]".
  iApply (gen_heap_valid with "[$][$]").
Qed.

Lemma interp_store i v e σ l vs:
  (0 ≤ i < length vs)%Z ->
  pointsto l (DfracOwn 1) vs -∗
  interp e σ ==∗
  interp e  (<[l:=<[Z.to_nat i:=v]> vs]> σ) ∗ pointsto l (DfracOwn 1) (<[Z.to_nat i:=v]>vs).
Proof.
  iIntros (?) "Hl [% [% (?&?)]]".
  iMod (gen_heap_update with "[$][$]") as "(?&Hl)".
  by iFrame.
Qed.

Lemma goal_alloc (i:Z) p ks :
  (0 <= i)%Z ->
  running p (fill_items ks (Alloc i)) -∗
  (∀ (l:loc), pointsto l (DfracOwn 1) (replicate (Z.to_nat i) VUnit) -∗
              running p (fill_items ks l) -∗ goal) -∗
  goal.
Proof.
  iIntros (?) "Hrun Hwp".
  iApply goal_unfold. rewrite /goal_pre.
  iIntros (e σ) "%Hv Hi".

  iMod (interp_run (fill_items ks (VLoc (fresh (dom σ)))) with "[$][$]") as "[% (?&?&%Hpropagate)]".

  iMod (interp_alloc with "[$]") as "(?&?)". by apply is_fresh.
  iModIntro.
  iSpecialize ("Hwp" with "[$][$]").
  iExists _,_. iFrame.
  iPureIntro.
  eapply Hpropagate, step_fill_items. constructor.
  constructor. done. apply is_fresh. done.
Qed.

Lemma goal_load (l:loc) (i:Z) (v:val) vs q p ks :
  (0 ≤ i < length vs)%Z ->
  vs !! Z.to_nat i = Some v ->
  pointsto l q vs -∗
  running p (fill_items ks (Load l i)) -∗
  (pointsto l q vs -∗ running p (fill_items ks v) -∗ goal) -∗
   goal.
Proof.
  iIntros (??) "Hl". startproof.

  iMod (interp_run (fill_items ks v) with "[$][$]") as "[% (?&?&%Hpropagate)]".

  iDestruct (interp_lookup with "[$][$]") as "%".
  iSpecialize ("Hwp" with "[$][$]").
  conclude.
Qed.

Lemma goal_length (l:loc) vs q p ks :
  pointsto l q vs -∗
  running p (fill_items ks (Length l)) -∗
  (pointsto l q vs -∗ running p (fill_items ks (length vs)) -∗ goal) -∗
   goal.
Proof.
  iIntros "Hl". startproof.

  iMod (interp_run (fill_items ks _) with "[$][$]") as "[% (?&?&%Hpropagate)]".

  iDestruct (interp_lookup with "[$][$]") as "%".
  iSpecialize ("Hwp" with "[$][$]").
  conclude.
Qed.

Lemma goal_assert p ks :
  running p (fill_items ks (Assert (VBool true))) -∗
  (running p (fill_items ks VUnit) -∗ goal) -∗
  goal.
Proof. doproof. Qed.

Lemma goal_store (l:loc) (i:Z) (v:val) vs p ks :
  (0 ≤ i < length vs)%Z ->
  pointsto l (DfracOwn 1) vs -∗
  running p (fill_items ks (Store l i v)) -∗
  (pointsto l (DfracOwn 1) (<[Z.to_nat i:=v]>vs) -∗
   running p (fill_items ks VUnit) -∗ goal) -∗
  goal.
Proof.
  iIntros (?) "Hl Hrun Hwp".
  iApply goal_unfold. rewrite /goal_pre.
  iIntros (e σ) "%Hv Hi".

  iMod (interp_run (fill_items ks VUnit) with "[$][$]") as "[% (?&?&%Hpropagate)]".

  iDestruct (interp_lookup with "[$][$]") as "%".
  iMod (interp_store with "[$][$]") as "(?&?)". done.
  iSpecialize ("Hwp" with "[$][$]").
  conclude.
Qed.

Lemma goal_cas (l:loc) (i:Z) (v0 v v':val) vs p ks :
  (0 ≤ i < length vs)%Z ->
  vs !! Z.to_nat i = Some v0 ->
  pointsto l (DfracOwn 1) vs -∗
  running p (fill_items ks (CAS l i v v')) -∗
  (pointsto l (DfracOwn 1) (if bool_decide (v0 = v) then <[Z.to_nat i := v']>vs else vs) -∗
   running p (fill_items ks (bool_decide (v0 = v))) -∗ goal) -∗
  goal.
Proof.
  iIntros (??) "Hl Hrun Hwp".
  iApply goal_unfold. rewrite /goal_pre.
  iIntros (e σ) "%Hv Hi".

  iMod (interp_run (fill_items ks (bool_decide (v0 = v))) with "[$][$]") as "[% (?&?&%Hpropagate)]".

  iDestruct (interp_lookup with "[$][$]") as "%".
  case_bool_decide.
  { iMod (interp_store with "[$][$]") as "(?&?)". done.
    iSpecialize ("Hwp" with "[$][$]").
    iModIntro. iExists _,_. iFrame.
    iPureIntro. apply Hpropagate.
    apply step_fill_items.
    constructor.
    replace true with (bool_decide (v0=v)) by rewrite bool_decide_eq_true_2 //.
    eapply HeadCAS; try done. rewrite bool_decide_eq_true_2 //. }
  { iSpecialize ("Hwp" with "[$][$]").
    iModIntro. iExists _,_. iFrame.
    iPureIntro. apply Hpropagate.
    apply step_fill_items.
    constructor.
    replace false with (bool_decide (v0=v)) by rewrite bool_decide_eq_false_2 //.
    eapply HeadCAS; try done. rewrite bool_decide_eq_false_2 //. }
Qed.

Lemma goal_fst (v1 v2:val)  p ks :
  running p (fill_items ks (Fst (VPair v1 v2))) -∗
  (running p (fill_items ks v1) -∗ goal) -∗
  goal.
Proof. doproof. Qed.

Lemma goal_snd (v1 v2:val)  p ks :
  running p (fill_items ks (Snd (VPair v1 v2))) -∗
  (running p (fill_items ks v2) -∗ goal) -∗
  goal.
Proof. doproof. Qed.

Lemma goal_pair (v1 v2:val)  p ks :
  running p (fill_items ks (Pair v1 v2)) -∗
  (running p (fill_items ks (VPair v1 v2)) -∗ goal) -∗
  goal.
Proof. doproof. Qed.

(* Yield and Run *)


(* The story is with two proof mode:
   * The "scheduler" mode, where the goal is [goal],
   that allows the user to run any yielded task.
   * The "run" mode, looking like a WP, that is focused on one task.
   This task can "yield" at any point, and go back
   to the scheduler mode.

   In fact, I wrote "task" but I mean "subtask", ie,
   any subexpression of a task. A "task identifier"
   is the pair of a path in the task tree and a list of evaluation
   contexts, identifying the subtask.
   In particular, yielding, running, and yielding again will lead to
   two different task ids (from the pov of the user). *)

Definition tid : Type := (path * list ctx).
Definition yielded (π:tid) e := running (fst π) (fill_items (snd π) e).

Definition run e Q : iProp Σ :=
  ∀ π, yielded π e -∗ (∀ (v:val), yielded π v ∗ Q v  -∗ goal) -∗ goal.

Lemma run_mono e Q1 Q2 :
  run e Q1 -∗
  (∀ v, Q1 v -∗ Q2 v) -∗
  run e Q2.
Proof.
  iIntros "Hrun HQ". iIntros (π) "X1 X2".
  iApply ("Hrun" with "X1"). iIntros (?) "(?&?)".
  iApply "X2". iFrame. by iApply "HQ".
Qed.

Lemma yield_subtask e Q :
  (∀ π, yielded π e -∗ (∀ (v:val), yielded π v ∗ Q v  -∗ goal) -∗ goal) -∗
  run e Q.
Proof. iIntros "?". iFrame. Qed.

Lemma resume_subtask π e :
  yielded π e -∗
  run e (fun v => yielded π v -∗ goal) -∗
  goal.
Proof.
  iIntros "His Hrun".
  iSpecialize ("Hrun" $! (_, _) with "His").
  iApply "Hrun". iIntros (?) "(Hr&Hv)".
  iApply "Hv". done.
Qed.

Definition goleft '((p,ks) : tid) : tid := (true::p,nil).
Definition goright '((p,ks) : tid) : tid := (false::p,nil).

Lemma fork e1 e2 Q :
  (∀ π, yielded (goleft π) e1 -∗ yielded (goright π) e2 -∗ (∀ (v1 v2:val), yielded (goleft π) v1 ∗ yielded (goright π) v2 ∗ Q (VPair v1 v2) -∗ goal) -∗ goal) -∗
  run (Par e1 e2) Q.
Proof.
  iIntros "Hwait". iIntros (π) "Hr Hended".
  iApply (goal_fork with "[-Hr][$]").
  iIntros "Hr1 Hr2 Hp".
  iSpecialize ("Hwait" $! (fst π, snd π) with "[$][$]").
  iApply "Hwait". iIntros (v1 v2) "(E1&E2&E3)". simpl.
  iApply (goal_join with "[Hended E3][$][$][$]"). iIntros.
  iApply ("Hended" with "[$]").
Qed.

(* For show off *)
Lemma run_par_seql e1 e2 Q :
  run e1 (fun v1 => run e2 (fun v2 => Q (VPair v1 v2))) -∗
  run (Par e1 e2) Q.
Proof.
  iIntros "Hrun". iApply fork. iIntros (?) "E1 E2 Hq".
  iApply (resume_subtask with "E1").
  iApply (run_mono with "Hrun").
  iIntros (v) "Hrun Hy1".
  iApply (resume_subtask with "E2").
  iApply (run_mono with "Hrun").
  iIntros (?) "? ?". iApply "Hq". iFrame.
Qed.

Lemma run_par_seqr e1 e2 Q :
  run e2 (fun v2 => run e1 (fun v1 => Q (VPair v1 v2))) -∗
  run (Par e1 e2) Q.
Proof.
  iIntros "Hrun". iApply fork. iIntros (?) "E1 E2 Hq".
  iApply (resume_subtask with "E2").
  iApply (run_mono with "Hrun").
  iIntros (v2) "Hrun Hy1".
  iApply (resume_subtask with "E1").
  iApply (run_mono with "Hrun").
  iIntros (v1) "? ?". iApply "Hq". iFrame.
Qed.

Lemma run_call self args body vs Q :
  run (substs' [(self,VCode self args body); (args,vs)] body) Q -∗
  run (Call (VCode self args body) (Val vs)) Q.
Proof.
  iIntros "Hrun".
  iIntros (π) "Hr Hended".
  iApply (goal_call with "[$]").
  iIntros "X". by iApply ("Hrun" with "X").
Qed.

Lemma run_let_val x (v:val) e Q :
  run (subst' x v e) Q -∗
  run (Let x v e) Q.
Proof.
  iIntros "Hrun".
  iIntros (π) "Hr Hended".
  iApply (goal_let_val with "[$]").
  iIntros "X". by iApply ("Hrun" with "X").
Qed.

Lemma run_if (b:bool) e1 e2 Q :
  run (if b then e1 else e2) Q -∗
  run (If b e1 e2) Q.
Proof.
  iIntros "Hrun".
  iIntros (π) "Hr Hended".
  iApply (goal_if with "[$]").
  iIntros "X". by iApply ("Hrun" with "X").
Qed.

Lemma run_code self arg code Q :
  run (VCode self arg code) Q -∗
  run (Code self arg code) Q.
Proof.
  iIntros "Hrun".
  iIntros (π) "Hr Hended".
  iApply (goal_code with "[$]").
  iIntros "X". by iApply ("Hrun" with "X").
Qed.

Lemma run_bind K e Q :
  run e (fun v => run (fill_item K v) Q) -∗
  run (fill_item K e) Q.
Proof.
  iIntros "Hrun".
  iIntros (π) "Hr Hended". destruct π as (p,ks).
  unfold yielded. simpl.
  rewrite -(fill_items_app _ [_]).
  iApply ("Hrun" $! (_,(ks ++ [K])) with "[$]").
  iIntros (v) "(?&Hrun)". unfold yielded. simpl.
  rewrite fill_items_app.
  iApply ("Hrun" $! (_,_) with "[$]"). done.
Qed.

Lemma run_val (v:val) Q :
  Q v -∗
  run v Q.
Proof.
  iIntros "HQ".
  iIntros (π) "Hr Hended". destruct π as (p,ks).
  unfold yielded. simpl in *.
  iApply "Hended". iFrame.
Qed.

Lemma run_alloc (i:Z) :
  (0 <= i)%Z ->
  ⊢ run (Alloc i) (fun v => ∃ (l:loc), ⌜v=VLoc l⌝ ∗  pointsto l (DfracOwn 1) (replicate (Z.to_nat i) VUnit))%I.
Proof.
  iIntros (?).
  iIntros (π) "Hr Hended". destruct π as (p,ks).
  unfold yielded. simpl.
  iApply (goal_alloc with "[$]"). done.
  iIntros. iApply "Hended". by iFrame.
Qed.

Lemma run_load (l:loc) (i:Z) (v:val) vs q :
  (0 ≤ i < length vs)%Z ->
  vs !! Z.to_nat i = Some v ->
  pointsto l q vs -∗
  run (Load l i) (fun w => ⌜w=v⌝ ∗ pointsto l q vs).
Proof.
  iIntros (??) "Hl".
  iIntros (π) "Hr Hended".
  iApply (goal_load with "[$][$]"). 1,2:done.
  iIntros. iApply "Hended". by iFrame.
Qed.

Lemma run_length (l:loc) vs q :
  pointsto l q vs -∗
  run (Length l) (fun w => ⌜w=VInt (length vs)⌝ ∗ pointsto l q vs).
Proof.
  iIntros "Hl".
  iIntros (π) "Hr Hended".
  iApply (goal_length with "[$][$]").
  iIntros. iApply "Hended". by iFrame.
Qed.

Lemma run_assert b :
  b = true ->
  ⊢ run (Assert (VBool b)) (fun w => ⌜w=VUnit⌝).
Proof.
  iIntros (-> π) "Hr Hended".
  iApply (goal_assert with "[$]").
  iIntros. iApply "Hended". by iFrame.
Qed.

Lemma run_store (l:loc) (i:Z) (v:val) vs :
  (0 ≤ i < length vs)%Z ->
  pointsto l (DfracOwn 1) vs -∗
  run (Store l i v) (fun w => ⌜w=VUnit⌝ ∗ pointsto l (DfracOwn 1) (<[Z.to_nat i:=v]>vs)).
Proof.
  iIntros (?) "Hl".
  iIntros (π) "Hr Hended".
  iApply (goal_store with "[$][$]"). done.
  iIntros. iApply "Hended". by iFrame.
Qed.

Lemma run_call_prim p v1 v2 v :
  eval_call_prim p v1 v2 = Some v ->
  ⊢ run (CallPrim p v1 v2) (fun v' => ⌜v'=v⌝).
Proof.
  iIntros (?).
  iIntros (π) "Hr Hended".
  iApply (goal_call_prim with "[$]"). done.
  iIntros. iApply "Hended". by iFrame.
Qed.

Lemma run_fst (v1 v2:val) :
  ⊢ run (Fst (VPair v1 v2)) (fun w => ⌜w=v1⌝).
Proof.
  iIntros (π) "Hr Hended".
  iApply (goal_fst with "[$]").
  iIntros. iApply "Hended". by iFrame.
Qed.

Lemma run_snd (v1 v2:val) :
  ⊢ run (Snd (VPair v1 v2)) (fun w => ⌜w=v2⌝).
Proof.
  iIntros (π) "Hr Hended".
  iApply (goal_snd with "[$]").
  iIntros. iApply "Hended". by iFrame.
Qed.

Lemma run_pair (v1 v2:val) :
  ⊢ run (Pair v1 v2) (fun w => ⌜w=VPair v1 v2⌝).
Proof.
  iIntros (π) "Hr Hended".
  iApply (goal_pair with "[$]").
  iIntros. iApply "Hended". by iFrame.
Qed.

Lemma run_cas (l:loc) (i:Z) vs (v0 v v':val) :
  (0 <= i < Z.of_nat (length vs))%Z ->
  vs !! (Z.to_nat i) = Some v0 ->
  pointsto l (DfracOwn 1) vs -∗
  run (CAS l i v v') (fun x => ⌜x=bool_decide (v0 = v)⌝ ∗ pointsto l (DfracOwn 1) (if bool_decide (v0 = v) then <[Z.to_nat i := v']>vs else vs)).
Proof.
  iIntros.
  iIntros (π) "Hr Hended".
  iApply (goal_cas with "[$][$]"). 1,2:try done.
  iIntros. iApply "Hended". by iFrame.
Qed.

End goal.
