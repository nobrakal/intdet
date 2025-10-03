From stdpp Require Import relations.

From iris.proofmode Require Import base proofmode.

From intdet.lang Require Import reducible atomic locations.
From intdet.angelic Require Import trees run.

Definition terminated x := is_val (cexpr x).

Section adequacy_pre.

Context `{seqlogGS Σ}.

Definition ignore {A:Type} P : unit -> A := fun _ => P.

Lemma goal_sound c :
  interp (cexpr c) (cstore c) ∗ goal ={⊤}=∗
  ⌜∃ c', rtc step' c c' /\ terminated c'⌝.
Proof.
  iIntros "(Hi&Hwp)".
  iRevert (c) "Hi".
  iAssert (ignore (∀ c, interp (cexpr c) (cstore c) ={⊤}=∗ ⌜∃ c' : config, rtc step' c c' ∧ terminated c'⌝) tt)%I with "[-]" as "?"; last by iFrame.
  iApply (least_fixpoint_ind with "[] Hwp").
  { apply run.goal_pre_mono'. }
  iModIntro. iIntros ([]). rewrite /run.goal_pre' /goal_pre /ignore.
  iIntros "Hwp". iIntros ([e σ])" Hi".
  destruct_decide (decide (is_val e)).
  { iPureIntro. exists (mk_config e σ). done. }
  { iMod ("Hwp" with "[%//][$]") as "(%e'&%σ'&%Hstep&Hi&[Hend _])".
    iMod ("Hend" $! (mk_config e' σ') with "[$]") as "(%c&%Hc1&%Hc2)".
    iPureIntro.  exists c. split; last done.
    apply rtc_l with (y := mk_config e' σ'). done. done. }
Qed.

Lemma ended_init_gives_goal (v:val) :
  yielded ([],[]) v -∗ goal.
Proof.
  iIntros "Hend".
  rewrite goal_unfold /goal_pre.
  iIntros (???) "Hi".
  iDestruct (interp_root with "[$][$]") as "%".
  exfalso. subst. naive_solver.
Qed.

End adequacy_pre.

Module Initialization.

  Definition seqlogΣ : gFunctors :=
    #[ invΣ;
       gen_heapΣ loc (list val);
       ghost_mapΣ path status ].

  Class seqlogPreG (Σ : gFunctors) :=
  { sl1 : invGpreS Σ;
    sl2 : gen_heapGpreS loc (list val) Σ;
    sl3 : ghost_mapG Σ path status }.

  #[global] Existing Instance sl1.
  #[local] Existing Instance sl2.
  #[local] Existing Instance sl3.

  Global Instance subG_seqlogPreG Σ :
    subG seqlogΣ Σ → seqlogPreG Σ.
  Proof. solve_inG. Qed.

  Global Instance intdetPreG_intdetΣ : seqlogPreG seqlogΣ.
  Proof. eauto with typeclass_instances. Qed.

  Lemma seqlog_init `{!seqlogPreG Σ, hinv:!invGS_gen HasLc Σ} e :
    ⊢ |==> ∃ hi : seqlogGS Σ, ⌜@iinvgs Σ hi = hinv⌝ ∗
    interp e ∅ ∗ running nil e.
  Proof.
    rewrite /interp.
    iMod (gen_heap_init ∅) as "[% (?&_)]".
    iMod (@ghost_map_alloc_empty _ path status _ _ _) as "[%γ1 ?]".
    iMod (ghost_map_insert nil (Running e) with "[$]") as "(?&?)". done.
    iExists (@SeqlogGS Σ hinv _ γ1 _).
    iFrame. iSplitR; first done. iExists Leaf. iPureIntro.
    split.
    { rewrite dom_insert_L //. }
    { constructor. done. }
  Qed.

End Initialization.

Import Initialization.

Lemma run_adequacy_open `{seqlogPreG Σ} e :
  (∀ `{!seqlogGS Σ}, ⊢ run e (fun _ => True))  ->
  exists c, rtc step' (init e) c /\ terminated c.
Proof.
  intros Hwp.
  eapply uPred.pure_soundness.
  apply (@step_fupdN_soundness_lc Σ _ _ _ 0 0).

  iIntros. simpl.
  iMod (seqlog_init e) as "[% (%Xeq&?&Hrun)]".

  iDestruct (Hwp $! ([],[]) with "[Hrun]") as "Hgoal". done.
  iSpecialize ("Hgoal" with "[]").
  { iIntros (?) "(?&_)". by iApply ended_init_gives_goal. }

  rewrite -Xeq.
  iMod (goal_sound (init e) with "[$]"). iFrame.
  iApply @fupd_mask_intro. done. eauto.
Qed.

Lemma run_adequacy e :
  (∀ `{!seqlogGS Σ}, ⊢ run e (fun _ => True))  ->
  exists c, rtc step' (init e) c /\ terminated c.
Proof.
  eauto using run_adequacy_open with typeclass_instances.
Qed.
