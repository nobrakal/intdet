From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export gen_heap ghost_map.
From iris.program_logic Require Import weakestpre.
From iris.algebra Require Import gset gmap frac.

From intdet.utils Require Import more_cmras.
From intdet.lang Require Import reducible invert_step.
From intdet.lang Require Export semantics atomic locations.
From intdet.musketeer Require Import wpg ininj.

Class intdetGS (Σ : gFunctors) :=
  IntdetGS {
      iinvgs : invGS_gen HasNoLc Σ;
      istorel : gen_heapGS loc (list val) Σ; (* the left store *)
      γstorer : gname;                (* the right store *)
      istorer : ghost_mapG Σ loc (list val);
      iininj  : inInjG Σ;             (* the injection *)
    }.

#[global] Existing Instance iinvgs.
#[global] Existing Instance istorel.
#[global] Existing Instance istorer.
#[global] Existing Instance iininj.

Ltac destruct_interp Hi :=
  iDestruct Hi as "(Hσl&Hσr&Hinj)".

Section go.

Context `{intdetGS Σ}.

Definition interp (σl:store) (σr:store) : iProp Σ :=
    gen_heap_interp σl ∗
    ghost_map_auth γstorer 1%Qp σr ∗
    interp_inj (dom σl) (dom σr)
.

Definition pointstol l q (v:list val) := gen_heap.pointsto l q v.

Lemma interp_storel σl σr l v v' :
  interp σl σr ∗ pointstol l (DfracOwn 1) v ==∗
  interp (<[l:=v']>σl) σr ∗ pointstol l (DfracOwn 1) v'.
Proof.
  iIntros "(Hi&?)". destruct_interp "Hi".
  iDestruct (gen_heap_valid with "Hσl [$]") as "%".
  iMod (gen_heap_update with "[$][$]") as "(?&?)". iFrame.
  rewrite dom_insert_lookup_L //.
Qed.

Definition pointstor (l:loc) q (vs:list val) : iProp Σ :=
  ∃ lr vsl, ininj l lr ∗ ([∗ list] v;vl ∈ vs;vsl, vininj v vl) ∗ ghost_map_elem γstorer lr q vsl.

Lemma interp_storer (σl σr:store) l (v v':list val) :
  interp σl σr ∗ ghost_map_elem γstorer l (DfracOwn 1) v ==∗
  interp σl (<[l:=v']>σr) ∗ ghost_map_elem γstorer l (DfracOwn 1) v'.
Proof.
  iIntros "(Hi&Hl)". destruct_interp "Hi".
  iDestruct (ghost_map_lookup with "Hσr Hl") as "%".
  iMod (ghost_map_update with "Hσr [$]") as "(?&?)".
  iFrame. rewrite dom_insert_lookup_L //.
Qed.

Lemma interp_allocl l v σl σr :
  l ∉ dom σl ->
  interp σl σr ==∗
  interp (<[l:=v]> σl) σr ∗ pointstol l (DfracOwn 1) v ∗ waiting l ∗ meta_token l ⊤.
Proof.
  iIntros (?) "Hi".
  destruct_interp "Hi". iFrame.
  iMod (gen_heap_alloc with "[$]") as "(?&?&?)".
  by eapply not_elem_of_dom. iFrame.
  iMod (ininj_insert_waiting with "[$]") as "(?&?)". done.
  rewrite dom_insert_L //. by iFrame.
Qed.

Lemma interp_allocr l lr vr σl σr :
  lr ∉ dom σr ->
  interp σl σr ∗ waiting l ==∗
  interp σl (<[lr:=vr]> σr) ∗  ghost_map_elem γstorer lr (DfracOwn 1) vr ∗ ininj l lr.
Proof.
  iIntros (?) "(Hi&Hw)".
  destruct_interp "Hi".

  iMod (ghost_map_insert lr vr with "Hσr") as "(?&?)". by eapply not_elem_of_dom.
  iMod (ininj_insert_inj with "[$][$]") as "(?&?)". done.
  iFrame. iModIntro. rewrite dom_insert_L //.
Qed.

Lemma use_pointstol σl σr l q v :
  interp σl σr ∗ pointstol l q v -∗ ⌜σl !! l = Some v⌝.
Proof.
  iIntros "(Hi&Hl)".
  destruct_interp "Hi".
  iApply (gen_heap_valid with "Hσl Hl").
Qed.

Lemma use_pointstor a σr l q v :
  interp a σr ∗ l ↪[γstorer]{q} v -∗ ⌜σr !! l = Some v⌝.
Proof.
  iIntros "(Hi&Hl)".
  destruct_interp "Hi".
  iApply (ghost_map_lookup with "Hσr Hl").
Qed.

Lemma wpGSl : wpGS true Σ _ store (fun x σ => interp σ x) pointstol (fun l => waiting l ∗ meta_token l ⊤)%I ininj.
Proof.
  constructor; intros.
  { apply interp_storel. }
  { rewrite right_id. iIntros.
    iMod (interp_allocl with "[$]") as "(?&?&?&?)".
    done. by iFrame. }
  { apply use_pointstol. }
Qed.

Definition wpl E e Q : iProp Σ :=
  @wpg _ _ _ _ _ _ _ _ wpGSl E e Q.

Lemma wpGSr : wpGS false Σ _ store (fun x σ => interp x σ) (ghost_map_elem γstorer) waiting ininj.
Proof.
  constructor; intros.
  { apply interp_storer. }
  { by apply interp_allocr. }
  { apply use_pointstor. }
Qed.

Definition wpgr := @wpg _ _ _ _ _ _ _ _ wpGSr.

Definition wpr E e Q : iProp Σ :=
  (∀ e', eininj e e' -∗ wpgr E e' (fun v' => ∃ v, vininj v v' ∗ Q v)).

Lemma wpr_use_ininj P X E e Q :
  ¬ is_val e ->
  (∀ g1 g2, P -∗ interp_inj g1 g2 -∗ ⌜X⌝) -∗
  P ∗ (⌜X⌝-∗ wpgr E e Q) -∗ wpgr E e Q.
Proof.
  iIntros (Hv) "H (?&Hwp)".
  rewrite /wpr /wpgr wpg_unfold /wpg_pre.
  apply is_val_false in Hv. rewrite Hv.
  iIntros (??) "Hi". destruct_interp "Hi".
  iDestruct ("H" with "[$][$]") as "%".
  iApply "Hwp". done. iFrame.
Qed.

Lemma wpr_load E (l:loc) (i:Z) q vs v :
  (0 <= i < length vs)%Z ->
  vs !! (Z.to_nat i) = Some v ->
  pointstor l q vs -∗
  wpr E (Load l i) (fun v' => ⌜v'=v⌝ ∗ pointstor l q vs)%I.
Proof.
  iIntros (??) "Hl".
  iIntros (?) "#Hinj". simpl.
  destruct e'; try done.
  iDestruct "Hinj" as "(X1&X2)".
  destruct e'1; try done.
  destruct v0; try (iDestruct "X1" as "%"; congruence).
  destruct e'2; try done.
  iDestruct "X2" as "<-".
  iDestruct "Hl" as "[% [% (#?&#?&Hl)]]".
  iDestruct (ininj_partial_func l l0 lr with "[$][$]") as "%". subst.
  iDestruct (big_sepL2_length with "[$]") as "%".
  assert (is_Some (vsl !! Z.to_nat i)) as (?&?).
  { apply lookup_lt_is_Some_2. lia. }
  iDestruct (big_sepL2_lookup with "[$]") as "?". done. done.
  iApply (wpg_mono with "[Hl]").
  { iApply (wpg_load_r with "Hl"). lia. done. }
  iIntros (?) "(->&?)". by iFrame "#∗".
Qed.

Lemma wpr_store E l (i:Z) vs (v:val) :
  (0 <= i < length vs)%Z ->
  pointstor l (DfracOwn 1) vs -∗
  wpr E (Store l i v) (fun w => ⌜w=VUnit⌝ ∗ pointstor l (DfracOwn 1) (<[Z.to_nat i:=v]>vs)).
Proof.
  iIntros (?) "Hl". iIntros (?) "#Hinj".
  destruct e'; try done. simpl.
  iDestruct "Hinj" as "(Hinj&X&?)".
  destruct e'1; try done.
  destruct v0; try (iDestruct "Hinj" as "%"; congruence).
  destruct e'2; try done. iDestruct "X" as "<-".
  destruct e'3; try done.
  iDestruct "Hl" as "[% [% (#?&#?&Hl)]]".
  iDestruct (ininj_partial_func l l0 lr with "[$][$]") as "->".
  iDestruct (big_sepL2_length with "[$]") as "%".
  iApply (wpg_mono with "[Hl]").
  { iApply wpg_store; last done. eexists. split. done. lia. }
  assert (is_Some (vs !! Z.to_nat i)) as (?&?).
  { apply lookup_lt_is_Some_2. lia. }
  assert (is_Some (vsl !! Z.to_nat i)) as (?&?).
  { apply lookup_lt_is_Some_2. lia. }
  iIntros (?) "[% ((%Eq&->&_)&?)]". inversion Eq. subst.
  iExists VUnit. iFrame "#∗".
  iSplitR; first done. iSplitR; first done.
  iDestruct (big_sepL2_insert_acc with "[$]") as "(_&X)". 1,2:done.
  by iApply "X".
Qed.

Lemma big_sepL_replicate {A} (P:A -> iProp Σ) n x :
  □ P x -∗
  [∗ list] x ∈ replicate n x, P x.
Proof.
  iIntros. iInduction n as [] "IH". done.
  rewrite replicate_S big_sepL_cons. iFrame "#".
Qed.

Lemma wpr_alloc E l (n:Z) :
  (0 <= n)%Z ->
  waiting l -∗
  wpr E (Alloc n) (fun w => ⌜w=VLoc l⌝ ∗ pointstor l (DfracOwn 1) (replicate (Z.to_nat n) VUnit)).
Proof.
  iIntros (?) "Hl". iIntros (?) "#Hinj".
  destruct e'; try done. simpl. destruct e'; try done.
  iDestruct "Hinj" as "<-".
  iApply (wpg_mono with "[Hl]").
  { iApply wpg_alloc. eauto. done. }
  iIntros (?) "[%n' [%l' ((%Eq&->&_)&?&#?)]]".
  inversion Eq. subst n'.
  iExists l. iFrame "#∗". iSplitR; first done.
  iApply big_sepL2_replicate_l. rewrite replicate_length //.
  by iApply big_sepL_replicate.
Qed.

Lemma wpr_cas E (l:loc) (i:Z) vs (v v0 v':val)  :
  (0 <= i < Z.of_nat (length vs))%Z ->
  vs !! (Z.to_nat i) = Some v0 ->
  pointstor l (DfracOwn 1) vs -∗
  wpr E (CAS l i v v')
     (fun x => ⌜x=bool_decide (v0 = v)⌝ ∗ pointstor l (DfracOwn 1) (if bool_decide (v0 = v) then <[Z.to_nat i := v']>vs else vs)).
Proof.
  iIntros (??) "Hl". iIntros (?) "Hinj".
  destruct e'; try done. simpl.
  iDestruct "Hinj" as "(X1&X2&X3&X4)".
  destruct e'1; try done.
  destruct v1; try (iDestruct "X1" as "%"; congruence).
  destruct e'2; try done. iDestruct "X2" as "<-".
  destruct e'3; try done. destruct e'4; try done.
  iDestruct "Hl" as "[% [% (#?&#?&Hl)]]".
  iDestruct (ininj_partial_func l l0 lr with "[$][$]") as "->". subst.
  iDestruct (big_sepL2_length with "[$]") as "%".
  assert (is_Some (vsl !! Z.to_nat i)) as (?&?).
  { apply lookup_lt_is_Some_2. lia. }
  iDestruct (big_sepL2_insert_acc with "[$]") as "(#?&X)". 1,2:done.

  iApply wpr_use_ininj. naive_solver.
  { iIntros (??). iApply (vininj_preserves_eq v0 v x v1). done. }

  iFrame "#∗". iIntros "%X".
  iApply (wpg_mono with "[Hl]").
  { iApply wpg_cas; last done. lia. done. }
  iIntros (?) "(->&?)". iFrame "#∗".
  replace (bool_decide (x = v1)) with (bool_decide (v0 = v)).
  2:{ do 2 case_decide; naive_solver. }
  iExists (VBool _).
  do 2 (iSplitR; first done).
  case_bool_decide.
  { by iApply "X". }
  { rewrite -{3}(list_insert_id _ _ _ H1)  -{3}(list_insert_id _ _ _ H3).
    by iApply "X". }
Qed.

Lemma wpr_if E (b:bool) e1 e2 Q :
  wpr E (if b then e1 else e2) Q -∗
  wpr E (If b e1 e2) Q.
Proof.
  iIntros "Hwp". iIntros (?) "#Hinj".
  destruct e'; try done. simpl.
  iDestruct "Hinj" as "(X&?&?)".
  destruct e'1; try done.
  iDestruct "X" as "<-".
  iApply wpg_if. eauto.
  iIntros (b' Eq). inversion Eq. subst b'.
  destruct b; iApply "Hwp"; done.
Qed.

Lemma wpr_pair E (v1 v2:val) :
  ⊢ wpr E (Pair v1 v2) (fun v' => ⌜v'=VPair v1 v2⌝).
Proof.
  iIntros (?) "#Hinj".
  destruct e'; try done. simpl.
  iDestruct "Hinj" as "(?&?)".
  destruct e'1; try done. destruct e'2; try done. simpl.
  iApply wpg_mono. iApply wpg_pair. iIntros (?) "->".
  iExists _. iSplitR; last done. iFrame "#".
Qed.

Lemma wpr_fst E (v1 v2:val) :
  ⊢ wpr E (Fst (VPair v1 v2)) (fun v' => ⌜v'=v1⌝).
Proof.
  iIntros (?) "#Hinj".
  destruct e'; try done. simpl.
  destruct e'; try done. simpl.
  destruct v; try (iDestruct "Hinj" as "%"; congruence).
  iDestruct "Hinj" as "(?&?)".
  iApply wpg_mono. iApply wpg_fst. iIntros (?) "->".
  iExists _. iSplitR; last done. iFrame "#".
Qed.

Lemma wpr_length E (l:loc) q vs :
  pointstor l q vs -∗
  wpr E (Length l) (fun v' => ⌜v'=length vs⌝ ∗ pointstor l q vs).
Proof.
  iIntros "[% [% (#?&#?&Hl)]]". iIntros (?) "#Hinj".
  destruct e'; try done. simpl. destruct e'; try done.
  destruct v; try (iDestruct "Hinj" as "%"; congruence).
  iDestruct (ininj_partial_func l l0 lr with "[$][$]") as "->".
  iDestruct (big_sepL2_length with "[$]") as "%X".

  iApply (wpg_mono with "[Hl]").
  { by iApply wpg_length. }
  iIntros (?) "(->&?)".
  iExists (length vs). rewrite X. simpl.
  do 2 (iSplitR; first done).
  iFrame "#∗".
Qed.

Lemma wpr_snd E (v1 v2:val) :
  ⊢ wpr E (Snd (VPair v1 v2)) (fun v' => ⌜v'=v2⌝).
Proof.
  iIntros (?) "#Hinj".
  destruct e'; try done. simpl.
  destruct e'; try done. simpl.
  destruct v; try (iDestruct "Hinj" as "%"; congruence).
  iDestruct "Hinj" as "(?&?)".
  iApply wpg_mono. iApply wpg_snd. iIntros (?) "->".
  iExists _. iSplitR; last done. iFrame "#".
Qed.

Lemma wpr_let_val E x (v:val) e Q :
  wpr E (subst' x v e) Q -∗
  wpr E (Let x v e) Q.
Proof.
  iIntros "Hwp". iIntros (?) "#Hinj".
  destruct e'; try done. simpl.
  iDestruct "Hinj" as "(->&?&?)".
  destruct e'1; try done.
  iApply wpg_let_val.
  iApply "Hwp". by iApply eininj_subst'.
Qed.

Lemma wpr_code E self args code :
  ⊢ wpr E (Code self args code) (λ v : val, ⌜v = VCode self args code⌝).
Proof.
  iIntros (?) "Hinj". destruct e'; try done. simpl.
  iDestruct "Hinj" as "((->&->)&?)".
  iApply wpg_mono. iApply wpg_code. iIntros (?) "->".
  iExists _. iSplitL; last done. by iFrame.
Qed.

Lemma wpr_assert E :
  ⊢ wpr E (Assert true) (fun v => ⌜v=VUnit⌝).
Proof.
  iIntros (?) "Hinj".
  destruct e'; try done. simpl.
  destruct e'; try done. iDestruct "Hinj" as "<-".
  iApply wpg_mono. by iApply wpg_assert.
  iIntros (?) "(->&_)". iExists VUnit. done.
Qed.

(* Too strong for binds_inv *)
Lemma wpr_binds E e ks Q :
  wpr E e (fun v => wpr E (fill_items ks v) Q) -∗
  wpr E (fill_items ks e) Q.
Proof.
  iIntros "Hwp".
  iIntros (e') "#HInj".
  iDestruct (eininj_fill_items_inv with "[$]") as "[% [% (->&?&#Hinj)]]".
  iApply wpg_binds. iSpecialize ("Hwp" with "[$]").
  iApply (wpg_mono with "[$]").
  iIntros (?) "[% (?&Hwp)]".
  iDestruct (eininj_fill_items _ _ (Val _) (Val _) with "[$][$]") as "?".
  iApply ("Hwp" with "[$]").
Qed.

Lemma wpr_mono E e Q' Q :
  wpr E e Q' -∗
  (∀ v, Q' v -∗ Q v) -∗
  wpr E e Q.
Proof.
  iIntros "Hwp X". iIntros (?) "?".
  iSpecialize ("Hwp" with "[$]").
  iApply (wpg_mono with "Hwp").
  iIntros (?) "[% (?&?)]". iFrame. by iApply "X".
Qed.

Lemma wpr_call_prim E p v1 v2 v :
  eval_call_prim p v1 v2 = Some v ->
  ⊢ wpr E (CallPrim p v1 v2) (fun v' => ⌜v'=v⌝)%I.
Proof.
  iIntros (??) "Hinj".
  destruct e'; try done. simpl.
  iDestruct "Hinj" as "(->&?&?)".
  destruct e'1; try done.
  destruct e'2; try done.
  iApply wpr_use_ininj. naive_solver.
  { iIntros (??). iApply ininj_preserve_call_prim. done. }
  iFrame. iIntros (?).
  iApply wpg_mono. by iApply wpg_call_prim.
  iIntros (?) "%Eq". iExists _. iSplit; last done.
  replace v4 with v by naive_solver.
  iApply vininj_refl.
  apply eval_call_prim_no_loc in H1. done.
Qed.

Lemma wpr_call E self args body ts vs Q :
  ts = Val vs ->
  ▷ wpr E (substs' [(self,VCode self args body); (args,vs)] body) Q -∗
  wpr E (Call (VCode self args body) ts) Q.
Proof.
  iIntros (?) "Hwp". iIntros (?) "Hinj".
  destruct e'; try done. simpl.
  iDestruct "Hinj" as "(Hinj&Hinj')".
  destruct e'1; try done.
  destruct v; try (iDestruct "Hinj" as "%"; congruence).
  iDestruct "Hinj" as "((->&->)&#?)". subst.
  iDestruct "Hinj'" as "#Hinj'".
  destruct e'2; try done.
  iApply wpg_call. done. iModIntro.
  iApply (wpr_mono with "[$]"). by iIntros.
  iApply eininj_subst'. iApply eininj_subst'. done. done.
  by iFrame "#".
Qed.

Lemma wpr_atomic E1 E2 e Q :
  Atomic e ∨ is_val e ->
  (|={E1,E2}=> wpr E2 e (fun v => |={E2,E1}=> Q v)) ⊢ wpr E1 e Q.
Proof.
  iIntros (?) "Hwp". iIntros (?) "#?".
  iDestruct (eininj_atomic with "[$]") as "%". done.
  iApply wpg.wpg_atomic. done.
  iMod "Hwp". iModIntro. iSpecialize ("Hwp" with "[$]").
  iApply (wpg.wpg_mono with "[$]").
  iIntros (?) "[% (?&X)]". iMod "X". iModIntro. iFrame.
Qed.

Lemma fupd_wpr E e Q :
  (|={E}=> wpr E e Q) ⊢ wpr E e Q.
Proof.
  iIntros "Hwp". iIntros (e') "?".
  iApply wpg.fupd_wpg. iMod "Hwp". iModIntro.
  by iApply "Hwp".
Qed.

(*******************************************************************)

(*
  + For now, [dwp] enforce determinism (vininj vl vr).
  This is not needed if I'm ready to tolerate a forall quantifier
  for the innermost wpr. Indeed, determinism is needed only for
  dwp_par, where I have to "guess" the return result of the innermost
  parallel pair in advance.

  + dwp reuses the allocations of the outermost execution to name
  the allocations of the innermost one. This bounds the number of allocations
  of the innermost one.
  I guess I can apply the ininj trick to the left program too, using a global
  set of logical names. Is this needed for some examples?
 *)

(* A chained triple [ { Pl } el { Ql | Pr } er { Qr } ]
   is realized as [ □ (Pl -∗ dwp ⊤ el Pr er Ql Qr) ] *)
Definition dwp {A:Type} E el P er Ql Qr : iProp Σ :=
  wpl E el (fun vl => ∃ (x:A), Ql vl x ∗ (P x -∗ wpr E er (fun vr => ⌜vl=vr⌝ ∗ Qr x vl)))%I.

Lemma fupd_dwp {A} E el P er Ql Qr :
  (|={E}=> dwp E el P er Ql Qr) -∗
  dwp (A:=A) E el P er Ql Qr.
Proof. iIntros "Hwp". iApply fupd_wpg. iMod "Hwp". done. Qed.

Definition dwpk {A} E ksl el P ksr er Ql Qr: iProp Σ :=
  dwp (A:=A) E (fill_items ksl el) P (fill_items ksr er) Ql Qr.

Lemma dwp_properN {A} n E el Pr1 er Ql1 Qr1 Pr2 Ql2 Qr2 :
  (forall v, Pr1 v ≡{n}≡ Pr2 v) ->
  (forall v x, Ql1 v x ≡{n}≡ Ql2 v x) ->
  (forall v v', Qr1 v v' ≡{n}≡ Qr2 v v') ->
  dwp (A:=A) E el Pr1 er Ql1 Qr1 ≡{n}≡ dwp (A:=A) E el Pr2 er Ql2 Qr2.
Proof.
  intros E1 E2 E3. unfold dwpk, dwp.
  apply wpg_properN. intros. do 3 f_equiv. eauto.
  f_equiv. eauto. unfold wpr. do 3 f_equiv.
  apply wpg_properN. intros. f_equiv. eauto. do 3 f_equiv. eauto.
Qed.

Lemma dwpk_conseq_r_strong {A} P' E ksl el P ksr er Ql Qr :
  (∀ v, P v ={E}=∗ P' v) -∗
  dwpk E ksl el P' ksr er Ql Qr -∗
  dwpk (A:=A) E ksl el P ksr er Ql Qr.
Proof.
  iIntros "HP HWP".
  iApply (wpg_mono with "HWP").
  iIntros (?) "[% (?&HC)]". iFrame. iIntros.
  iMod ("HP" with "[$]").
  by iApply "HC".
Qed.

Lemma dwpk_conseq_r {A} P' E ksl el P ksr er Ql Qr :
  (∀ v, P v -∗ P' v) -∗
  dwpk E ksl el P' ksr er Ql Qr -∗
  dwpk (A:=A) E ksl el P ksr er Ql Qr.
Proof.
  iIntros "X1 X2". iApply (dwpk_conseq_r_strong with "[X1] X2").
  iIntros. by iApply "X1".
Qed.

Lemma dwpk_chain {A} E ksl el Pr ksr er Ql X Qr :
  dwpk E ksl el Pr ksr er (fun vl a => Ql vl a ∗ X) Qr -∗
  dwpk (A:=A) E ksl el (fun x => (X -∗ Pr x )) ksr er Ql Qr .
Proof.
  iIntros "Hwp".
  iApply (wpg_mono with "[$]").
  iIntros (?) "(%&(?&?)&Hwp)". iFrame.
  iIntros "HP". iApply "Hwp". by iApply "HP".
Qed.

Lemma dwpk_val {A} E v P Ql Qr :
  (∃ x, Ql v x ∗ (P x -∗ Qr x v)) -∗
  dwpk (A:=A) E nil (Val v) P nil (Val v) Ql Qr.
Proof.
  iIntros "[% (E1&E2)]".
  iApply wpg_val. iFrame. iIntros.
  iIntros (e') "Hinj".
  destruct e'; try done. iApply wpg.wpg_val.
  iExists _. iFrame. iSplitR; first done. by iApply "E2".
Qed.

Lemma dwpk_mono_pre_r {A} P' E ksl el P ksr er Ql Qr :
  dwpk E ksl el P ksr er Ql Qr -∗
  (∀ v, P' v -∗ P v) -∗
  dwpk (A:=A) E ksl el P' ksr er Ql Qr.
Proof.
  iIntros "X1 X2". iApply (wpg_mono with "[$]").
  iIntros (?) "[% (?&Hwp)]". iFrame. iIntros.
  iApply "Hwp". by  iApply "X2".
Qed.

Lemma dwpk_bind_l {A} E ksl el P ksr er Ql Qr :
  wpl E el (fun v => dwpk E ksl v P ksr er Ql Qr) -∗
  dwpk (A:=A) E ksl el P ksr er Ql Qr.
Proof.
  iIntros. iApply wpg_binds. done.
Qed.

(* This form is strange but stands for the fact that
   the logic verifies determinacy: the user should guess v0 in advance.
   NB: this is needed only for preserving abstraction over dwpk. *)

Lemma dwpk_bind_r {A} Q E ksl el P ksr er Ql Qr v0 :
  (∀ v, P v -∗ wpr E er (fun v' => ⌜v'=v0⌝ ∗ Q v)) -∗
  dwpk (A:=A) E ksl el Q ksr v0 Ql Qr -∗
  dwpk (A:=A) E ksl el P ksr er Ql Qr.
Proof.
  iIntros "Hwp ?". iApply (wpg_mono with "[$]").
  iIntros (?) "[% (?&Hwp')]". iFrame. iIntros.
  iApply wpr_binds.
  iSpecialize ("Hwp" with "[$]").
  iApply (wpr_mono with "[$]").
  iIntros (?) "(->&?)".
  iApply ("Hwp'" with "[$]").
Qed.

Lemma dwpk_let_val_l {A} E ksl x (v:val) el ksr P er Ql Qr :
  dwpk E ksl (subst' x v el) P ksr er Ql Qr -∗
  dwpk (A:=A) E ksl (Let x v el) P ksr er Ql Qr.
Proof.
  iIntros "Hwp".
  iApply wpg_binds. iDestruct (wpg_binds_inv with "Hwp") as "Hwp".
  iApply wpg_let_val. done.
Qed.

Lemma dwpk_let_val_r {A} E ksl ksr x (v:val) P el er Ql Qr :
  dwpk E ksl el P ksr (subst' x v er) Ql Qr -∗
  dwpk (A:=A) E ksl el P ksr (Let x v er) Ql Qr.
Proof.
  iIntros "Hwp".
  iApply (wpg_mono with "[$]"). iIntros (?) "[% (HQ&Hwp)]".
  iExists _. iFrame.
  iIntros.

  (* Breaking abstraction. *)
  iIntros (?) "Hinj".
  iDestruct (eininj_fill_items_inv with "Hinj") as "[% [% (->&?&Hinj)]]".
  destruct er'; try done. simpl.
  iDestruct "Hinj" as "(->&?&?)".
  destruct er'1; try done.

  iApply wpg_binds.
  iApply wpg_let_val.
  iApply wpg_binds_inv.
  iApply ("Hwp" with "[$]").
  iApply (eininj_fill_items with "[$]").
  destruct b; first done.
  iApply (eininj_subst with "[$][$]").
Qed.

Lemma dwpk_if_l {A} E ksl v e1 e2 ksr P er Ql Qr :
  (∀ b, ⌜v=VBool b⌝ -∗ dwpk E ksl (if b then e1 else e2) P ksr er Ql Qr) -∗
  dwpk (A:=A) E ksl (If v e1 e2) P ksr er Ql Qr.
Proof.
  iIntros "Hwp".
  iApply wpg_binds.
  iApply wpg_if. done.
  iIntros. iSpecialize ("Hwp" with "[%//]").
  iDestruct (wpg_binds_inv with "Hwp") as "Hwp".
  done.
Qed.

Lemma dwpk_if_r {A} E ksl ksr (b:bool) e1 e2 P el Ql Qr :
  dwpk E ksl el P ksr (if b then e1 else e2) Ql Qr -∗
  dwpk (A:=A) E ksl el P ksr (If b e1 e2) Ql Qr.
Proof.
  iIntros "Hwp".
  iApply (wpg_mono with "[$]"). iIntros (?) "[% (HQ&Hwp)]".
  iExists _. iFrame.
  iIntros.

  (* Breaking abstraction. *)
  iIntros (?) "Hinj".
  iDestruct (eininj_fill_items_inv with "Hinj") as "[% [% (->&?&Hinj)]]".
  destruct er'; try done. simpl.
  iDestruct "Hinj" as "(X&?&?)".
  destruct er'1; try done.
  iDestruct "X" as "<-".

  iApply wpg_binds.
  iApply wpg_if. eauto. iIntros (b' Eq). inversion Eq. subst b'.
  iApply wpg_binds_inv.
  iApply ("Hwp" with "[$]").
  iApply (eininj_fill_items with "[$]").
  destruct b; done.
Qed.

Lemma dwpk_code_l {A} E ksl ksr self arg code P er Ql Qr :
  dwpk E ksl (VCode self arg code) P ksr er Ql Qr -∗
  dwpk (A:=A) E ksl (Code self arg code) P ksr er Ql Qr.
Proof.
  iIntros "Hwp".
  iApply wpg_binds.
  iApply wpg_mono. iApply wpg_code. iIntros (?) "->". done.
Qed.

Lemma dwpk_code_r {A} E ksl ksr self arg code P el Ql Qr :
  dwpk E ksl el P ksr (VCode self arg code) Ql Qr -∗
  dwpk (A:=A) E ksl el P ksr (Code self arg code) Ql Qr.
Proof.
  iIntros "Hwp". iApply dwpk_bind_r; last done.
  iIntros. iApply wpr_mono. iApply wpr_code. iIntros (?) "->".
  by iFrame.
Qed.

Lemma dwpk_pair_l {A} E ksl ksr (v1 v2:val) P er Ql Qr :
  dwpk E ksl (VPair v1 v2) P ksr er Ql Qr -∗
  dwpk (A:=A) E ksl (Pair v1 v2) P ksr er Ql Qr.
Proof.
  iIntros "Hwp".
  iApply wpg_binds.
  iApply wpg_mono. iApply wpg_pair. iIntros (?) "->". done.
Qed.

Lemma dwpk_pair_r {A} E ksl ksr (v1 v2:val) P el Ql Qr :
  dwpk E ksl el P ksr (VPair v1 v2) Ql Qr -∗
  dwpk (A:=A) E ksl el P ksr (Pair v1 v2) Ql Qr.
Proof.
  iIntros "Hwp". iApply dwpk_bind_r; last done.
  iIntros. iApply wpr_mono. iApply wpr_pair. iIntros (?) "->".
  by iFrame.
Qed.

Lemma dwpk_fst_l {A} E ksl ksr (v1 v2:val) P er Ql Qr :
  dwpk E ksl (v1) P ksr er Ql Qr -∗
  dwpk (A:=A) E ksl (Fst (VPair v1 v2)) P ksr er Ql Qr.
Proof.
  iIntros "Hwp".
  iApply wpg_binds.
  iApply wpg_mono. iApply wpg_fst. iIntros (?) "->". done.
Qed.

Lemma dwpk_fst_r {A} E ksl ksr (v1 v2:val) P el Ql Qr :
  dwpk E ksl el P ksr v1 Ql Qr -∗
  dwpk (A:=A) E ksl el P ksr (Fst (VPair v1 v2)) Ql Qr.
Proof.
  iIntros "Hwp". iApply dwpk_bind_r; last done.
  iIntros. iApply wpr_mono. iApply wpr_fst. iIntros (?) "->".
  by iFrame.
Qed.

Lemma dwpk_snd_l {A} E ksl ksr (v1 v2:val) P er Ql Qr :
  dwpk E ksl v2 P ksr er Ql Qr -∗
  dwpk (A:=A) E ksl (Snd (VPair v1 v2)) P ksr er Ql Qr.
Proof.
  iIntros "Hwp".
  iApply wpg_binds.
  iApply wpg_mono. iApply wpg_snd. iIntros (?) "->". done.
Qed.

Lemma dwpk_snd_r {A} E ksl ksr (v1 v2:val) P el Ql Qr :
  dwpk E ksl el P ksr v2 Ql Qr -∗
  dwpk (A:=A) E ksl el P ksr (Snd (VPair v1 v2)) Ql Qr.
Proof.
  iIntros "Hwp". iApply dwpk_bind_r; last done.
  iIntros. iApply wpr_mono. iApply wpr_snd. iIntros (?) "->".
  by iFrame.
Qed.

Lemma dwpk_alloc_l {A} E ksl (v:val) ksr P er Ql Qr :
  (∀ n l, ⌜v = VInt n /\ 0<=n⌝%Z -∗ pointstol l (DfracOwn 1) (replicate (Z.to_nat n) VUnit) ∗ waiting l ∗ meta_token l ⊤ -∗ dwpk E ksl l P ksr er Ql Qr) -∗
  dwpk (A:=A) E ksl (Alloc v) P ksr er Ql Qr.
Proof.
  iIntros "Hwp".
  iApply wpg_binds.
  iApply (wpg_mono with "[-Hwp]").
  { by iApply wpg_alloc. }
  simpl.
  iIntros (?) "[%[% ((%Eq&->&%)&?&?)]]".
  by iApply ("Hwp" with "[%//][$]").
  Unshelve. exact inhabitant.
Qed.

Lemma dwpk_alloc_r {A} l E ksl (n:Z) ksr P el Ql Qr :
  (0 <= n)%Z ->
  waiting l -∗
  dwpk E ksl el (fun x => pointstor l (DfracOwn 1) (replicate (Z.to_nat n) VUnit) ∗ P x) ksr l Ql Qr -∗
  dwpk (A:=A) E ksl el P ksr (Alloc n) Ql Qr.
Proof.
  iIntros (?) "HP Hwp". iApply (dwpk_bind_r with "[HP]"); last done.
  iIntros. iApply (wpr_mono with "[HP]"). by iApply wpr_alloc.
  iIntros (?) "(->&?)". by iFrame.
Qed.

Lemma dwpk_store_l {A} E ksl ksr (l:loc) vs (w:val) (v:val) P er Ql Qr :
  pointstol l (DfracOwn 1) vs -∗
  (∀ i, ⌜w=VInt i /\ 0 <= i < length vs⌝%Z -∗ pointstol l (DfracOwn 1) (<[Z.to_nat i:=v]>vs) -∗ dwpk E ksl VUnit P ksr er Ql Qr) -∗
  dwpk (A:=A) E ksl (Store l w v) P ksr er Ql Qr.
Proof.
  iIntros "Hl Hwp".
  iApply dwpk_bind_l.
  iApply (wpg_mono with "[Hl]").
  { by iApply wpg_store. }
  iIntros (?) "[%i ((%&->&%)&Hl)]".
  iSpecialize ("Hwp" with "[%//][$]"). iApply "Hwp".
Qed.

Lemma dwpk_load_l {A} E ksl ksr (l:loc) w vs q P er Ql Qr :
  pointstol l q vs -∗
  (∀ i (v:val), ⌜w=VInt i /\ (0 <= i < length vs)%Z /\ vs !! (Z.to_nat i) = Some v⌝ -∗ pointstol l q vs -∗ dwpk E ksl v P ksr er Ql Qr) -∗
  dwpk (A:=A) E ksl (Load l w) P ksr er Ql Qr.
Proof.
  iIntros "Hl Hwp".
  iApply dwpk_bind_l.
  iApply (wpg_mono with "[Hl]").
  { by iApply (wpg_load_l with "Hl"). }
  iIntros (?) "[%((%&%&%)&?)]".
  by iApply "Hwp".
Qed.

Lemma dwpk_load_r {A} P' P E ksl ksr (l:loc) i vs (v:val) q el Ql Qr :
  (0 <= i < length vs)%Z ->
  vs !! (Z.to_nat i) = Some v ->
  (∀ v', P v' -∗ pointstor l q vs ∗ P' v') -∗
  (dwpk E ksl el (fun v' => pointstor l q vs ∗ P' v') ksr v Ql Qr) -∗
  dwpk (A:=A) E ksl el P ksr (Load l i) Ql Qr.
Proof.
  iIntros (??) "HP Hwp".
  iApply (dwpk_bind_r with "[HP]"); last done.
  iIntros. iDestruct ("HP" with "[$]") as "(Hl&?)".
  iApply (wpr_mono with "[Hl]"). by iApply wpr_load.
  iIntros (?) "(->&?)". by iFrame.
Qed.

Lemma dwpk_length_l {A} E ksl ksr (l:loc) vs q P er Ql Qr :
  pointstol l q vs -∗
  (pointstol l q vs -∗ dwpk E ksl (length vs) P ksr er Ql Qr) -∗
  dwpk (A:=A) E ksl (Length l) P ksr er Ql Qr.
Proof.
  iIntros "Hl Hwp".
  iApply dwpk_bind_l.
  iApply (wpg_mono with "[Hl]").
  { by iApply (wpg_length with "Hl"). }
  iIntros (?) "(->&?)".
  by iApply "Hwp".
Qed.

Lemma dwpk_length_r {A} P' P E ksl ksr (l:loc) vs q el Ql Qr :
  (∀ v', P v' -∗ pointstor l q vs ∗ P' v') -∗
  (dwpk E ksl el (fun v' => pointstor l q vs ∗ P' v') ksr (length vs) Ql Qr) -∗
  dwpk (A:=A) E ksl el P ksr (Length l) Ql Qr.
Proof.
  iIntros "HP Hwp".
  iApply (dwpk_bind_r with "[HP]"); last done.
  iIntros. iDestruct ("HP" with "[$]") as "(Hl&?)".
  iApply (wpr_mono with "[Hl]"). by iApply wpr_length.
  iIntros (?) "(->&?)". by iFrame.
Qed.

Lemma dwpk_store_r {A} P E ksl ksr (l:loc) i vs (v:val) P' el Ql Qr :
  (0 <= i < length vs)%Z ->
  (∀ v', P' v' -∗ pointstor l (DfracOwn 1) vs ∗ P v') -∗
  dwpk E ksl el (fun x => pointstor l (DfracOwn 1) (<[Z.to_nat i:=v]>vs) ∗ P x) ksr VUnit Ql Qr -∗
  dwpk (A:=A) E ksl el P' ksr (Store l i v) Ql Qr.
Proof.
  iIntros (?) "HP Hwp".
  iApply (dwpk_bind_r with "[HP]"); last done.
  iIntros. iDestruct ("HP" with "[$]") as "(Hl&?)".
  iApply (wpr_mono with "[Hl]"). by iApply wpr_store.
  iIntros (?) "(->&?)". by iFrame.
Qed.

Lemma dwpk_call_l {A} E ksl self args body P ksr er Ql Qr ts vs :
  ts = Val vs ->
  ▷ dwpk E ksl (substs' [(self,VCode self args body); (args,vs)] body) P ksr er Ql Qr -∗
  dwpk (A:=A) E ksl (Call (VCode self args body) ts) P ksr er Ql Qr.
Proof.
  iIntros (->) "Hwp".
  iApply dwpk_bind_l.
  iApply wpg_call; try done. iModIntro.
  iDestruct (wpg_binds_inv with "[$]") as "Hwp".
  iApply (wpg_mono with "Hwp").
  iIntros.
  iApply (wpg_mono with "[$]").
  iIntros (?) "[% (?&X)]". iFrame.
Qed.

Lemma dwpk_call_r {A} E ksl self args body P ksr el Ql Qr vs ts :
  ts = Val vs ->
  dwpk E ksl el P ksr (substs' [(self,VCode self args body); (args,vs)] body) Ql Qr -∗
  dwpk (A:=A) E ksl el (fun v => ▷ P v) ksr (Call (VCode self args body) ts) Ql Qr.
Proof.
  iIntros (->) "Hwp".
  iApply (wpg_mono with "[$]").
  iIntros (?) "[% (?&Hwp)]". iFrame.
  iIntros "HP". iIntros (?) "?".
  iDestruct (eininj_fill_items_inv with "[$]") as "[% [% (->&#?&Hinj)]]".
  iApply wpg_binds.
  destruct er'; try done. simpl.
  iDestruct "Hinj" as "(Hinj&Hinj')".
  destruct er'1; try done.
  destruct v0; try (iDestruct "Hinj" as "%"; congruence).
  iDestruct "Hinj" as "((->&->)&#?)".
  destruct er'2; try done.
  iDestruct "Hinj'" as "#?".
  iApply wpg_call. done. iModIntro.
  iSpecialize ("Hwp" with "[$]").
  iDestruct (eininj_fill_items with "[$][]") as "?".
  2:{ iSpecialize ("Hwp" with "[$]"). by iApply wpg_binds_inv. }
  { iApply eininj_subst'. iApply eininj_subst'. done. done.
    by iFrame "#". }
Qed.

Lemma dwpk_push_l {A} E K ksl ksr el er P Ql Qr :
  dwpk E (ksl ++ [K]) el P ksr er Ql Qr -∗
  dwpk (A:=A) E ksl (fill_item K el) P ksr er Ql Qr.
Proof. rewrite /dwpk !fill_items_app //. by iIntros. Qed.

Lemma dwpk_pop_l {A} E K ksl ksr el er P Ql Qr :
  dwpk E ksl (fill_item K el) P ksr er Ql Qr -∗
  dwpk (A:=A) E (ksl ++ [K]) el P ksr er Ql Qr.
Proof. rewrite /dwpk !fill_items_app //. by iIntros. Qed.

Lemma dwpk_push_r {A} E K ksl ksr el er P Ql Qr :
  dwpk E ksl el P (ksr ++ [K]) er Ql Qr -∗
  dwpk (A:=A) E ksl el P ksr (fill_item K er) Ql Qr.
Proof. rewrite /dwpk !fill_items_app //. by iIntros. Qed.

Lemma dwpk_pop_r {A} E K ksl ksr el er P Ql Qr :
  dwpk E ksl el P ksr (fill_item K er) Ql Qr -∗
  dwpk (A:=A) E ksl el P (ksr ++ [K]) er Ql Qr.
Proof. rewrite /dwpk !fill_items_app //. by iIntros. Qed.

Lemma dwpk_par {A B C} P P1 P2 Ql1 Ql2 Qr1 Qr2 P0 E ksl ksr el1 el2 er1 er2  Ql Qr:

  (dwpk (A:=A) E nil el1 P1 nil er1 Ql1 Qr1) -∗
  (dwpk (A:=B) E nil el2 P2 nil er2 Ql2 Qr2) -∗
  (∀ v1 x v2 y, Ql1 v1 x ∗ Ql2 v2 y -∗
            (∀ c, P0 c -∗ P1 x ∗ P2 y ∗ P c) ∗
            dwpk (A:=C) E ksl (VPair v1 v2) (fun c => P c ∗ Qr1 x v1 ∗ Qr2 y v2) ksr (VPair v1 v2) Ql Qr) -∗
  dwpk (A:=C) E ksl (Par el1 el2) P0 ksr (Par er1 er2) Ql Qr.
Proof.
  iIntros "Hwp1 Hwp2 Hwp3".
  iApply wpg_binds.
  iApply (wpg_mono with "[Hwp1 Hwp2]").
  { iApply (wpg_par with "[Hwp1]"); done. }
  simpl.
  iIntros (?) "[% [% (->&[% (X11&X12)]&[% (X21&X22)])]]".
  iDestruct ("Hwp3" $! v1 x v2 x0 with "[$]") as "(HP&Hwp3)".
  iApply (wpg_mono with "Hwp3").
  iIntros (?) "[% (?&Hwp)]". iFrame.
  iIntros. iIntros (?) "Hinj".
  iDestruct ("HP" with "[$]") as "(H1&H2&X)".

  iDestruct (eininj_fill_items_inv with "[$]") as "[% [% (->&#?&Hinj)]]".
  destruct er'; try done. simpl.
  iDestruct "Hinj" as "#(?&?)".
  iApply wpg_binds.
  iApply (wpg_mono with "[-Hwp X]").
  { iApply (wpg_par with "[X12 H1]").
    { iApply ("X12" with "[$][$]"). }
    { iApply ("X22" with "[$][$]"). } } simpl.
  iIntros (?) "[% [% (->&[% (?&->&?)]&[% (?&->&?)])]]".
  iApply ("Hwp" with "[$]"); last iFrame.
  iApply (eininj_fill_items with "[$]"). iFrame.
Qed.

Lemma dwpk_assert_l {A} E ksl v P ksr er Ql Qr :
  (⌜v=VBool true⌝ -∗ dwpk E ksl VUnit P ksr er Ql Qr) -∗
  dwpk (A:=A) E ksl (Assert v) P ksr er Ql Qr.
Proof.
  iIntros "Hwp".
  iApply dwpk_bind_l.
  iApply (wpg_mono with "[]").
  { by iApply wpg_assert. }
  iIntros (?) "(->&->)".
  by iApply "Hwp".
Qed.

Lemma dwpk_assert_r {A} E ksl P ksr el Ql Qr :
  dwpk E ksl el P ksr VUnit Ql Qr -∗
  dwpk (A:=A) E ksl el P ksr (Assert true) Ql Qr.
Proof.
  iIntros "Hwp".
  iApply (dwpk_bind_r with "[-Hwp]"); last done.
  iIntros. iApply wpr_mono. iApply wpr_assert.
  iIntros (?) "->". by iFrame.
Qed.

Lemma dwpk_call_prim_l {A} E ksl ksr p (v1 v2 v : val) P er Ql Qr :
  (∀ v, ⌜eval_call_prim p v1 v2 = Some v⌝ -∗ dwpk E ksl v P ksr er Ql Qr) -∗
  dwpk (A:=A) E ksl (CallPrim p v1 v2) P ksr er Ql Qr.
Proof.
  iIntros "Hwp".
  iApply dwpk_bind_l.
  iApply wpg_mono.
  { by iApply wpg_call_prim. }
  iIntros (?) "->". by iApply "Hwp".
Qed.

Lemma dwpk_call_prim_r {A} E ksl ksr p (v1 v2 v : val) P el Ql Qr :
  eval_call_prim p v1 v2 = Some v ->
  dwpk E ksl el P ksr v Ql Qr -∗
  dwpk (A:=A) E ksl el P ksr (CallPrim p v1 v2) Ql Qr.
Proof.
  iIntros (?) "Hwp".
  iApply (dwpk_bind_r with "[]"); last done.
  iIntros. iApply wpr_mono. iApply wpr_call_prim. done.
  iIntros. by iFrame.
Qed.

End go.

Global Instance dwp_proper `{intdetGS Σ} A E e :
  Proper ((pointwise_relation _ (≡)) ==> (=) ==> (pointwise_relation _ (pointwise_relation _ (≡))) ==> (pointwise_relation _ (pointwise_relation _ (≡))) ==> (≡)) (dwp (A:=A) E e).
Proof.
  intros ?? X1 ?? -> ?? X2 ?? X3.
  apply equiv_dist. intros. apply dwp_properN.
  all:intros; apply equiv_dist; try done. apply X2. apply X3.
Qed.

Module Initialization.

  Import Initialization.

  Definition intdetΣ : gFunctors :=
    #[ invΣ;
       gen_heapΣ loc (list val);
       ghost_mapΣ loc (list val);
       inInjΣ ].

  (* The difference between the *PreG and *G is the presence of the names
     of ghost cells. (ie. gname) *)
  Class intdetPreG (Σ : gFunctors) :=
  { pi1 : invGpreS Σ;
    pi2 : gen_heapGpreS loc (list val) Σ;
    pi3 : ghost_mapG Σ loc (list val);
    pi4 : inInjpreG Σ }.

  #[global] Existing Instance pi1.
  #[local] Existing Instance pi2.
  #[local] Existing Instance pi3.
  #[local] Existing Instance pi4.

  Global Instance subG_intdetPreG Σ :
    subG intdetΣ Σ → intdetPreG Σ.
  Proof. solve_inG. Qed.

  Global Instance intdetPreG_intdetΣ : intdetPreG intdetΣ.
  Proof. eauto with typeclass_instances. Qed.

  Lemma intdet_init `{!intdetPreG Σ, hinv:!invGS_gen HasNoLc Σ} :
    ⊢ |==> ∃ hi : intdetGS Σ, ⌜@iinvgs Σ hi = hinv⌝ ∗
    interp ∅ ∅.
  Proof.
    rewrite /interp.
    iMod (gen_heap_init ∅) as "[% (?&_)]".
    iMod (@ghost_map_alloc_empty _ loc (list val) _ _ _) as "[%γstorer ?]".
    iMod ininj_alloc as "[%X ?]".
    iExists (@IntdetGS Σ hinv _ γstorer _ X).
    by iFrame.
  Qed.

End Initialization.
