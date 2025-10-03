From iris.proofmode Require Import base proofmode.
From iris.bi Require Import telescopes.
From iris.bi.lib Require Export atomic.

From intdet.lang Require Import notations.
From intdet.musketeer Require Import wpg.

(* From https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/program_logic/atomic.v *)

Definition atomic_wpg `{wpGS lr Σ A interp pointsto} {TA TB : tele}
  (e: expr) (* expression *)
  (E : coPset) (* *implementation* mask *)
  (α: TA → iProp Σ) (* atomic pre-condition *)
  (β: TA → TB → iProp Σ) (* atomic post-condition *)
  (post : val -> TA -> TB -> iProp Σ) (* private post *)
  : iProp Σ :=
  ∀ (Q : val → iProp Σ),
    atomic_update (⊤∖E) ∅ α β (λ.. x y, ∀ z, post z x y -∗ Q z) -∗
    wpg E e Q.

Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' β '|' Q '}>>'" :=
  (atomic_wpg (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
             (fun v => tele_app $ λ x1, .. (λ xn,
                         tele_app $ (Q v)%I
                        ) .. ))
  (at level 20, E, β, α at level 200, x1 binder, xn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/'  Q  ']' '}>>' ']'")
  : bi_scope.
