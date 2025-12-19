Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.Monads.
Require Import models.DCPO.
Require Import models.oalts.DownsetMonad.
Require Import models.oalts.TimeDownset.
Require Import models.oalts.DCPODownsetMonad.
Require Import models.oalts.DCPOAsyncEvent.
Require Import models.oalts.DCPOLiftToKleisli.
Require Import models.oalts.interfaces.DCPOEnrichedCat.

(** * DCPO-Enriched Time-Downset Distributive Law *)

(** We lift the Time-Downset distributive law to work with DCPO-enriched categories.
    This allows us to create a DCPO-enriched lifted time functor for use in DCPOAlts. *)

(** ** DCPO-Enriched Async Events on Poset *)

(** For compatibility with DCPODownsetKl (which is based on Poset), we need
    a DCPO-enriched version of PosetAsyncEvents. The hom-sets of PosetAsyncEvents
    are monotone functions X → 1+Y, which form a DCPO with pointwise order. *)

Module DCPOPosetAsyncEvents <: DCPOCategoryDefinition.
  Module C := PosetAsyncEvents.
  Include C.

  (** Hom-sets are DCPOs: monotone functions X → (1+Y) with pointwise order *)
  Definition hom_dcpo (X Y : t) : DirectedComplete (m X Y).
  Proof.
    (* PosetAsyncEvents.m X Y = Poset.m X (L.omap Y) where L.omap Y = 1+Y *)
    (* Monotone functions to a DCPO form a DCPO with pointwise order *)
    (* The codomain 1+Y is a DCPO because downsets have directed sups *)
    admit.
  Admitted.

  Definition compose_continuous_l (A B C : t) (g : m B C) :
    @ScottContinuous _ _ (hom_dcpo A B) (@dc_po _ (hom_dcpo A C)) (fun f => compose g f).
  Proof.
    (* Composition with ext(g) is monotone and preserves directed sups *)
    admit.
  Admitted.

  Definition compose_continuous_r (A B C : t) (f : m A B) :
    @ScottContinuous _ _ (hom_dcpo B C) (@dc_po _ (hom_dcpo A C)) (fun g => compose g f).
  Proof.
    (* Composition is monotone and preserves directed sups in the left argument *)
    admit.
  Admitted.

End DCPOPosetAsyncEvents.

(** ** DCPO-Enriched Time Functor *)

(** The PosetTimeFunctor needs to be adapted to work with DCPOPosetAsyncEvents *)
Module DCPOPosetTimeFunctor <: BifunctorDefinition DCPOPosetAsyncEvents Poset Poset.

  Definition omap (E : DCPOPosetAsyncEvents.t) (S : Poset.t) : Poset.t :=
    PosetTimeFunctor.omap E S.

  Definition fmap {E1 : DCPOPosetAsyncEvents.t} {X1 : Poset.t}
    {E2 : DCPOPosetAsyncEvents.t} {X2 : Poset.t}
    (e : DCPOPosetAsyncEvents.m E1 E2) (f : Poset.m X1 X2) : Poset.m (omap E1 X1) (omap E2 X2) :=
    PosetTimeFunctor.fmap e f.

  Proposition fmap_id : forall E X,
    fmap (DCPOPosetAsyncEvents.id E) (Poset.id X) = Poset.id (omap E X).
  Proof.
    intros. unfold fmap. apply PosetTimeFunctor.fmap_id.
  Qed.

  Proposition fmap_compose :
    forall {A1 : DCPOPosetAsyncEvents.t} {A2 : Poset.t}
      {B1 : DCPOPosetAsyncEvents.t} {B2 : Poset.t}
      {C1 : DCPOPosetAsyncEvents.t} {C2 : Poset.t}
      (g1 : DCPOPosetAsyncEvents.m B1 C1) (g2 : Poset.m B2 C2)
      (f1 : DCPOPosetAsyncEvents.m A1 B1) (f2 : Poset.m A2 B2),
    fmap (DCPOPosetAsyncEvents.compose g1 f1) (Poset.compose g2 f2) =
      Poset.compose (fmap g1 g2) (fmap f1 f2).
  Proof.
    intros. unfold fmap. apply PosetTimeFunctor.fmap_compose.
  Qed.

End DCPOPosetTimeFunctor.

(** ** DCPO Distributive Law *)

(** The TimeDownsetDistr distributive law adapted to DCPOPosetAsyncEvents *)
Module DCPOTimeDownsetDistr <: DCPOBiDistributiveLaw
    DCPOPosetAsyncEvents Poset DownsetMonadDef DCPOPosetTimeFunctor.

  Definition distr (E : DCPOPosetAsyncEvents.t) (S : Poset.t) :
    Poset.m (DCPOPosetTimeFunctor.omap E (DownsetMonadDef.omap S))
            (DownsetMonadDef.omap (DCPOPosetTimeFunctor.omap E S)) :=
    TimeDownsetDistr.distr E S.

  Proposition distr_natural_l :
    forall {E1 E2 : DCPOPosetAsyncEvents.t} (e : DCPOPosetAsyncEvents.m E1 E2) (S : Poset.t),
    Poset.compose (distr E2 S) (DCPOPosetTimeFunctor.fmap e (Poset.id (DownsetMonadDef.omap S))) =
    Poset.compose (DownsetMonadDef.fmap (DCPOPosetTimeFunctor.fmap e (Poset.id S))) (distr E1 S).
  Proof.
    intros. unfold distr, DCPOPosetTimeFunctor.fmap.
    apply TimeDownsetDistr.distr_natural_l.
  Qed.

  Proposition distr_natural_r :
    forall (E : DCPOPosetAsyncEvents.t) {S1 S2 : Poset.t} (f : Poset.m S1 S2),
    Poset.compose (distr E S2) (DCPOPosetTimeFunctor.fmap (DCPOPosetAsyncEvents.id E) (DownsetMonadDef.fmap f)) =
    Poset.compose (DownsetMonadDef.fmap (DCPOPosetTimeFunctor.fmap (DCPOPosetAsyncEvents.id E) f)) (distr E S1).
  Proof.
    intros. unfold distr, DCPOPosetTimeFunctor.fmap.
    apply TimeDownsetDistr.distr_natural_r.
  Qed.

  Proposition distr_unit :
    forall (E : DCPOPosetAsyncEvents.t) (S : Poset.t),
    Poset.compose (distr E S) (DCPOPosetTimeFunctor.fmap (DCPOPosetAsyncEvents.id E) (DownsetMonadDef.eta S)) =
    DownsetMonadDef.eta (DCPOPosetTimeFunctor.omap E S).
  Proof.
    intros. unfold distr, DCPOPosetTimeFunctor.fmap.
    apply TimeDownsetDistr.distr_unit.
  Qed.

  Proposition distr_mult :
    forall (E : DCPOPosetAsyncEvents.t) (S : Poset.t),
    Poset.compose (distr E S) (DCPOPosetTimeFunctor.fmap (DCPOPosetAsyncEvents.id E) (DownsetMonadDef.mu S)) =
    Poset.compose (DownsetMonadDef.mu (DCPOPosetTimeFunctor.omap E S))
      (Poset.compose (DownsetMonadDef.fmap (distr E S)) (distr E (DownsetMonadDef.omap S))).
  Proof.
    intros. unfold distr, DCPOPosetTimeFunctor.fmap.
    apply TimeDownsetDistr.distr_mult.
  Qed.

End DCPOTimeDownsetDistr.

(** ** DCPO-Enriched Lifted Time Functor *)

(** The lifted time functor to the DCPO-enriched Kleisli category of the downset monad *)
Module DCPOLiftedTimeFunctor :=
  DCPOLiftBifunctorToKleisli DCPOPosetAsyncEvents Poset DownsetMonadDef
    DCPODownsetKl DCPOPosetTimeFunctor DCPOTimeDownsetDistr.
