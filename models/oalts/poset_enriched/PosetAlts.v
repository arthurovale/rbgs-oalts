Require Import models.oalts.poset_enriched.PosetLCoalg.
Require Import models.oalts.poset_enriched.PosetAsyncEvents.
Require Import models.oalts.poset_enriched.PosetDownsetKleisli.
Require Import models.oalts.poset_enriched.TimeDownset.

(** * Poset-Enriched Alternating Simulations (ALTS)

    We instantiate the poset-enriched labelled coalgebra framework with:
    - Labels: async events (posets with a lifting functor L(E) = 1 + E)
    - States: the Kleisli category of the Downset monad on Poset
    - Functor: the Time functor lifted via the distributive law

    This gives us ALTS with forward simulations as morphisms:
    - Forward simulation: step beta . f <= fmap(e,f) . step alpha
*)

(** Internal module with all simulation types *)
Module PosetAltsInternal := PosetLCoalg PosetAsyncEventsPosetCat PosetDownsetKl LiftedTimePosetBifunctor.

(** The category of ALTS with forward simulations as morphisms *)
Module PosetAlts := PosetAltsInternal.FW.
