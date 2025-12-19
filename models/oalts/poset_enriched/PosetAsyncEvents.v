Require Import interfaces.Category.
Require Import interfaces.MonoidalCategory.
Require Import interfaces.Limits.
Require Import models.DCPO.
Require Import models.oalts.AsyncEvent.
Require Import models.oalts.poset_enriched.PosetBicartesian.
Require Import models.oalts.interfaces.PosetEnrichedCat.
Require Import coqrel.LogicalRelations.

(** * Async Events on Poset *)

(** We instantiate the async events definition for the category of Posets. *)

Module PosetAsyncEvents := AsyncEventsDefinition PosetBicartesian PosetTerminals.

(** ** Poset-Enriched Structure for PosetAsyncEvents *)

(** The Kleisli category of the lift monad on Poset is poset-enriched.
    Morphisms have a pointwise partial order. *)

Module PosetAsyncEventsEnriched.
  Import PosetAsyncEvents.
  Import Poset.

  (** ** Computational Lemmas for Lift Monad *)

  (** These lemmas characterize how the lift monad operations compute
      on concrete inputs (inl/inr), avoiding complex abstract unfoldings. *)

  Section ExtComputation.
    Variables E1 E2 : PosetAsyncEvents.t.

    Let LE1 := L.omap E1.
    Let LE2 := L.omap E2.

    (** ext maps left to left *)
    Lemma ext_inl (g : PosetAsyncEvents.m E1 E2) (u : unit) :
      Poset.apply LE1 LE2 (L.ext g) (inl u) = inl tt.
    Proof.
      unfold L.ext. simpl. destruct u. reflexivity.
    Qed.

    (** When g e = inl, ext g (inr e) = inl tt *)
    Lemma ext_inr_inl (g : PosetAsyncEvents.m E1 E2) (e : E1) (u : PosetTerminals.unit) :
      g e = inl u ->
      Poset.apply LE1 LE2 (L.ext g) (inr e) = inl tt.
    Proof.
      intros Hg. unfold L.ext. simpl.
      destruct (g e) as [u' | e'] eqn:Hge.
      - reflexivity.
      - rewrite Hg in Hge. discriminate.
    Qed.

    (** When g e = inr e', ext g (inr e) = inr e' *)
    Lemma ext_inr_inr (g : PosetAsyncEvents.m E1 E2) (e : E1) (e' : E2) :
      g e = inr e' ->
      Poset.apply LE1 LE2 (L.ext g) (inr e) = inr e'.
    Proof.
      intros Hg. unfold L.ext. simpl.
      destruct (g e) as [u | e''] eqn:Hge.
      - rewrite Hg in Hge. discriminate.
      - rewrite Hg in Hge. exact Hg.
    Qed.

  End ExtComputation.

  Arguments ext_inl {E1 E2} g u.
  Arguments ext_inr_inl {E1 E2} g e {u} _.
  Arguments ext_inr_inr {E1 E2} g e {e'} _.

  (** eta is right injection *)
  Lemma eta_eq (E : PosetAsyncEvents.t) (e : E) :
    Poset.apply E (L.omap E) (L.eta E) e = inr e.
  Proof.
    reflexivity.
  Qed.

  (** ** Hom-sets have pointwise order *)
  Section HomPoset.
    Variables E1 E2 : PosetAsyncEvents.t.

    Let LE2 := L.omap E2.
    Let POLE2 := Poset.structure LE2.

    Definition hom_le (e1 e2 : PosetAsyncEvents.m E1 E2) : Prop :=
      forall x, @le _ POLE2 (Poset.apply E1 LE2 e1 x) (Poset.apply E1 LE2 e2 x).

    Lemma hom_le_preo : PreOrder hom_le.
    Proof.
      constructor.
      - intros e x. reflexivity.
      - intros e1 e2 e3 H12 H23 x. etransitivity; eauto.
    Qed.

    Lemma hom_le_po : Antisymmetric _ eq hom_le.
    Proof.
      intros e1 e2 H12 H21.
      apply Poset.meq. intros x.
      apply (@antisymmetry _ eq _ (@le _ POLE2)); auto.
      typeclasses eauto.
    Qed.

    Definition hom_PO : DCPO.PartialOrder (PosetAsyncEvents.m E1 E2) :=
      {| le := hom_le;
         le_preo := hom_le_preo;
         le_po := hom_le_po |}.

  End HomPoset.

  (** The Kleisli extension is monotonic in its function argument *)
  Section ExtMonotonic.
    Variables E1 E2 : PosetAsyncEvents.t.

    Let LE1 := L.omap E1.
    Let LE2 := L.omap E2.
    Let POLE2 := Poset.structure LE2.

    Lemma ext_monotonic (g1 g2 : PosetAsyncEvents.m E1 E2) :
      hom_le E1 E2 g1 g2 ->
      forall x, @le _ POLE2 (Poset.apply LE1 LE2 (L.ext g1) x)
                            (Poset.apply LE1 LE2 (L.ext g2) x).
    Proof.
      intros Hg x.
      unfold LE1, LE2.
      destruct x as [u | e1].
      - (* x = inl u *)
        rewrite !ext_inl. reflexivity.
      - (* x = inr e1 *)
        specialize (Hg e1).
        destruct (g1 e1) as [u1 | e1'] eqn:Hg1;
        destruct (g2 e1) as [u2 | e2'] eqn:Hg2.
        + rewrite (ext_inr_inl g1 e1 Hg1).
          rewrite (ext_inr_inl g2 e1 Hg2).
          reflexivity.
        + rewrite (ext_inr_inl g1 e1 Hg1).
          rewrite (ext_inr_inr g2 e1 Hg2).
          simpl. exact Hg.
        + rewrite (ext_inr_inr g1 e1 Hg1).
          rewrite (ext_inr_inl g2 e1 Hg2).
          simpl. exact Hg.
        + rewrite (ext_inr_inr g1 e1 Hg1).
          rewrite (ext_inr_inr g2 e1 Hg2).
          simpl. exact Hg.
    Qed.

  End ExtMonotonic.

  (** Composition is monotonic *)
  Section ComposeMonotonic.
    Variables E1 E2 E3 : PosetAsyncEvents.t.

    Lemma compose_monotonic_l (g : PosetAsyncEvents.m E2 E3) :
      Monotonic (fun f => PosetAsyncEvents.compose g f)
        (@le _ (hom_PO E1 E2) ++> @le _ (hom_PO E1 E3)).
    Proof.
      intros f1 f2 Hf x.
      unfold PosetAsyncEvents.compose, L.Kl.compose, L.ext.
      simpl.
      set (LE3 := L.omap E3).
      set (POLE3 := Poset.structure LE3).
      unfold hom_le in Hf.
      (* The composition involves applying the extension of g to f(x) *)
      (* Since f1(x) ≤ f2(x) and the extension of g is monotone, we get the result *)
      apply (Poset.morphism _ _ (L.KlU.fmap g)).
      apply Hf.
    Qed.

    Lemma compose_monotonic_r (f : PosetAsyncEvents.m E1 E2) :
      Monotonic (fun g => PosetAsyncEvents.compose g f)
        (@le _ (hom_PO E2 E3) ++> @le _ (hom_PO E1 E3)).
    Proof.
      intros g1 g2 Hg x.
      unfold PosetAsyncEvents.compose, L.Kl.compose.
      apply ext_monotonic; auto.
    Qed.

  End ComposeMonotonic.

End PosetAsyncEventsEnriched.

(** ** PosetAsyncEvents as a Poset-Enriched Category *)

Module PosetAsyncEventsPosetCat <: PosetCategoryDefinition.
  Module C := PosetAsyncEvents.
  Include C.

  Definition hom_po (E1 E2 : t) : DCPO.PartialOrder (m E1 E2) :=
    PosetAsyncEventsEnriched.hom_PO E1 E2.

  Definition compose_monotonic_l (E1 E2 E3 : t) (g : m E2 E3) :
    Monotonic (fun f => compose g f) (@le _ (hom_po E1 E2) ++> @le _ (hom_po E1 E3)) :=
    PosetAsyncEventsEnriched.compose_monotonic_l E1 E2 E3 g.

  Definition compose_monotonic_r (E1 E2 E3 : t) (f : m E1 E2) :
    Monotonic (fun g => compose g f) (@le _ (hom_po E2 E3) ++> @le _ (hom_po E1 E3)) :=
    PosetAsyncEventsEnriched.compose_monotonic_r E1 E2 E3 f.

End PosetAsyncEventsPosetCat.
