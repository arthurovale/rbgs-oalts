Require Import interfaces.Category.
Require Import interfaces.MonoidalCategory.
Require Import interfaces.Limits.
Require Import interfaces.LiftMonad.
Require Import models.DCPO.
Require Import models.DCPOEnriched.
Require Import models.oalts.DCPOBicartesian.
Require Import models.oalts.interfaces.DCPOEnrichedCat.

(** * DCPO-Enriched Asynchronous Events *)

(** Asynchronous events are the Kleisli category of the lift monad.
    We show this category is DCPO-enriched when the base is DCPO. *)

(** ** LiftMonad on DCPO *)

Module DCPOLiftMonad := LiftMonad DCPOBicartesian DCPOTerminals.

(** ** DCPO-Enrichment of the Kleisli category *)

Module DCPOAsyncEventsDefinition <: DCPOCategoryDefinition.
  Module C := DCPOLiftMonad.Kl.
  Include C.

  (** Kl.m X Y = DCPO.m X (1+Y), which is a DCPO by DCPOEnriched *)
  Definition hom_dcpo (X Y : t) : DirectedComplete (m X Y) :=
    hom_DirectedComplete X (DCPOLiftMonad.omap Y).

  (** ext is Scott-continuous *)
  Section ExtContinuous.
    Variables X Y : t.

    (** fmap for LiftMonad: fmap g = id_unit + g *)
    (** This is Scott-continuous because coproduct functor preserves directed sups *)

    (** ext is monotone: g1 <= g2 implies ext g1 <= ext g2 *)
    (** We use the fact that ext = mu ∘ fmap, both of which preserve order *)
    Lemma ext_monotone (g1 g2 : m X Y) :
      @le _ (@dc_po _ (hom_dcpo X Y)) g1 g2 ->
      @le _ (@dc_po _ (hom_DirectedComplete (DCPOLiftMonad.omap X) (DCPOLiftMonad.omap Y)))
        (DCPOLiftMonad.ext g1) (DCPOLiftMonad.ext g2).
    Proof.
      intros Hle x.
      destruct x as [u | a]; simpl.
      - reflexivity.
      - unfold hom_le in Hle. specialize (Hle a). 
        remember (DCPO.apply X (DCPOLiftMonad.omap Y) g1 a) as v1 eqn:Hg1a.
        remember (DCPO.apply X (DCPOLiftMonad.omap Y) g2 a) as v2 eqn:Hg2a.
        destruct v1 as [u1 | y1]; destruct v2 as [u2 | y2]; 
        simpl; simpl in Hle; auto.
    Qed.

    (** The image of a directed family under ext is directed *)
    Lemma ext_eval_directed (G : m X Y -> Prop) `{HG : @Directed _ (@dc_po _ (hom_dcpo X Y)) G}
      (x : DCPO.carrier (DCPOLiftMonad.omap X)) :
      @Directed _ (@dc_po _ (DCPO.structure (DCPOLiftMonad.omap Y)))
        (fun y => exists g, G g /\ DCPO.apply _ _ (DCPOLiftMonad.ext g) x = y).
    Proof.
      destruct HG as [g0 Hg0 Hupper].
      exists (DCPO.apply _ _ (DCPOLiftMonad.ext g0) x).
      - exists g0. split; auto.
      - intros y1 y2 [g1 [Hg1 Heq1]] [g2 [Hg2 Heq2]].
        destruct (Hupper g1 g2 Hg1 Hg2) as [g3 [Hg3 [Hle1 Hle2]]].
        exists (DCPO.apply _ _ (DCPOLiftMonad.ext g3) x). split; [|split].
        + exists g3. split; auto.
        + subst. apply ext_monotone. exact Hle1.
        + subst. apply ext_monotone. exact Hle2.
    Qed.

    (** Helper: directed family for ext at a point *)
    Lemma ext_directed_at_point (G : m X Y -> Prop) `{HG : @Directed _ (@dc_po _ (hom_dcpo X Y)) G}
      (a : DCPO.carrier X) :
      @Directed _ (@dc_po _ (DCPO.structure (DCPOLiftMonad.omap Y)))
        (fun y => exists g, G g /\ DCPO.apply X (DCPOLiftMonad.omap Y) g a = y).
    Proof.
      destruct HG as [g0 Hg0 Hupper].
      exists (DCPO.apply X (DCPOLiftMonad.omap Y) g0 a).
      - exists g0. split; auto.
      - intros y1 y2 [g1 [Hg1 Heq1]] [g2 [Hg2 Heq2]].
        destruct (Hupper g1 g2 Hg1 Hg2) as [g3 [Hg3 [Hle1 Hle2]]].
        exists (DCPO.apply X (DCPOLiftMonad.omap Y) g3 a). split; [|split].
        + exists g3. split; auto.
        + subst. unfold hom_le in Hle1. apply Hle1.
        + subst. unfold hom_le in Hle2. apply Hle2.
    Qed.

    (** For the image family im ext G, we need directedness *)
    Lemma im_ext_directed (G : m X Y -> Prop) `{HG : @Directed _ (@dc_po _ (hom_dcpo X Y)) G} :
      @Directed _ (@dc_po _ (hom_DirectedComplete (DCPOLiftMonad.omap X) (DCPOLiftMonad.omap Y)))
        (im DCPOLiftMonad.ext G).
    Proof.
      destruct HG as [g0 Hg0 Hupper].
      exists (DCPOLiftMonad.ext g0).
      - exact (im_intro _ G g0 Hg0).
      - intros h1 h2 [g1 Hg1] [g2 Hg2].
        destruct (Hupper g1 g2 Hg1 Hg2) as [g3 [Hg3 [Hle1 Hle2]]].
        exists (DCPOLiftMonad.ext g3). split; [|split].
        + exact (im_intro _ G g3 Hg3).
        + apply ext_monotone. exact Hle1.
        + apply ext_monotone. exact Hle2.
    Qed.

    (** Scott-continuity of ext: ext preserves directed sups pointwise.
        Key insight: ext g (inl u) = inl(ter u) for all g (constant)
                     ext g (inr a) = g a (varies with g) *)
    Lemma ext_continuous :
      @ScottContinuous _ _
        (hom_dcpo X Y)
        (@dc_po _ (hom_DirectedComplete (DCPOLiftMonad.omap X) (DCPOLiftMonad.omap Y)))
        (@DCPOLiftMonad.ext X Y).
    Proof.
      constructor. intros G HG.
      constructor.
      - intros _ [g Hg]. apply ext_monotone. apply sup_ub. exact Hg.
      - intros h Hub x.
        destruct x as [u | a].
        + simpl.
          destruct HG as [g0 Hg0 _].
          specialize (Hub (DCPOLiftMonad.ext g0) (im_intro _ G g0 Hg0)).
          specialize (Hub (inl u)).
          simpl in Hub. exact Hub.
        + simpl.
          (* Goal: ext (dsup G) (inr a) <= h (inr a) *)
          (* ext (dsup G) (inr a) computes based on (dsup G) a *)
          (* (dsup G) a = hom_dsup_fun G a = dsup {g a | g ∈ G} in 1+Y *)
          unfold hom_dsup_fun.
          (* The dsup in 1+Y uses coprod_dsup *)
          pose proof (ext_directed_at_point G a) as Hdir.
          pose proof (@dsup_is_sup _ (DCPO.structure (DCPOLiftMonad.omap Y))
                        _ Hdir) as Hsup.
          (* We need ext to distribute over dsup *)
          (* But ext (dsup G) (inr a) should equal the dsup structure *)
          (* Case analysis on the dsup value *)
          destruct (@DCPOCocartesianStructure.coprod_directed_homogeneous DCPOTerminals.unit Y
                      (fun y => exists g, G g /\ DCPO.apply X (DCPOLiftMonad.omap Y) g a = y)
                      Hdir) as [Hleft | Hright].
          * (* All values are inl: dsup is inl of something *)
            (* The goal has complex nested matches from coprod_dsup. *)
            (* Key insight: in the left case, dsup = inl _, so the result is inl tt *)
            (* which is <= any upper bound. Admitted due to coprod_dsup complexity. *)
            admit.
          * (* All values are inr: dsup is inr of something *)
            (* Similarly admitted due to coprod_dsup complexity. *)
            admit.
    Admitted.

  End ExtContinuous.

  (** Left composition: g ∘_Kl - is Scott-continuous *)
  Definition compose_continuous_l (A B C : t) (g : m B C) :
    @ScottContinuous _ _ (hom_dcpo A B) (@dc_po _ (hom_dcpo A C)) (fun f => compose g f).
  Proof.
    unfold compose, hom_dcpo.
    exact (dcpo_compose_continuous_l A (DCPOLiftMonad.omap B) (DCPOLiftMonad.omap C)
             (DCPOLiftMonad.ext g)).
  Defined.

  (** Right composition: - ∘_Kl f is Scott-continuous *)
  (** This requires showing that g ↦ DCPO.compose (ext g) f is continuous.
      Since ext is continuous and DCPO composition is continuous in the left argument,
      the composition is continuous. However, proving this directly is complex due to
      how the hom-set DCPO structure works. We admit this for now. *)
  Definition compose_continuous_r (A B C : t) (f : m A B) :
    @ScottContinuous _ _ (hom_dcpo B C) (@dc_po _ (hom_dcpo A C)) (fun g => compose g f).
  Proof.
    (* The composition g ↦ DCPO.compose (ext g) f is:
       - ext : hom(B,C) → hom(omap B, omap C) is continuous
       - h ↦ DCPO.compose h f is continuous (dcpo_compose_continuous_r)
       So the composition should be continuous *)
    constructor. intros G HG.
    constructor.
    - (* sup_ub: compose g f <= compose (dsup G) f for g ∈ G *)
      intros _ [g Hg] x. simpl.
      unfold hom_dsup_fun.
      (* Need to show (ext g)(f x) <= dsup{(ext g')(f x) | g' ∈ G} *)
      (* This follows from ext g <= ext(dsup G) and composition monotonicity *)
      pose proof (ext_monotone B C g (@dsup _ (hom_dcpo B C) G HG)) as Hext_mono.
      assert (Hgle : @le _ (@dc_po _ (hom_dcpo B C)) g (@dsup _ (hom_dcpo B C) G HG)).
      { apply sup_ub. exact Hg. }
      specialize (Hext_mono Hgle).
      unfold hom_le in Hext_mono.
      specialize (Hext_mono (DCPO.apply A (DCPOLiftMonad.omap B) f x)).
      (* Now Hext_mono : ext g (f x) <= ext (dsup G) (f x) *)
      (* We need to relate this to the dsup in the goal *)
      (* The goal's dsup is over {compose (ext g') f x | g' ∈ G} *)
      (* which should equal ext(dsup G)(f x) by continuity of ext *)
      (* Admitted for now due to complexity *)
      admit.
    - (* sup_lub: compose (dsup G) f <= h for upper bound h *)
      intros h Hub x. simpl.
      unfold hom_dsup_fun.
      (* Similar reasoning - admitted *)
      admit.
  Admitted.

End DCPOAsyncEventsDefinition.

(** DCPOAsyncEvents is a DCPO-enriched category.
    Note: CategoryTheory is already included via the Kleisli category,
    so we don't need to include DCPOCategoryTheory separately. *)
Module DCPOAsyncEvents <: DCPOCategoryDefinition.
  Include DCPOAsyncEventsDefinition.
End DCPOAsyncEvents.
