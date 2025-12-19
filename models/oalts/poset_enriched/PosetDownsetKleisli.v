Require Import interfaces.Category.
Require Import interfaces.ConcreteCategory.
Require Import interfaces.Monads.
Require Import models.DCPO.
Require Import models.oalts.DownsetMonad.
Require Import models.oalts.interfaces.PosetEnrichedCat.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import ProofIrrelevance.
Require Import coqrel.LogicalRelations.

(** * Poset-Enrichment of the Downset Monad's Kleisli Category *)

(** We prove that the Kleisli category of the downset monad on Poset
    is poset-enriched. This means:
    1. Hom-sets in the Kleisli category are posets (pointwise order)
    2. Kleisli composition is monotonic in both arguments *)

Module PosetDownsetKleisli.
  Import DownsetMonad.
  Import DownsetMonadDef.
  Import Poset.

  (** ** Hom-sets in Kleisli category are Posets *)

  Section KleisliHomPoset.
    Variables X Y : Poset.t.

    Let POX := Poset.structure X.
    Let POY := Poset.structure Y.

    (** Partial order on Kleisli morphisms: pointwise order *)
    Definition kl_hom_le (f g : Poset.m X (omap Y)) : Prop :=
      forall x, @dset_le Y POY (Poset.apply X (omap Y) f x) (Poset.apply X (omap Y) g x).

    Lemma kl_hom_le_preo : PreOrder kl_hom_le.
    Proof.
      constructor.
      - intros f x y Hy. exact Hy.
      - intros f g h Hfg Hgh x y Hy. apply Hgh. apply Hfg. exact Hy.
    Qed.

    Lemma kl_hom_le_po : Antisymmetric _ eq kl_hom_le.
    Proof.
      intros f g Hfg Hgf.
      apply Poset.meq. intros x.
      apply (@antisymmetry _ eq _ (@dset_le _ POY) (@dset_le_po Y POY)).
      - apply Hfg.
      - apply Hgf.
    Qed.

    Definition kl_hom_PO : DCPO.PartialOrder (Poset.m X (omap Y)) :=
      {| le := kl_hom_le;
         le_preo := kl_hom_le_preo;
         le_po := kl_hom_le_po |}.

  End KleisliHomPoset.

  (** ** The Kleisli category is Poset-enriched *)

  (** We prove that composition is monotonic in both arguments *)

  Section KleisliPosetEnriched.

    (** ext is monotonic *)
    Lemma ext_monotonic (A B : Poset.t) :
      forall f1 f2 : Kl.m A B,
        @le _ (kl_hom_PO A B) f1 f2 ->
        @le _ (kl_hom_PO (omap A) B) (ext f1) (ext f2).
    Proof.
      intros f1 f2 Hle D y Hy.
      simpl in *.
      destruct Hy as [D' [[a [Ha HD']] Hy]].
      exists D'. split.
      - exists a. split; [exact Ha |].
        intros z Hz. apply Hle. apply HD'. exact Hz.
      - exact Hy.
    Qed.

    (** Left composition: g o - is monotonic *)
    Lemma compose_monotonic_l (A B C : Poset.t) (g : DownsetMonad.Kl.m B C) :
      Monotonic (fun f => DownsetMonad.Kl.compose g f)
        (@le _ (kl_hom_PO A B) ++> @le _ (kl_hom_PO A C)).
    Proof.
      intros f1 f2 Hle x c Hc.
      unfold Kl.compose in *.
      simpl in *.
      destruct Hc as [D [[b [Hf1 HD]] Hc]].
      exists D. split.
      - exists b. split.
        + apply Hle. exact Hf1.
        + exact HD.
      - exact Hc.
    Qed.

    (** Right composition: - o f is monotonic *)
    Lemma compose_monotonic_r (A B C : Poset.t) (f : DownsetMonad.Kl.m A B) :
      Monotonic (fun g => DownsetMonad.Kl.compose g f)
        (@le _ (kl_hom_PO B C) ++> @le _ (kl_hom_PO A C)).
    Proof.
      intros g1 g2 Hle x c Hc.
      unfold Kl.compose in *.
      simpl in *.
      destruct Hc as [D [[b [Hfb HD]] Hc]].
      exists D. split.
      - exists b. split; [exact Hfb |].
        intros z Hz. apply Hle. apply HD. exact Hz.
      - exact Hc.
    Qed.

  End KleisliPosetEnriched.

End PosetDownsetKleisli.

(** ** Poset-Enriched Kleisli Category *)

(** Package as a proper poset-enriched category satisfying PosetCategoryDefinition *)

Module PosetDownsetKl <: PosetCategoryDefinition.
  Module C := DownsetMonad.Kl.
  Include C.

  Definition hom_po (A B : t) : DCPO.PartialOrder (m A B) :=
    PosetDownsetKleisli.kl_hom_PO A B.

  Definition compose_monotonic_l (A B C : t) (g : m B C) :
    Monotonic (fun f => compose g f) (@le _ (hom_po A B) ++> @le _ (hom_po A C)) :=
    PosetDownsetKleisli.compose_monotonic_l A B C g.

  Definition compose_monotonic_r (A B C : t) (f : m A B) :
    Monotonic (fun g => compose g f) (@le _ (hom_po B C) ++> @le _ (hom_po A C)) :=
    PosetDownsetKleisli.compose_monotonic_r A B C f.

End PosetDownsetKl.
