Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import coqrel.LogicalRelations.
Require Import models.DCPO.

(** * Poset-enriched categories *)

Module Type PosetCategoryDefinition <: CategoryDefinition.
    Declare Module C : CategoryDefinition.
    Include C.

    Parameter hom_po : forall A B, PartialOrder (m A B).

    Parameter compose_monotonic_l : forall A B C (g : m B C),
        Monotonic (fun f => compose g f) (@le _ (hom_po A B) ++> @le _ (hom_po A C)).

    Parameter compose_monotonic_r : forall A B C (f : m A B),
        Monotonic (fun g => compose g f) (@le _ (hom_po B C) ++> @le _ (hom_po A C)).
End PosetCategoryDefinition.

Module PosetCategoryTheory (C : PosetCategoryDefinition).
    Include CategoryTheory C.
End PosetCategoryTheory.

Module Type PosetCategory.
  Include PosetCategoryDefinition.
  Include PosetCategoryTheory.
End PosetCategory.

(** * Monotone functors for Poset-enriched categories *)

Module Type PosetFunctorDefinition
  (C : PosetCategoryDefinition) (D : PosetCategoryDefinition).

  Declare Module F : FunctorDefinition C D.
  Include F.

  (** fmap is monotone w.r.t. the hom-set orders *)
  Parameter fmap_monotonic :
    forall {A B},
      Monotonic (@fmap A B) (@le _ (C.hom_po A B) ++> @le _ (D.hom_po (omap A) (omap B))).

End PosetFunctorDefinition.

Module PosetFunctorTheory (C D : PosetCategory) (F : PosetFunctorDefinition C D).
  Include FunctorTheory C D F.
End PosetFunctorTheory.

Module Type PosetFunctor (C D : PosetCategory).
  Include PosetFunctorDefinition C D.
  Include PosetFunctorTheory C D.
End PosetFunctor.

(** * Monotone bifunctors for Poset-enriched categories *)

Module Type PosetBifunctorDefinition
  (C1 : PosetCategoryDefinition) (C2 : PosetCategoryDefinition) (D : PosetCategoryDefinition).

  Declare Module F : BifunctorDefinition C1 C2 D.
  Include F.

  (** fmap is monotone in the first argument *)
  Parameter fmap_monotonic_l :
    forall {A1 A2 B1 B2} (f2 : C2.m A2 B2),
      Monotonic (fun f1 => fmap f1 f2)
        (@le _ (C1.hom_po A1 B1) ++> @le _ (D.hom_po (omap A1 A2) (omap B1 B2))).

  (** fmap is monotone in the second argument *)
  Parameter fmap_monotonic_r :
    forall {A1 A2 B1 B2} (f1 : C1.m A1 B1),
      Monotonic (fun f2 => fmap f1 f2)
        (@le _ (C2.hom_po A2 B2) ++> @le _ (D.hom_po (omap A1 A2) (omap B1 B2))).

End PosetBifunctorDefinition.

Module PosetBifunctorTheory (C1 C2 D : PosetCategory) (F : PosetBifunctorDefinition C1 C2 D).
  Include BifunctorTheory C1 C2 D F.

End PosetBifunctorTheory.

Module Type PosetBifunctor (C1 C2 D : PosetCategory).
  Include PosetBifunctorDefinition C1 C2 D.
  Include PosetBifunctorTheory C1 C2 D.
End PosetBifunctor.
