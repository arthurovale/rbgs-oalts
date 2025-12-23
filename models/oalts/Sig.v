Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.MonoidalCategory.
Require Import interfaces.Limits.
Require Import AsyncEvents.
Require Import Coq.Logic.FunctionalExtensionality.

(** * Polarized Signatures *)

(** ** A Polarized signature is a pair of two asynchronous event sets
  [(A^-, A^+)]. A "base" morphism of signatures is a pair of
  asynchronous morphisms f^- : A^- -> B^- and f^+ : A^+ -> B^+ *)
Module SigBase <: Category.
  Import AsyncEvents.

  Definition t : Type := Type * Type.

  Notation "A ^-" := (fst A) (at level 1, only parsing).
  Notation "A ^+" := (snd A) (at level 1, only parsing).

  Definition m : t -> t -> Type :=
    fun A => fun B =>
      ((AsyncEvents.m B^- A^-) * (AsyncEvents.m A^+ B^+))%type.

  Definition id (A : t) : m A A :=
    (AsyncEvents.id A^-, AsyncEvents.id A^+).

  Definition compose : forall {A B C}, m B C -> m A B -> m A C :=
    fun A B C => fun g => fun f => (f^- @ g^-, g^+ @ f^+).

  Proposition compose_id_left :
    forall {A B} (f : m A B), compose (id B) f = f.
  Proof.
    intros; apply injective_projections.
    - apply AsyncEvents.compose_id_right.
    - apply AsyncEvents.compose_id_left.
  Qed.

  Proposition compose_id_right :
    forall {A B} (f : m A B), compose f (id A) = f.
  Proof.
    intros; apply injective_projections.
    - apply AsyncEvents.compose_id_left.
    - apply AsyncEvents.compose_id_right.
  Qed.

  Proposition compose_assoc :
    forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
    compose (compose h g) f = compose h (compose g f).
  Proof.
    intros; apply injective_projections.
    - symmetry; apply AsyncEvents.compose_assoc.
    - apply AsyncEvents.compose_assoc.
  Qed.

  Include CategoryTheory.
  Include AddOp.
End SigBase.

(** ** Bicartesian structure for SigBase
    We show that SigBase has both products and coproducts. *)
Module SigBaseBicartesian <: BicartesianCategory.
  Import AsyncEvents.
  Include SigBase.

  (** First we establish the cartesian (product) structure *)
  Module Prod <: CartesianStructure SigBase.

    (** Terminal object: (unit, unit) *)
    Definition unit : t := (Empty_set : Type, Empty_set : Type).

    Definition ter (X : t) : m X unit :=
      (Plus.ini X^-, Prod.ter X^+).

    Proposition ter_uni : forall {X} (x y : m X unit), x = y.
    Proof.
      intros; apply injective_projections.
      - apply Plus.ini_uni.
      - apply Prod.ter_uni.
    Qed.

    (** Binary products: (A-, A+) * (B-, B+) = (A- + B-, A+ * B+)
        The negative component uses coproduct due to contravariance *)
    Definition omap (A B : t) : t :=
      (A^- + B^-, A^+ && B^+)%obj.

    Definition p1 {A B : t} : m (omap A B) A :=
      (Plus.i1, Prod.p1).

    Definition p2 {A B : t} : m (omap A B) B :=
      (Plus.i2, Prod.p2).

    Definition pair {X A B : t}
      (f : m X A) (g : m X B) : m X (omap A B) :=
      (Plus.copair f^- g^-, Prod.pair f^+ g^+).

    Proposition p1_pair : forall {X A B} (f : m X A) (g : m X B),
      compose p1 (pair f g) = f.
    Proof.
      intros; apply injective_projections.
      - apply Plus.copair_i1.
      - apply Prod.p1_pair.
    Qed.

    Proposition p2_pair : forall {X A B} (f : m X A) (g : m X B),
      compose p2 (pair f g) = g.
    Proof.
      intros; apply injective_projections.
      - apply Plus.copair_i2.
      - apply Prod.p2_pair.
    Qed.

    Proposition pair_pi_compose : forall {X A B} f,
      @pair X A B (compose p1 f) (compose p2 f) = f.
    Proof.
      intros; apply injective_projections.
      - apply Plus.copair_iota_compose.
      - apply Prod.pair_pi_compose.
    Qed.

    Include CartesianStructureTheory SigBase.
    Include BifunctorTheory SigBase SigBase SigBase.
    Include SymmetricMonoidalStructureTheory SigBase.
  End Prod.

  Include CartesianTheory SigBase.

  (** Then we add the cocartesian (coproduct) structure *)
  Module Plus <: CocartesianStructure SigBase.

    (** Initial object: (Empty_set, Empty_set) *)
    Definition unit : t := (Empty_set : Type, Empty_set : Type).

    Definition ini (X : t) : m unit X :=
      (AsyncEvents.Prod.ter X^-, AsyncEvents.Plus.ini X^+).

    Proposition ini_uni : forall {X} (x y : m unit X), x = y.
    Proof.
      intros; apply injective_projections.
      - apply AsyncEvents.Prod.ter_uni.
      - apply AsyncEvents.Plus.ini_uni.
    Qed.

    (** Binary coproducts: (A-, A+) + (B-, B+) = (A- * B-, A+ + B+)
        The negative component uses product due to contravariance *)
    Definition omap (A B : t) : t :=
      (AsyncEvents.Prod.omap A^- B^-, (A^+ + B^+)%obj).

    Definition i1 {A B : t} : m A (omap A B) :=
      (AsyncEvents.Prod.p1, AsyncEvents.Plus.i1).

    Definition i2 {A B : t} : m B (omap A B) :=
      (AsyncEvents.Prod.p2, AsyncEvents.Plus.i2).

    Definition copair {X A B : t}
      (f : m A X) (g : m B X) : m (omap A B) X :=
      (AsyncEvents.Prod.pair f^- g^-, AsyncEvents.Plus.copair f^+ g^+).

    Proposition copair_i1 : forall {X A B} (f : m A X) (g : m B X),
      compose (copair f g) i1 = f.
    Proof.
      intros; apply injective_projections.
      - apply AsyncEvents.Prod.p1_pair.
      - apply AsyncEvents.Plus.copair_i1.
    Qed.

    Proposition copair_i2 : forall {X A B} (f : m A X) (g : m B X),
      compose (copair f g) i2 = g.
    Proof.
      intros; apply injective_projections.
      - apply AsyncEvents.Prod.p2_pair.
      - apply AsyncEvents.Plus.copair_i2.
    Qed.

    Proposition copair_iota_compose : forall {X A B} x,
      @copair X A B (compose x i1) (compose x i2) = x.
    Proof.
      intros; apply injective_projections.
      - apply AsyncEvents.Prod.pair_pi_compose.
      - apply AsyncEvents.Plus.copair_iota_compose.
    Qed.

    Include CocartesianStructureTheory SigBase.
    Include BifunctorTheory SigBase SigBase SigBase.
    Include SymmetricMonoidalStructureTheory SigBase.
  End Plus.

  Include CocartesianTheory SigBase.

End SigBaseBicartesian.

Module Negate <: Functor SigBase SigBase.Op.
  Import SigBaseBicartesian.
  Open Scope obj_scope.
  Open Scope hom_scope.
  (** Negate swaps the polarity: (A^-, A^+) ↦ (A^+, A^-)
      This is a contravariant functor: fmap f : ¬B → ¬A when f : A → B *)

  Definition omap (A : t) : t := (A^+, A^-).

  Notation "¬ A" := (omap A) (at level 35, right associativity) : obj_scope.

  (** Contravariant: f : A → B maps to ¬f : ¬B → ¬A *)
  Definition fmap {A B : t} (f : m A B) : m (¬B) (¬A) := (f^+, f^-).

  Notation "¬ f" := (fmap f) (at level 35, right associativity) : hom_scope.

  Proposition fmap_id : forall A, ¬(id A) = id (¬ A).
  Proof.
    reflexivity.
  Qed.

  (** Contravariant functor law: ¬(g ∘ f) = ¬f ∘ ¬g *)
  Proposition fmap_compose :
    forall {A B C} (g : m B C) (f : m A B),
      ¬(compose g f) = compose (¬f) (¬g).
  Proof.
    reflexivity.
  Qed.

  Include FunctorTheory SigBase SigBase.Op.

  Proposition faithful :
    forall {A B} (f g : m A B), ¬f = ¬g -> f = g.
  Proof.
    intros; inversion H; apply injective_projections; assumption.
  Qed.

  Proposition involutive :
    forall {A B} (f : m A B), ¬¬f = f.
  Proof.
    unfold fmap; destruct f; reflexivity.
  Qed.

  Close Scope hom_scope.

  (** ** De Morgan Laws *)

  (** ¬(A × B) = ¬A + ¬B *)
  Proposition demorgan_prod : forall A B,
    ¬ (A && B) =  (¬ A) + (¬ B).
  Proof.
    reflexivity.
  Qed.

  (** ¬(A + B) = ¬A × ¬B *)
  Proposition demorgan_plus : forall A B,
    ¬ (A + B) = (¬ A) && (¬ B).
  Proof.
    reflexivity.
  Qed.

  (** ¬1 = 0 (negation of terminal is initial) *)
  Proposition demorgan_unit : ¬ T = 0.
  Proof.
    reflexivity.
  Qed.

  (** ¬0 = 1 (negation of initial is terminal) *)
  Proposition demorgan_zero : ¬ 0 = T.
  Proof.
    reflexivity.
  Qed.

End Negate.

Module Sig <: BicartesianCategory.
  Include SigBaseBicartesian.
  Include Negate.
End Sig.
