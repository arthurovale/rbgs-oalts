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
      ((AsyncEvents.m A^- B^-) * (AsyncEvents.m A^+ B^+))%type.

  Definition id (A : t) : m A A := (id A^-, id A^+).

  Definition compose : forall {A B C}, m B C -> m A B -> m A C :=
    fun A B C => fun g => fun f => (g^- @ f^-, g^+ @ f^+).

  Proposition compose_id_left :
    forall {A B} (f : m A B), compose (id B) f = f.
  Proof.
    intros; apply injective_projections; 
    apply AsyncEvents.compose_id_left.
  Qed.

  Proposition compose_id_right :
    forall {A B} (f : m A B), compose f (id A) = f.
  Proof.
    intros; apply injective_projections; 
    apply AsyncEvents.compose_id_right.
  Qed.

  Proposition compose_assoc :
    forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
    compose (compose h g) f = compose h (compose g f).
  Proof.
    intros; apply injective_projections; 
    apply AsyncEvents.compose_assoc.
  Qed.

  Include CategoryTheory.
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
      (fun ev => τ, fun ev => τ).

    Proposition ter_uni : forall {X} (x y : SigBase.m X unit), x = y.
    Proof.
      intros; apply injective_projections; apply Prod.ter_uni.
    Qed.

    (** Binary products: (A-, A+) * (B-, B+) = (A- * B-, A+ * B+) *)
    Definition omap (A B : SigBase.t) : SigBase.t :=
      (A^- && B^-, A^+ && B^+)%obj.

    Definition p1 {A B : SigBase.t} : SigBase.m (omap A B) A :=
      (Prod.p1, Prod.p1).

    Definition p2 {A B : SigBase.t} : SigBase.m (omap A B) B :=
      (Prod.p2, Prod.p2).

    Definition pair {X A B : SigBase.t}
      (f : SigBase.m X A) (g : SigBase.m X B) : SigBase.m X (omap A B) :=
      (Prod.pair f^- g^-, Prod.pair f^+ g^+).

    Proposition p1_pair : forall {X A B} (f : SigBase.m X A) (g : SigBase.m X B),
      SigBase.compose p1 (pair f g) = f.
    Proof.
      intros; apply injective_projections; apply Prod.p1_pair.
    Qed.

    Proposition p2_pair : forall {X A B} (f : SigBase.m X A) (g : SigBase.m X B),
      SigBase.compose p2 (pair f g) = g.
    Proof.
      intros; apply injective_projections; apply Prod.p2_pair.
    Qed.

    Proposition pair_pi_compose : forall {X A B} f,
      @pair X A B (SigBase.compose p1 f) (SigBase.compose p2 f) = f.
    Proof.
      intros; apply injective_projections; apply Prod.pair_pi_compose.
    Qed.

    Include CartesianStructureTheory SigBase.
    Include BifunctorTheory SigBase SigBase SigBase.
    Include SymmetricMonoidalStructureTheory SigBase.
  End Prod.

  Include CartesianTheory SigBase.

  (** Then we add the cocartesian (coproduct) structure *)
  Module Plus <: CocartesianStructure SigBase.
    Import SigBase.

    (** Initial object: (Empty_set, Empty_set) *)
    Definition unit : SigBase.t := (Empty_set : Type, Empty_set : Type).

    Definition ini (X : SigBase.t) : SigBase.m unit X :=
      (Plus.ini X^-, Plus.ini X^+).

    Proposition ini_uni : forall {X} (x y : SigBase.m unit X), x = y.
    Proof.
      intros; apply injective_projections; apply Plus.ini_uni.
    Qed.

    (** Binary coproducts: (A-, A+) + (B-, B+) = (A- + B-, A+ + B+) *)
    Definition omap (A B : SigBase.t) : SigBase.t :=
      ((A^- + B^-)%type, (A^+ + B^+)%type).

    Definition i1 {A B : SigBase.t} : SigBase.m A (omap A B) :=
      (Plus.i1, Plus.i1).

    Definition i2 {A B : SigBase.t} : SigBase.m B (omap A B) :=
      (Plus.i2, Plus.i2).

    Definition copair {X A B : SigBase.t}
      (f : SigBase.m A X) (g : SigBase.m B X) : SigBase.m (omap A B) X :=
      (Plus.copair f^- g^-, Plus.copair f^+ g^+).

    Proposition copair_i1 : forall {X A B} (f : SigBase.m A X) (g : SigBase.m B X),
      SigBase.compose (copair f g) i1 = f.
    Proof.
      intros; apply injective_projections; apply Plus.copair_i1.
    Qed.

    Proposition copair_i2 : forall {X A B} (f : SigBase.m A X) (g : SigBase.m B X),
      SigBase.compose (copair f g) i2 = g.
    Proof.
      intros; apply injective_projections; apply Plus.copair_i2.
    Qed.

    Proposition copair_iota_compose : forall {X A B} x,
      @copair X A B (SigBase.compose x i1) (SigBase.compose x i2) = x.
    Proof.
      intros; apply injective_projections; apply Plus.copair_iota_compose.
    Qed.

    Include CocartesianStructureTheory SigBase.
    Include BifunctorTheory SigBase SigBase SigBase.
    Include SymmetricMonoidalStructureTheory SigBase.
  End Plus.

  Include CocartesianTheory SigBase.

End SigBaseBicartesian.

Module Negate <: FaithfulFunctor SigBase SigBase.
  Import SigBaseBicartesian.
  Open Scope obj_scope.
  Open Scope hom_scope.

  (** Negate swaps the polarity: (A^-, A^+) ↦ (A^+, A^-) *)

  Definition omap (A : t) : t :=  (A^+, A^-).
  Notation "¬ A" := (omap A) (at level 35, right associativity) : obj_scope.

  Definition fmap {A B : t} (f : m A B) : m (¬A) (¬B) := (f^+, f^-).
  Notation "¬ f" := (fmap f) (at level 35, right associativity) : hom_scope.

  Proposition fmap_id : forall A, ¬(id A) = id (omap A).
  Proof.
    reflexivity.
  Qed.

  Proposition fmap_compose :
    forall {A B C} (g : m B C) (f : m A B),
      ¬(compose g f) = compose (¬g) (¬f).
  Proof.
    reflexivity.
  Qed.

  Include FunctorTheory SigBase SigBase.

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

End Negate.

Module Sig <: BicartesianCategory.
  Include SigBaseBicartesian.
  Include Negate.

  Notation sig := t.
  Notation "⊖ x" := (AsyncEvents.vis (inl x)) (at level 10, x at next level).
  Notation "⊕ x" := (AsyncEvents.vis (inr x)) (at level 10, x at next level).
End Sig.
