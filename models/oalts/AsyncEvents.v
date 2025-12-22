Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.MonoidalCategory.
Require Import Coq.Logic.FunctionalExtensionality.

(** * Asynchronous Events *)

(** Asynchronous events are either a visible event or an invisible event. *)

(** ** First, we model asynchrony by implicitly considering tau moves
  this is nicely achieved by using the lift monad *)

Module AsyncEventsBase <: Category.

  Definition t : Type := Type.

  Notation τ := (inr tt).
  Notation "' x" := (inl x) (at level 9, x at next level).

  Definition m : t -> t -> Type :=
      fun A => fun B => A -> (B + unit).

  Program Definition id (A : t) : m A A := fun ev => 'ev.

  Program Definition compose {A B C : t} (g : m B C) (f : m A B)  :=
    fun ev =>
      match f ev with
      | 'ev' => g ev'
      | τ => τ
      end.

  Proposition compose_id_left :
    forall {A B} (f : m A B), compose (id B) f = f.
  Proof.
    intros; extensionality ev; unfold compose;
    destruct (f ev) as [ev' | []];
    easy.
  Qed.

  Proposition compose_id_right :
    forall {A B} (f : m A B), compose f (id A) = f.
  Proof.
    intros; extensionality ev; unfold compose; reflexivity.
  Qed.

  Proposition compose_assoc :
    forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
    compose (compose h g) f = compose h (compose g f).
  Proof.
    intros; extensionality ev; unfold compose;
    destruct (f ev) as [ev' | []]; reflexivity.
  Qed.

  Proposition unit_unique : forall x y : unit, x = y.
  Proof.
    destruct x; destruct y; reflexivity.
  Qed.

  Include CategoryTheory.
End AsyncEventsBase.

(** ** Bicartesian structure for AsyncEvents
    We show that AsyncEvents has both products and coproducts. *)
Module AsyncEventsBicartesian <: BicartesianCategory.
  Include AsyncEventsBase.

  (** First we establish the cartesian (product) structure *)
  Module Prod <: CartesianStructure AsyncEventsBase.

    (** Terminal object: Empty_set (any morphism to it must be τ) *)
    Definition unit : t := Empty_set : Type.

    Definition ter (X : t) : m X unit := fun ev => τ.

    Proposition ter_uni : forall {X} (x y : m X unit), x = y.
    Proof.
      intros; extensionality ev.
      destruct (x ev) as [[] | []], (y ev) as [[] | []]; reflexivity.
    Qed.

    Inductive asyncProd {A B : Type} : Type :=
    | sync (a : A) (b : B)
    | asyncl (a : A)
    | asyncr (b : B).

    (** Binary products: A × B *)
    Definition omap (A B : Type) : Type := @asyncProd A B.

    Notation "⟨ a | b ⟩" := (sync a b) (at level 0).
    Notation "⟨ a | ⟩" := (asyncl a) (at level 0).
    Notation "⟨ | b ⟩" := (asyncr b) (at level 0).

    Definition p1 {A B : t} : m (omap A B) A :=
      fun obs =>
        match obs with
        | ⟨a | b⟩ => 'a
        | ⟨a | ⟩ => 'a
        | ⟨ | b⟩ => τ
        end.

    Definition p2 {A B : t} : m (omap A B) B :=
      fun obs =>
        match obs with
        | ⟨a | b⟩ => 'b
        | ⟨a | ⟩ => τ
        | ⟨ | b⟩ => 'b
        end.

    Definition pair {X A B : t} (f : m X A) (g : m X B) : m X (omap A B) :=
      fun x =>
        match f x, g x with
        | 'a, 'b => '⟨a | b⟩
        | 'a, τ => '⟨a | ⟩
        | τ, 'b => '⟨ | b⟩
        | τ, τ => τ
        end.

    Proposition p1_pair : forall {X A B} (f : m X A) (g : m X B),
      compose p1 (pair f g) = f.
    Proof.
      intros; extensionality x; unfold compose, pair, p1.
      destruct (f x) as [a | []], (g x) as [b | []]; reflexivity.
    Qed.

    Proposition p2_pair : forall {X A B} (f : m X A) (g : m X B),
      compose p2 (pair f g) = g.
    Proof.
      intros; extensionality x; unfold compose, pair, p2.
      destruct (f x) as [a | []], (g x) as [b | []]; reflexivity.
    Qed.

    Proposition pair_pi_compose : forall {X A B} f,
      @pair X A B (compose p1 f) (compose p2 f) = f.
    Proof.
      intros; extensionality ev. unfold compose, pair, p1, p2.
      destruct (f ev) as [[a b | a | b] | []]. all: reflexivity.
    Qed.

    Include CartesianStructureTheory AsyncEventsBase.
    Include BifunctorTheory AsyncEventsBase AsyncEventsBase AsyncEventsBase.
    Include SymmetricMonoidalStructureTheory AsyncEventsBase.
  End Prod.

  Include CartesianTheory AsyncEventsBase.

  (** Then we add the cocartesian (coproduct) structure *)
  Module Plus <: CocartesianStructure AsyncEventsBase.

    (** Initial object: Empty_set *)
    Definition unit : t := Empty_set : Type.

    Definition ini (X : t) : m unit X := fun e => match e with end.

    Proposition ini_uni : forall {X} (x y : m unit X), x = y.
    Proof.
      intros; extensionality e; destruct e.
    Qed.

    (** Binary coproducts: A + B *)
    Definition omap (A B : t) : t := (A + B)%type.

    Definition i1 {A B : t} : m A (A + B)%type :=
      fun a => '(inl a).

    Definition i2 {A B : t} : m B (A + B)%type :=
      fun b => '(inr b).

    Definition copair {X A B : t} (f : m A X) (g : m B X) : m (A + B)%type X :=
      fun ab =>
        match ab with
        | inl a => f a
        | inr b => g b
        end.

    Proposition copair_i1 : forall {X A B} (f : m A X) (g : m B X),
      compose (copair f g) i1 = f.
    Proof.
      intros; extensionality a; unfold compose, copair, i1; reflexivity.
    Qed.

    Proposition copair_i2 : forall {X A B} (f : m A X) (g : m B X),
      compose (copair f g) i2 = g.
    Proof.
      intros; extensionality b; unfold compose, copair, i2; reflexivity.
    Qed.

    Proposition copair_iota_compose : forall {X A B} x,
      @copair X A B (compose x i1) (compose x i2) = x.
    Proof.
      intros; extensionality ab; unfold compose, copair, i1, i2.
      destruct ab as [a | b]; reflexivity.
    Qed.

    Include CocartesianStructureTheory AsyncEventsBase.
    Include BifunctorTheory AsyncEventsBase AsyncEventsBase AsyncEventsBase.
    Include SymmetricMonoidalStructureTheory AsyncEventsBase.
  End Plus.

End AsyncEventsBicartesian.

Module AsyncEvents <: BicartesianCategory.
  Include AsyncEventsBicartesian.
End AsyncEvents.