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
      (fun ev => ɛ, fun ev => ɛ).

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

  (** We define a handy alias [sig] for the signature type [Sig.t] *)
  Notation sig := t. 

  (** Events in strategies and OALTS between A and B will be generated by A -o B *)
  Notation "A -o B" := (¬A && B)%obj (at level 50, left associativity) : obj_scope.

  (** The way we actually generate these events is by [«A -o B»] for strategies 
    and [«A -o B» + ɛ] for OALTS *)
  Delimit Scope event_obj_scope with event_obj.
  Delimit Scope event_hom_scope with event_hom.
  Notation "« f »" := (AsyncEvents.Prod.fmap f^- f^+) : event_hom_scope.
  Notation "« A »" := (AsyncEvents.Prod.omap A^- A^+) : event_obj_scope.

  Module ProdF <: Functor SigBaseBicartesian AsyncEvents.

    Open Scope event_hom_scope.

    Definition omap (A : sig) := «A»%event_obj.

    Definition fmap {A B : sig} (f : m A B) := «f».

    Proposition fmap_id :
      forall A, «id A» = AsyncEvents.id («A»%event_obj).
    Proof.
      intros. rewrite AsyncEvents.Prod.fmap_id. reflexivity.
    Qed.

    Proposition fmap_compose :
      forall {A B C} (g : m B C) (f : m A B),
        «(g @ f)» = AsyncEvents.compose «g» «f».
    Proof.
      intros. unfold compose; simpl.
      rewrite AsyncEvents.Prod.fmap_compose. reflexivity.
    Qed.

    Include FunctorTheory SigBaseBicartesian AsyncEvents.
  End ProdF.

  (** It is worth hashing out what events are available in [«A -o B»].

    The structure is [⟨Env | Sys⟩] where:
    - [Env = A^+ && B^-] (environment events)
    - [Sys = A^- && B^+] (system events)

    Each of Env and Sys can be sync, async-left, async-right, or empty.
    This gives 4 x 4 = 16 combinations, minus the empty event = 15 events.

    The table below shows all 15 events. We mark:
    - [A-sync] when both [a^+] (env) and [a^-] (sys) are present
    - [B-sync] when both [b^-] (env) and [b^+] (sys) are present

<<
                 | Sys=⟨a⁻|b⁺⟩ | Sys=⟨a⁻|⟩  | Sys=⟨|b⁺⟩  | Sys=ɛ
    -------------+-------------+------------+------------+---------
    Env=⟨a⁺|b⁻⟩  | AB-sync     | A-sync, b⁻ | B-sync, a⁺ | a⁺, b⁻
    Env=⟨a⁺|⟩    | A-sync, b⁺  | A-sync     | a⁺, b⁺     | a⁺
    Env=⟨|b⁻⟩    | B-sync, a⁻  | a⁻, b⁻     | B-sync     | b⁻
    Env=ɛ        | a⁻, b⁺      | a⁻         | b⁺         | (empty)
>>

    Key insight: This encoding allows A-sync and B-sync simultaneously
    (top-left cell), which is needed for I/O automata style composition.
  *)


  (** At this point, we can define projections of events of [A -o B] to
    events of [A] and [B].

    Recall: «A -o B» = asyncProd Env Sys where:
      - Env = asyncProd A^+ B^-
      - Sys = asyncProd A^- B^+
    and «A» = asyncProd A^- A^+, «B» = asyncProd B^- B^+.

    We define projections using composition of the cartesian projections:
    - projL extracts A^- from Sys (via p1) and A^+ from Env (via p1)
    - projR extracts B^- from Env (via p2) and B^+ from Sys (via p2) *)
  Section Projections.
    Import AsyncEvents.

    Local Open Scope event_obj_scope.

    (** Project the A component from an A -o B event.
        A^- comes from Sys (p2 on outer, p1 on inner)
        A^+ comes from Env (p1 on outer, p1 on inner) *)
    Definition projL {A B : sig} : «A -o B» -> Async «A» :=
      Prod.pair (Prod.p1 @ Prod.p2) (Prod.p1 @ Prod.p1).

    (** Project the B component from an A -o B event.
        B^- comes from Env (p1 on outer, p2 on inner)
        B^+ comes from Sys (p2 on outer, p2 on inner) *)
    Definition projR {A B : sig} : «A -o B» -> Async «B» :=
      Prod.pair (Prod.p2 @ Prod.p1) (Prod.p2 @ Prod.p2).
  End Projections.

  (** In certain circumstnces, we will want to match on postive and
    negative events of [A] so we define special notation for that purpose. *)
  Notation "[ f ]" := (AsyncEvents.Plus.fmap f^- f^+) : event_hom_scope.
  Notation "[ A ]" := (AsyncEvents.Plus.omap A^- A^+) : event_obj_scope.

  Module PlusF <: Functor SigBaseBicartesian AsyncEvents.

    Open Scope event_hom_scope.

    Definition omap (A : sig) := [A]%event_obj.

    Definition fmap {A B : sig} (f : Sig.m A B) := [f].

    Proposition fmap_id :
      forall A, [id A] = AsyncEvents.id ([A]%event_obj).
    Proof.
      intros. rewrite AsyncEvents.Plus.fmap_id. reflexivity.
    Qed.

    Proposition fmap_compose :
      forall {A B C} (g : m B C) (f : m A B),
        [(g @ f)] = AsyncEvents.compose [g] [f].
    Proof.
      intros. unfold compose; simpl.
      rewrite AsyncEvents.Plus.fmap_compose. reflexivity.
    Qed.

    Include FunctorTheory SigBaseBicartesian AsyncEvents.
  End PlusF.

  Section ComposeHelpers.
    Import AsyncEvents.

    Local Open Scope event_obj_scope.

    (** ** Helpers for strategy composition *)

    (** Embed an A-only event from «A -o B» into «A -o C».
        A-only events have projR = ɛ, meaning no B component:
        - ⟨⟨ap | ⟩ | ⟨am | ⟩⟩ - A sync
        - ⟨⟨ap | ⟩ | ⟩ - env A only
        - ⟨ | ⟨am | ⟩⟩ - sys A only *)
    Definition embed_L {A B C : sig} (ev : «A -o B») (H : projR ev = ɛ) : «A -o C».
    Proof.
      (* ev : asyncProd (asyncProd A⁺ B⁻) (asyncProd A⁻ B⁺) *)
      destruct ev as [env sys | env | sys].
      - (* sync env sys *)
        destruct env as [ap bm | ap | bm];
        destruct sys as [am bp | am | bp];
        unfold projR, Prod.pair, compose, Prod.p1, Prod.p2 in H; simpl in H;
        try discriminate H.
        (* Only ⟨⟨ap | ⟩ | ⟨am | ⟩⟩ remains *)
        exact ⟨⟨ap | ⟩ | ⟨am | ⟩⟩.
      - (* asyncl env *)
        destruct env as [ap bm | ap | bm];
        unfold projR, Prod.pair, compose, Prod.p1, Prod.p2 in H; simpl in H;
        try discriminate H.
        (* Only ⟨⟨ap | ⟩ | ⟩ remains *)
        exact ⟨⟨ap | ⟩ | ⟩.
      - (* asyncr sys *)
        destruct sys as [am bp | am | bp];
        unfold projR, Prod.pair, compose, Prod.p1, Prod.p2 in H; simpl in H;
        try discriminate H.
        (* Only ⟨ | ⟨am | ⟩⟩ remains *)
        exact ⟨ | ⟨am | ⟩⟩.
    Defined.

    (** Embed a C-only event from «B -o C» into «A -o C».
        C-only events have projL = ɛ, meaning no B component:
        - ⟨⟨ | cm⟩ | ⟨ | cp⟩⟩ - C sync
        - ⟨⟨ | cm⟩ | ⟩ - env C only
        - ⟨ | ⟨ | cp⟩⟩ - sys C only *)
    Definition embed_R {A B C : sig} (ev : «B -o C») (H : projL ev = ɛ) : «A -o C».
    Proof.
      (* ev : asyncProd (asyncProd B⁺ C⁻) (asyncProd B⁻ C⁺) *)
      destruct ev as [env sys | env | sys].
      - (* sync env sys *)
        destruct env as [bp cm | bp | cm];
        destruct sys as [bm cp | bm | cp];
        unfold projL, Prod.pair, compose, Prod.p1, Prod.p2 in H; simpl in H;
        try discriminate H.
        (* Only ⟨⟨ | cm⟩ | ⟨ | cp⟩⟩ remains *)
        exact ⟨⟨ | cm⟩ | ⟨ | cp⟩⟩.
      - (* asyncl env *)
        destruct env as [bp cm | bp | cm];
        unfold projL, Prod.pair, compose, Prod.p1, Prod.p2 in H; simpl in H;
        try discriminate H.
        (* Only ⟨⟨ | cm⟩ | ⟩ remains *)
        exact ⟨⟨ | cm⟩ | ⟩.
      - (* asyncr sys *)
        destruct sys as [bm cp | bm | cp];
        unfold projL, Prod.pair, compose, Prod.p1, Prod.p2 in H; simpl in H;
        try discriminate H.
        (* Only ⟨ | ⟨ | cp⟩⟩ remains *)
        exact ⟨ | ⟨ | cp⟩⟩.
    Defined.

    (** Does a sync have at least one visible A or C component?
        Returns true if not a pure sync
        (pure sync = both evσ and evτ are asynchronous B events) *)
    Definition has_visible_AC {A B C : sig} (evσ : «A -o B») (evτ : «B -o C») : bool :=
      match projL evσ, projR evτ with
      | ɛ, ɛ => false  (* pure sync: no A component, no C component *)
      | _, _ => true   (* has A component, C component, or both *)
      end.
  End ComposeHelpers.

End Sig.
