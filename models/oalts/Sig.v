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

Module Sig <: BicartesianCategory.
  Include SigBaseBicartesian.

  (** We define a handy alias [sig] for the signature type [Sig.t] *)
  Notation sig := t. 

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

  (** Events in strategies and OALTS between A and B will be generated by A -o B *)
  Notation "A -o B" := (A && B)%obj (at level 50, left associativity) : obj_scope.

  (** Events in [[A -o B]] are a sum of two asyncProds:

    [A -o B = A && B = (A^- && B^-, A^+ && B^+)]
    [[A -o B] = (A^- && B^-) + (A^+ && B^+)]

    Left summand (inl) from [A^- && B^-] (input events):
    - [inl ⟨a^- | b^-⟩]: A input synced with B input
    - [inl ⟨a^- |⟩]: A input only
    - [inl ⟨| b^-⟩]: B input only

    Right summand (inr) from [A^+ && B^+] (output events):
    - [inr ⟨a^+ | b^+⟩]: A output synced with B output
    - [inr ⟨a^+ |⟩]: A output only
    - [inr ⟨| b^+⟩]: B output only
  *)


  (** To make events of [[A -o B]] we introduce some notation for 
    [inl] and [inr], calling them [neg] (meaning an A^- && B^- event) and 
    [pos] (meaning an A^+ && B^+ event), respectively. *)
  Notation "'neg' x" := (inl x) (at level 10, x at next level) : event_obj_scope.
  Notation "'pos' x" := (inr x) (at level 10, x at next level) : event_obj_scope.
  
  (** At this point, we can define projections of events of [A -o B] to 
    events of [A] and [B] *)
  Section Projections.
    Import AsyncEvents.

    Local Open Scope event_obj_scope.
    
    Definition projL {A B : sig} : [A -o B] -> Async [A] :=
      (Prod.p1 + Prod.p1).

    Definition projR {A B : sig} : [A -o B] -> Async [B] :=
      (Prod.p2 + Prod.p2).

    Lemma projL_ProjR_eq {A B : sig} {ev ev' : [A -o B]} :
      projL ev = projL ev' -> projR ev = projR ev' ->
      ev = ev'.
    Proof.
      intros HL HR;
      destruct ev as [[evm | evm | evm] | [evp | evp | evp]]; 
      destruct ev' as [[evm' | evm' | evm'] | [evp' | evp' | evp']]; 
      simpl in *.
      all: try unfold Plus.i1, Plus.i2, Prod.p1, Prod.p2, compose in HL, HR;  simpl.
      all: inversion HL; inversion HR; subst; reflexivity.
    Qed.

    Lemma projL_projR_eps {A B : sig} {ev : [A -o B]} :
      projL ev = ɛ -> projR ev = ɛ -> False.
    Proof.
      intros HL HR.
      destruct ev as [[evm | am | bm] | [evp | ap | bp]]; 
      simpl in *; discriminate.
    Qed.

  End Projections.

  Tactic Notation "unfold_projL" := 
        (unfold projL, AsyncEvents.Plus.fmap, 
              AsyncEvents.Plus.i1, AsyncEvents.Plus.i2,
              AsyncEvents.Prod.p1,
              AsyncEvents.compose; simpl).

  Tactic Notation "unfold_projL" "in" hyp(H) := 
    (unfold projL, AsyncEvents.Plus.fmap, 
          AsyncEvents.Plus.i1, AsyncEvents.Plus.i2,
          AsyncEvents.Prod.p1,
          AsyncEvents.compose in H; simpl in H).

  Tactic Notation "unfold_projR" := 
    (unfold projR, AsyncEvents.Plus.fmap, 
          AsyncEvents.Plus.i1, AsyncEvents.Plus.i2,
          AsyncEvents.Prod.p2,
          AsyncEvents.compose; simpl).

  Tactic Notation "unfold_projR" "in" hyp(H) := 
    (unfold projR, AsyncEvents.Plus.fmap, 
          AsyncEvents.Plus.i1, AsyncEvents.Plus.i2,
          AsyncEvents.Prod.p2,
          AsyncEvents.compose in H; simpl in H).

  Tactic Notation "unfold_proj" := 
    (unfold projL, projR, AsyncEvents.Plus.fmap, 
          AsyncEvents.Plus.i1, AsyncEvents.Plus.i2,
          AsyncEvents.Prod.p1, AsyncEvents.Prod.p2,
          AsyncEvents.compose; simpl).

  Tactic Notation "unfold_proj" "in" hyp(H) := 
    (unfold projL, projR, AsyncEvents.Plus.fmap, 
          AsyncEvents.Plus.i1, AsyncEvents.Plus.i2,
          AsyncEvents.Prod.p1, AsyncEvents.Prod.p2,
          AsyncEvents.compose in H; simpl in H).
              
End Sig.
