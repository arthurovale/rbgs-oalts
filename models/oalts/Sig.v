Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.MonoidalCategory.
Require Import interfaces.Limits.
Require Import models.PosetBicartesian.
Require Import models.oalts.AsyncEvent.
Require Import models.oalts.TimeDownset.
Require Import models.oalts.Alts.
Require Import models.oalts.DownsetMonad.

(** * Polarized Signatures *)

(** ** A Polarized signature is a pair of two objects [(A^-, A^+)] of C.
  A "base" morphism of signatures is a morphism f : A^- + A^+ -> A^- + B^+ *)
Module SigBaseDefinition (C : CocartesianCategory) <: Category.
  Import C.
  Open Scope obj_scope.

  Definition t : Type := C.t * C.t.
  Definition m : t -> t -> Type :=
    fun A => fun B =>
      C.m ((fst A) + (snd A)) ((fst B) + (snd B)).

  Definition id : forall A, m A A :=
    fun A => C.id ((fst A) + (snd A)).
  Definition compose : forall {A B C}, m B C -> m A B -> m A C :=
    fun A B C => fun g => fun f => g @ f.

  Proposition compose_id_left :
    forall {A B} (f : m A B), compose (id B) f = f.
  Proof.
    intros. apply compose_id_left.
  Qed.

  Proposition compose_id_right :
    forall {A B} (f : m A B), compose f (id A) = f.
  Proof.
    intros. apply compose_id_right.
  Qed.

  Proposition compose_assoc :
    forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
    compose (compose h g) f = compose h (compose g f).
  Proof.
    intros. apply compose_assoc.
  Qed.

  Include CategoryTheory.
End SigBaseDefinition.

Module Type SigBase (C : CocartesianCategory).
  Include (SigBaseDefinition C).
End SigBase.

(** ** With some work we can always derive a cocartesian structure to [SigBase C]*)
Module SigBaseCocartesian (C : CocartesianCategory) (S : SigBase C) <: CocartesianCategory.
  Include S.
  Import C.
  Open Scope obj_scope.

  Module Plus <: CocartesianStructure S.
    Import S.
    Local Infix "@" := C.compose (at level 45, right associativity) : hom_scope.

    (** Initial object: (0, 0) *)
    Definition unit : S.t := (C.Plus.unit, C.Plus.unit).

    Definition ini : forall X, S.m unit X :=
      fun X => C.Plus.copair (C.Plus.ini _) (C.Plus.ini _).

    Proposition ini_uni : forall {X} (x y : S.m unit X), x = y.
    Proof.
      intros.
      unfold S.m, unit. simpl.
      rewrite <- (C.Plus.copair_iota_compose x).
      rewrite <- (C.Plus.copair_iota_compose y).
      f_equal; apply C.Plus.ini_uni.
    Qed.

    (** Binary coproducts: (A1, A2) + (B1, B2) = (A1 + B1, A2 + B2) *)
    Definition omap (A B : S.t) : S.t :=
      (C.Plus.omap (fst A) (fst B), C.Plus.omap (snd A) (snd B)).

    Definition i1 : forall {A B : S.t}, S.m A (omap A B) :=
      fun A B => C.Plus.i1 + C.Plus.i1.

    Definition i2 : forall {A B : S.t}, S.m B (omap A B) :=
      fun A B => C.Plus.i2 + C.Plus.i2.

    Definition interchange (A1 B1 A2 B2 : C.t) : C.iso ((A1 + B1) + (A2 + B2)) ((A1 + A2) + (B1 + B2)) :=
      C.compose_iso (C.Plus.assoc A1 A2 (B1 + B2))
      (C.compose_iso (C.Plus.fmap_iso C.id_iso (C.bw_iso (C.Plus.assoc A2 B1 B2)))
      (C.compose_iso (C.Plus.fmap_iso C.id_iso (C.Plus.fmap_iso (C.Plus.swap_iso B1 A2) C.id_iso))
      (C.compose_iso (C.Plus.fmap_iso C.id_iso (C.Plus.assoc B1 A2 B2))
      (C.bw_iso (C.Plus.assoc A1 B1 (A2 + B2)))))).

    Lemma interchange_i1_i1 A1 B1 A2 B2 :
      interchange A1 B1 A2 B2 @ C.Plus.i1 @ C.Plus.i1 = C.Plus.i1 @ C.Plus.i1.
    Proof.
      unfold interchange. cbn [C.fw C.compose_iso C.bw_iso C.Plus.fmap_iso C.id_iso].
      rewrite !C.compose_assoc.
      pose (C.Plus.assoc_i1 A1 B1 (A2 + B2)). apply (C.eq_fw_bw_l_1 (C.Plus.assoc _ _ _)) in e.
      symmetry in e. rewrite e.
      rewrite C.Plus.i1_nat, C.compose_id_right.
      rewrite C.Plus.i1_nat, C.compose_id_right.
      rewrite C.Plus.i1_nat, C.compose_id_right.
      rewrite Plus.assoc_i1.
      reflexivity.
    Qed.

    Lemma interchange_i1_i2 A1 B1 A2 B2 :
      interchange A1 B1 A2 B2 @ C.Plus.i1 @ C.Plus.i2 = C.Plus.i2 @ C.Plus.i1.
    Proof.
      unfold interchange. cbn [C.fw C.compose_iso C.bw_iso C.Plus.fmap_iso C.id_iso].
      rewrite !C.compose_assoc.
      pose (C.Plus.assoc_i2_i1 A1 B1 (A2 + B2)).
      apply (C.eq_fw_bw_l_1 (C.Plus.assoc _ _ _)) in e. rewrite <- e.
      replace ((C.id A1 + Plus.assoc B1 A2 B2) @ C.Plus.i2 @ C.Plus.i1)
        with (((C.id A1 + Plus.assoc B1 A2 B2) @ C.Plus.i2) @ C.Plus.i1)
        by (rewrite <- C.compose_assoc; reflexivity).
      rewrite C.Plus.i2_nat. rewrite C.compose_assoc.
      rewrite C.Plus.assoc_i1.
      replace ((C.id A1 + (Plus.swap_iso B1 A2 + C.id B2)) @ C.Plus.i2 @ C.Plus.i1 @ C.Plus.i1)
        with ((((C.id A1 + (Plus.swap_iso B1 A2 + C.id B2)) @ C.Plus.i2) @ C.Plus.i1) @ C.Plus.i1)
        by (rewrite <- !C.compose_assoc; reflexivity).
      rewrite C.Plus.i2_nat.
      replace ((C.Plus.i2 @ (Plus.swap_iso B1 A2 + C.id B2)) @ C.Plus.i1)
        with (C.Plus.i2 (A := A1) @ ((Plus.swap_iso B1 A2 + C.id B2) @ C.Plus.i1))
        by (rewrite <- !C.compose_assoc; reflexivity).
      rewrite C.Plus.i1_nat. rewrite !C.compose_assoc.
      rewrite C.Plus.swap_i1.
      replace ((C.id A1 + C.bw (Plus.assoc A2 B1 B2)) @ C.Plus.i2 @ C.Plus.i1 @ C.Plus.i2)
        with ((((C.id A1 + C.bw (Plus.assoc A2 B1 B2)) @ C.Plus.i2) @ C.Plus.i1) @ C.Plus.i2)
        by (rewrite <- !C.compose_assoc; reflexivity).
      rewrite C.Plus.i2_nat. rewrite !C.compose_assoc.
      clear e. pose (C.Plus.assoc_i2_i1 A2 B1 B2).
      apply (C.eq_fw_bw_l_1 (C.Plus.assoc _ _ _)) in e. rewrite <- e.
      rewrite <- !C.compose_assoc.
      replace ((Plus.assoc A1 A2 (B1 + B2) @ C.Plus.i2) @ C.Plus.i2)
        with (Plus.assoc A1 A2 (B1 + B2) @ C.Plus.i2 @ C.Plus.i2)
        by (rewrite <- !C.compose_assoc; reflexivity).
      rewrite C.Plus.assoc_i2_i2. reflexivity.
    Qed.

    Lemma interchange_i2_i1 A1 B1 A2 B2 :
      interchange A1 B1 A2 B2 @ C.Plus.i2 @ C.Plus.i1 = C.Plus.i1 @ C.Plus.i2.
    Proof.
      unfold interchange. cbn [C.fw C.compose_iso C.bw_iso C.Plus.fmap_iso C.id_iso].
      rewrite !C.compose_assoc.
      pose (C.Plus.assoc_i2_i2 A1 B1 (A2 + B2)).
      apply (C.eq_fw_bw_l_1 (C.Plus.assoc _ _ _)) in e.
      symmetry in e.
      replace (C.bw (Plus.assoc A1 B1 (A2 + B2)) @ C.Plus.i2 @ C.Plus.i1)
        with ((C.bw (Plus.assoc A1 B1 (A2 + B2)) @ C.Plus.i2) @ C.Plus.i1)
        by (rewrite <- C.compose_assoc; reflexivity). rewrite e.
      replace ((C.id A1 + Plus.assoc B1 A2 B2) @ (C.Plus.i2 @ C.Plus.i2) @ C.Plus.i1)
        with ((((C.id A1 + Plus.assoc B1 A2 B2) @ C.Plus.i2) @ C.Plus.i2) @ C.Plus.i1)
        by (rewrite !C.compose_assoc; reflexivity). rewrite C.Plus.i2_nat.
      replace (((C.Plus.i2 @ Plus.assoc B1 A2 B2) @ C.Plus.i2) @ C.Plus.i1)
        with (C.Plus.i2 (A := A1) @ (Plus.assoc B1 A2 B2 @ C.Plus.i2 @ C.Plus.i1))
        by (rewrite !C.compose_assoc; reflexivity).
      rewrite C.Plus.assoc_i2_i1.
      replace ((C.id A1 + (Plus.swap_iso B1 A2 + C.id B2)) @ C.Plus.i2 @ C.Plus.i1 @ C.Plus.i2)
        with (((C.id A1 + (Plus.swap_iso B1 A2 + C.id B2)) @ C.Plus.i2) @ C.Plus.i1 @ C.Plus.i2)
        by (rewrite !C.compose_assoc; reflexivity).
      rewrite C.Plus.i2_nat. rewrite C.compose_assoc.
      replace ((Plus.swap_iso B1 A2 + C.id B2) @ C.Plus.i1 @ C.Plus.i2)
        with (((Plus.swap_iso B1 A2 + C.id B2) @ C.Plus.i1) @ C.Plus.i2)
        by (rewrite !C.compose_assoc; reflexivity).
      rewrite C.Plus.i1_nat.
      replace ((C.Plus.i1 @ Plus.swap_iso B1 A2) @ C.Plus.i2)
        with (C.Plus.i1 (B:= B2) @ (Plus.swap_iso B1 A2 @ C.Plus.i2))
        by (rewrite !C.compose_assoc; reflexivity).
      rewrite C.Plus.swap_i2.
      replace ((C.id A1 + C.bw (Plus.assoc A2 B1 B2)) @ C.Plus.i2 @ C.Plus.i1 @ C.Plus.i1)
        with (((C.id A1 + C.bw (Plus.assoc A2 B1 B2)) @ C.Plus.i2) @ C.Plus.i1 @ C.Plus.i1)
        by (rewrite !C.compose_assoc; reflexivity).
      rewrite C.Plus.i2_nat.
      clear e. pose (C.Plus.assoc_i1 A2 B1 B2).
      apply (C.eq_fw_bw_l_1 (C.Plus.assoc _ _ _)) in e.
      replace ((C.Plus.i2 @ C.bw (Plus.assoc A2 B1 B2)) @ C.Plus.i1 @ C.Plus.i1)
        with (C.Plus.i2 (A := A1) @ (C.bw (Plus.assoc A2 B1 B2)) @ C.Plus.i1 @ C.Plus.i1)
        by (rewrite !C.compose_assoc; reflexivity). rewrite <- e.
      apply C.Plus.assoc_i2_i1.
    Qed.

    Lemma interchange_i2_i2 A1 B1 A2 B2 :
      interchange A1 B1 A2 B2 @ C.Plus.i2 @ C.Plus.i2 = C.Plus.i2 @ C.Plus.i2.
    Proof.
      unfold interchange. cbn [C.fw C.compose_iso C.bw_iso C.Plus.fmap_iso C.id_iso].
      rewrite !C.compose_assoc.
      pose (C.Plus.assoc_i2_i2 A1 B1 (A2 + B2)).
      apply (C.eq_fw_bw_l_1 (C.Plus.assoc _ _ _)) in e.
      symmetry in e.
      replace (C.bw (Plus.assoc A1 B1 (A2 + B2)) @ C.Plus.i2 @ C.Plus.i2)
        with ((C.bw (Plus.assoc A1 B1 (A2 + B2)) @ C.Plus.i2) @ C.Plus.i2)
        by (rewrite <- C.compose_assoc; reflexivity). rewrite e.
      replace ((C.id A1 + Plus.assoc B1 A2 B2) @ (C.Plus.i2 @ C.Plus.i2) @ C.Plus.i2)
        with ((((C.id A1 + Plus.assoc B1 A2 B2) @ C.Plus.i2) @ C.Plus.i2) @ C.Plus.i2)
        by (rewrite <- !C.compose_assoc; reflexivity).
      rewrite C.Plus.i2_nat. rewrite !C.compose_assoc.
      rewrite C.Plus.assoc_i2_i2.
      replace ((C.id A1 + (Plus.swap_iso B1 A2 + C.id B2)) @ C.Plus.i2 @ C.Plus.i2)
        with (((C.id A1 + (Plus.swap_iso B1 A2 + C.id B2)) @ C.Plus.i2) @ C.Plus.i2)
        by (rewrite <- !C.compose_assoc; reflexivity).
      rewrite C.Plus.i2_nat. rewrite !C.compose_assoc. rewrite C.Plus.i2_nat.
      rewrite C.compose_id_right.
      replace ((C.id A1 + C.bw (Plus.assoc A2 B1 B2)) @ C.Plus.i2 @ C.Plus.i2)
        with (((C.id A1 + C.bw (Plus.assoc A2 B1 B2)) @ C.Plus.i2) @ C.Plus.i2)
        by (rewrite <- !C.compose_assoc; reflexivity).
      rewrite C.Plus.i2_nat. rewrite !C.compose_assoc.
      clear e. pose (C.Plus.assoc_i2_i2 A2 B1 B2).
      apply (C.eq_fw_bw_l_1 (C.Plus.assoc _ _ _)) in e. rewrite <- e.
      rewrite <- C.Plus.assoc_i2_i2. rewrite !C.compose_assoc. reflexivity.
    Qed.

    Lemma interchange_i1 A1 B1 A2 B2 :
      interchange A1 B1 A2 B2 @ (C.Plus.i1 + C.Plus.i1) = C.Plus.i1.
    Proof.
      rewrite <- (C.Plus.copair_iota_compose C.Plus.i1).
      unfold C.Plus.fmap. rewrite C.Plus.copair_compose.
      f_equal.
      - apply interchange_i1_i1.
      - apply interchange_i2_i1.
    Qed.

    Lemma interchange_i2 A1 B1 A2 B2 :
      interchange A1 B1 A2 B2 @ (C.Plus.i2 + C.Plus.i2) = C.Plus.i2.
    Proof.
      rewrite <- (C.Plus.copair_iota_compose C.Plus.i2).
      unfold C.Plus.fmap. rewrite C.Plus.copair_compose.
      f_equal.
      - apply interchange_i1_i2.
      - apply interchange_i2_i2.
    Qed.

    Lemma interchange_bw A1 B1 A2 B2 :
      C.Plus.copair (C.Plus.i1 + C.Plus.i1) (C.Plus.i2 + C.Plus.i2) =
      C.bw (interchange A1 B1 A2 B2).
    Proof.
      symmetry.  apply C.Plus.copair_uni.
      - symmetry. apply (C.eq_fw_bw_l_1 (interchange _ _ _ _)).
      apply interchange_i1.
      - symmetry. apply (C.eq_fw_bw_l_1 (interchange _ _ _ _)).
      apply interchange_i2.
    Qed.

    Definition copair : forall {X A B : S.t}, S.m A X -> S.m B X -> S.m (omap A B) X :=
      fun X A B f g =>
        C.Plus.copair f g @ interchange (fst A) (fst B) (snd A) (snd B).

    Proposition copair_i1 : forall {X A B} (f : S.m A X) (g : S.m B X),
      S.compose (copair f g) i1 = f.
    Proof.
      intros. unfold compose, copair, i1.
      rewrite C.compose_assoc.
      rewrite (interchange_i1 (fst A) (fst B) (snd A) (snd B)) at 1.
      apply C.Plus.copair_i1.
    Qed.

    Proposition copair_i2 : forall {X A B} (f : S.m A X) (g : S.m B X),
      S.compose (copair f g) i2 = g.
    Proof.
      intros. unfold compose, copair, i2.
      rewrite C.compose_assoc.
      rewrite (interchange_i2 (fst A) (fst B) (snd A) (snd B)) at 1.
      apply C.Plus.copair_i2.
    Qed.

    Proposition copair_iota_compose : forall {X A B} x,
      @copair X A B (S.compose x i1) (S.compose x i2) = x.
    Proof.
      intros. unfold compose, copair, i1, i2.
      rewrite <- C.Plus.copair_compose.
      rewrite C.compose_assoc.
      epose (interchange_bw (fst A) (fst B) (snd A) (snd B)).
      rewrite e at 1.
      rewrite (C.bw_fw (interchange (fst A) (fst B) (snd A) (snd B))) at 1.
      rewrite C.compose_id_right.
      reflexivity.
    Qed.

    Include CocartesianStructureTheory S.
    Include BifunctorTheory S S S.
    Include SymmetricMonoidalStructureTheory S.
  End Plus.

  Include CocartesianTheory S.
End SigBaseCocartesian.

(** ** With some work we can also derive a cartesian structure to [SigBase C]
    Note: We need C to have both products and coproducts since:
    - The morphism definition uses coproducts (SigBase is built on CocartesianCategory)
    - The cartesian structure requires products *)
Module SigBaseCartesian (C : BicartesianCategory) (S : SigBase C) <: CartesianCategory.
  Include S.
  Import C.
  Open Scope obj_scope.

  Module Prod <: CartesianStructure S.
    Import S.
    Local Infix "@" := C.compose (at level 45, right associativity) : hom_scope.

    (** Terminal object: (1, 1) *)
    Definition unit : S.t := (C.Prod.unit, C.Prod.unit).

    Definition ter : forall X, S.m X unit :=
      fun X => C.Plus.copair (C.Plus.i1 @ C.Prod.ter (fst X)) (C.Plus.i2 @ C.Prod.ter (snd X)).

    Proposition ter_uni : forall {X} (x y : S.m X unit), x = y.
    Admitted.

    (** Binary products: (A1, A2) × (B1, B2) = (A1 × B1, A2 × B2) *)
    Definition omap (A B : S.t) : S.t :=
      (C.Prod.omap (fst A) (fst B), C.Prod.omap (snd A) (snd B)).

    Definition p1 : forall {A B : S.t}, S.m (omap A B) A :=
      fun A B => C.Prod.p1 + C.Prod.p1.

    Definition p2 : forall {A B : S.t}, S.m (omap A B) B :=
      fun A B => C.Prod.p2 + C.Prod.p2.

    (** The interchange isomorphism swaps products and coproducts *)
    Definition interchange (A1 B1 A2 B2 : C.t) : C.iso (C.Prod.omap (A1 + A2) (B1 + B2)) ((C.Prod.omap A1 B1) + (C.Prod.omap A2 B2)).
    Admitted.

    Definition pair : forall {X A B : S.t}, S.m X A -> S.m X B -> S.m X (omap A B) :=
      fun X A B f g =>
        C.fw (interchange (fst A) (fst B) (snd A) (snd B)) @ C.Prod.pair f g.

    Proposition p1_pair : forall {X A B} (f : S.m X A) (g : S.m X B),
      S.compose p1 (pair f g) = f.
    Admitted.

    Proposition p2_pair : forall {X A B} (f : S.m X A) (g : S.m X B),
      S.compose p2 (pair f g) = g.
    Admitted.

    Proposition pair_pi_compose : forall {X A B} x,
      @pair X A B (S.compose p1 x) (S.compose p2 x) = x.
    Admitted.

    Include CartesianStructureTheory S.
    Include BifunctorTheory S S S.
    Include SymmetricMonoidalStructureTheory S.
  End Prod.

  Include CartesianTheory S.
End SigBaseCartesian.

(** ** The category Sig has the same objects as SigBase but morphisms are async events *)
Module SigDefinition (C : CocartesianCategory) (T : Terminals C) <: Category.
  Module Ev := AsyncEventsDefinition C T.
  Import C.
  Open Scope obj_scope.

  Definition t : Type := C.t * C.t.

  Definition m (A B : t) : Type :=
    Ev.m ((fst A) + (snd A)) ((fst B) + (snd B)).

  Definition id (A : t) : m A A :=
    Ev.id ((fst A) + (snd A)).

  Definition compose {A B C : t} (g : m B C) (f : m A B) : m A C :=
    Ev.compose g f.

  Proposition compose_id_left :
    forall {A B} (f : m A B), compose (id B) f = f.
  Proof.
    intros. apply Ev.compose_id_left.
  Qed.

  Proposition compose_id_right :
    forall {A B} (f : m A B), compose f (id A) = f.
  Proof.
    intros. apply Ev.compose_id_right.
  Qed.

  Proposition compose_assoc :
    forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
    compose (compose h g) f = compose h (compose g f).
  Proof.
    intros. apply Ev.compose_assoc.
  Qed.

  Include CategoryTheory.
End SigDefinition.

Module Type Sig (C : CocartesianCategory) (T : Terminals C).
  Include (SigDefinition C T).

  Definition neg (S : t) := fst S.
  Definition pos (S : t) := snd S.
End Sig.

(** ** Cocartesian structure for Sig *)
Module SigCocartesian (C : CocartesianCategory) (T : Terminals C)
  (S : Sig C T) <: CocartesianCategory.
  Include S.
  Import C.
  Open Scope obj_scope.

  Module Plus <: CocartesianStructure S.
    Import S.

    (** We reuse the SigBase cocartesian structure and lift via KlF *)
    Module SB := SigBaseDefinition C.
    Module SBC := SigBaseCocartesian C SB.

    (** Initial object: (0, 0) *)
    Definition unit : S.t := (C.Plus.unit, C.Plus.unit).

    (** The initial morphism lifted to Kleisli *)
    Definition ini (X : S.t) : S.m unit X :=
      Ev.L.KlF.fmap (SBC.Plus.ini X).

    Proposition ini_uni : forall {X} (x y : S.m unit X), x = y.
    Proof.
      intros.
      unfold S.m, unit in *. simpl in *.
      (* Morphisms from 0+0 are unique: factor through copair and use ini_uni *)
      rewrite <- (C.Plus.copair_iota_compose x).
      rewrite <- (C.Plus.copair_iota_compose y).
      f_equal; apply C.Plus.ini_uni.
    Qed.

    (** Binary coproducts: (A1, A2) + (B1, B2) = (A1 + B1, A2 + B2) *)
    Definition omap (A B : S.t) : S.t :=
      (C.Plus.omap (fst A) (fst B), C.Plus.omap (snd A) (snd B)).

    (** Injections lifted to Kleisli *)
    Definition i1 {A B : S.t} : S.m A (omap A B) :=
      Ev.L.KlF.fmap (SBC.Plus.i1 (A:=A) (B:=B)).

    Definition i2 {A B : S.t} : S.m B (omap A B) :=
      Ev.L.KlF.fmap (SBC.Plus.i2 (A:=A) (B:=B)).

    (** Copair in Kleisli: f and g are already Kleisli morphisms,
        so C.Plus.copair f g is a Kleisli morphism too *)
    Definition copair {X A B : S.t} (f : S.m A X) (g : S.m B X) : S.m (omap A B) X :=
      Ev.L.Kl.compose
        (C.Plus.copair f g)
        (Ev.L.KlF.fmap (SBC.Plus.interchange (fst A) (fst B) (snd A) (snd B))).

    Proposition copair_i1 : forall {X A B} (f : S.m A X) (g : S.m B X),
      S.compose (copair f g) i1 = f.
    Proof.
      intros. unfold S.compose, copair, i1, SBC.Plus.i1.
      rewrite Ev.L.Kl.compose_assoc.
      rewrite <- Ev.L.KlF.fmap_compose.
      rewrite (@SBC.Plus.interchange_i1 (fst A) (fst B) (snd A) (snd B)) at 1.
      unfold Ev.L.Kl.compose, Ev.L.KlF.fmap.
      rewrite <- C.compose_assoc, Ev.L.ext_eta_r.
      apply C.Plus.copair_i1.
    Qed.

    Proposition copair_i2 : forall {X A B} (f : S.m A X) (g : S.m B X),
      S.compose (copair f g) i2 = g.
    Proof.
      intros. unfold S.compose, copair, i2, SBC.Plus.i2.
      rewrite Ev.L.Kl.compose_assoc.
      rewrite <- Ev.L.KlF.fmap_compose.
      rewrite (@SBC.Plus.interchange_i2 (fst A) (fst B) (snd A) (snd B)) at 1.
      unfold Ev.L.Kl.compose, Ev.L.KlF.fmap.
      rewrite <- C.compose_assoc, Ev.L.ext_eta_r.
      apply C.Plus.copair_i2.
    Qed.

    Proposition copair_iota_compose : forall {X A B} x,
      @copair X A B (S.compose x i1) (S.compose x i2) = x.
    Proof.
      intros. unfold S.compose, copair, i1, i2, SBC.Plus.i1, SBC.Plus.i2.
      unfold Ev.L.Kl.compose, Ev.L.KlF.fmap.
      rewrite <- !C.compose_assoc.
      rewrite !Ev.L.ext_eta_r.
      rewrite <- C.Plus.copair_compose.
      rewrite !C.compose_assoc.
      rewrite (@SBC.Plus.interchange_bw (fst A) (fst B) (snd A) (snd B)) at 1.
      rewrite C.bw_fw, C.compose_id_right.
      reflexivity.
    Qed.

    Include CocartesianStructureTheory S.
    Include BifunctorTheory S S S.
    Include SymmetricMonoidalStructureTheory S.
  End Plus.

  Include CocartesianTheory S.
End SigCocartesian.

(** ** Cartesian structure for Sig
    Note: We need C to be bicartesian for the same reason as SigBaseCartesian *)
Module SigCartesian (C : BicartesianCategory) (T : Terminals C)
  (S : Sig C T) <: CartesianCategory.
  Include S.
  Import C.
  Open Scope obj_scope.

  Module Prod <: CartesianStructure S.
    Import S.

    (** We reuse the SigBase cartesian structure and lift via KlF *)
    Module SB := SigBaseDefinition C.
    Module SBC := SigBaseCartesian C SB.

    (** Terminal object: (1, 1) *)
    Definition unit : S.t := (C.Prod.unit, C.Prod.unit).

    (** The terminal morphism lifted to Kleisli *)
    Definition ter (X : S.t) : S.m X unit :=
      Ev.L.KlF.fmap (SBC.Prod.ter X).

    Proposition ter_uni : forall {X} (x y : S.m X unit), x = y.
    Admitted.

    (** Binary products: (A1, A2) × (B1, B2) = (A1 × B1, A2 × B2) *)
    Definition omap (A B : S.t) : S.t :=
      (C.Prod.omap (fst A) (fst B), C.Prod.omap (snd A) (snd B)).

    (** Projections lifted to Kleisli *)
    Definition p1 {A B : S.t} : S.m (omap A B) A :=
      Ev.L.KlF.fmap (SBC.Prod.p1 (A:=A) (B:=B)).

    Definition p2 {A B : S.t} : S.m (omap A B) B :=
      Ev.L.KlF.fmap (SBC.Prod.p2 (A:=A) (B:=B)).

    (** Pair in Kleisli: f and g are already Kleisli morphisms,
        constructing the pair requires careful handling of the monad *)
    Definition pair {X A B : S.t} (f : S.m X A) (g : S.m X B) : S.m X (omap A B).
    Admitted.

    Proposition p1_pair : forall {X A B} (f : S.m X A) (g : S.m X B),
      S.compose p1 (pair f g) = f.
    Admitted.

    Proposition p2_pair : forall {X A B} (f : S.m X A) (g : S.m X B),
      S.compose p2 (pair f g) = g.
    Admitted.

    Proposition pair_pi_compose : forall {X A B} x,
      @pair X A B (S.compose p1 x) (S.compose p2 x) = x.
    Admitted.

    Include CartesianStructureTheory S.
    Include BifunctorTheory S S S.
    Include SymmetricMonoidalStructureTheory S.
  End Prod.

  Include CartesianTheory S.
End SigCartesian.

(** ** There is an obvious embedding from [SigBase C] to [C] *)
Module SigBaseToC (C : CocartesianCategory) (S : SigBase C) <: FaithfulFunctor S C.
  Import C.
  Open Scope obj_scope.

  Definition omap (X : S.t) : C.t := (fst X) + (snd X).

  Definition fmap {A B : S.t} (f : S.m A B) : C.m (omap A) (omap B) :=
    f.

  Proposition fmap_id : forall A, fmap (S.id A) = C.id (omap A).
  Proof. reflexivity. Qed.

  Proposition fmap_compose :
    forall {A B C} (g : S.m B C) (f : S.m A B),
    fmap (S.compose g f) = (fmap g) @ (fmap f).
  Proof. reflexivity. Qed.

  Proposition faithful :
    forall {A B} (f g : S.m A B), fmap f = fmap g -> f = g.
  Proof. intros; assumption. Qed.

  Include (FunctorTheory S C).
End SigBaseToC.

(** ** Polarized signatures generate corresponding sets of async events *)
Module SigToAsyncEvent (C : CocartesianCategory) (T : Terminals C)
  (S : Sig C T) (Ev : AsyncEvents C T) <: FaithfulFunctor S Ev.
  Import C.
  Open Scope obj_scope.

  Definition omap (X : S.t) : Ev.t := (fst X) + (snd X).

  Definition fmap {A B : S.t} (f : S.m A B) : Ev.m (omap A) (omap B) := f.

  Proposition fmap_id : forall A, fmap (S.id A) = Ev.id (omap A).
  Proof. reflexivity. Qed.

  Proposition fmap_compose :
    forall {A B C} (g : S.m B C) (f : S.m A B),
    fmap (S.compose g f) = Ev.compose (fmap g) (fmap f).
  Proof. reflexivity. Qed.

  Proposition faithful :
    forall {A B} (f g : S.m A B), fmap f = fmap g -> f = g.
  Proof. intros; assumption. Qed.

  Include (FunctorTheory S Ev).
End SigToAsyncEvent.

(** ** Bicartesian structure for SigBase *)
Module SigBaseBicartesian (BC : BicartesianCategory) (S : SigBase BC) <: BicartesianCategory.
  Module C <: CartesianCategory.
    Include S.
    Module SBC := SigBaseCartesian BC S.
    Module Prod := SBC.Prod.
    Include CartesianTheory S.
  End C.

  Module CC <: Cocartesian C.
    Module SBCo := SigBaseCocartesian BC S.
    Module Plus := SBCo.Plus.
    Include CocartesianTheory C.
  End CC.

  Include C.
  Include CC.
End SigBaseBicartesian.

(** ** Bicartesian structure for Sig *)
Module SigBicartesian (BC : BicartesianCategory) (T : Terminals BC)
  (S : Sig BC T) <: BicartesianCategory.
  Module C <: CartesianCategory.
    Include S.
    Module SC := SigCartesian BC T S.
    Module Prod := SC.Prod.
    Include CartesianTheory S.
  End C.

  Module CC <: Cocartesian C.
    Module SCo := SigCocartesian BC T S.
    Module Plus := SCo.Plus.
    Include CocartesianTheory C.
  End CC.

  Include C.
  Include CC.
End SigBicartesian.

(** ** Embedding a signature as a ALTS *)

Module SigToAlts (S : Sig PosetBicartesian PosetTerminals) <: FaithfulFunctor S Alts.
  Import S.
  Import PosetBicartesian.
  Import DCPO.
  Import DownsetMonad.
  Open Scope obj_scope.  
  
  Program Definition omap (X : S.t) : Alts.t := 
    {|
      Alts.labels := neg X + pos X;
      Alts.states := T;
      Alts.step := 
        @mkm T _ (fun _ =>
          mk_dset (fun _ => True) _) _;
    |}.
  Next Obligation.
    trivial.
  Qed.
  Next Obligation.
    intros; constructor.
  Qed.

  Program Definition fmap {A B : S.t} (f : S.m A B) : Alts.m (omap A) (omap B) :=
    {|
      Alts.morL := f;
      Alts.morS := Kl.id T;
    |}.
  Next Obligation.
  Admitted.

  Proposition fmap_id : forall A, fmap (S.id A) = Alts.id (omap A).
  Admitted.

  Proposition fmap_compose :
    forall {A B C} (g : S.m B C) (f : S.m A B),
    fmap (S.compose g f) = Alts.compose (fmap g) (fmap f).
  Admitted.

  Proposition faithful :
    forall {A B} (f g : S.m A B), fmap f = fmap g -> f = g.
  Admitted.

  Include (FunctorTheory S Alts).
End SigToAlts.
