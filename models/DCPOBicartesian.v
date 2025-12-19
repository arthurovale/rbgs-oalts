Require Import interfaces.Category.
Require Import interfaces.ConcreteCategory.
Require Import interfaces.Functor.
Require Import interfaces.MonoidalCategory.
Require Import interfaces.Limits.
Require Import models.DCPO.
Require Import models.PosetBicartesian.
Require Import coqrel.LogicalRelations.
Require Import PropExtensionality.
Require Import FunctionalExtensionality.

(** * The category of DCPOs is Bicartesian *)

(** We show that [DCPO] from DCPO.v has both products and
    coproducts, making it a bicartesian category. *)

(** ** Cartesian Structure *)

Module DCPOCartesianStructure <: CartesianStructureDefinition DCPO.
  Import PosetBicartesian.
  Import DCPO.

  (** The unit type is trivially directed-complete *)
  Program Definition unit_DirectedComplete : DirectedComplete unit :=
    {| dc_po := Prod.unit_PartialOrder;
       dsup := fun _ _ => tt |}.
  Next Obligation.
    constructor; intros x _; destruct x; reflexivity.
  Defined.

  Definition unit : t := @DCPO.mkt unit unit_DirectedComplete.

  Program Definition ter (X : t) : m X unit := @DCPO.mkm X unit (fun _ => tt) _.
  Next Obligation.
    constructor. intros D HD.
    constructor.
    - intros _ [a Ha]. reflexivity.
    - intros y _. destruct y. reflexivity.
  Defined.

  Proposition ter_uni : forall {X} (f g : m X unit), f = g.
  Proof.
    intros. apply DCPO.meq. intros x.
    destruct (f x), (g x). reflexivity.
  Qed.

  (** *** Binary products: pointwise order and pointwise directed suprema *)

  Section Product.
    Variables A B : t.

    Let CA := DCPO.carrier A.
    Let CB := DCPO.carrier B.
    Let DA := DCPO.structure A.
    Let DB := DCPO.structure B.
    Let ProdPO := Prod.ProdPO_PartialOrder A B.
    
    (** Directed sets in products project to directed sets *)
    Lemma prod_directed_fst (D : CA * CB -> Prop) :
      @Directed _ ProdPO D ->
      @Directed _ (@dc_po _ DA) (im fst D).
    Proof.
      intros HD. exists (fst (@non_empty_wit _ _ _ HD)).
      - constructor. exact (@non_empty _ _ _ HD).
      - intros _ _ [p1 Hp1] [p2 Hp2].
        destruct (@upper _ _ _ HD p1 p2 Hp1 Hp2) as [p3 [Hp3 [Hle1 Hle2]]].
        exists (fst p3). split; [|split].
        + constructor; assumption.
        + destruct Hle1; assumption.
        + destruct Hle2; assumption.
    Qed.

    Lemma prod_directed_snd (D : CA * CB -> Prop) :
      @Directed _ ProdPO D ->
      @Directed _ (@dc_po _ DB) (im snd D).
    Proof.
      intros HD. exists (snd (@non_empty_wit _ _ _ HD)).
      - constructor. exact (@non_empty _ _ _ HD).
      - intros _ _ [p1 Hp1] [p2 Hp2].
        destruct (@upper _ _ _ HD p1 p2 Hp1 Hp2) as [p3 [Hp3 [Hle1 Hle2]]].
        exists (snd p3). split; [|split].
        + constructor; assumption.
        + destruct Hle1; assumption.
        + destruct Hle2; assumption.
    Qed.

    (** Pointwise directed supremum *)
    Definition prod_dsup (D : CA * CB -> Prop)
      `{HD: @Directed _ ProdPO D} : CA * CB :=
      (@dsup _ DA (im fst D) (prod_directed_fst D HD),
       @dsup _ DB (im snd D) (prod_directed_snd D HD)).
  End Product.

  Program Definition ProdDCPO_DirectedComplete (A B : t) : 
    DirectedComplete (carrier A * carrier B) :=
    {| dc_po := Prod.ProdPO_PartialOrder A B;
        dsup := prod_dsup A B |}.
  Next Obligation.
    constructor.
    - intros [a b] Hab. split; simpl.
      + apply sup_ub. exact (im_intro fst D (a, b) Hab).
      + apply sup_ub. exact (im_intro snd D (a, b) Hab).
    - intros [ya yb] Hub. split; simpl;
      apply sup_lub; intros _ [p Hp]; destruct (Hub p Hp); assumption.
  Qed.

  Definition prod (A B : t) : t := @DCPO.mkt (carrier A * carrier B) (ProdDCPO_DirectedComplete A B).

  Definition omap (A B : t) : t := prod A B.
  Program Definition p1 {A B} : m (omap A B) A := @DCPO.mkm (prod A B) A fst _.
  Next Obligation.
    constructor. intros D HD.
    simpl. unfold prod_dsup.
    constructor.
    - intros _ [[a b] Hab]. simpl.
      apply sup_ub. exact (im_intro fst D (a, b) Hab).
    - intros y Hub.
      apply sup_lub. intros _ [[a b] Hab]. simpl.
      apply Hub. exact (im_intro fst D (a, b) Hab).
  Defined.

  Program Definition p2 {A B} : m (omap A B) B := @DCPO.mkm (prod A B) B snd _.
  Next Obligation.
    constructor. intros D HD.
    simpl. unfold prod_dsup.
    constructor.
    - intros _ [[a b] Hab]. simpl. apply sup_ub. exact (im_intro snd D (a, b) Hab).
    - intros y Hub.
      apply sup_lub. intros _ [[a b] Hab]. simpl.
      apply Hub. exact (im_intro snd D (a, b) Hab).
  Defined.

  Program Definition pair {X A B} (f : m X A) (g : m X B) : m X (omap A B) := 
    @DCPO.mkm X (prod A B) (fun x => (DCPO.apply X A f x, DCPO.apply X B g x)) _.
  Next Obligation.
    pose proof (DCPO.morphism X A f) as Hf.
    pose proof (DCPO.morphism X B g) as Hg.
    constructor. intros D HD.
    constructor.
    - intros _ [x Hx]. split.
      + apply (@sc_le _ _ (DCPO.structure X) (@dc_po _ (structure A)) (DCPO.apply X A f) Hf).
        apply sup_ub; assumption.
      + apply (@sc_le _ _ (DCPO.structure X) (@dc_po _ (structure B)) (DCPO.apply X B g) Hg).
        apply sup_ub; assumption.
    - intros [ya yb] Hub. split.
      + rewrite (@sc_dsup _ _ (DCPO.structure X) (structure A) (DCPO.apply X A f) Hf).
        apply sup_lub. intros _ [x Hx].
        destruct (Hub _ (im_intro _ D x Hx)) as [Hle _]; assumption.
      + rewrite (@sc_dsup _ _ (DCPO.structure X) (structure B) (DCPO.apply X B g) Hg).
        apply sup_lub. intros _ [x Hx].
        destruct (Hub _ (im_intro _ D x Hx)) as [_ Hle]. exact Hle.
  Defined.

  Proposition p1_pair : forall {X A B} (f : m X A) (g : m X B), compose p1 (pair f g) = f.
  Proof. intros. apply DCPO.meq. intros x. reflexivity. Qed.

  Proposition p2_pair : forall {X A B} (f : m X A) (g : m X B), compose p2 (pair f g) = g.
  Proof. intros. apply DCPO.meq. intros x. reflexivity. Qed.

  Proposition pair_pi_compose : forall {X A B} f, @pair X A B (compose p1 f) (compose p2 f) = f.
  Proof.
    intros. apply DCPO.meq. intros x. simpl.
    destruct (DCPO.apply X (omap A B) f x) as [a b].
    reflexivity.
  Qed.

End DCPOCartesianStructure.

Module DCPOCartesian <: CartesianStructure DCPO.
  Include DCPOCartesianStructure.
  Include CartesianStructureTheory DCPO DCPOCartesianStructure.
  Include BifunctorTheory DCPO DCPO DCPO.
  Include SymmetricMonoidalStructureTheory DCPO.
End DCPOCartesian.

(** ** Cocartesian Structure *)

(** For coproducts of DCPOs, we use the fact that directed sets in a
    disjoint union must be "component-homogeneous" - they cannot mix
    elements from both sides since inl and inr are incomparable. *)

Module DCPOCocartesianStructure <: CocartesianStructureDefinition DCPO.
  Import PosetBicartesian.
  Import DCPO.

  (** *** Initial object: empty DCPO *)

  Proposition Empty_directed_false (D : Empty_set -> Prop) :
    @Directed _ Plus.Empty_PartialOrder D -> False.
  Proof.
    intros HD. destruct (@non_empty_wit _ _ _ HD).
  Qed.

  Program Definition Empty_DirectedComplete : DirectedComplete Empty_set :=
    {| dc_po := Plus.Empty_PartialOrder;
       dsup := fun D HD => match Empty_directed_false D HD with end |}.
  Next Obligation.
    constructor; intros x _; destruct x; reflexivity.
  Defined.

  Definition unit : t := @DCPO.mkt Empty_set Empty_DirectedComplete.

  Program Definition ini (X : t) : m unit X :=
    @DCPO.mkm unit X (fun e => match e with end) _.
  Next Obligation.
    constructor. intros D HD.
    constructor.
    - intros. destruct H. contradiction.
    - intros y _. destruct (dsup D).
  Defined.

  Proposition ini_uni : forall {X} (f g : m unit X), f = g.
  Proof.
    intros. apply DCPO.meq. intros [].
  Qed.

  (** *** Binary coproducts: disjoint union with component-wise order *)

  Section Coproduct.
    Variables A B : t.

    Let CA := DCPO.carrier A.
    Let CB := DCPO.carrier B.
    Let DA := DCPO.structure A.
    Let DB := DCPO.structure B.
    Let CoprodPO := Plus.CoprodPO_PartialOrder A B.

    Definition coprod_directed_homogeneous (D : CA + CB -> Prop) :
      @Directed _ CoprodPO D ->
      {forall x, D x -> exists a, x = inl a} +
      {forall x, D x -> exists b, x = inr b}.
    Proof.
      intros HD.
      pose proof (@non_empty _ _ _ HD) as H0.
      destruct (@non_empty_wit _ _ _ HD) as [a0 | b0].
      - left. intros [a | b] Hx.
        + exists a. reflexivity.
        + exfalso.
          destruct (@upper _ _ _ HD (inl a0) (inr b) H0 Hx) as [[c | c] [Hc [Hac Hbc]]].
          * exact Hbc.
          * exact Hac.
      - right. intros [a | b] Hx.
        + exfalso.
          destruct (@upper _ _ _ HD (inl a) (inr b0) Hx H0) as [[c | c] [Hc [Hac Hbc]]].
          * exact Hbc.
          * exact Hac.
        + exists b. reflexivity.
    Defined.

    (** Extract the left/right projections of directed sets *)
    Definition coprod_left_proj (D : CA + CB -> Prop) : CA -> Prop :=
      fun a => D (inl a).

    Definition coprod_right_proj (D : CA + CB -> Prop) : CB -> Prop :=
      fun b => D (inr b).

    Lemma coprod_left_directed (D : CA + CB -> Prop) :
      @Directed _ CoprodPO D ->
      (forall x, D x -> exists a, x = inl a) ->
      @Directed _ (@dc_po _ DA) (coprod_left_proj D).
    Proof.
      intros HD Hleft.
      pose proof (@non_empty _ _ _ HD) as H.
      remember (@non_empty_wit _ _ _ HD) as x. clear Heqx.
      destruct x.      
      - exists c. 
        + exact H.
        + intros a1 a2 Ha1 Ha2. 
          destruct (@upper _ _ _ HD (inl a1) (inl a2) Ha1 Ha2) as [z [Hz [Hle1 Hle2]]].
          specialize (Hleft z Hz).
          destruct z. 
          * exists c0. split; try split; assumption.
          * contradiction.
      - specialize (Hleft (inr c) H). exfalso. destruct Hleft. discriminate.
    Qed.
        
    Lemma coprod_right_directed (D : CA + CB -> Prop) :
      @Directed _ CoprodPO D ->
      (forall x, D x -> exists b, x = inr b) ->
      @Directed _ (@dc_po _ DB) (coprod_right_proj D).
    Proof.
      intros HD Hright.
      pose proof (@non_empty _ _ _ HD) as H.
      remember (@non_empty_wit _ _ _ HD) as x. clear Heqx.
      destruct x.
      - specialize (Hright (inl c) H). exfalso. destruct Hright. discriminate.
      - exists c.
        + exact H.
        + intros b1 b2 Hb1 Hb2.
          destruct (@upper _ _ _ HD (inr b1) (inr b2) Hb1 Hb2) as [z [Hz [Hle1 Hle2]]].
          specialize (Hright z Hz).
          destruct z.
          * contradiction.
          * exists c0. split; try split; assumption.
    Qed.

    (** The directed supremum in coproduct *)
    Definition coprod_dsup (D : CA + CB -> Prop)
      `{HD: @Directed _ CoprodPO D} : CA + CB.
    Proof.
      destruct (coprod_directed_homogeneous D HD) as [Hleft | Hright].
      - exact (inl (@dsup _ DA (coprod_left_proj D) (coprod_left_directed D HD Hleft))).
      - exact (inr (@dsup _ DB (coprod_right_proj D) (coprod_right_directed D HD Hright))).
    Defined.

    Lemma coprod_dsup_is_sup (D : CA + CB -> Prop)
      `{HD: @Directed _ CoprodPO D} : @IsSup _ CoprodPO D (coprod_dsup D).
    Proof.
      unfold coprod_dsup.
      destruct (coprod_directed_homogeneous D HD) as [Hleft | Hright].
      - constructor.
        + intros x Hx.
          destruct (Hleft x Hx) as [a Heq]. subst. simpl.
          apply sup_ub. exact Hx.
        + intros [ya | yb] Hub.
          * simpl. apply sup_lub. intros a Ha.
            specialize (Hub (inl a) Ha). exact Hub.
          * simpl. pose proof (@non_empty _ _ _ HD) as Hnemp. 
            destruct (Hleft _ Hnemp) as [a Heq]. rewrite Heq in Hnemp.
            specialize (Hub (inl a) Hnemp). exact Hub.
      - constructor.
        + intros x Hx.
          destruct (Hright x Hx) as [b Heq]. subst. simpl.
          apply sup_ub. exact Hx.
        + intros [ya | yb] Hub.
          * simpl. pose proof (@non_empty _ _ _ HD) as Hnemp. 
            destruct (Hright _ Hnemp) as [b Heq]. rewrite Heq in Hnemp.
            specialize (Hub (inr b) Hnemp). exact Hub.
          * simpl. apply sup_lub. intros b Hb.
            specialize (Hub (inr b) Hb). exact Hub.
    Qed.

  End Coproduct.

  Program Definition CoprodDCPO_DirectedComplete (A B : t) :
    DirectedComplete (carrier A + carrier B) :=
    {| dc_po := Plus.CoprodPO_PartialOrder A B;
       dsup := coprod_dsup A B |}.
  Next Obligation.
    apply coprod_dsup_is_sup.
  Qed.

  Definition coprod (A B : t) : t := @DCPO.mkt (carrier A + carrier B) (CoprodDCPO_DirectedComplete A B).

  Definition omap (A B : t) : t := coprod A B.

  Program Definition i1 {A B} : m A (omap A B) := @DCPO.mkm A (coprod A B) inl _.
  Next Obligation.
    constructor. intros D HD.
    constructor.
    - intros _ [a Ha]. simpl. apply sup_ub. exact Ha.
    - intros [ya | yb] Hub.
      + simpl. apply sup_lub. intros a Ha.
        pose proof (Hub (inl a) (@im_intro _ _ (@inl (carrier A) (carrier B)) D a Ha)) as Hle.
        simpl in Hle. exact Hle.
      + simpl.
        pose proof (Hub (inl (@non_empty_wit _ _ _ HD)) (@im_intro _ _ (@inl (carrier A) (carrier B)) D _ (@non_empty _ _ _ HD))) as Hle.
        exact Hle.
  Defined.

  Program Definition i2 {A B} : m B (omap A B) := @DCPO.mkm B (coprod A B) inr _.
  Next Obligation.
    constructor. intros D HD.
    constructor.
    - intros _ [b Hb]. simpl. apply sup_ub. exact Hb.
    - intros [ya | yb] Hub.
      + simpl.
        pose proof (Hub (inr (@non_empty_wit _ _ _ HD)) (@im_intro _ _ (@inr (carrier A) (carrier B)) D _ (@non_empty _ _ _ HD))) as Hle.
        exact Hle.
      + simpl. apply sup_lub. intros b Hb.
        pose proof (Hub (inr b) (@im_intro _ _ (@inr (carrier A) (carrier B)) D b Hb)) as Hle.
        simpl in Hle. exact Hle.
  Defined.

  Program Definition copair {X A B} (f : m A X) (g : m B X) : m (omap A B) X :=
    @DCPO.mkm (coprod A B) X
      (fun ab => match ab with
                 | inl a => DCPO.apply A X f a
                 | inr b => DCPO.apply B X g b
                 end) _.
  Next Obligation.
    pose proof (DCPO.morphism A X f) as Hf.
    pose proof (DCPO.morphism B X g) as Hg.
    constructor. intros D HD.
    simpl. unfold coprod_dsup.
    destruct (coprod_directed_homogeneous A B D HD) as [Hleft | Hright]; simpl.
    - set (HleftDir := coprod_left_directed A B D HD Hleft).
      set (Hsc := @sc_dsup_sup _ _ (structure A) (@dc_po _ (DCPO.structure X)) (DCPO.apply A X f) Hf (coprod_left_proj A B D) HleftDir).
      constructor.
      + intros _ [[a | b] Hab].
        * apply (@sup_ub _ (@dc_po _ (DCPO.structure X)) _ _ Hsc (DCPO.apply A X f a)).
          exact (@im_intro _ _ _ _ a Hab).
        * destruct (Hleft (inr b) Hab) as [a' Hcontra]. discriminate.
      + intros y Hub.
        apply (@sup_lub _ (@dc_po _ (DCPO.structure X)) _ _ Hsc y). intros _ [a Ha].
        apply Hub. exact (@im_intro _ _ _ D (inl a) Ha).
    - set (HrightDir := coprod_right_directed A B D HD Hright).
      set (Hsc := @sc_dsup_sup _ _ (structure B) (@dc_po _ (DCPO.structure X)) (DCPO.apply B X g) Hg (coprod_right_proj A B D) HrightDir).
      constructor.
      + intros _ [[a | b] Hab].
        * destruct (Hright (inl a) Hab) as [b' Hcontra]. discriminate.
        * apply (@sup_ub _ (@dc_po _ (DCPO.structure X)) _ _ Hsc (DCPO.apply B X g b)).
          exact (@im_intro _ _ _ _ b Hab).
      + intros y Hub.
        apply (@sup_lub _ (@dc_po _ (DCPO.structure X)) _ _ Hsc y). intros _ [b Hb].
        apply Hub. exact (@im_intro _ _ _ D (inr b) Hb).
  Defined.

  Proposition copair_i1 : forall {X A B} (f : m A X) (g : m B X), compose (copair f g) i1 = f.
  Proof. intros. apply DCPO.meq. intros a. reflexivity. Qed.

  Proposition copair_i2 : forall {X A B} (f : m A X) (g : m B X), compose (copair f g) i2 = g.
  Proof. intros. apply DCPO.meq. intros b. reflexivity. Qed.

  Proposition copair_iota_compose : forall {X A B} x, @copair X A B (compose x i1) (compose x i2) = x.
  Proof. intros. apply DCPO.meq. intros [a | b]; reflexivity. Qed.

End DCPOCocartesianStructure.

Module DCPOCocartesian <: CocartesianStructure DCPO.
  Include DCPOCocartesianStructure.
  Include CocartesianStructureTheory DCPO DCPOCocartesianStructure.
  Include BifunctorTheory DCPO DCPO DCPO.
  Include SymmetricMonoidalStructureTheory DCPO.
End DCPOCocartesian.

(** ** Bicartesian Category *)

Module DCPOBicartesian <: BicartesianCategory.
  Module C <: CartesianCategory.
    Include DCPO.
    Module Prod := DCPOCartesian.
    Include CartesianTheory DCPO.
  End C.

  Module CC <: Cocartesian C.
    Module Plus := DCPOCocartesian.
    Include CocartesianTheory C.
  End CC.

  Include C.
  Include CC.
End DCPOBicartesian.

(** ** Setup: Extract Terminals from DCPO's Cartesian Structure *)

Module DCPOTerminals := TerminalsFromCartesian DCPOBicartesian.C.
