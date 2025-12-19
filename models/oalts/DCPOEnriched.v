Require Import interfaces.Category.
Require Import interfaces.ConcreteCategory.
Require Import models.DCPO.
Require Import models.oalts.interfaces.DCPOEnrichedCat.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import ProofIrrelevance.
Require Import coqrel.LogicalRelations.

(** * DCPO is a DCPO-Enriched Category *)

(** We prove that DCPO (the category of DCPOs with Scott-continuous maps)
    is itself DCPO-enriched. This means:
    1. Hom-sets DCPO(X,Y) are DCPOs with pointwise order
    2. Composition is Scott-continuous in both arguments *)

(** ** Hom-sets are DCPOs *)

Section DCPOHomDCPO.
  Variables X Y : DCPO.t.

  Let CX := DCPO.carrier X.
  Let CY := DCPO.carrier Y.
  Let DX := DCPO.structure X.
  Let DY := DCPO.structure Y.

  (** Pointwise order on Scott-continuous maps *)
  Definition hom_le (f g : DCPO.m X Y) : Prop :=
    forall x, @le _ (@dc_po _ DY) (DCPO.apply X Y f x) (DCPO.apply X Y g x).

  Lemma hom_le_preo : PreOrder hom_le.
  Proof.
    constructor.
    - intros f x. reflexivity.
    - intros f g h Hfg Hgh x. etransitivity; [apply Hfg | apply Hgh].
  Qed.

  Lemma hom_le_po : Antisymmetric (DCPO.m X Y) eq hom_le.
  Proof.
    intros f g Hfg Hgf.
    apply DCPO.meq. intros x.
    apply (@antisymmetry _ eq _ (@le _ (@dc_po _ DY)) (@le_po _ (@dc_po _ DY))).
    - apply Hfg.
    - apply Hgf.
  Qed.

  Definition hom_PO : DCPO.PartialOrder (DCPO.m X Y) :=
    {| le := hom_le;
       le_preo := hom_le_preo;
       le_po := hom_le_po |}.

  (** Pointwise evaluation of a directed family is directed *)
  Lemma eval_directed (F : DCPO.m X Y -> Prop)
    `{HF : @Directed _ hom_PO F} (x : CX) :
    @Directed _ (@dc_po _ DY) (fun y => exists f, F f /\ DCPO.apply X Y f x = y).
  Proof.
    destruct HF as [f0 Hf0 Hupper].
    exists (DCPO.apply X Y f0 x).
    - exists f0. split; auto.
    - intros y1 y2 [f1 [Hf1 Heq1]] [f2 [Hf2 Heq2]].
      destruct (Hupper f1 f2 Hf1 Hf2) as [f3 [Hf3 [Hle1 Hle2]]].
      exists (DCPO.apply X Y f3 x). split; [|split].
      + exists f3. split; auto.
      + subst. apply Hle1.
      + subst. apply Hle2.
  Qed.

  (** Pointwise supremum of a directed family *)
  Definition hom_dsup_fun (F : DCPO.m X Y -> Prop)
    `{HF : @Directed _ hom_PO F} (x : CX) : CY :=
    @dsup _ DY (fun y => exists f, F f /\ DCPO.apply X Y f x = y) (eval_directed F x).

  (** The pointwise supremum is Scott-continuous *)
  Lemma hom_dsup_scott (F : DCPO.m X Y -> Prop)
    `{HF : @Directed _ hom_PO F} :
    @ScottContinuous _ _ DX (@dc_po _ DY) (hom_dsup_fun F).
  Proof.
    constructor. intros D HD.
    constructor.
    - (* sup_ub: show each f(x) for x ∈ D is ≤ f(dsup D) *)
      intros _ [x Hx].
      unfold hom_dsup_fun.
      apply sup_lub. intros z [g [Hg Heqz]].
      apply (@transitivity _ (@le _ (@dc_po _ DY)) _ z (DCPO.apply X Y g (@dsup _ DX D HD)) _).
      + rewrite <- Heqz.
        apply (@sc_le _ _ DX (@dc_po _ DY) (DCPO.apply X Y g) (DCPO.morphism X Y g)).
        apply sup_ub. exact Hx.
      + apply sup_ub. exists g. split; auto.
    - (* sup_lub: show dsup is least upper bound *)
      intros y Hub.
      unfold hom_dsup_fun.
      apply sup_lub. intros z [g [Hg Heqz]].
      rewrite <- Heqz.
      rewrite (@sc_dsup _ _ DX DY (DCPO.apply X Y g) (DCPO.morphism X Y g)).
      apply sup_lub. intros _ [x Hx].
      apply (@transitivity _ (@le _ (@dc_po _ DY)) _ (DCPO.apply X Y g x) (hom_dsup_fun F x) y).
      + apply sup_ub. exists g. split; auto.
      + apply Hub. exact (im_intro _ D x Hx).
  Qed.

  Definition hom_dsup (F : DCPO.m X Y -> Prop)
    `{HF : @Directed _ hom_PO F} : DCPO.m X Y :=
    @DCPO.mkm X Y (hom_dsup_fun F) (hom_dsup_scott F).

  Lemma hom_dsup_is_sup (F : DCPO.m X Y -> Prop)
    `{HF : @Directed _ hom_PO F} :
    @IsSup _ hom_PO F (hom_dsup F).
  Proof.
    constructor.
    - intros f Hf x. simpl. unfold hom_dsup_fun.
      apply sup_ub. exists f. split; auto.
    - intros g Hub x. simpl. unfold hom_dsup_fun.
      apply sup_lub. intros y [f [Hf Heq]].
      rewrite <- Heq. apply Hub. exact Hf.
  Qed.

  Definition hom_DirectedComplete : DirectedComplete (DCPO.m X Y) :=
    {| dc_po := hom_PO;
       dsup := @hom_dsup;
       dsup_is_sup := @hom_dsup_is_sup |}.

End DCPOHomDCPO.

(** ** Composition is Scott-continuous *)

Section DCPOCompositionContinuous.

  (** Left composition: g ∘ - is Scott-continuous *)
  Lemma dcpo_compose_continuous_l (A B C : DCPO.t) (g : DCPO.m B C) :
    @ScottContinuous _ _
      (hom_DirectedComplete A B)
      (@dc_po _ (hom_DirectedComplete A C))
      (fun f => DCPO.compose g f).
  Proof.
    constructor. intros F HF.
    constructor.
    - (* sup_ub: (g ∘ f) ≤ (g ∘ dsup F) for each f ∈ F *)
      intros _ [f Hf] x. simpl.
      apply (@sc_le _ _ (DCPO.structure B) (@dc_po _ (DCPO.structure C))
               (DCPO.apply B C g) (DCPO.morphism B C g)).
      simpl. unfold hom_dsup_fun.
      apply sup_ub. exists f. split; auto.
    - (* sup_lub: (g ∘ dsup F) ≤ h for any upper bound h *)
      intros h Hub x. simpl.
      (* Goal: g(dsup_fun F x) ≤ h(x) where dsup_fun F x = dsup {f(x) | f ∈ F} *)
      (* By Scott-continuity of g: g(dsup {f(x)}) = dsup {g(f(x))} *)
      pose proof (DCPO.morphism B C g) as Hg.
      pose proof (@sc_dsup_sup _ _ (DCPO.structure B) (@dc_po _ (DCPO.structure C))
                    (DCPO.apply B C g) Hg
                    (fun y => exists f, F f /\ DCPO.apply A B f x = y)
                    (eval_directed A B F x)) as Hsup.
      apply (@sup_lub _ (@dc_po _ (DCPO.structure C)) _ _ Hsup).
      intros y [b [f [Hf Heqb]]]. simpl in *.
      rewrite <- Heqb.
      apply (Hub (DCPO.compose g f) (im_intro _ F f Hf) x).
  Qed.

  (** Right composition: - ∘ f is Scott-continuous *)
  Lemma dcpo_compose_continuous_r (A B C : DCPO.t) (f : DCPO.m A B) :
    @ScottContinuous _ _
      (hom_DirectedComplete B C)
      (@dc_po _ (hom_DirectedComplete A C))
      (fun g => DCPO.compose g f).
  Proof.
    constructor. intros G HG.
    constructor.
    - (* sup_ub *)
      intros _ [g Hg] x. simpl.
      simpl. unfold hom_dsup_fun.
      apply sup_ub. exists g. split; auto.
    - (* sup_lub *)
      intros h Hub x. simpl.
      simpl. unfold hom_dsup_fun.
      apply sup_lub. intros y [g [Hg Heq]].
      rewrite <- Heq.
      apply (Hub (DCPO.compose g f) (im_intro _ G g Hg) x).
  Qed.

End DCPOCompositionContinuous.

(** ** Package as DCPOCategoryDefinition *)

Module DCPOAsDCPOCategory <: DCPOCategoryDefinition.
  Module C := DCPO.
  Include C.

  Definition hom_dcpo (A B : t) : DirectedComplete (m A B) :=
    hom_DirectedComplete A B.

  Definition compose_continuous_l (A B C : t) (g : m B C) :
    @ScottContinuous _ _ (hom_dcpo A B) (@dc_po _ (hom_dcpo A C)) (fun f => compose g f) :=
    dcpo_compose_continuous_l A B C g.

  Definition compose_continuous_r (A B C : t) (f : m A B) :
    @ScottContinuous _ _ (hom_dcpo B C) (@dc_po _ (hom_dcpo A C)) (fun g => compose g f) :=
    dcpo_compose_continuous_r A B C f.

End DCPOAsDCPOCategory.
