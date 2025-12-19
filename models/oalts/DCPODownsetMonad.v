Require Import interfaces.Category.
Require Import interfaces.ConcreteCategory.
Require Import interfaces.Monads.
Require Import models.DCPO.
Require Import models.oalts.DownsetMonad.
Require Import models.oalts.interfaces.DCPOEnrichedCat.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import ProofIrrelevance.
Require Import coqrel.LogicalRelations.

(** * DCPO-Enrichment of the Downset Monad's Kleisli Category *)

(** We prove that the Kleisli category of the downset monad on Poset
    is DCPO-enriched. This means:
    1. Downsets of a poset form a DCPO (directed sup = union)
    2. Hom-sets in the Kleisli category are DCPOs
    3. Kleisli composition is Scott-continuous in both arguments *)

Module DCPODownsetKleisli.
  Import DownsetMonad.
  Import Poset.

  (** ** Downsets form a DCPO *)

  Section DownsetDCPO.
    Variable P : Type.
    Variable PO : DCPO.PartialOrder P.

    (** Directed union of downsets *)
    Lemma dset_dsup_closed (DD : dset PO -> Prop) `{HD : @Directed _ (dset_PO PO) DD} :
      forall a b : P, a [= b ->
        (exists D, DD D /\ has D b) -> (exists D, DD D /\ has D a).
    Proof.
      intros a b Hab [D0 [HDD HDb]].
      exists D0. split; [exact HDD |].
      eapply (@closed P PO); eauto.
    Qed.

    Program Definition dset_dsup (DD : dset PO -> Prop)
      `{HD : @Directed _ (dset_PO PO) DD} : dset PO :=
      {| has := fun x => exists D, DD D /\ has D x; |}.
    Next Obligation.
      intros  DD Dir a b Hab [D0 [HDD HDb]].
      exists D0. split; [exact HDD |].
      eapply (@closed P PO); eauto.
    Defined.

    Lemma dset_dsup_is_sup (DD : dset PO -> Prop)
      `{HD : @Directed _ (dset_PO PO) DD} :
      @IsSup _ (dset_PO PO) DD (dset_dsup DD).
    Proof.
      constructor.
      - intros D HDD. unfold dset_le. simpl.
        intros x Hx. exists D. split; auto.
      - intros y Hub. unfold dset_le. simpl.
        intros x [D [HDD Hx]].
        apply (Hub D HDD). exact Hx.
    Qed.

    Definition dset_DirectedComplete : DirectedComplete (dset PO) :=
      {| dc_po := dset_PO PO;
         dsup := @dset_dsup;
         dsup_is_sup := @dset_dsup_is_sup |}.

  End DownsetDCPO.

  (** ** Hom-sets in Kleisli category are DCPOs *)

  Section KleisliHomDCPO.
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

    (** Pointwise evaluation of a directed family is directed *)
    Lemma eval_directed (F : Poset.m X (omap Y) -> Prop)
      `{HF : @Directed _ kl_hom_PO F} (x : X) :
      @Directed _ (dset_PO POY) (fun D => exists f, F f /\ Poset.apply X (omap Y) f x = D).
    Proof.
      destruct HF as [f0 Hf0 Hupper].
      exists (Poset.apply X (omap Y) f0 x).
      - exists f0. split; auto.
      - intros D1 D2 [f1 [Hf1 Heq1]] [f2 [Hf2 Heq2]].
        destruct (Hupper f1 f2 Hf1 Hf2) as [f3 [Hf3 [Hle1 Hle2]]].
        exists (Poset.apply X (omap Y) f3 x). split; [|split].
        + exists f3. split; auto.
        + subst. apply Hle1.
        + subst. apply Hle2.
    Qed.

    (** Pointwise supremum: union of all f(x) for f in F *)
    Lemma kl_hom_dsup_fun_closed (F : Poset.m X (omap Y) -> Prop)
      `{HF : @Directed _ kl_hom_PO F} (x : X) :
      forall a b : Y, @le Y POY a b ->
        (exists f, F f /\ has (Poset.apply X (omap Y) f x) b) ->
        (exists f, F f /\ has (Poset.apply X (omap Y) f x) a).
    Proof.
      intros a b Hab [f [Hf Hb]].
      exists f. split; [exact Hf |].
      eapply (@closed Y POY); eauto.
    Qed.

    Definition kl_hom_dsup_fun (F : Poset.m X (omap Y) -> Prop)
      `{HF : @Directed _ kl_hom_PO F} (x : X) : dset POY :=
      {| has := fun y => exists f, F f /\ has (Poset.apply X (omap Y) f x) y;
         closed := kl_hom_dsup_fun_closed F x |}.

    (** The pointwise supremum is monotone in x *)
    Lemma kl_hom_dsup_monotone (F : Poset.m X (omap Y) -> Prop)
      `{HF : @Directed _ kl_hom_PO F} :
      @Poset.Morphism _ _ POX (dset_PO POY) (kl_hom_dsup_fun F).
    Proof.
      intros x1 x2 Hle y [f [Hf Hy]].
      exists f. split; auto.
      exact (Poset.morphism X (omap Y) f x1 x2 Hle y Hy).
    Qed.

    (** Pointwise supremum of a directed family of Kleisli morphisms *)
    Definition kl_hom_dsup (F : Poset.m X (omap Y) -> Prop)
      `{HF : @Directed _ kl_hom_PO F} : Poset.m X (omap Y) :=
      @Poset.mkm X (omap Y) (kl_hom_dsup_fun F) (kl_hom_dsup_monotone F).

    Lemma kl_hom_dsup_is_sup (F : Poset.m X (omap Y) -> Prop)
      `{HF : @Directed _ kl_hom_PO F} :
      @IsSup _ kl_hom_PO F (kl_hom_dsup F).
    Proof.
      constructor.
      - intros f Hf x y Hy. simpl.
        exists f. split; auto.
      - intros g Hub x y [f [Hf Hy]]. simpl in Hy.
        apply (Hub f Hf x). exact Hy.
    Qed.

    Definition kl_hom_DirectedComplete : DirectedComplete (Poset.m X (omap Y)) :=
      {| dc_po := kl_hom_PO;
         dsup := @kl_hom_dsup;
         dsup_is_sup := @kl_hom_dsup_is_sup |}.

  End KleisliHomDCPO.

  (** ** The Kleisli category is DCPO-enriched *)

  (** We prove that composition is Scott-continuous in both arguments *)

  Section KleisliDCPOEnriched.

    (** Left composition: g o - is Scott-continuous *)
    Lemma compose_continuous_l (A B C : Poset.t) (g : DownsetMonad.Kl.m B C) :
      @ScottContinuous _ _
        (kl_hom_DirectedComplete A B)
        (@dc_po _ (kl_hom_DirectedComplete A C))
        (fun f => DownsetMonad.Kl.compose g f).
    Proof.
      constructor. intros F HF.
      constructor.
      - intros _ [f Hf]. simpl.
        intros a c Hc. simpl.
        unfold Kl.compose in *.
        simpl in *.
        destruct Hc as [D [[b [Hfab Hle]] Hc]].
        exists (Poset.apply B (omap C) g b). split.
        + exists b. split.
          * exists f. split; auto.
          * intros z Hz. exact Hz.
        + apply Hle. exact Hc.
      - intros h Hub a c Hc. simpl in *.
        unfold Kl.compose in *.
        simpl in *.
        destruct Hc as [D [[b [[f [Hf Hfab]] Hle]] Hc]].
        pose proof (Hub (Poset.compose (ext g) f)
                        (im_intro _ F f Hf)) as Hfh.
        apply Hfh.
        exists (Poset.apply B (omap C) g b). split.
        + exists b. split; [exact Hfab | intros z Hz; exact Hz].
        + apply Hle. exact Hc.
    Qed.

    (** Right composition: - o f is Scott-continuous *)
    Lemma compose_continuous_r (A B C : Poset.t) (f : DownsetMonad.Kl.m A B) :
      @ScottContinuous _ _
        (kl_hom_DirectedComplete B C)
        (@dc_po _ (kl_hom_DirectedComplete A C))
        (fun g => DownsetMonad.Kl.compose g f).
    Proof.
      constructor. intros G HG.
      constructor.
      - intros _ [g Hg]. simpl.
        intros a c Hc.
        unfold Kl.compose in *.
        simpl in *.
        destruct Hc as [D [[b [Hfab Hle]] Hc]].
        exists (kl_hom_dsup_fun B C G b). split.
        + exists b. split; [exact Hfab | intros z Hz; exact Hz].
        + simpl. exists g. split; [exact Hg |].
          apply Hle. exact Hc.
      - intros h Hub a c Hc. simpl in *.
        unfold Kl.compose in *.
        simpl in *.
        destruct Hc as [D [[b [Hfab Hle]] Hc]].
        pose proof (Hle c Hc) as HdsupGb. simpl in HdsupGb.
        destruct HdsupGb as [g [Hg Hgbc]].
        pose proof (Hub (Poset.compose (ext g) f)
                        (im_intro _ G g Hg)) as Hgh.
        apply Hgh.
        exists (Poset.apply B (omap C) g b). split.
        + exists b. split; [exact Hfab | intros z Hz; exact Hz].
        + exact Hgbc.
    Qed.

  End KleisliDCPOEnriched.

End DCPODownsetKleisli.

(** ** DCPO-Enriched Kleisli Category *)

(** Package as a proper DCPO-enriched category satisfying DCPOCategoryDefinition *)

Module DCPODownsetKl <: DCPOCategoryDefinition.
  Module C := DownsetMonad.Kl.
  Include C.

  Definition hom_dcpo (A B : t) : DirectedComplete (m A B) :=
    DCPODownsetKleisli.kl_hom_DirectedComplete A B.

  Definition compose_continuous_l (A B C : t) (g : m B C) :
    @ScottContinuous _ _ (hom_dcpo A B) (@dc_po _ (hom_dcpo A C)) (fun f => compose g f) :=
    DCPODownsetKleisli.compose_continuous_l A B C g.

  Definition compose_continuous_r (A B C : t) (f : m A B) :
    @ScottContinuous _ _ (hom_dcpo B C) (@dc_po _ (hom_dcpo A C)) (fun g => compose g f) :=
    DCPODownsetKleisli.compose_continuous_r A B C f.

End DCPODownsetKl.
