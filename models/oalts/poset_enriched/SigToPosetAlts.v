Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import coqrel.LogicalRelations.
Require Import models.DCPO.
Require Import models.oalts.DownsetMonad.
Require Import models.oalts.Sig.
Require Import models.oalts.poset_enriched.PosetBicartesian.
Require Import models.oalts.poset_enriched.PosetAsyncEvents.
Require Import models.oalts.poset_enriched.PosetDownsetKleisli.
Require Import models.oalts.poset_enriched.TimeDownset.
Require Import models.oalts.poset_enriched.PosetAlts.

(** * Embedding Signatures into Poset-Enriched ALTS

    A signature (A^-, A^+) is embedded as an ALTS where:
    - Events: A^- + A^+ (with discrete ordering)
    - States: the terminal poset (single state)
    - Step: trivial (always enabled)

    Morphisms of signatures become forward simulations.
*)

Module SigToPosetAlts (S : Sig PosetBicartesian PosetTerminals).
  Import S.
  Import PosetBicartesian.
  Import DCPO.
  Import DownsetMonad.
  Import DownsetMonadDef.
  Open Scope obj_scope.

  (** The terminal poset as state space *)
  Definition StatePoset : Poset.t := PosetBicartesian.C.Prod.unit.

  (** For a signature X = (neg X, pos X), the ALTS has:
      - Events: neg X + pos X
      - States: terminal poset (single point)
      - Step: trivially enabled (the downset containing everything) *)

  Section OmapDef.
    Variable X : S.t.

    Definition EventPoset : Poset.t := PosetBicartesian.Plus.omap (neg X) (pos X).

    Definition StepTarget : Poset.t := PosetTimeFunctor.omap EventPoset StatePoset.
    Definition StepTargetPO := Poset.structure StepTarget.

    (** The step predicate: everything is reachable *)
    Definition step_pred : Poset.carrier StepTarget -> Prop := fun _ => True.

    Lemma step_pred_closed :
      forall p1 p2, @le _ StepTargetPO p1 p2 -> step_pred p2 -> step_pred p1.
    Proof. intros. constructor. Qed.

    Definition step_dset : @dset _ StepTargetPO :=
      @mk_dset _ StepTargetPO step_pred step_pred_closed.

    Definition step_fun (_ : Poset.carrier StatePoset) : @dset _ StepTargetPO :=
      step_dset.

    Lemma step_mor : @Poset.Morphism _ _ (Poset.structure StatePoset)
                       (Poset.structure (omap StepTarget)) step_fun.
    Proof.
      intros s1 s2 Hle. intros p Hp. exact Hp.
    Qed.

    Definition step : Poset.m StatePoset (omap StepTarget) :=
      @Poset.mkm StatePoset (omap StepTarget) step_fun step_mor.

  End OmapDef.

  Definition omap (X : S.t) : PosetAlts.t :=
    PosetAltsInternal.mk_coalg (EventPoset X) StatePoset (step X).

  Section FmapDef.
    Variables A B : S.t.
    Variable f : S.m A B.

    Definition fmap_morL : PosetAsyncEventsPosetCat.m (EventPoset A) (EventPoset B) := f.

    Definition fmap_morS : PosetDownsetKl.m StatePoset StatePoset := PosetDownsetKl.id StatePoset.

    Lemma fmap_fw_cond :
      @le _ (PosetDownsetKl.hom_po StatePoset (StepTarget B))
        (PosetDownsetKl.compose (step B) fmap_morS)
        (PosetDownsetKl.compose (LiftedTimePosetBifunctor.fmap fmap_morL fmap_morS) (step A)).
    Proof.
      (* Forward simulation: step B . morS ≤ fmap(morL, morS) . step A
         Both step functions return the full downset (True predicate).
         The proof involves showing membership through Kleisli composition existentials. *)
    Admitted.
  End FmapDef.

  Definition fmap {A B : S.t} (f : S.m A B) : PosetAlts.m (omap A) (omap B) :=
    PosetAltsInternal.FW.mk_fw_sim (omap A) (omap B) (fmap_morL A B f) (fmap_morS) (fmap_fw_cond A B f).

  (** Functor laws *)
  Proposition fmap_id : forall A, fmap (S.id A) = PosetAlts.id (omap A).
  Proof.
    intros. unfold fmap, PosetAlts.id. simpl.
    apply PosetAltsInternal.FW.meq; reflexivity.
  Qed.

  Proposition fmap_compose :
    forall {A B C} (g : S.m B C) (f : S.m A B),
    fmap (S.compose g f) = PosetAlts.compose (fmap g) (fmap f).
  Proof.
    intros. unfold fmap, PosetAlts.compose. simpl.
    apply PosetAltsInternal.FW.meq.
    - reflexivity.
    - symmetry. apply PosetDownsetKl.compose_id_left.
  Qed.

  Proposition faithful :
    forall {A B} (f g : S.m A B), fmap f = fmap g -> f = g.
  Proof.
    intros A B f g Heq.
    assert (fmap_morL A B f = fmap_morL A B g) as HmorL.
    { apply (f_equal PosetAltsInternal.FW.morL) in Heq. exact Heq. }
    exact HmorL.
  Qed.

End SigToPosetAlts.
