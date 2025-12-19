Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import coqrel.LogicalRelations.
Require Import models.DCPO.
Require Import models.oalts.interfaces.PosetEnrichedCat.
Require Import models.oalts.LCoalg.

Require Import ProofIrrelevance.

(** * Poset-enriched labelled coalgebras *)

(** This is a generalization of DCPOLCoalg that only requires PosetCategory
    (monotonic composition) instead of DCPOCategory (Scott-continuous composition). *)

Module Type PosetLCoalgDefinition
  (L : CategoryDefinition) (S : PosetCategoryDefinition)
  (F : BifunctorDefinition L S S)
  <: CategoryDefinition.

  Declare Module LCoalg : LCoalgDefinition L S F.
  Include LCoalg.

End PosetLCoalgDefinition.

Module PosetLCoalgTheory
  (L : CategoryDefinition) (S : PosetCategoryDefinition)
  (F : BifunctorDefinition L S S)
  (C : PosetLCoalgDefinition L S F).
  Include CategoryTheory C.
  Import C.

  Local Notation "x [= y" := (@le _ (S.hom_po _ _) x y) (at level 70).

  Module FW <: CategoryDefinition.
    Record fw_sim (α β : coalg) :=
      mk_fw_sim {
        morL : L.m (labels α) (labels β);
        morS : S.m (states α) (states β);
        coalg_fw_sim_cond :
          S.compose β morS [= S.compose (F.fmap morL morS) α;
      }.
    Arguments morL {_ _}.
    Arguments morS {_ _}.
    Arguments coalg_fw_sim_cond {_ _}.

    Program Definition mor_to_fw_sim {α β : coalg} (f : coalg_mor α β) : fw_sim α β :=
      {|
        morL := C.morL f;
        morS := C.morS f;
      |}.
    Next Obligation.
      destruct f as [fl fs H]; cbn. rewrite H. reflexivity.
    Defined.

    Coercion mor_to_fw_sim : coalg_mor >-> fw_sim.

    Lemma meq {α β : coalg} (f : fw_sim α β) (g : fw_sim α β) :
      (morL f) = (morL g) -> (morS f) = (morS g) -> f = g.
    Proof.
      destruct f as [fl fs Hf]; destruct g as [gl gs Hg].
      cbn. intros Hl Hs. subst. f_equal. apply proof_irrelevance.
    Qed.

    Definition t : Type := C.t.

    Definition m (α β : t) : Type := fw_sim α β.

    Definition id (α : t) : m α α := C.id α.

    Program Definition compose {α β γ} (g : m β γ) (f : m α β) : m α γ :=
    {|
      morL := L.compose (morL g) (morL f);
      morS := @S.compose (states α) (states β) (states γ) (morS g) (morS f);
    |}.
    Next Obligation.
      pose proof (coalg_fw_sim_cond g) as Hg.
      pose proof (coalg_fw_sim_cond f) as Hf.
      pose proof (S.compose_monotonic_r (states α) (states β) (F.omap (labels γ) (states γ)) (morS f)) as Hmono_r.
      pose proof (S.compose_monotonic_l (states α) (F.omap (labels β) (states β)) (F.omap (labels γ) (states γ)) (F.fmap (morL g) (morS g))) as Hmono_l.
      etransitivity.
      - rewrite <- S.compose_assoc.
        apply Hmono_r. exact Hg.
      - rewrite S.compose_assoc.
        etransitivity.
        + apply Hmono_l. exact Hf.
        + rewrite <- S.compose_assoc.
          rewrite <- F.fmap_compose.
          reflexivity.
    Defined.

    Proposition compose_id_left :
      forall {A B} (f : m A B), compose (id B) f = f.
    Proof.
      intros. unfold compose, id. simpl.
      apply meq; cbn. rewrite L.compose_id_left; reflexivity.
      rewrite S.compose_id_left; reflexivity.
    Qed.

    Proposition compose_id_right :
      forall {A B} (f : m A B), compose f (id A) = f.
    Proof.
      intros. unfold compose, id. simpl.
      apply meq; cbn. rewrite L.compose_id_right; reflexivity.
      rewrite S.compose_id_right; reflexivity.
    Qed.

    Proposition compose_assoc :
      forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
      compose (compose h g) f = compose h (compose g f).
    Proof.
      intros. unfold compose. simpl.
      apply meq; cbn. rewrite L.compose_assoc; reflexivity.
      rewrite S.compose_assoc; reflexivity.
    Qed.

  End FW.

  Module BW <: CategoryDefinition.
    Record bw_sim (α β : coalg) :=
      mk_bw_sim {
        morL : L.m (labels α) (labels β);
        morS : S.m (states α) (states β);
        coalg_bw_sim_cond :
          S.compose (F.fmap morL morS) α [= S.compose β morS;
      }.
    Arguments morL {_ _}.
    Arguments morS {_ _}.
    Arguments coalg_bw_sim_cond {_ _}.

    Program Definition mor_to_bw_sim {α β : coalg} (f : coalg_mor α β) : bw_sim α β :=
      {|
        morL := C.morL f;
        morS := C.morS f;
      |}.
    Next Obligation.
      destruct f as [fl fs H]; cbn. rewrite H. reflexivity.
    Defined.

    Coercion mor_to_bw_sim : coalg_mor >-> bw_sim.

    Lemma meq {α β : coalg} (f : bw_sim α β) (g : bw_sim α β) :
      (morL f) = (morL g) -> (morS f) = (morS g) -> f = g.
    Proof.
      destruct f as [fl fs Hf]; destruct g as [gl gs Hg].
      cbn. intros Hl Hs. subst. f_equal. apply proof_irrelevance.
    Qed.

    Definition t : Type := C.t.

    Definition m (α β : t) : Type := bw_sim α β.

    Definition id (α : t) : m α α := C.id α.

    Program Definition compose {α β γ} (g : m β γ) (f : m α β) : m α γ :=
    {|
      morL := L.compose (morL g) (morL f);
      morS := @S.compose (states α) (states β) (states γ) (morS g) (morS f);
    |}.
    Next Obligation.
      pose proof (coalg_bw_sim_cond g) as Hg.
      pose proof (coalg_bw_sim_cond f) as Hf.
      pose proof (S.compose_monotonic_r (states α) (states β) (F.omap (labels γ) (states γ)) (morS f)) as Hmono_r.
      pose proof (S.compose_monotonic_l (states α) (F.omap (labels β) (states β)) (F.omap (labels γ) (states γ)) (F.fmap (morL g) (morS g))) as Hmono_l.
      etransitivity.
      - rewrite F.fmap_compose. rewrite S.compose_assoc. reflexivity.
      - etransitivity.
        + apply Hmono_l. exact Hf.
        + rewrite <- !S.compose_assoc.
          apply Hmono_r. exact Hg.
    Defined.

    Proposition compose_id_left :
      forall {A B} (f : m A B), compose (id B) f = f.
    Proof.
      intros. unfold compose, id. simpl.
      apply meq; cbn. rewrite L.compose_id_left; reflexivity.
      rewrite S.compose_id_left; reflexivity.
    Qed.

    Proposition compose_id_right :
      forall {A B} (f : m A B), compose f (id A) = f.
    Proof.
      intros. unfold compose, id. simpl.
      apply meq; cbn. rewrite L.compose_id_right; reflexivity.
      rewrite S.compose_id_right; reflexivity.
    Qed.

    Proposition compose_assoc :
      forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
      compose (compose h g) f = compose h (compose g f).
    Proof.
      intros. unfold compose. simpl.
      apply meq; cbn. rewrite L.compose_assoc; reflexivity.
      rewrite S.compose_assoc; reflexivity.
    Qed.
  End BW.

End PosetLCoalgTheory.

Module PosetLCoalg
  (L : PosetCategoryDefinition) (S : PosetCategoryDefinition)
  (F : PosetBifunctorDefinition L S S) <: Category.
  Include PosetLCoalgDefinition L S F.
  Include PosetLCoalgTheory L S F.
End PosetLCoalg.
