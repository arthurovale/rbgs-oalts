Require Import oalts.AsyncEvents.
Require Import oalts.Sig.
Require Import models.Sets.
From Paco Require Import paco.
Require Import coqrel.RelOperators.

Module Tree. (* <: Category. *)
  Import AsyncEvents.

  Variant treeF (A : Type) (tree : Type) : Type :=
  | StepF (X : Type) (step : X -> A) (k : X -> tree)
  | EpsF (k : tree).

  CoInductive tree (A : Type) : Type :=
    go { _observe : treeF A (tree A) }.

  Arguments StepF {A} [tree].
  Arguments EpsF {A} [tree].
  Arguments _observe {A}.
  Arguments go {A}.

  Notation tree' A := (treeF A (tree A)).

  Definition observe {A} (t : tree A) : tree' A := @_observe A t.

  Lemma tree_eta : forall {A} (t : tree A), t = go (observe t).
  Proof.
    intros A t. destruct t; reflexivity.
  Qed.

  Section StrongSimulation.
    Definition ssimF {A : Type}
      (R : tree A -> tree A -> Prop) (p : tree A) (q : tree A) : Prop :=
      match observe p, observe q with
      |  StepF X step_p k_p, StepF X' step_q k_q =>
        forall x, exists x', step_p x = step_q x' /\ R (k_p x) (k_q x')
      | EpsF p', EpsF q' => R p' q'
      | _, _ => False
      end.

    Lemma ssimF_mon {A : Type} : monotone2 (@ssimF A).
    Proof.
      unfold monotone2, ssimF. intros p q R R' H LE.
      destruct (observe p) as [X step_p k_p | p'];
      destruct (observe q) as [X' step_q k_q | q'];
      try apply LE; try assumption.
      intros x. specialize (H x).
      destruct H as [x' [Heq HR]]. exists x'. split; auto.
    Qed.

    Hint Resolve ssimF_mon : paco.

    Lemma ssimF_refl {A : Type} (R : tree A -> tree A -> Prop) (p : tree A) :
      (forall t, R t t) -> ssimF R p p.
    Proof.
      unfold ssimF. intros Hrefl.
      destruct (observe p) as [X step_p k_p | p'].
      - intros x. exists x. split.
        + reflexivity.
        + apply Hrefl.
      - apply Hrefl.
    Qed.

    Lemma ssimF_trans {A : Type} (R S : tree A -> tree A -> Prop) (p q s : tree A) :
      ssimF R p q -> ssimF S q s -> ssimF (rel_compose R S) p s.
    Proof.
      unfold ssimF. intros Hpq Hqs.
      destruct (observe p) as [X step_p k_p | p'];
      destruct (observe q) as [Y step_q k_q | q'];
      destruct (observe s) as [Z step_s k_s | s'];
      try contradiction.
      - intros x.
        specialize (Hpq x). destruct Hpq as [y [Heq_pq HR_pq]].
        specialize (Hqs y). destruct Hqs as [z [Heq_qs HR_qs]].
        exists z. split.
        + transitivity (step_q y); assumption.
        + exists (k_q y). split; assumption.
      - exists q'. split; assumption.
    Qed.

    Definition ssim {A : Type} : tree A -> tree A -> Prop :=
      paco2 ssimF bot2.

    Proposition ssimF_ssim : forall {A : Type} (p : tree A) (q : tree A),
      ssimF (ssim) p q -> ssim p q.
    Proof.
      intros A p q H. pfold. unfold ssimF in *.
      destruct (observe p) as [X step_p k_p | p'];
      destruct (observe q) as [X' step_q k_q | q'];
      try assumption.
      - intros x. specialize (H x).
        destruct H as [x' [Heq HR]]. exists x'. split; auto.
      - left. exact H.
    Qed.

    Proposition ssim_ssimF : forall {A : Type} (p : tree A) (q : tree A),
      ssim p q -> ssimF ssim p q.
    Proof.
      intros A p q H. punfold H. unfold ssimF in *.
      destruct (observe p) as [X step_p k_p | p'];
      destruct (observe q) as [X' step_q k_q | q'];
      try assumption.
      - intros x. specialize (H x).
        destruct H as [x' [Heq HR]]. exists x'. split; auto.
        destruct HR; auto. contradiction.
      - destruct H; auto. contradiction.
    Qed.

    Proposition ssim_refl {A : Type} (p : tree A) : ssim p p.
    Proof.
      revert p. pcofix IH. intros p. pfold.
      apply ssimF_refl. intros t. right. apply IH.
    Qed.

    Proposition ssim_trans {A : Type} (p q s : tree A) :
      ssim p q -> ssim q s -> ssim p s.
    Proof.
      revert p q s. pcofix IH. intros p q s Hpq Hqs.
      punfold Hpq. punfold Hqs. pfold.
      eapply ssimF_mon.
      - eapply ssimF_trans; eassumption.
      - intros a c [b [Hab Hbc]].
        destruct Hab as [Hab | []]. destruct Hbc as [Hbc | []].
        right. eapply IH; eassumption.
    Qed.
  End StrongSimulation.

  #[export] Hint Resolve ssimF_mon : paco.

  Section StrongBisimulation.
    Definition sbisimF {A : Type}
      (R : tree A -> tree A -> Prop) (p : tree A) (q : tree A) : Prop :=
      match observe p, observe q with
      | StepF X step_p k_p, StepF X' step_q k_q =>
        (forall x, exists x', step_p x = step_q x' /\ R (k_p x) (k_q x')) /\
        (forall x', exists x, step_p x = step_q x' /\ R (k_p x) (k_q x'))
      | EpsF p', EpsF q' => R p' q'
      | _, _ => False
      end.

    Lemma sbisimF_mon {A : Type} : monotone2 (@sbisimF A).
    Proof.
      unfold monotone2, sbisimF. intros p q R R' H LE.
      destruct (observe p) as [X step_p k_p | p'];
      destruct (observe q) as [X' step_q k_q | q'];
      try apply LE; try assumption.
      destruct H as [Hfw Hbw]; split.
      - intros x. specialize (Hfw x).
        destruct Hfw as [x' [Heq Hr]].
        exists x'. split. 2: apply LE.
        all: assumption.
      - intros x'. specialize (Hbw x').
        destruct Hbw as [x [Heq Hr]].
        exists x. split. 2: apply LE.
        all: assumption.
    Qed.

    Hint Resolve sbisimF_mon : paco.

    Lemma sbisimF_refl {A : Type} (R : tree A -> tree A -> Prop) (p : tree A) :
      (forall t, R t t) -> sbisimF R p p.
    Proof.
      unfold sbisimF. intros Hrefl.
      destruct (observe p) as [X step_p k_p | p'].
      - split; intros x; exists x; split;
        try reflexivity; try (apply Hrefl).
      - apply Hrefl.
    Qed.

    Lemma sbisimF_trans {A : Type} (R S : tree A -> tree A -> Prop) (p q s : tree A) :
      sbisimF R p q -> sbisimF S q s -> sbisimF (rel_compose R S) p s.
    Proof.
      unfold sbisimF. intros Hpq Hqs.
      destruct (observe p) as [X step_p k_p | p'];
      destruct (observe q) as [Y step_q k_q | q'];
      destruct (observe s) as [Z step_s k_s | s'];
      try contradiction.
      - destruct Hpq as [Hpq_fw Hpq_bw].
        destruct Hqs as [Hqs_fw Hqs_bw].
        split.
        + intros x.
          specialize (Hpq_fw x). destruct Hpq_fw as [y [Heq_pq HR_pq]].
          specialize (Hqs_fw y). destruct Hqs_fw as [z [Heq_qs HR_qs]].
          exists z. split.
          * transitivity (step_q y); assumption.
          * exists (k_q y). split; assumption.
        + intros z.
          specialize (Hqs_bw z). destruct Hqs_bw as [y [Heq_qs HR_qs]].
          specialize (Hpq_bw y). destruct Hpq_bw as [x [Heq_pq HR_pq]].
          exists x. split.
          * transitivity (step_q y); assumption.
          * exists (k_q y). split; assumption.
      - exists q'. split; assumption.
    Qed.

    Lemma sbisimF_ssimF {A : Type} (R : tree A -> tree A -> Prop) (p q : tree A) :
      sbisimF R p q -> ssimF R p q.
    Proof.
      unfold sbisimF, ssimF.
      destruct (observe p) as [X step_p k_p | p'];
      destruct (observe q) as [X' step_q k_q | q'];
      try contradiction; auto.
      intros [Hfw _]. exact Hfw.
    Qed.

    Proposition sbisimF_sym {A : Type} (R : tree A -> tree A -> Prop) (p q : tree A) :
      sbisimF R p q -> sbisimF (flip R) q p.
    Proof.
      unfold sbisimF.
      destruct (observe p) as [X step_p k_p | p'];
      destruct (observe q) as [X' step_q k_q | q'];
      try contradiction; auto.
      intros [Hfw Hbw]. split.
      - intros x'. specialize (Hbw x').
        destruct Hbw as [x [Heq HR]].
        exists x. split.
        + symmetry. exact Heq.
        + exact HR.
      - intros x. specialize (Hfw x).
        destruct Hfw as [x' [Heq HR]].
        exists x'. split.
        + symmetry. exact Heq.
        + exact HR.
    Qed.

    Lemma sbisimF_mutual_ssimF {A : Type} (R : tree A -> tree A -> Prop) (p q : tree A) :
      sbisimF R p q <-> ssimF R p q /\ ssimF (flip R) q p.
    Proof.
      split.
      - intros H. split.
        + apply sbisimF_ssimF. exact H.
        + apply sbisimF_ssimF. apply sbisimF_sym. exact H.
      - unfold sbisimF, ssimF.
        destruct (observe p) as [X step_p k_p | p'];
        destruct (observe q) as [X' step_q k_q | q'].
        + intros [Hfw Hbw]. split.
          * exact Hfw.
          * intros x'. specialize (Hbw x').
            destruct Hbw as [x [Heq HR]].
            exists x. split.
            -- symmetry. exact Heq.
            -- exact HR.
        + intros [Hfw _]. contradiction.
        + intros [Hfw _]. contradiction.
        + intros [Hfw _]. exact Hfw.
    Qed.

    Definition sbisim {A : Type} : tree A -> tree A -> Prop :=
      paco2 (sbisimF) bot2.

    Proposition sbisimF_sbisim : forall {A : Type} (p : tree A) (q : tree A),
      sbisimF sbisim p q -> sbisim p q.
    Proof.
      intros A p q H. pfold. unfold sbisimF in *.
      destruct (observe p) as [X step_p k_p | p'];
      destruct (observe q) as [X' step_q k_q | q'];
      try assumption.
      - destruct H as [Hfw Hbw]. split.
        + intros x. specialize (Hfw x).
          destruct Hfw as [x' [Heq HR]]. exists x'. split; auto.
        + intros x'. specialize (Hbw x').
          destruct Hbw as [x [Heq HR]]. exists x. split; auto.
      - left. exact H.
    Qed.

    Proposition sbisim_sbisimF : forall {A : Type} (p : tree A) (q : tree A),
      sbisim p q -> sbisimF sbisim p q.
    Proof.
      intros A p q H. punfold H. unfold sbisimF in *.
      destruct (observe p) as [X step_p k_p | p'];
      destruct (observe q) as [X' step_q k_q | q'];
      try assumption.
      - destruct H as [Hfw Hbw]. split.
        + intros x. specialize (Hfw x).
          destruct Hfw as [x' [Heq HR]]. exists x'. split; auto.
          destruct HR; auto. contradiction.
        + intros x'. specialize (Hbw x').
          destruct Hbw as [x [Heq HR]]. exists x. split; auto.
          destruct HR; auto. contradiction.
      - destruct H; auto. contradiction.
    Qed.

    Proposition sbisim_refl {A : Type} (p : tree A) : sbisim p p.
    Proof.
      revert p. pcofix IH. intros p. pfold.
      apply sbisimF_refl. intros t. right. apply IH.
    Qed.

    Proposition sbisim_sym {A : Type} (p q : tree A) : sbisim p q -> sbisim q p.
    Proof.
      revert p q. pcofix IH. intros p q H.
      punfold H. pfold.
      apply sbisimF_sym in H.
      eapply sbisimF_mon. exact H.
      intros p' q' Hflip. unfold flip in Hflip.
      destruct Hflip as [Hflip | []].
      right. apply IH. exact Hflip.
    Qed.

    Proposition sbisim_trans {A : Type} (p q s : tree A) :
      sbisim p q -> sbisim q s -> sbisim p s.
    Proof.
      revert p q s. pcofix IH. intros p q s Hpq Hqs.
      punfold Hpq. punfold Hqs. pfold.
      eapply sbisimF_mon.
      - eapply sbisimF_trans; eassumption.
      - intros a c [b [Hab Hbc]].
        destruct Hab as [Hab | []]. destruct Hbc as [Hbc | []].
        right. eapply IH; eassumption.
    Qed.

    Lemma sbisim_ssim_fwd {A : Type} (p q : tree A) :
      sbisim p q -> ssim p q.
    Proof.
      revert p q. pcofix IH. intros p q H.
      punfold H. pfold.
      apply sbisimF_ssimF in H.
      eapply ssimF_mon. exact H.
      intros p' q' Hbisim.
      destruct Hbisim as [Hbisim | []].
      right. apply IH. exact Hbisim.
    Qed.

    Proposition sbisim_impl_ssim {A : Type} (p q : tree A) :
      sbisim p q -> ssim p q /\ ssim q p.
    Proof.
      intros H. split.
      - apply sbisim_ssim_fwd. exact H.
      - apply sbisim_ssim_fwd. apply sbisim_sym. exact H.
    Qed.

  End StrongBisimulation.

  #[export] Hint Resolve sbisimF_mon : paco.

End Tree.