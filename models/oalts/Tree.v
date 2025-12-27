Require Import oalts.AsyncEvents.
Require Import oalts.Sig.
Require Import models.Sets.
From Paco Require Import paco.

Module Tree. (* <: Category. *)
  Import AsyncEvents.

  Variant treeF (A : Type) (tree : Type) : Type :=
  (* step *)
  | StepF {X : Type} (step : X -> A) (k : X -> tree).

  CoInductive tree (A : Type) : Type :=
    go { _observe : treeF A (tree A) }.

  Arguments StepF {A} [tree] [X].
  Arguments _observe {A}.
  Arguments go {A}.

  Notation tree' A := (treeF A (tree A)).

  Definition observe {A} (t : tree A) : tree' A := @_observe A t.

  Lemma tree_eta : forall {A} (t : tree A), t = go (observe t).
  Proof.
    intros A t. destruct t as [[X step k]]. reflexivity.
  Qed.

  Section Simulation.
    Definition simF {A : Type}
      (R : tree A -> tree A -> Prop) (p : tree A) (q : tree A) : Prop :=
      match observe p, observe q with
      |  @StepF _ _ X step_p k_p, @StepF _ _ X' step_q k_q =>
        forall x, exists x', step_p x = step_q x' /\ R (k_p x) (k_q x')
      end.

    Lemma simF_mon {A : Type} : monotone2 (@simF A).
    Proof.
      unfold monotone2, simF. intros p q R R' H LE.
      destruct (observe p) as [X step_p k_p].
      destruct (observe q) as [X' step_q k_q].
      intros x. specialize (H x).
      destruct H as [x' [Heq HR]]. exists x'. split; auto.
    Qed.

    Hint Resolve simF_mon : paco.

    Definition sim {A : Type} : tree A -> tree A -> Prop :=
      paco2 simF bot2.

    Proposition simF_sim : forall {A : Type} (p : tree A) (q : tree A),
      simF (sim) p q -> sim p q.
    Proof.
      intros A p q H. pfold. unfold simF in *.
      destruct (observe p) as [X step_p k_p].
      destruct (observe q) as [X' step_q k_q].
      intros x. specialize (H x).
      destruct H as [x' [Heq HR]]. exists x'. split; auto.
    Qed.

    Proposition sim_simF : forall {A : Type} (p : tree A) (q : tree A),
      sim p q -> simF sim p q.
    Proof.
      intros A p q H. punfold H. unfold simF in *.
      destruct (observe p) as [X step_p k_p].
      destruct (observe q) as [X' step_q k_q].
      intros x. specialize (H x).
      destruct H as [x' [Heq HR]]. exists x'. split; auto.
      destruct HR; auto. contradiction.
    Qed.

    Proposition sim_refl {A : Type} (p : tree A) : sim p p.
    Proof.
      revert p. pcofix IH.
      intros p. pfold. unfold simF.
      destruct (observe p) as [X step_p k_p].
      intros x. exists x. split.
      - reflexivity.
      - right. apply IH.
    Qed.

    (* Note: Simulation is NOT symmetric. That's what distinguishes it from
       bisimulation. sim p q /\ sim q p <-> bisim p q *)

    Proposition sim_trans {A : Type} (p q s : tree A) :
      sim p q -> sim q s -> sim p s.
    Proof.
      revert p q s. pcofix IH. intros p q s Hpq Hqs.
      punfold Hpq. punfold Hqs. pfold. unfold simF in *.
      destruct (observe p) as [X step_p k_p].
      destruct (observe q) as [Y step_q k_q].
      destruct (observe s) as [Z step_s k_s].
      intros x.
      specialize (Hpq x). destruct Hpq as [y [Heq_pq HR_pq]].
      specialize (Hqs y). destruct Hqs as [z [Heq_qs HR_qs]].
      exists z. split.
      - transitivity (step_q y); assumption.
      - destruct HR_pq as [HR_pq | []]. destruct HR_qs as [HR_qs | []].
        right. eapply IH; eassumption.
    Qed.
  End Simulation.

  #[export] Hint Resolve simF_mon : paco.

  Section Bisimulation.
    Definition bisimF {A : Type}
      (R : tree A -> tree A -> Prop) (p : tree A) (q : tree A) : Prop :=
      match observe p, observe q with
      |  @StepF _ _ X step_p k_p, @StepF _ _ X' step_q k_q =>
        (forall x, exists x', step_p x = step_q x' /\ R (k_p x) (k_q x')) /\
        (forall x', exists x, step_p x = step_q x' /\ R (k_p x) (k_q x'))
      end.

    Lemma bisimF_mon {A : Type} : monotone2 (@bisimF A).
    Proof.
      unfold monotone2, bisimF. intros p q R R' H LE.
      destruct (observe p) as [X step_p k_p].
      destruct (observe q) as [X' step_q k_q].
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

    Hint Resolve bisimF_mon : paco.

    Definition bisim {A : Type} : tree A -> tree A -> Prop :=
      paco2 (bisimF) bot2.

    Proposition bisimF_bisim : forall {A : Type} (p : tree A) (q : tree A),
      bisimF bisim p q -> bisim p q.
    Proof.
      intros A p q H. pfold. unfold bisimF in *.
      destruct (observe p) as [X step_p k_p].
      destruct (observe q) as [X' step_q k_q].
      destruct H as [Hfw Hbw]. split.
      - intros x. specialize (Hfw x).
        destruct Hfw as [x' [Heq HR]]. exists x'. split; auto.
      - intros x'. specialize (Hbw x').
        destruct Hbw as [x [Heq HR]]. exists x. split; auto.
    Qed.

    Proposition bisim_bisimF : forall {A : Type} (p : tree A) (q : tree A),
      bisim p q -> bisimF bisim p q.
    Proof.
      intros A p q H. punfold H. unfold bisimF in *.
      destruct (observe p) as [X step_p k_p].
      destruct (observe q) as [X' step_q k_q].
      destruct H as [Hfw Hbw]. split.
      - intros x. specialize (Hfw x).
        destruct Hfw as [x' [Heq HR]]. exists x'. split; auto.
        destruct HR; auto. contradiction.
      - intros x'. specialize (Hbw x').
        destruct Hbw as [x [Heq HR]]. exists x. split; auto.
        destruct HR; auto. contradiction.
    Qed.

    Proposition bisim_refl {A : Type} (p : tree A) : bisim p p.
    Proof.
      revert p. pcofix IH.
      intros p. pfold. unfold bisimF.
      destruct (observe p) as [X step_p k_p].
      split.
      - intros x. exists x. split.
        + reflexivity.
        + right. apply IH.
      - intros x'. exists x'. split.
        + reflexivity.
        + right. apply IH.
    Qed.

    Proposition bisim_sym {A : Type} (p q : tree A) : bisim p q -> bisim q p.
    Proof.
      revert p q. pcofix IH. intros p q H.
      punfold H. pfold. unfold bisimF in *.
      destruct (observe p) as [X step_p k_p].
      destruct (observe q) as [X' step_q k_q].
      destruct H as [Hfw Hbw]. split.
      - intros x'. specialize (Hbw x').
        destruct Hbw as [x [Heq HR]].
        exists x. split.
        + symmetry. exact Heq.
        + destruct HR as [HR | []]. right. apply IH. exact HR.
      - intros x. specialize (Hfw x).
        destruct Hfw as [x' [Heq HR]].
        exists x'. split.
        + symmetry. exact Heq.
        + destruct HR as [HR | []]. right. apply IH. exact HR.
    Qed.

    Proposition bisim_trans {A : Type} (p q s : tree A) :
      bisim p q -> bisim q s -> bisim p s.
    Proof.
      revert p q s. pcofix IH. intros p q s Hpq Hqs.
      punfold Hpq. punfold Hqs. pfold. unfold bisimF in *.
      destruct (observe p) as [X step_p k_p].
      destruct (observe q) as [Y step_q k_q].
      destruct (observe s) as [Z step_s k_s].
      destruct Hpq as [Hpq_fw Hpq_bw].
      destruct Hqs as [Hqs_fw Hqs_bw].
      split.
      - intros x.
        specialize (Hpq_fw x). destruct Hpq_fw as [y [Heq_pq HR_pq]].
        specialize (Hqs_fw y). destruct Hqs_fw as [z [Heq_qs HR_qs]].
        exists z. split.
        + transitivity (step_q y); assumption.
        + destruct HR_pq as [HR_pq | []]. destruct HR_qs as [HR_qs | []].
          right. eapply IH; eassumption.
      - intros z.
        specialize (Hqs_bw z). destruct Hqs_bw as [y [Heq_qs HR_qs]].
        specialize (Hpq_bw y). destruct Hpq_bw as [x [Heq_pq HR_pq]].
        exists x. split.
        + transitivity (step_q y); assumption.
        + destruct HR_pq as [HR_pq | []]. destruct HR_qs as [HR_qs | []].
          right. eapply IH; eassumption.
    Qed.

    Lemma bisim_sim_fwd {A : Type} (p q : tree A) :
      bisim p q -> sim p q.
    Proof.
      revert p q. pcofix IH. intros p q H.
      punfold H. pfold. unfold bisimF, simF in *.
      destruct (observe p) as [X step_p k_p].
      destruct (observe q) as [X' step_q k_q].
      destruct H as [Hfw Hbw].
      intros x.
      specialize (Hfw x). destruct Hfw as [x' [Heq HR]].
      exists x'. split.
      - exact Heq.
      - destruct HR as [HR | []]. right. apply IH. exact HR.
    Qed.

    Proposition bisim_impl_sim {A : Type} (p q : tree A) :
      bisim p q -> sim p q /\ sim q p.
    Proof.
      intros H. split.
      - apply bisim_sim_fwd. exact H.
      - apply bisim_sim_fwd. apply bisim_sym. exact H.
    Qed.

  End Bisimulation.

End Tree.

