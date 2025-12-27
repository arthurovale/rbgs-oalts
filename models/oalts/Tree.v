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
    Definition simF {A B : Type} (f : m A B)
      (R : tree A -> tree B -> Prop) (p : tree A) (q : tree B) : Prop :=
      match observe p, observe q with
      |  @StepF _ _ X step_p k_p, @StepF _ _ X' step_q k_q =>
        forall x,
          match f (step_p x) with
          | 'ev' => exists x', step_q x' = ev' /\ R (k_p x) (k_q x')
          | τ => R (k_p x) q
          end
      end.

    Lemma simF_mon {A B : Type} (f : m A B) : monotone2 (simF f).
    Proof.
      unfold monotone2, simF. intros p q R R' H LE.
      destruct (observe p) as [X step_p k_p].
      destruct (observe q) as [X' step_q k_q].
      intros x. specialize (H x).
      destruct (f (step_p x)) as [ev' |].
      - destruct H as [x' [Heq HR]]. exists x'. split; auto.
      - apply LE. exact H.
    Qed.

    Hint Resolve simF_mon : paco.

    Definition sim {A B : Type} (f : m A B) : tree A -> tree B -> Prop :=
      paco2 (simF f) bot2.

    Proposition simF_sim : forall {A B : Type} (f : m A B) (p : tree A) (q : tree B),
      simF f (sim f) p q -> sim f p q.
    Proof.
      intros A B f p q H. pfold. unfold simF in *.
      destruct (observe p) as [X step_p k_p].
      destruct (observe q) as [X' step_q k_q].
      intros x. specialize (H x).
      destruct (f (step_p x)) as [ev' |].
      - destruct H as [x' [Heq HR]]. exists x'. split; auto.
      - left. exact H.
    Qed.

    Proposition sim_simF : forall {A B : Type} (f : m A B) (p : tree A) (q : tree B),
      sim f p q -> simF f (sim f) p q.
    Proof.
      intros A B f p q H. punfold H. unfold simF in *.
      destruct (observe p) as [X step_p k_p].
      destruct (observe q) as [X' step_q k_q].
      intros x. specialize (H x).
      destruct (f (step_p x)) as [ev' |].
      - destruct H as [x' [Heq HR]]. exists x'. split; auto.
        destruct HR; auto. contradiction.
      - destruct H; auto. contradiction.
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

  End Bisimulation.

End Tree.
