Require Import oalts.AsyncEvents.
Require Import oalts.Sig.
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

  (* R comes before p, q for paco compatibility *)
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

End Tree.