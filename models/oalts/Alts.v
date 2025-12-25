Require Import interfaces.Category.
Require Import oalts.AsyncEvents.
Require Import oalts.Sig.
Require Import oalts.Tree.
From Paco Require Import paco.

Module ALTS. (* <: Category. *)
  Import AsyncEvents.  
  Import Tree.

  Record alts {A : Type} := {
    states : Type;
    trans : states -> [A] -> states -> Prop;
  }.
  Arguments alts : clear implicits.

  Section Beh.
    Context {A : Type}.
    Variable σ : alts A.

    Inductive tau_star : states σ -> states σ -> Prop :=
    | tau_refl : forall s, tau_star s s
    | tau_step : forall s1 s2 s3, 
        trans σ s1 τ s2 -> tau_star s2 s3 -> tau_star s1 s3.

    Lemma tau_star_trans : forall (s1 s2 s3 : states σ),
      tau_star s1 s2 -> tau_star s2 s3 -> tau_star s1 s3.
    Proof.
      intros s1 s2 s3 H1 H2.
      induction H1; auto.
      econstructor; eauto.
    Qed.

    (* τ* followed by visible step *)
    Definition weak_trans (s : states σ) (ev : A) (s' : states σ) : Prop :=
      exists s'', tau_star s s'' /\ trans σ s'' (vis ev) s'.

    CoFixpoint beh (s : states σ) : tree A :=
      go (
        StepF 
          (X := { ev : A  &  { s' : states σ | weak_trans s ev s' }})
          (fun x => projT1 x)
          (fun x => beh (proj1_sig (projT2 x)))
      ).
  End Beh.

  Section Sim.
    Context {A B : Type} (f : m A B).
    Variable σ : alts A.
    Variable ρ : alts B.

    (* Convention: σ states are s1, s2, etc. and ρ states are s1', s2', etc. *)

    (* R comes before s1, s1' for paco compatibility *)
    Definition alts_simF (R : states σ -> states ρ -> Prop)
      (s1 : states σ) (s1' : states ρ) : Prop :=
      (forall ev s2, trans σ s1 (vis ev) s2 ->
        match f ev with
        | 'ev' => exists s2', weak_trans ρ s1' ev' s2' /\ R s2 s2'
        | τ => R s2 s1'
        end) /\
      (forall s2, trans σ s1 τ s2 -> R s2 s1').

    Lemma alts_simF_mon : monotone2 alts_simF.
    Proof.
      unfold monotone2, alts_simF. intros s1 s1' R R' [Hvis Htau] LE.
      split.
      - intros ev s2 Htrans. specialize (Hvis ev s2 Htrans).
        destruct (f ev) as [ev' |].
        + destruct Hvis as [s2' [Hweak HR]]. exists s2'. split; auto.
        + apply LE. exact Hvis.
      - intros s2 Htrans. apply LE. apply Htau. exact Htrans.
    Qed.

    #[local] Hint Resolve alts_simF_mon : paco.

    Definition alts_sim : states σ -> states ρ -> Prop :=
      paco2 alts_simF bot2.

    Proposition alts_simF_sim : forall s1 s1',
      alts_simF alts_sim s1 s1' -> alts_sim s1 s1'.
    Proof.
      intros s1 s1' [Hvis Htau]. pfold. split.
      - intros ev s2 Htrans. specialize (Hvis ev s2 Htrans).
        destruct (f ev) as [ev' |].
        + destruct Hvis as [s2' [Hweak HR]]. exists s2'. split; auto.
        + left. exact Hvis.
      - intros s2 Htrans. left. apply Htau. exact Htrans.
    Qed.

    Proposition alts_sim_simF : forall s1 s1',
      alts_sim s1 s1' -> alts_simF alts_sim s1 s1'.
    Proof.
      intros s1 s1' H. punfold H. destruct H as [Hvis Htau]. split.
      - intros ev s2 Htrans. specialize (Hvis ev s2 Htrans).
        destruct (f ev) as [ev' |].
        + destruct Hvis as [s2' [Hweak HR]]. exists s2'. split; auto.
          destruct HR; auto. contradiction.
        + destruct Hvis; auto. contradiction.
      - intros s2 Htrans. specialize (Htau s2 Htrans).
        destruct Htau; auto. contradiction.
    Qed.

    Lemma alts_sim_tau_star : forall s1 s2 s1',
      alts_sim s1 s1' -> tau_star σ s1 s2 -> alts_sim s2 s1'.
    Proof.
      intros s1 s2 s1' Hsim Hstar.
      induction Hstar.
      - exact Hsim.
      - apply alts_sim_simF in Hsim as [Hvis Htau].
        apply IHHstar.
        apply Htau. exact H.
    Qed.

  Theorem alts_sim_beh : forall s1 s1',
    alts_sim s1 s1' -> sim f (beh σ s1) (beh ρ s1').
  Proof.
    pcofix CIH.
    intros s1 s1' Hsim.
    pfold. simpl.
    intros [ev [s2 Hweak]]. simpl.
    destruct Hweak as [s3 [Hstar Htrans]].
    pose proof (alts_sim_tau_star s1 s3 s1' Hsim Hstar) as Hsim'.
    apply alts_sim_simF in Hsim' as [Hvis Htau].
    specialize (Hvis ev s2 Htrans).
    destruct (f ev) as [ev' |] eqn:Hf.
    + (* Visible case *)
      destruct Hvis as [s2' [Hweak2 Hsim'']].
      exists (existT _ ev' (exist _ s2' Hweak2)).
      simpl. split.
      * reflexivity.
      * right. apply CIH. exact Hsim''.
    + (* Tau case *)
      right. apply CIH. exact Hvis.
  Qed.

  End Sim.

End ALTS.