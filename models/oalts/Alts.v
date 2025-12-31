Require Import interfaces.Category.
Require Import oalts.AsyncEvents.
Require Import oalts.Tree.
From Paco Require Import paco.

Module ALTS. (* <: Category. *)
  Import AsyncEvents.  
  Import Tree.

  Record alts {A : Type} := {
    states : Type;
    start : states -> Prop;
    trans :> states -> [A] -> states -> Prop;
  }.
  Arguments alts : clear implicits.

  Bind Scope alts_scope with alts.
  Delimit Scope alts_scope with alts.
  Open Scope alts_scope.

  Section Beh.
    Context {A : Type}.
    Variable σ : alts A.

    Inductive eps_star : states σ -> states σ -> Prop :=
    | eps_refl : forall s, eps_star s s
    | eps_step : forall s1 s2 s3,
        σ s1 ɛ s2 -> eps_star s2 s3 -> eps_star s1 s3.

    Lemma eps_star_trans : forall (s1 s2 s3 : states σ),
      eps_star s1 s2 -> eps_star s2 s3 -> eps_star s1 s3.
    Proof.
      intros s1 s2 s3 H1 H2.
      induction H1; auto.
      econstructor; eauto.
    Qed.

    (* ɛ* followed by visible step *)
    Definition weak_trans (s : states σ) (ev : A) (s' : states σ) : Prop :=
      exists s'', eps_star s s'' /\ σ s'' (vis ev) s'.

    CoFixpoint beh (s : states σ) : tree A :=
      go (
        StepF
          { ev : A  &  { s' : states σ | weak_trans s ev s' }}
          (fun x => projT1 x)
          (fun x => beh (proj1_sig (projT2 x)))
      ).
  End Beh.

  Section Sim.
    Context {A : Type}.
    Variable σ : alts A.
    Variable ρ : alts A.

    (* Convention: σ states are s1, s2, etc. and ρ states are s1', s2', etc. *)

    Definition alts_simF (R : states σ -> states ρ -> Prop)
      (s1 : states σ) (s1' : states ρ) : Prop :=
      (forall ev s2, σ s1 (vis ev) s2 ->
        exists s2', weak_trans ρ s1' ev s2' /\ R s2 s2') /\
      (forall s2, σ s1 ɛ s2 -> R s2 s1').

    Lemma alts_simF_mon : monotone2 alts_simF.
    Proof.
      unfold monotone2, alts_simF. intros s1 s1' R R' [Hvis Heps] LE.
      split.
      - intros ev s2 Htrans. specialize (Hvis ev s2 Htrans).
        destruct Hvis as [s2' [Hweak HR]]. exists s2'. split; auto.
      - intros s2 Htrans. apply LE. apply Heps. exact Htrans.
    Qed.

    #[local] Hint Resolve alts_simF_mon : paco.

    Definition alts_sim' : states σ -> states ρ -> Prop :=
      paco2 alts_simF bot2.

    Proposition alts_simF_sim' : forall s1 s1',
      alts_simF alts_sim' s1 s1' -> alts_sim' s1 s1'.
    Proof.
      intros s1 s1' [Hvis Heps]. pfold. split.
      - intros ev s2 Htrans. specialize (Hvis ev s2 Htrans).
        destruct Hvis as [s2' [Hweak HR]]. exists s2'. split; auto.
      - intros s2 Htrans. left. apply Heps. exact Htrans.
    Qed.

    Proposition alts_sim'_simF : forall s1 s1',
      alts_sim' s1 s1' -> alts_simF alts_sim' s1 s1'.
    Proof.
      intros s1 s1' H. punfold H. destruct H as [Hvis Heps]. split.
      - intros ev s2 Htrans. specialize (Hvis ev s2 Htrans).
        destruct Hvis as [s2' [Hweak HR]]. exists s2'. split; auto.
        destruct HR; auto. contradiction.
      - intros s2 Htrans. specialize (Heps s2 Htrans).
        destruct Heps; auto. contradiction.
    Qed.

    Lemma alts_sim_coind (R : states σ -> states ρ -> Prop) :
      (forall s1 s2, R s1 s2 -> alts_simF R s1 s2) ->
      forall s1 s2, R s1 s2 -> alts_sim' s1 s2.
    Proof.
      intros HR. pcofix CIH. intros s1 s2 Hrel.
      pfold. apply HR in Hrel. destruct Hrel as [Hvis Heps]. split.
      - intros ev s2' Htrans. specialize (Hvis ev s2' Htrans).
        destruct Hvis as [s1' [Hweak HRnew]].
        exists s1'. split; [exact Hweak | right; apply CIH; exact HRnew].
      - intros s2' Htrans. right. apply CIH. apply Heps. exact Htrans.
    Qed.

    Lemma alts_sim'_eps_star : forall s1 s2 s1',
      alts_sim' s1 s1' -> eps_star σ s1 s2 -> alts_sim' s2 s1'.
    Proof.
      intros s1 s2 s1' Hsim Hstar.
      induction Hstar.
      - exact Hsim.
      - apply alts_sim'_simF in Hsim as [Hvis Heps].
        apply IHHstar.
        apply Heps. exact H.
    Qed.

    Theorem alts_sim'_beh : forall s1 s1',
      alts_sim' s1 s1' -> ssim (beh σ s1) (beh ρ s1').
    Proof.
      pcofix CIH.
      intros s1 s1' Hsim.
      pfold. simpl.
      intros [ev [s2 Hweak]]. simpl.
      destruct Hweak as [s3 [Hstar Htrans]].
      pose proof (alts_sim'_eps_star s1 s3 s1' Hsim Hstar) as Hsim'.
      apply alts_sim'_simF in Hsim' as [Hvis Heps].
      specialize (Hvis ev s2 Htrans).
      destruct Hvis as [s2' [Hweak2 Hsim'']].
      exists (existT _ ev (exist _ s2' Hweak2)).
      simpl. split.
      - reflexivity.
      - right. apply CIH. exact Hsim''.
    Qed.

  End Sim.

  #[export] Hint Resolve alts_simF_mon : paco.

  (** Notation for state-level simulation *)
  Notation "s1 ≲'[ σ , ρ ] s1'" := (alts_sim' σ ρ s1 s1') (at level 70) : alts_scope.

  (** ** State-level simulation properties *)

  Lemma alts_sim'_refl_gen {A : Type} (σ : alts A) (s s' : states σ) :
    eps_star σ s' s -> alts_sim' σ σ s s'.
  Proof.
    revert s s'. pcofix IH. intros s s' Hstar. pfold. split.
    - intros ev s2 Htrans.
      exists s2. split.
      + exists s. split; [exact Hstar | exact Htrans].
      + right. apply IH. constructor.
    - intros s2 Htrans.
      right. apply IH.
      eapply eps_star_trans; 
      [exact Hstar | econstructor; [exact Htrans | constructor]].
  Qed.

  Proposition alts_sim'_refl {A : Type} (σ : alts A) (s : states σ) :
    alts_sim' σ σ s s.
  Proof.
    apply alts_sim'_refl_gen. constructor.
  Qed.

  Proposition alts_sim'_trans {A : Type} (σ ρ τ : alts A)
    (s1 : states σ) (s2 : states ρ) (s3 : states τ) :
    alts_sim' σ ρ s1 s2 -> alts_sim' ρ τ s2 s3 -> alts_sim' σ τ s1 s3.
  Proof.
    revert s1 s2 s3. pcofix IH. intros s1 s2 s3 H12 H23.
    apply alts_sim'_simF in H12 as [Hvis12 Heps12].
    pfold. split.
    - intros ev s1' Htrans.
      specialize (Hvis12 ev s1' Htrans).
      destruct Hvis12 as [s2' [[s2'' [Hstar12 Htrans12]] Hsim12]].
      pose proof (alts_sim'_eps_star ρ τ s2 s2'' s3 H23 Hstar12) as H23'.
      apply alts_sim'_simF in H23' as [Hvis23' Heps23'].
      specialize (Hvis23' ev s2' Htrans12).
      destruct Hvis23' as [s3' [Hweak23 Hsim23]].
      exists s3'. split.
      + exact Hweak23.
      + right. eapply IH; eassumption.
    - intros s1' Htrans.
      specialize (Heps12 s1' Htrans).
      right. eapply IH.
      + exact Heps12.
      + exact H23.
  Qed.

  (** State-level bisimulation: mutual simulation *)
  Definition alts_bisim' {A : Type} (σ ρ : alts A)
    (s1 : states σ) (s1' : states ρ) : Prop :=
    alts_sim' σ ρ s1 s1' /\ alts_sim' ρ σ s1' s1.

  Notation "s1 ≈'[ σ , ρ ] s1'" := (alts_bisim' σ ρ s1 s1') (at level 70) : alts_scope.

  Proposition alts_bisim'_refl {A : Type} (σ : alts A) (s : states σ) :
    alts_bisim' σ σ s s.
  Proof.
    split; apply alts_sim'_refl.
  Qed.

  Proposition alts_bisim'_sym {A : Type} (σ ρ : alts A)
    (s1 : states σ) (s2 : states ρ) :
    alts_bisim' σ ρ s1 s2 -> alts_bisim' ρ σ s2 s1.
  Proof.
    intros [H1 H2]. split; assumption.
  Qed.

  Proposition alts_bisim'_trans {A : Type} (σ ρ τ : alts A)
    (s1 : states σ) (s2 : states ρ) (s3 : states τ) :
    alts_bisim' σ ρ s1 s2 -> alts_bisim' ρ τ s2 s3 -> alts_bisim' σ τ s1 s3.
  Proof.
    intros [H12 H21] [H23 H32]. split.
    - eapply alts_sim'_trans; eassumption.
    - eapply alts_sim'_trans; eassumption.
  Qed.

  (** ** System-level simulation *)

  (** System-level simulation: for all start states of σ, exists a simulating start state of ρ *)
  Definition alts_sim {A : Type} (σ ρ : alts A) : Prop :=
    forall s1, start σ s1 -> exists s1', start ρ s1' /\ alts_sim' σ ρ s1 s1'.

  Notation "σ ≲ ρ" := (alts_sim σ ρ) (at level 70) : alts_scope.

  Proposition alts_sim_refl {A : Type} (σ : alts A) : σ ≲ σ.
  Proof.
    intros s Hstart. exists s. split.
    - exact Hstart.
    - apply alts_sim'_refl.
  Qed.

  Proposition alts_sim_trans {A : Type} (σ ρ τ : alts A) :
    σ ≲ ρ -> ρ ≲ τ -> σ ≲ τ.
  Proof.
    intros H12 H23 s1 Hstart1.
    specialize (H12 s1 Hstart1).
    destruct H12 as [s2 [Hstart2 Hsim12]].
    specialize (H23 s2 Hstart2).
    destruct H23 as [s3 [Hstart3 Hsim23]].
    exists s3. split.
    - exact Hstart3.
    - eapply alts_sim'_trans; eassumption.
  Qed.

  (** ** System-level bisimulation *)

  Definition alts_bisim {A : Type} (σ ρ : alts A) : Prop :=
    alts_sim σ ρ /\ alts_sim ρ σ.

  Notation "σ ≈ ρ" := (alts_bisim σ ρ) (at level 70) : alts_scope.

  Proposition alts_bisim_refl {A : Type} (σ : alts A) : σ ≈ σ.
  Proof.
    split; apply alts_sim_refl.
  Qed.

  Proposition alts_bisim_sym {A : Type} (σ ρ : alts A) :
    σ ≈ ρ -> ρ ≈ σ.
  Proof.
    intros [H1 H2]. split; assumption.
  Qed.

  Proposition alts_bisim_trans {A : Type} (σ ρ τ : alts A) :
    σ ≈ ρ -> ρ ≈ τ -> σ ≈ τ.
  Proof.
    intros [H12 H21] [H23 H32]. split.
    - eapply alts_sim_trans; eassumption.
    - eapply alts_sim_trans; eassumption.
  Qed.

  Add Parametric Relation {A : Type} : (alts A) alts_sim
  reflexivity proved by alts_sim_refl
  transitivity proved by alts_sim_trans
  as alts_sim_preorder.  

  Add Parametric Relation {A : Type} : (alts A) alts_bisim
    reflexivity proved by alts_bisim_refl
    symmetry proved by alts_bisim_sym
    transitivity proved by alts_bisim_trans
    as alts_bisim_equiv.

End ALTS.