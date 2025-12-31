Require Import Oalts.

Module KaroubiBase. (* <: Category *)
  Export OALTS.

  Record idem (A : sig) : Type := {
    carrier :> oalts A A;
    idempotency : carrier ;; carrier ≈ carrier;
  }.
  Arguments carrier {A}. 
  Arguments idempotency {A}.

  Program Definition id_idem (A : sig) : idem A := {|
    carrier := OALTS.id A;
  |}.
  Next Obligation.
    rewrite OALTS.compose_id_left. reflexivity.
  Defined.

  Record idem_mor {A B : sig} (e : idem A) (e' : idem B) : Type := {
    carrier_mor :> oalts A B;
    saturation : e ;; carrier_mor ;; e' ≈ carrier_mor;
  }.
  Arguments carrier_mor {A B} {e e'}.
  Arguments saturation {A B} {e e'}.    

  Proposition saturation_left {A B : sig} {e : idem A} {e' : idem B} :
    forall (σ : idem_mor e e'), e' @ σ ≈ (σ : oalts A B).
  Proof.
    intros σ. rewrite <- (saturation σ) at 1.
    rewrite <- !OALTS.compose_assoc. rewrite (idempotency e').
    exact (saturation σ).
  Qed.

  Proposition saturation_right {A B : sig} {e : idem A} {e' : idem B} :
    forall (σ : idem_mor e e'), σ @ e ≈ (σ : oalts A B).
  Proof.
    intros σ. rewrite <- (saturation σ) at 1.
    rewrite !OALTS.compose_assoc. rewrite (idempotency e).
    rewrite <- !OALTS.compose_assoc. exact (saturation σ).
  Qed.

  Program Definition id {A : sig} (e : idem A) : idem_mor e e := {|
    carrier_mor := e;
  |}.
  Next Obligation.
    rewrite !idempotency. reflexivity.
  Defined.

  Program Definition compose {A B C : sig} {eA : idem A} {eB : idem B} {eC : idem C}
    (τ : idem_mor eB eC) (σ : idem_mor eA eB) : idem_mor eA eC := {|
      carrier_mor := τ @ σ
    |}.
  Next Obligation.
    rewrite !OALTS.compose_assoc. rewrite (saturation_right σ).
    rewrite <- !OALTS.compose_assoc. rewrite (saturation_left τ).
    reflexivity.
  Defined.
  
  Close Scope oalts_scope.

  Notation "τ @ σ" := (compose τ σ) (at level 45, right associativity) : karoubi_scope.
  Notation "σ ;; τ" := (compose τ σ) (at level 60, right associativity) : karoubi_scope.

  Open Scope karoubi_scope.

  Section Simulation.

    (** Simulation lifting: σ simulates τ iff their carriers do *)
    Definition idem_mor_sim {A B : sig} {e : idem A} {e' : idem B}
      (σ τ : idem_mor e e') : Prop :=
      (σ : oalts A B) ≲ (τ : oalts A B).

    Local Notation "σ ≲ τ" := (idem_mor_sim σ τ).

    (** Bisimulation lifting: σ ≈ τ iff their carriers are bisimilar *)
    Definition idem_mor_bisim {A B : sig} {e : idem A} {e' : idem B}
      (σ τ : idem_mor e e') : Prop :=
      (σ : oalts A B) ≈ (τ : oalts A B).

    Local Notation "σ ≈ τ" := (idem_mor_bisim σ τ).

    (** Simulation properties *)
    Lemma idem_mor_sim_refl {A B : sig} {e : idem A} {e' : idem B} :
      forall (σ : idem_mor e e'), σ ≲ σ.
    Proof. intro. apply alts_sim_refl. Qed.

    Lemma idem_mor_sim_trans {A B : sig} {e : idem A} {e' : idem B} :
      forall (σ τ ρ : idem_mor e e'), σ ≲ τ -> τ ≲ ρ -> σ ≲ ρ.
    Proof. intros. eapply alts_sim_trans; eassumption. Qed.

    (** Bisimulation properties *)
    Lemma idem_mor_bisim_refl {A B : sig} {e : idem A} {e' : idem B} :
      forall (σ : idem_mor e e'), σ ≈ σ.
    Proof. intro. apply alts_bisim_refl. Qed.

    Lemma idem_mor_bisim_sym {A B : sig} {e : idem A} {e' : idem B} :
      forall (σ τ : idem_mor e e'), σ ≈ τ -> τ ≈ σ.
    Proof. intros. apply alts_bisim_sym. assumption. Qed.

    Lemma idem_mor_bisim_trans {A B : sig} {e : idem A} {e' : idem B} :
      forall (σ τ ρ : idem_mor e e'), σ ≈ τ -> τ ≈ ρ -> σ ≈ ρ.
    Proof. intros. eapply alts_bisim_trans; eassumption. Qed.

    (** Register bisimulation as equivalence relation for setoid rewriting *)
    Add Parametric Relation {A B : sig} {e : idem A} {e' : idem B}
      : (idem_mor e e') idem_mor_bisim
      reflexivity proved by idem_mor_bisim_refl
      symmetry proved by idem_mor_bisim_sym
      transitivity proved by idem_mor_bisim_trans
      as idem_mor_bisim_equiv.

    (** Compose is proper with respect to bisimulation *)
    Add Parametric Morphism {A B C : sig} {eA : idem A} {eB : idem B} {eC : idem C}
      : (@compose A B C eA eB eC)
      with signature idem_mor_bisim ==> idem_mor_bisim ==> idem_mor_bisim
      as karoubi_compose_morphism.
    Proof.
      intros τ τ' Hτ σ σ' Hσ. simpl.
      apply OALTS.compose_cong; assumption.
    Qed.

  End Simulation.

  Arguments idem_mor_bisim {A B e e'} _ _ /.
  Arguments idem_mor_sim {A B e e'} _ _ /.

  Bind Scope karoubi_scope with idem_mor.
  Bind Scope karoubi_scope with idem.

  Notation "σ ≲ τ" := (idem_mor_sim σ τ) : karoubi_scope.
  Notation "σ ≈ τ" := (idem_mor_bisim σ τ) : karoubi_scope.

  Proposition compose_id_left {A B} {e : idem A} {e' : idem B} 
    (σ : idem_mor e e') : id e' @ σ ≈ σ.
  Proof.
    apply saturation_left.
  Qed.

  Proposition compose_id_right {A B} {e : idem A} {e' : idem B} 
    (σ : idem_mor e e') : σ @ id e ≈ σ.
  Proof.
    apply saturation_right.
  Qed.

  Proposition compose_assoc {A B C D} 
    {eA : idem A} {eB : idem B} {eC : idem C} {eD : idem D}
    (σ : idem_mor eA eB) (τ : idem_mor eB eC) (ρ : idem_mor eC eD) : 
    (ρ @ τ) @ σ ≈ ρ @ (τ @ σ).
  Proof.
    apply OALTS.compose_assoc.
  Qed.

End KaroubiBase.

Module Emb.
  Import KaroubiBase.

  Program Definition Emb {A B : sig}
    (σ : oalts A B) : idem_mor (id_idem A) (id_idem B) := 
    {|
      carrier_mor := σ;
    |}.
  Next Obligation.
    rewrite OALTS.compose_id_left. rewrite OALTS.compose_id_right.
    reflexivity.
  Defined.

  Proposition fmap_id {A : sig} : Emb (OALTS.id A) ≈ id (id_idem A).
  Proof.
    simpl; reflexivity.
  Qed.

  Proposition fmap_compose {A B C : sig} (σ : oalts A B) (τ : oalts B C) :
    Emb (σ ;; τ) ≈ Emb σ ;; Emb τ.
  Proof.
    simpl; reflexivity.
  Qed.

End Emb.

Module KarOp.
  Import KaroubiBase.

  Program Definition K {A B : sig} (e : idem A) (e' : idem B) (σ : oalts A B) :
    idem_mor e e' := {| carrier_mor := e ;; σ ;; e' |}.
  Next Obligation.
    rewrite !OALTS.compose_assoc. rewrite (idempotency e).
    rewrite <- !OALTS.compose_assoc. rewrite (idempotency e').
    reflexivity.
  Defined.

  Add Parametric Morphism {A B : sig} (e : idem A) (e' : idem B)
    : (K e e')
    with signature alts_bisim ==> idem_mor_bisim
    as K_morphism.
  Proof.
    intros σ τ Hbisim. simpl.
    apply OALTS.compose_cong; [apply alts_bisim_refl |].
    apply OALTS.compose_cong; [exact Hbisim | apply alts_bisim_refl].
  Qed.

  Proposition K_id {A : sig} {e : idem A} :
    K e e (OALTS.id A) ≈ id e.
  Proof.
    simpl. rewrite OALTS.compose_id_right.
    apply (idempotency e).
  Qed.

  Proposition K_idempotent {A B : sig} {e : idem A} {e' : idem B} :
    forall σ, K e e' (K e e' σ) ≈ K e e' σ.
  Proof.
    intros σ. simpl.
    rewrite !OALTS.compose_assoc. rewrite (idempotency e).
    rewrite <- !OALTS.compose_assoc. rewrite (idempotency e').
    reflexivity.
  Qed.

  Proposition K_surjective {A B : sig} {eA : idem A} {eB : idem B} : 
    forall (σ : idem_mor eA eB), K eA eB σ ≈ σ.
  Proof.
    intros σ. simpl. rewrite (saturation σ). reflexivity.
  Qed.

End KarOp.

Module Karoubi.
  Include KaroubiBase.
  Include Emb.
  Include KarOp.
End Karoubi.