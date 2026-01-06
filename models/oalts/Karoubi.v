Require Import Oalts.
Require Import Morphisms.
Require Import Coq.Program.Basics.

Module KaroubiBase. (* <: Category *)
  Import OALTS.

  Record idem (A : sig) : Type := {
    carrier :> oalts A A;
    idempotence : carrier ;; carrier ≈ carrier;
  }.
  Arguments carrier {A}. 
  Arguments idempotence {A}.

  Program Definition id_idem (A : sig) : idem A := {|
    carrier := OALTS.id A;
  |}.
  Next Obligation.
    rewrite OALTS.compose_id_left. reflexivity.
  Defined.

  Record idem_mor {A B : sig} (eA: idem A) (eB : idem B) : Type := {
    carrier_mor :> oalts A B;
    saturation : eA ;; carrier_mor ;; eB ≈ carrier_mor;
  }.
  Arguments carrier_mor {A B} {eA eB}.
  Arguments saturation {A B} {eA eB}.

  Proposition saturation_left {A B : sig} {eA : idem A} {eB : idem B} :
    forall (σ : idem_mor eA eB), eB @ σ ≈ (σ : oalts A B).
  Proof.
    intros σ. rewrite <- (saturation σ) at 1.
    rewrite <- !OALTS.compose_assoc. rewrite (idempotence eB).
    exact (saturation σ).
  Qed.

  Proposition saturation_right {A B : sig} {eA : idem A} {eB : idem B} :
    forall (σ : idem_mor eA eB), σ @ eA ≈ (σ : oalts A B).
  Proof.
    intros σ. rewrite <- (saturation σ) at 1.
    rewrite !OALTS.compose_assoc. rewrite (idempotence eA).
    rewrite <- !OALTS.compose_assoc. exact (saturation σ).
  Qed.

  Program Definition id {A : sig} (e : idem A) : idem_mor e e := {|
    carrier_mor := e;
  |}.
  Next Obligation.
    rewrite !idempotence. reflexivity.
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
    Definition idem_mor_sim {A B : sig} {eA : idem A} {eB : idem B}
      (σ τ : idem_mor eA eB) : Prop :=
      (σ : oalts A B) ≲ (τ : oalts A B).

    Lemma idem_mor_sim_intro {A B : sig} {eA : idem A} {eB : idem B}
      {σ τ : idem_mor eA eB} :
      (σ : oalts A B) ≲ (τ : oalts A B) -> idem_mor_sim σ τ.
    Proof. auto. Qed.

    Lemma idem_mor_sim_elim {A B : sig} {eA : idem A} {eB : idem B}
      {σ τ : idem_mor eA eB} :
      idem_mor_sim σ τ -> (σ : oalts A B) ≲ (τ : oalts A B).
    Proof. auto. Qed.

    Notation "σ ≲ τ" := (idem_mor_sim σ τ).

    (** Bisimulation lifting: σ ≈ τ iff their carriers are bisimilar *)
    Definition idem_mor_bisim {A B : sig} {eA : idem A} {eB : idem B}
      (σ τ : idem_mor eA eB) : Prop :=
      (σ : oalts A B) ≈ (τ : oalts A B).
      
    Lemma idem_mor_bisim_intro {A B : sig} {eA : idem A} {eB : idem B}
      {σ τ : idem_mor eA eB} :
      (σ : oalts A B) ≈ (τ : oalts A B) -> idem_mor_bisim σ τ.
    Proof. auto. Qed.

    Lemma idem_mor_bisim_elim {A B : sig} {eA : idem A} {eB : idem B}
      {σ τ : idem_mor eA eB} :
      idem_mor_bisim σ τ -> (σ : oalts A B) ≈ (τ : oalts A B).
    Proof. auto. Qed.

    Local Notation "σ ≈ τ" := (idem_mor_bisim σ τ).

    (** Simulation properties *)
    Lemma idem_mor_sim_refl {A B : sig} {eA : idem A} {eB : idem B} :
      forall (σ : idem_mor eA eB), σ ≲ σ.
    Proof. intro. apply alts_sim_refl. Qed.

    Lemma idem_mor_sim_trans {A B : sig} {eA : idem A} {eB : idem B} :
      forall (σ τ ρ : idem_mor eA eB), σ ≲ τ -> τ ≲ ρ -> σ ≲ ρ.
    Proof. intros. eapply alts_sim_trans; eassumption. Qed.

    (** Bisimulation properties *)
    Lemma idem_mor_bisim_refl {A B : sig} {eA : idem A} {eB : idem B} :
      forall (σ : idem_mor eA eB), σ ≈ σ.
    Proof. intro. apply alts_bisim_refl. Qed.

    Lemma idem_mor_bisim_sym {A B : sig} {eA : idem A} {eB : idem B} :
      forall (σ τ : idem_mor eA eB), σ ≈ τ -> τ ≈ σ.
    Proof. intros. apply alts_bisim_sym. assumption. Qed.

    Lemma idem_mor_bisim_trans {A B : sig} {eA : idem A} {eB : idem B} :
      forall (σ τ ρ : idem_mor eA eB), σ ≈ τ -> τ ≈ ρ -> σ ≈ ρ.
    Proof. intros. eapply alts_bisim_trans; eassumption. Qed.
  End Simulation.

  Add Parametric Relation {A B : sig} {eA : idem A} {eB : idem B}
    : (idem_mor eA eB) idem_mor_sim
    reflexivity proved by idem_mor_sim_refl
    transitivity proved by idem_mor_sim_trans
    as idem_mor_sim_preorder.

  Add Parametric Morphism {A B C : sig} {eA : idem A} {eB : idem B} {eC : idem C}
    : (@compose A B C eA eB eC)
    with signature idem_mor_sim ==> idem_mor_sim ==> idem_mor_sim
    as karoubi_compose_sim_morphism.
  Proof.
    intros τ τ' Hτ σ σ' Hσ. simpl.
    apply OALTS.compose_mon; assumption.
  Qed.

  (** Register bisimulation as equivalence relation for setoid rewriting *)
  Add Parametric Relation {A B : sig} {eA : idem A} {eB : idem B}
    : (idem_mor eA eB) idem_mor_bisim
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

  (** Simulation is proper with respect to bisimulation *)
  Add Parametric Morphism {A B : sig} {eA : idem A} {eB : idem B}
    : (@idem_mor_sim A B eA eB)
    with signature idem_mor_bisim ==> idem_mor_bisim ==> iff
    as idem_mor_sim_bisim_morphism.
  Proof.
    intros σ σ' Hσ τ τ' Hτ.
    apply alts_sim_bisim_morphism; assumption.
  Qed.

  (** Rewriting simulations inside simulation goals *)
  Add Parametric Morphism {A B : sig} {eA : idem A} {eB : idem B}
    : (@idem_mor_sim A B eA eB)
    with signature idem_mor_sim ==> flip idem_mor_sim ==> flip impl
    as idem_mor_sim_sim_morphism.
  Proof.
    intros σ σ' Hσ τ τ' Hτ H.
    unfold idem_mor_sim in *.
    eapply alts_sim_trans; [exact Hσ |].
    eapply alts_sim_trans; [exact H | exact Hτ].
  Qed.

  Arguments idem_mor_bisim {A B eA eB} _ _.
  Arguments idem_mor_sim {A B eA eB} _ _.

  Delimit Scope karoubi_scope with karoubi.
  Bind Scope karoubi_scope with idem_mor.
  Bind Scope karoubi_scope with idem.

  Notation "σ ≲ τ" := (idem_mor_sim σ τ) : karoubi_scope.
  Notation "σ ≈ τ" := (idem_mor_bisim σ τ) : karoubi_scope.

  Proposition idem_mor_bisim_sim_fw {A B} {eA : idem A} {eB : idem B}
    (σ τ : idem_mor eA eB) : σ ≈ τ -> σ ≲ τ.
  Proof.
    apply alts_bisim_sim_fw.
  Qed.

  Proposition idem_mor_bisim_sim_bw {A B} {eA : idem A} {eB : idem B}
    (σ τ : idem_mor eA eB) : σ ≈ τ -> τ ≲ σ.
  Proof.
    apply alts_bisim_sim_bw.
  Qed.

  Proposition compose_id_left {A B} {eA : idem A} {eB : idem B} 
    (σ : idem_mor eA eB) : id eB @ σ ≈ σ.
  Proof.
    apply saturation_left.
  Qed.

  Proposition compose_id_right {A B} {eA : idem A} {eB : idem B} 
    (σ : idem_mor eA eB) : σ @ id eA ≈ σ.
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
  Import OALTS.
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
    unfold idem_mor_bisim; reflexivity.
  Qed.

  Proposition fmap_compose {A B C : sig} (σ : oalts A B) (τ : oalts B C) :
    Emb (σ ;; τ) ≈ Emb σ ;; Emb τ.
  Proof.
    unfold idem_mor_bisim; reflexivity.
  Qed.

End Emb.

Module KarOp.
  Import OALTS.
  Import KaroubiBase.

  Program Definition K {A B : sig} (eA : idem A) (eB : idem B) (σ : oalts A B) :
    idem_mor eA eB := {| carrier_mor := eA ;; σ ;; eB |}.
  Next Obligation.
    rewrite !OALTS.compose_assoc. rewrite (idempotence eA).
    rewrite <- !OALTS.compose_assoc. rewrite (idempotence eB).
    reflexivity.
  Defined.

  Add Parametric Morphism {A B : sig} (eA : idem A) (eB : idem B)
    : (K eA eB)
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
    unfold idem_mor_bisim; simpl. rewrite OALTS.compose_id_right.
    apply (idempotence e).
  Qed.

  Proposition K_idempotent {A B : sig} {eA : idem A} {eB : idem B} :
    forall σ, K eA eB (K eA eB σ) ≈ K eA eB σ.
  Proof.
    intros σ. unfold idem_mor_bisim; simpl.
    rewrite !OALTS.compose_assoc. rewrite (idempotence eA).
    rewrite <- !OALTS.compose_assoc. rewrite (idempotence eB).
    reflexivity.
  Qed.

  Proposition K_surjective {A B : sig} {eA : idem A} {eB : idem B} : 
    forall (σ : idem_mor eA eB), K eA eB σ ≈ σ.
  Proof.
    intros σ. unfold idem_mor_bisim. rewrite (saturation σ). reflexivity.
  Qed.

  Proposition K_Emb {A B : sig} :
    forall (σ : oalts A B), Emb.Emb σ ≈ K (id_idem A) (id_idem B) σ.
  Proof.
    intros. unfold idem_mor_bisim; simpl. 
    rewrite OALTS.compose_id_left. rewrite OALTS.compose_id_right.
    reflexivity.
  Qed.

End KarOp.

Module Karoubi.
  Include KaroubiBase.
  Include Emb.
  Include KarOp.

End Karoubi.