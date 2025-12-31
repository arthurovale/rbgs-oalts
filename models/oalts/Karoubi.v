Require Import Oalts.
Require Import BisimSetoid.

Module Karoubi.
  Import OALTS.

  Open Scope oalts_scope.

  Record idem (A : sig) : Type := {
    carrier :> oalts A A;
    idempotency : carrier ;; carrier ≈ carrier
  }.
  Arguments carrier {A}. 
  Arguments idempotency {A}.

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

  Program Definition id_idem {A : sig} : idem A := {|
    carrier := OALTS.id A;
  |}.
  Next Obligation.
    rewrite OALTS.compose_id_left. reflexivity.
  Defined.

  Proposition compose_id_left {A B} {e : idem A} {e' : idem B} 
    (σ : idem_mor e e') : id e' @ σ ≈ (σ : oalts A B).
  Proof.
    apply saturation_left.
  Qed.

  Proposition compose_id_right {A B} {e : idem A} {e' : idem B} 
    (σ : idem_mor e e') : σ @ id e ≈ (σ : oalts A B).
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
End Karoubi.
