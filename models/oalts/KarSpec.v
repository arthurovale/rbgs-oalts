Require Import Oalts.
Require Import Karoubi.

Import OALTS.
Import Karoubi.

Open Scope karoubi_scope.

Definition Spec {A : sig} (eA : idem A) := oalts T A.

Definition Kar {A : sig} {eA : idem A} (ν : Spec eA) :=
  K (id_idem T) eA ν.

Record impl {A B : sig} {eA : idem A} {eB : idem B} 
  (νA : Spec eA) (νB : Spec eB) := 
  {
    carrier_mor :> idem_mor eA eB;
    impl_cond : Kar νA ;; carrier_mor ≲ Kar νB;
  }.
Arguments carrier_mor {A B} {eA eB} {νA νB}.
Arguments impl_cond {A B} {eA eB} {νA νB}.

Program Definition id {A : sig} {eA : idem A} (νA : Spec eA) : impl νA νA :=
  {|
    carrier_mor := Karoubi.id eA;
  |}.
Next Obligation.
  apply compose_id_left.
Defined.

Program Definition compose {A B C : sig} {eA : idem A} {eB : idem B} {eC : idem C}
  {νA : Spec eA} {νB : Spec eB} {νC : Spec eC} (τ : impl νB νC) (σ : impl νA νB)
  : impl νA νC :=
  {|
    carrier_mor := τ @ σ
  |}.
Next Obligation.
  rewrite compose_assoc. rewrite (impl_cond σ). apply (impl_cond τ).
Defined.

Bind Scope karspec_scope with impl.
Delimit Scope karspec_scope with karspec.

Notation "τ @ σ" := (compose τ σ) (at level 45, right associativity) : karspec_scope.
Notation "σ ;; τ" := (compose τ σ) (at level 60, right associativity) : karspec_scope.

Open Scope karspec_scope.

Proposition compose_id_left {A B : sig} {eA : idem A} {eB : idem B} {νA : Spec eA} {νB : Spec eB}
  (σ : impl νA νB) : (id νB) @ σ ≈ σ.
Proof.
  apply compose_id_left.
Qed.

Proposition compose_id_right {A B : sig} {eA : idem A} {eB : idem B} {νA : Spec eA} {νB : Spec eB}
  (σ : impl νA νB) : σ @ (id νA) ≈ σ.
Proof.
  apply compose_id_right.
Qed.

Proposition compose_assoc {A B C D : sig} 
  {eA : idem A} {eB : idem B} {eC : idem C} {eD : idem D}
  {νA : Spec eA} {νB : Spec eB} {νC : Spec eC} {νD : Spec eD}
  (σ : impl νA νB) (τ : impl νB νC) (ρ : impl νC νD) :
  (ρ @ τ) @ σ ≈ ρ @ (τ @ σ).
Proof.
  apply compose_assoc.
Qed.