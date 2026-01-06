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

Proposition impl_cond_by_obs_ref {A B : sig} {eA : idem A} {eB : idem B} 
  {νA : Spec eA} {νB : Spec eB} (σ : idem_mor eA eB) :
  ((νA ;; σ)%oalts ≲ (Kar νB : oalts _ _))%alts <-> 
  Kar νA ;; σ ≲ Kar νB.
Proof.
  split.
  - intros H. apply idem_mor_sim_intro. simpl. 
    rewrite !OALTS.compose_assoc. rewrite OALTS.compose_id_right.
    rewrite <- !OALTS.compose_assoc. rewrite (saturation_right σ). 
    simpl in H. assumption.
  - intros. apply idem_mor_sim_elim in H. simpl in H. 
    rewrite OALTS.compose_assoc in H. rewrite OALTS.compose_id_right in H.
    rewrite <- OALTS.compose_assoc in H. rewrite (saturation_right σ) in H.
    exact H.
Qed.

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

Open Scope oalts_scope.
Definition lin {A : sig} {eA : idem A} 
  (νA' : Spec eA) (νA : Spec eA) := (νA' ;; eA ≲ νA ;; eA)%alts.
Close Scope oalts_scope.

Notation "νA' ⊒ νA" := (lin νA' νA) (at level 70) : karspec_scope.

Proposition lin_refl {A : sig} {eA : idem A} {νA : Spec eA} : νA ⊒ νA.
Proof.
  unfold lin. reflexivity.
Qed.

Proposition lin_trans {A : sig} {eA : idem A}
  {νA'' : Spec eA} {νA' : Spec eA} {νA : Spec eA} :
  νA'' ⊒ νA' -> νA' ⊒ νA -> νA'' ⊒ νA.
Proof.
  unfold lin. apply alts_sim_trans.
Qed.

Proposition lin_sim {A : sig} {eA : idem A} {νA' νA : Spec eA} :
  (νA' ≲ (νA ;; eA)%oalts)%alts -> νA' ⊒ νA.
Proof.
  intros H. unfold lin. rewrite H. rewrite <- OALTS.compose_assoc.
  rewrite (idempotence eA). reflexivity.
Qed.

Program Definition impl_conseq {A B : sig} {eA : idem A} {eB : idem B} 
  {νA' νA : Spec eA} {νB νB' : Spec eB}  
  (HA : νA' ⊒ νA) (HB : νB ⊒ νB') (σ : impl νA νB) : impl νA' νB' :=
  {|
    carrier_mor := σ;
  |}.
Next Obligation.
  destruct σ as [σ H]. apply idem_mor_sim_intro. simpl.
  unfold lin in *. rewrite HA. apply idem_mor_sim_elim in H. rewrite H.
  simpl. rewrite !OALTS.compose_assoc. rewrite !OALTS.compose_id_right.
  exact HB.
Defined.

Proposition impl_coseq_carrier_eq {A B : sig} {eA : idem A} {eB : idem B} 
  {νA' νA : Spec eA} {νB νB' : Spec eB}  {HA : νA' ⊒ νA} {HB : νB ⊒ νB'} 
  {σ : impl νA νB} : 
  carrier_mor (impl_conseq HA HB σ) = σ.
Proof.
  reflexivity.
Qed.