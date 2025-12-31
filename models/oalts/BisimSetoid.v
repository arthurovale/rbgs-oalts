Require Import Setoid.
Require Import Morphisms.
Require Import Oalts.

Import OALTS.

Add Parametric Relation {A : Type} : (alts A) alts_bisim
  reflexivity proved by alts_bisim_refl
  symmetry proved by alts_bisim_sym
  transitivity proved by alts_bisim_trans
  as alts_bisim_equiv.

Add Parametric Morphism {A B C : sig} : (@compose A B C)
  with signature alts_bisim ==> alts_bisim ==> alts_bisim
  as compose_morphism.
Proof.
  intros τ τ' Hτ σ σ' Hσ.
  apply compose_cong; assumption.
Qed.

Export Setoid Morphisms.