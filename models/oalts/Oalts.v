Require Import interfaces.Category.
Require Import oalts.AsyncEvents.
Require Import oalts.Alts.
Require Import oalts.Sig.
From Paco Require Import paco.

Module OALTS. (* <: Category. *)
  Import AsyncEvents.
  Import Sig.
  Import ALTS.

  Definition oalts (A B : sig) := alts («A -o B»)%event_obj.

  Definition compose {A B C : sig} (σ : oalts A B) (τ : oalts B C) : oalts A C :=
    {|
      states := states σ * states τ;
      start := fun s => start σ (fst s) /\ start τ (snd s);
      trans := fun s ev s' =>
        (exists evs evt,
          (projR evs = projL evt /\ projL evs = ext projL ev /\ projR evt = ext projR ev) /\
          (σ (fst s) ('evs) (fst s') /\ τ (snd s) ('evt) (snd s'))) \/
        (exists evs,
          (projR evs = ɛ /\ projL evs = ext projL ev /\ ɛ = ext projR ev) /\
          (trans σ (fst s) ('evs) (fst s') /\ snd s = snd s')) \/
        (exists evt,
          (ɛ = projL evt /\ ɛ = ext projL ev /\ projR evt = ext projR ev) /\
          (fst s = fst s' /\ trans τ (snd s) ('evt) (snd s')));
    |}.

  Module StLess.
    Open Scope event_obj_scope.

    Definition StLess {A B : sig} (gen : Sig.m A B) : oalts A B :=
      {|
        states := unit;
        start := fun _ => True;
        trans := fun _ ev _ =>
          ext («gen»)%event_hom (ext projL ev) = ext projR ev
      |}.

    Proposition StLess_compose {A B C : sig} {gen : Sig.m A B} {gen' : Sig.m B C} :
      compose (StLess gen) (StLess gen') ≈ StLess (Sig.compose gen' gen).
    Proof.
    Admitted.
    
  End StLess.

End OALTS.