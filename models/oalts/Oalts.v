Require Import interfaces.Category.
Require Import oalts.AsyncEvents.
Require Import oalts.Alts.
Require Import oalts.Sig.

Module OALTS. (* <: Category. *)
  Import AsyncEvents.
  Import Sig.
  Import ALTS.

  Definition oalts (A B : sig) := alts («A -o B»)%event.

  Definition compose {A B C : sig} (σ : oalts A B) (τ : oalts B C) : oalts A C := 
    {|
      states := states σ * states τ;
      trans := fun s ev s' => 
        (exists evs evt, 
          (projR evs = projL evt /\ projL evs = projL ev /\ projR evt = projR ev) /\
          (σ (fst s) evs (fst s') /\ τ (snd s) evt (snd s'))) (*\/*)
        (* (exists evs, 
          (projR evs = ɛ /\ projL evs = projL ev /\ ɛ = projR ev) /\
          (trans σ (fst s) evs (fst s') /\ snd s = snd s')) \/
        (exists evt,
          (ɛ = projL evt /\ ɛ = projL ev /\ projR evt = projR ev) /\
          (fst s = fst s' /\ trans τ (snd s) evt (snd s'))); *)
    |}.

End OALTS.