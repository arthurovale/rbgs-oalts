Require Import interfaces.Category.
Require Import oalts.AsyncEvents.
Require Import oalts.Sig.
Require Import oalts.Tree.

From Paco Require Import paco.

Module Strat. (* <: Category *)
  Import AsyncEvents.
  Import Sig.
  Import Tree.

  Local Open Scope event_scope.
  Definition strat (A B : sig) : Type := tree «A -o B».

  Definition id_gen {A : sig} (ev : [A]) : «A -o A» :=
    match ev with
    | inl a => ⟨tgt a | src a⟩
    | inr a => ⟨src a | tgt a⟩
    end.

  CoFixpoint id (A : sig) : strat A A :=
    go (StepF (X := [A]) id_gen (fun _ => id A)).

  Module StLess.
    Import Sets.

    CoFixpoint StLess {A B : sig} (gen : Sig.m A B) : strat A B :=
      go (StepF (X := [A]) 
        (fun ev => 
          match ev with 
          | inl a => 
            match gen^- a with 
            | 'b => ⟨tgt b | src a⟩
            | ɛ => ⟨ | src a⟩
            end
          | inr a =>
            match gen^+ a with 
            | 'b => ⟨src a | tgt b⟩
            | ɛ => ⟨src a | ⟩
            end
          end)
        (fun _ => StLess gen)).

    Proposition id_stless_id {A : sig} :
      bisim (id A) (StLess (Sig.id A)).
    Proof.
      pcofix IH. pfold. unfold bisimF. simpl.
      split; intros ev; exists ev;
      destruct ev as [a | a]; split; 
      try reflexivity; right; exact IH.
    Qed.
  End StLess.
    
End Strat.
