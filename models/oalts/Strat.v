Require Import interfaces.Category.
Require Import oalts.AsyncEvents.
Require Import oalts.Sig.
Require Import oalts.Tree.

Module OPALTS. (* <: Category *)
  Import AsyncEvents.
  Import Sig.
  Import Tree.

  Local Open Scope event_scope.
  Definition strat (A B : sig) : Type := tree [A -o B].

  Definition id_gen {A : sig} (ev : {+A+}) : [A -o A] :=
    match ev with
    | ⊖ a => ⟨⊕a | ⊖a⟩
    | ⊕ a => ⟨⊖a | ⊕a⟩
    end.

  CoFixpoint id (A : sig) : strat A A :=
    go (StepF (X := {+A+}) id_gen (fun _ => id A)).

  Axiom compose : forall {A B C : sig}, strat A B -> strat B C -> strat A C.

End OPALTS.