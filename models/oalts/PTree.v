Require Import oalts.AsyncEvents.
Require Import oalts.Sig.

Module PTree. (* <: Category. *) 
  Import AsyncEvents.
  Import Sig.

  Variant ptreeF (A : sig) (ptree : Type) : Type :=
  (* step *)
  | StepF {X : Type} (step : X -> A^- + A^+) (k : X -> ptree).

  CoInductive ptree (A : sig) : Type :=
    go { _observe : ptreeF A (ptree A) }.

  Arguments StepF {A} [ptree] [X].
  Arguments _observe {A}.
  Arguments go {A}.

  Notation ptree' A := (ptreeF A (ptree A)).

  Definition observe {A} (t : ptree A) : ptree' A := @_observe A t.

  
End PTree.