Require Import interfaces.Category.
Require Import oalts.AsyncEvents.
Require Import oalts.Sig.
Require Import oalts.PTree.

Module ALTS. (* <: Category. *)
  Import AsyncEvents.  
  Import Sig.
  Import PTree.

  Record ALTS {A : sig} := {
    states : Type;
    trans : states -> [A^- + A^+] -> states -> Prop;
  }.
  Arguments ALTS : clear implicits.

  Section Beh.
    Context {A : sig}.
    Variable σ : ALTS A.

    Inductive tau_star : states σ -> states σ -> Prop :=
    | tau_refl : forall s, tau_star s s
    | tau_step : forall s1 s2 s3, 
        trans σ s1 τ s2 -> tau_star s2 s3 -> tau_star s1 s3.

    (* τ* followed by visible step *)
    Definition weak_trans (s : states σ) (ev : A^- + A^+) (s' : states σ) : Prop :=
      exists s'', tau_star s s'' /\ trans σ s'' (vis ev) s'.

    CoFixpoint beh (s : states σ) : ptree A :=
      go (
        StepF 
          (X := { ev : A^- + A^+  &  { s' : states σ | weak_trans s ev s' }})
          (fun x => projT1 x)
          (fun x => beh (proj1_sig (projT2 x)))
      ).
  End Beh.
End ALTS.